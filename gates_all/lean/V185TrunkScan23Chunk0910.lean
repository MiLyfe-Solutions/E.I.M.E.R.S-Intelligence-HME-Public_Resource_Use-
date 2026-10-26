import V185TrunkScan23Chunk0909

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5386424 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 5, 2, 2]
def baseStart_5386424 : Nat := 118140960795 + 5386424 * 2 ^ 59
def prefixEnd_5386424 : Nat := 4983230072969 + 3 ^ 40 * 5386424 * 2
def baseEnd_5386424 : Nat := 2765824520913538825028293

theorem tailTrace_5386424 : CollatzResearch.WordTrace tailWord_5386424 prefixEnd_5386424 2765824520913538825028293 := by
  unfold tailWord_5386424
  simp only [CollatzResearch.WordTrace]
  refine ⟨98229511518956625412551163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130972682025275500550068217 98229511518956625412551163)
  ·
    refine ⟨147344267278434938118826745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98229511518956625412551163 147344267278434938118826745)
    ·
      refine ⟨110508200458826203589120059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147344267278434938118826745 110508200458826203589120059)
      ·
        refine ⟨165762300688239305383680089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110508200458826203589120059 165762300688239305383680089)
        ·
          refine ⟨124321725516179479037760067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165762300688239305383680089 124321725516179479037760067)
          ·
            refine ⟨186482588274269218556640101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124321725516179479037760067 186482588274269218556640101)
            ·
              refine ⟨34965485301425478479370019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186482588274269218556640101 34965485301425478479370019)
              ·
                refine ⟨52448227952138217719055029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34965485301425478479370019 52448227952138217719055029)
                ·
                  refine ⟨4917021370512957911161409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52448227952138217719055029 4917021370512957911161409)
                  ·
                    refine ⟨3687766027884718433371057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4917021370512957911161409 3687766027884718433371057)
                    ·
                      refine ⟨2765824520913538825028293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3687766027884718433371057 2765824520913538825028293)
                      ·
                        rfl

theorem cell23_5386424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 5, 2, 2].length) (baseStart_5386424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386424 prefixEnd_5386424 := by exact prefixLift 5386424
  have htrace : WordTrace (prefixWord ++ tailWord_5386424) baseStart_5386424 baseEnd_5386424 := by
    simpa [prefixWord, tailWord_5386424, baseEnd_5386424] using wordTrace_append hprefix tailTrace_5386424
  have hstable : (prefixWord ++ tailWord_5386424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386424).length < 2 ^ (prefixWord ++ tailWord_5386424).sum := by decide
  have hdescent : baseEnd_5386424 < baseStart_5386424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386427 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 3]
def baseStart_5386427 : Nat := 118140960795 + 5386427 * 2 ^ 59
def prefixEnd_5386427 : Nat := 4983230072969 + 3 ^ 40 * 5386427 * 2
def baseEnd_5386427 : Nat := 2765826061355502313290779

theorem tailTrace_5386427 : CollatzResearch.WordTrace tailWord_5386427 prefixEnd_5386427 2765826061355502313290779 := by
  unfold tailWord_5386427
  simp only [CollatzResearch.WordTrace]
  refine ⟨196459132456902382337461535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130972754971268254891641023 196459132456902382337461535)
  ·
    refine ⟨294688698685353573506192303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196459132456902382337461535 294688698685353573506192303)
    ·
      refine ⟨442033048028030360259288455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294688698685353573506192303 442033048028030360259288455)
      ·
        refine ⟨663049572042045540388932683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442033048028030360259288455 663049572042045540388932683)
        ·
          refine ⟨994574358063068310583399025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663049572042045540388932683 994574358063068310583399025)
          ·
            refine ⟨745930768547301232937549269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 994574358063068310583399025 745930768547301232937549269)
            ·
              refine ⟨17482752387827372646973811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 745930768547301232937549269 17482752387827372646973811)
              ·
                refine ⟨26224128581741058970460717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17482752387827372646973811 26224128581741058970460717)
                ·
                  refine ⟨9834048218152897113922769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26224128581741058970460717 9834048218152897113922769)
                  ·
                    refine ⟨7375536163614672835442077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9834048218152897113922769 7375536163614672835442077)
                    ·
                      refine ⟨2765826061355502313290779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7375536163614672835442077 2765826061355502313290779)
                      ·
                        rfl

theorem cell23_5386427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 3].length) (baseStart_5386427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386427 prefixEnd_5386427 := by exact prefixLift 5386427
  have htrace : WordTrace (prefixWord ++ tailWord_5386427) baseStart_5386427 baseEnd_5386427 := by
    simpa [prefixWord, tailWord_5386427, baseEnd_5386427] using wordTrace_append hprefix tailTrace_5386427
  have hstable : (prefixWord ++ tailWord_5386427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386427).length < 2 ^ (prefixWord ++ tailWord_5386427).sum := by decide
  have hdescent : baseEnd_5386427 < baseStart_5386427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386474 : List Nat := [3, 1, 3, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_5386474 : Nat := 118140960795 + 5386474 * 2 ^ 59
def prefixEnd_5386474 : Nat := 4983230072969 + 3 ^ 40 * 5386474 * 2
def baseEnd_5386474 : Nat := 2765850194946263629403063

theorem tailTrace_5386474 : CollatzResearch.WordTrace tailWord_5386474 prefixEnd_5386474 2765850194946263629403063 := by
  unfold tailWord_5386474
  simp only [CollatzResearch.WordTrace]
  refine ⟨49115211671933027341105619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130973897791821406242948317 49115211671933027341105619)
  ·
    refine ⟨73672817507899541011658429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49115211671933027341105619 73672817507899541011658429)
    ·
      refine ⟨27627306565462327879371911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73672817507899541011658429 27627306565462327879371911)
      ·
        refine ⟨41440959848193491819057867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27627306565462327879371911 41440959848193491819057867)
        ·
          refine ⟨62161439772290237728586801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41440959848193491819057867 62161439772290237728586801)
          ·
            refine ⟨46621079829217678296440101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62161439772290237728586801 46621079829217678296440101)
            ·
              refine ⟨8741452467978314680582519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46621079829217678296440101 8741452467978314680582519)
              ·
                refine ⟨13112178701967472020873779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8741452467978314680582519 13112178701967472020873779)
                ·
                  refine ⟨19668268052951208031310669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13112178701967472020873779 19668268052951208031310669)
                  ·
                    refine ⟨7375600519856703011741501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19668268052951208031310669 7375600519856703011741501)
                    ·
                      refine ⟨2765850194946263629403063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7375600519856703011741501 2765850194946263629403063)
                      ·
                        rfl

theorem cell23_5386474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_5386474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386474 prefixEnd_5386474 := by exact prefixLift 5386474
  have htrace : WordTrace (prefixWord ++ tailWord_5386474) baseStart_5386474 baseEnd_5386474 := by
    simpa [prefixWord, tailWord_5386474, baseEnd_5386474] using wordTrace_append hprefix tailTrace_5386474
  have hstable : (prefixWord ++ tailWord_5386474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386474).length < 2 ^ (prefixWord ++ tailWord_5386474).sum := by decide
  have hdescent : baseEnd_5386474 < baseStart_5386474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386517 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 1, 6, 3]
def baseStart_5386517 : Nat := 118140960795 + 5386517 * 2 ^ 59
def prefixEnd_5386517 : Nat := 4983230072969 + 3 ^ 40 * 5386517 * 2
def baseEnd_5386517 : Nat := 2765872274614406961165365

theorem tailTrace_5386517 : CollatzResearch.WordTrace tailWord_5386517 prefixEnd_5386517 2765872274614406961165365 := by
  unfold tailWord_5386517
  simp only [CollatzResearch.WordTrace]
  refine ⟨196462415026576327708237805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130974943351050885138825203 196462415026576327708237805)
  ·
    refine ⟨73673405634966122890589177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196462415026576327708237805 73673405634966122890589177)
    ·
      refine ⟨55255054226224592167941883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73673405634966122890589177 55255054226224592167941883)
      ·
        refine ⟨82882581339336888251912825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55255054226224592167941883 82882581339336888251912825)
        ·
          refine ⟨62161936004502666188934619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82882581339336888251912825 62161936004502666188934619)
          ·
            refine ⟨93242904006753999283401929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62161936004502666188934619 93242904006753999283401929)
            ·
              refine ⟨69932178005065499462551447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93242904006753999283401929 69932178005065499462551447)
              ·
                refine ⟨104898267007598249193827171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69932178005065499462551447 104898267007598249193827171)
                ·
                  refine ⟨157347400511397373790740757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104898267007598249193827171 157347400511397373790740757)
                  ·
                    refine ⟨7375659398971751896440973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 157347400511397373790740757 7375659398971751896440973)
                    ·
                      refine ⟨2765872274614406961165365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7375659398971751896440973 2765872274614406961165365)
                      ·
                        rfl

theorem cell23_5386517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_5386517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386517 prefixEnd_5386517 := by exact prefixLift 5386517
  have htrace : WordTrace (prefixWord ++ tailWord_5386517) baseStart_5386517 baseEnd_5386517 := by
    simpa [prefixWord, tailWord_5386517, baseEnd_5386517] using wordTrace_append hprefix tailTrace_5386517
  have hstable : (prefixWord ++ tailWord_5386517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386517).length < 2 ^ (prefixWord ++ tailWord_5386517).sum := by decide
  have hdescent : baseEnd_5386517 < baseStart_5386517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386525 : List Nat := [1, 4, 2, 3, 2, 1, 3, 1, 2, 1, 3]
def baseStart_5386525 : Nat := 118140960795 + 5386525 * 2 ^ 59
def prefixEnd_5386525 : Nat := 4983230072969 + 3 ^ 40 * 5386525 * 2
def baseEnd_5386525 : Nat := 2765876382459642929865329

theorem tailTrace_5386525 : CollatzResearch.WordTrace tailWord_5386525 prefixEnd_5386525 2765876382459642929865329 := by
  unfold tailWord_5386525
  simp only [CollatzResearch.WordTrace]
  refine ⟨196462706810547345074529029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130975137873698230049686019 196462706810547345074529029)
  ·
    refine ⟨36836757526977627201474193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196462706810547345074529029 36836757526977627201474193)
    ·
      refine ⟨27627568145233220401105645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36836757526977627201474193 27627568145233220401105645)
      ·
        refine ⟨10360338054462457650414617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27627568145233220401105645 10360338054462457650414617)
        ·
          refine ⟨7770253540846843237810963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10360338054462457650414617 7770253540846843237810963)
          ·
            refine ⟨11655380311270264856716445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7770253540846843237810963 11655380311270264856716445)
            ·
              refine ⟨4370767616726349321268667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11655380311270264856716445 4370767616726349321268667)
              ·
                refine ⟨6556151425089523981903001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4370767616726349321268667 6556151425089523981903001)
                ·
                  refine ⟨4917113568817142986427251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6556151425089523981903001 4917113568817142986427251)
                  ·
                    refine ⟨7375670353225714479640877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4917113568817142986427251 7375670353225714479640877)
                    ·
                      refine ⟨2765876382459642929865329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7375670353225714479640877 2765876382459642929865329)
                      ·
                        rfl

theorem cell23_5386525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_5386525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386525 prefixEnd_5386525 := by exact prefixLift 5386525
  have htrace : WordTrace (prefixWord ++ tailWord_5386525) baseStart_5386525 baseEnd_5386525 := by
    simpa [prefixWord, tailWord_5386525, baseEnd_5386525] using wordTrace_append hprefix tailTrace_5386525
  have hstable : (prefixWord ++ tailWord_5386525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386525).length < 2 ^ (prefixWord ++ tailWord_5386525).sum := by decide
  have hdescent : baseEnd_5386525 < baseStart_5386525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386548 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_5386548 : Nat := 118140960795 + 5386548 * 2 ^ 59
def prefixEnd_5386548 : Nat := 4983230072969 + 3 ^ 40 * 5386548 * 2
def baseEnd_5386548 : Nat := 2765888192514696339877723

theorem tailTrace_5386548 : CollatzResearch.WordTrace tailWord_5386548 prefixEnd_5386548 2765888192514696339877723 := by
  unfold tailWord_5386548
  simp only [CollatzResearch.WordTrace]
  refine ⟨98231772844732010001308149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130975697126309346668410865 98231772844732010001308149)
  ·
    refine ⟨9209228704193625937622639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98231772844732010001308149 9209228704193625937622639)
    ·
      refine ⟨13813843056290438906433959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9209228704193625937622639 13813843056290438906433959)
      ·
        refine ⟨20720764584435658359650939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13813843056290438906433959 20720764584435658359650939)
        ·
          refine ⟨31081146876653487539476409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20720764584435658359650939 31081146876653487539476409)
          ·
            refine ⟨23310860157490115654607307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31081146876653487539476409 23310860157490115654607307)
            ·
              refine ⟨34966290236235173481910961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23310860157490115654607307 34966290236235173481910961)
              ·
                refine ⟨26224717677176380111433221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34966290236235173481910961 26224717677176380111433221)
                ·
                  refine ⟨4917134564470571270893729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26224717677176380111433221 4917134564470571270893729)
                  ·
                    refine ⟨3687850923352928453170297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4917134564470571270893729 3687850923352928453170297)
                    ·
                      refine ⟨2765888192514696339877723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3687850923352928453170297 2765888192514696339877723)
                      ·
                        rfl

theorem cell23_5386548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_5386548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386548 prefixEnd_5386548 := by exact prefixLift 5386548
  have htrace : WordTrace (prefixWord ++ tailWord_5386548) baseStart_5386548 baseEnd_5386548 := by
    simpa [prefixWord, tailWord_5386548, baseEnd_5386548] using wordTrace_append hprefix tailTrace_5386548
  have hstable : (prefixWord ++ tailWord_5386548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386548).length < 2 ^ (prefixWord ++ tailWord_5386548).sum := by decide
  have hdescent : baseEnd_5386548 < baseStart_5386548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386577 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 1, 1, 7]
def baseStart_5386577 : Nat := 118140960795 + 5386577 * 2 ^ 59
def prefixEnd_5386577 : Nat := 4983230072969 + 3 ^ 40 * 5386577 * 2
def baseEnd_5386577 : Nat := 2765903083453676726415089

theorem tailTrace_5386577 : CollatzResearch.WordTrace tailWord_5386577 prefixEnd_5386577 2765903083453676726415089 := by
  unfold tailWord_5386577
  simp only [CollatzResearch.WordTrace]
  refine ⟨196464603406358957955421985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130976402270905971970281323 196464603406358957955421985)
  ·
    refine ⟨147348452554769218466566489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196464603406358957955421985 147348452554769218466566489)
    ·
      refine ⟨110511339416076913849924867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147348452554769218466566489 110511339416076913849924867)
      ·
        refine ⟨165767009124115370774887301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110511339416076913849924867 165767009124115370774887301)
        ·
          refine ⟨31081314210771632020291369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165767009124115370774887301 31081314210771632020291369)
          ·
            refine ⟨23310985658078724015218527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31081314210771632020291369 23310985658078724015218527)
            ·
              refine ⟨34966478487118086022827791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23310985658078724015218527 34966478487118086022827791)
              ·
                refine ⟨52449717730677129034241687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34966478487118086022827791 52449717730677129034241687)
                ·
                  refine ⟨78674576596015693551362531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52449717730677129034241687 78674576596015693551362531)
                  ·
                    refine ⟨118011864894023540327043797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78674576596015693551362531 118011864894023540327043797)
                    ·
                      refine ⟨2765903083453676726415089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118011864894023540327043797 2765903083453676726415089)
                      ·
                        rfl

theorem cell23_5386577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_5386577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386577 prefixEnd_5386577 := by exact prefixLift 5386577
  have htrace : WordTrace (prefixWord ++ tailWord_5386577) baseStart_5386577 baseEnd_5386577 := by
    simpa [prefixWord, tailWord_5386577, baseEnd_5386577] using wordTrace_append hprefix tailTrace_5386577
  have hstable : (prefixWord ++ tailWord_5386577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386577).length < 2 ^ (prefixWord ++ tailWord_5386577).sum := by decide
  have hdescent : baseEnd_5386577 < baseStart_5386577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386617 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 2, 1, 6]
def baseStart_5386617 : Nat := 118140960795 + 5386617 * 2 ^ 59
def prefixEnd_5386617 : Nat := 4983230072969 + 3 ^ 40 * 5386617 * 2
def baseEnd_5386617 : Nat := 2765923622679856569914905

theorem tailTrace_5386617 : CollatzResearch.WordTrace tailWord_5386617 prefixEnd_5386617 2765923622679856569914905 := by
  unfold tailWord_5386617
  simp only [CollatzResearch.WordTrace]
  refine ⟨196466062326214044786878105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130977374884142696524585403 196466062326214044786878105)
  ·
    refine ⟨147349546744660533590158579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196466062326214044786878105 147349546744660533590158579)
    ·
      refine ⟨221024320116990800385237869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147349546744660533590158579 221024320116990800385237869)
      ·
        refine ⟨82884120043871550144464201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221024320116990800385237869 82884120043871550144464201)
        ·
          refine ⟨62163090032903662608348151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82884120043871550144464201 62163090032903662608348151)
          ·
            refine ⟨93244635049355493912522227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62163090032903662608348151 93244635049355493912522227)
            ·
              refine ⟨139866952574033240868783341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93244635049355493912522227 139866952574033240868783341)
              ·
                refine ⟨52450107215262465325793753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139866952574033240868783341 52450107215262465325793753)
                ·
                  refine ⟨39337580411446848994345315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52450107215262465325793753 39337580411446848994345315)
                  ·
                    refine ⟨59006370617170273491517973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39337580411446848994345315 59006370617170273491517973)
                    ·
                      refine ⟨2765923622679856569914905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59006370617170273491517973 2765923622679856569914905)
                      ·
                        rfl

theorem cell23_5386617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_5386617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386617 prefixEnd_5386617 := by exact prefixLift 5386617
  have htrace : WordTrace (prefixWord ++ tailWord_5386617) baseStart_5386617 baseEnd_5386617 := by
    simpa [prefixWord, tailWord_5386617, baseEnd_5386617] using wordTrace_append hprefix tailTrace_5386617
  have hstable : (prefixWord ++ tailWord_5386617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386617).length < 2 ^ (prefixWord ++ tailWord_5386617).sum := by decide
  have hdescent : baseEnd_5386617 < baseStart_5386617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386638 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2]
def baseStart_5386638 : Nat := 118140960795 + 5386638 * 2 ^ 59
def prefixEnd_5386638 : Nat := 4983230072969 + 3 ^ 40 * 5386638 * 2
def baseEnd_5386638 : Nat := 2765934405773600987752309

theorem tailTrace_5386638 : CollatzResearch.WordTrace tailWord_5386638 prefixEnd_5386638 2765934405773600987752309 := by
  unfold tailWord_5386638
  simp only [CollatzResearch.WordTrace]
  refine ⟨24558353532392245671674071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130977885506091976915595045 24558353532392245671674071)
  ·
    refine ⟨36837530298588368507511107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24558353532392245671674071 36837530298588368507511107)
    ·
      refine ⟨55256295447882552761266661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36837530298588368507511107 55256295447882552761266661)
      ·
        refine ⟨10360555396477978642737499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55256295447882552761266661 10360555396477978642737499)
        ·
          refine ⟨15540833094716967964106249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10360555396477978642737499 15540833094716967964106249)
          ·
            refine ⟨11655624821037725973079687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15540833094716967964106249 11655624821037725973079687)
            ·
              refine ⟨17483437231556588959619531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11655624821037725973079687 17483437231556588959619531)
              ·
                refine ⟨26225155847334883439429297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17483437231556588959619531 26225155847334883439429297)
                ·
                  refine ⟨19668866885501162579571973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26225155847334883439429297 19668866885501162579571973)
                  ·
                    refine ⟨3687912541031467983669745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19668866885501162579571973 3687912541031467983669745)
                    ·
                      refine ⟨2765934405773600987752309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3687912541031467983669745 2765934405773600987752309)
                      ·
                        rfl

theorem cell23_5386638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_5386638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386638 prefixEnd_5386638 := by exact prefixLift 5386638
  have htrace : WordTrace (prefixWord ++ tailWord_5386638) baseStart_5386638 baseEnd_5386638 := by
    simpa [prefixWord, tailWord_5386638, baseEnd_5386638] using wordTrace_append hprefix tailTrace_5386638
  have hstable : (prefixWord ++ tailWord_5386638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386638).length < 2 ^ (prefixWord ++ tailWord_5386638).sum := by decide
  have hdescent : baseEnd_5386638 < baseStart_5386638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386687 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 2, 10]
def baseStart_5386687 : Nat := 118140960795 + 5386687 * 2 ^ 59
def prefixEnd_5386687 : Nat := 4983230072969 + 3 ^ 40 * 5386687 * 2
def baseEnd_5386687 : Nat := 921986522108557098679861

theorem tailTrace_5386687 : CollatzResearch.WordTrace tailWord_5386687 prefixEnd_5386687 921986522108557098679861 := by
  unfold tailWord_5386687
  simp only [CollatzResearch.WordTrace]
  refine ⟨196468615435960446741926315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130979076957306964494617543 196468615435960446741926315)
  ·
    refine ⟨294702923153940670112889473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196468615435960446741926315 294702923153940670112889473)
    ·
      refine ⟨221027192365455502584667105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294702923153940670112889473 221027192365455502584667105)
      ·
        refine ⟨165770394274091626938500329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221027192365455502584667105 165770394274091626938500329)
        ·
          refine ⟨124327795705568720203875247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165770394274091626938500329 124327795705568720203875247)
          ·
            refine ⟨186491693558353080305812871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124327795705568720203875247 186491693558353080305812871)
            ·
              refine ⟨279737540337529620458719307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186491693558353080305812871 279737540337529620458719307)
              ·
                refine ⟨419606310506294430688078961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279737540337529620458719307 419606310506294430688078961)
                ·
                  refine ⟨314704732879720823016059221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 419606310506294430688078961 314704732879720823016059221)
                  ·
                    refine ⟨921986522108557098679861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 314704732879720823016059221 921986522108557098679861)
                    ·
                      rfl

theorem cell23_5386687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 10].length) (baseStart_5386687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386687 prefixEnd_5386687 := by exact prefixLift 5386687
  have htrace : WordTrace (prefixWord ++ tailWord_5386687) baseStart_5386687 baseEnd_5386687 := by
    simpa [prefixWord, tailWord_5386687, baseEnd_5386687] using wordTrace_append hprefix tailTrace_5386687
  have hstable : (prefixWord ++ tailWord_5386687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386687).length < 2 ^ (prefixWord ++ tailWord_5386687).sum := by decide
  have hdescent : baseEnd_5386687 < baseStart_5386687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386704 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 8, 4]
def baseStart_5386704 : Nat := 118140960795 + 5386704 * 2 ^ 59
def prefixEnd_5386704 : Nat := 4983230072969 + 3 ^ 40 * 5386704 * 2
def baseEnd_5386704 : Nat := 921989431832265909842335

theorem tailTrace_5386704 : CollatzResearch.WordTrace tailWord_5386704 prefixEnd_5386704 921989431832265909842335 := by
  unfold tailWord_5386704
  simp only [CollatzResearch.WordTrace]
  refine ⟨98234617738449429322647583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130979490317932572430196777 98234617738449429322647583)
  ·
    refine ⟨147351926607674143983971375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98234617738449429322647583 147351926607674143983971375)
    ·
      refine ⟨221027889911511215975957063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147351926607674143983971375 221027889911511215975957063)
      ·
        refine ⟨331541834867266823963935595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221027889911511215975957063 331541834867266823963935595)
        ·
          refine ⟨497312752300900235945903393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331541834867266823963935595 497312752300900235945903393)
          ·
            refine ⟨372984564225675176959427545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497312752300900235945903393 372984564225675176959427545)
            ·
              refine ⟨279738423169256382719570659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 372984564225675176959427545 279738423169256382719570659)
              ·
                refine ⟨419607634753884574079355989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279738423169256382719570659 419607634753884574079355989)
                ·
                  refine ⟨4917276969772084852492453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 419607634753884574079355989 4917276969772084852492453)
                  ·
                    refine ⟨921989431832265909842335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4917276969772084852492453 921989431832265909842335)
                    ·
                      rfl

theorem cell23_5386704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 8, 4].length) (baseStart_5386704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386704 prefixEnd_5386704 := by exact prefixLift 5386704
  have htrace : WordTrace (prefixWord ++ tailWord_5386704) baseStart_5386704 baseEnd_5386704 := by
    simpa [prefixWord, tailWord_5386704, baseEnd_5386704] using wordTrace_append hprefix tailTrace_5386704
  have hstable : (prefixWord ++ tailWord_5386704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386704).length < 2 ^ (prefixWord ++ tailWord_5386704).sum := by decide
  have hdescent : baseEnd_5386704 < baseStart_5386704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386708 : List Nat := [2, 4, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_5386708 : Nat := 118140960795 + 5386708 * 2 ^ 59
def prefixEnd_5386708 : Nat := 4983230072969 + 3 ^ 40 * 5386708 * 2
def baseEnd_5386708 : Nat := 921990116473138571292329

theorem tailTrace_5386708 : CollatzResearch.WordTrace tailWord_5386708 prefixEnd_5386708 921990116473138571292329 := by
  unfold tailWord_5386708
  simp only [CollatzResearch.WordTrace]
  refine ⟨98234690684442183664220389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130979587579256244885627185 98234690684442183664220389)
  ·
    refine ⟨18419004503332909437041323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98234690684442183664220389 18419004503332909437041323)
    ·
      refine ⟨27628506754999364155561985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18419004503332909437041323 27628506754999364155561985)
      ·
        refine ⟨20721380066249523116671489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27628506754999364155561985 20721380066249523116671489)
        ·
          refine ⟨15541035049687142337503617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20721380066249523116671489 15541035049687142337503617)
          ·
            refine ⟨11655776287265356753127713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15541035049687142337503617 11655776287265356753127713)
            ·
              refine ⟨8741832215449017564845785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11655776287265356753127713 8741832215449017564845785)
              ·
                refine ⟨6556374161586763173634339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8741832215449017564845785 6556374161586763173634339)
                ·
                  refine ⟨9834561242380144760451509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6556374161586763173634339 9834561242380144760451509)
                  ·
                    refine ⟨921990116473138571292329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9834561242380144760451509 921990116473138571292329)
                    ·
                      rfl

theorem cell23_5386708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_5386708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386708 prefixEnd_5386708 := by exact prefixLift 5386708
  have htrace : WordTrace (prefixWord ++ tailWord_5386708) baseStart_5386708 baseEnd_5386708 := by
    simpa [prefixWord, tailWord_5386708, baseEnd_5386708] using wordTrace_append hprefix tailTrace_5386708
  have hstable : (prefixWord ++ tailWord_5386708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386708).length < 2 ^ (prefixWord ++ tailWord_5386708).sum := by decide
  have hdescent : baseEnd_5386708 < baseStart_5386708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386714 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5]
def baseStart_5386714 : Nat := 118140960795 + 5386714 * 2 ^ 59
def prefixEnd_5386714 : Nat := 4983230072969 + 3 ^ 40 * 5386714 * 2
def baseEnd_5386714 : Nat := 2765973430303342690401959

theorem tailTrace_5386714 : CollatzResearch.WordTrace tailWord_5386714 prefixEnd_5386714 2765973430303342690401959 := by
  unfold tailWord_5386714
  simp only [CollatzResearch.WordTrace]
  refine ⟨49117400051715657588289799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130979733471241753568772797 49117400051715657588289799)
  ·
    refine ⟨73676100077573486382434699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49117400051715657588289799 73676100077573486382434699)
    ·
      refine ⟨110514150116360229573652049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73676100077573486382434699 110514150116360229573652049)
      ·
        refine ⟨82885612587270172180239037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110514150116360229573652049 82885612587270172180239037)
        ·
          refine ⟨31082104720226314567589639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82885612587270172180239037 31082104720226314567589639)
          ·
            refine ⟨46623157080339471851384459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31082104720226314567589639 46623157080339471851384459)
            ·
              refine ⟨69934735620509207777076689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46623157080339471851384459 69934735620509207777076689)
              ·
                refine ⟨52451051715381905832807517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69934735620509207777076689 52451051715381905832807517)
                ·
                  refine ⟨19669144393268214687302819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52451051715381905832807517 19669144393268214687302819)
                  ·
                    refine ⟨29503716589902322030954229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19669144393268214687302819 29503716589902322030954229)
                    ·
                      refine ⟨2765973430303342690401959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29503716589902322030954229 2765973430303342690401959)
                      ·
                        rfl

theorem cell23_5386714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_5386714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386714 prefixEnd_5386714 := by exact prefixLift 5386714
  have htrace : WordTrace (prefixWord ++ tailWord_5386714) baseStart_5386714 baseEnd_5386714 := by
    simpa [prefixWord, tailWord_5386714, baseEnd_5386714] using wordTrace_append hprefix tailTrace_5386714
  have hstable : (prefixWord ++ tailWord_5386714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386714).length < 2 ^ (prefixWord ++ tailWord_5386714).sum := by decide
  have hdescent : baseEnd_5386714 < baseStart_5386714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386731 : List Nat := [1, 1, 1, 1, 2, 3, 3, 5, 1, 2, 3]
def baseStart_5386731 : Nat := 118140960795 + 5386731 * 2 ^ 59
def prefixEnd_5386731 : Nat := 4983230072969 + 3 ^ 40 * 5386731 * 2
def baseEnd_5386731 : Nat := 2765982159474469123889381

theorem tailTrace_5386731 : CollatzResearch.WordTrace tailWord_5386731 prefixEnd_5386731 2765982159474469123889381 := by
  unfold tailWord_5386731
  simp only [CollatzResearch.WordTrace]
  refine ⟨196470220247801042256528047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130980146831867361504352031 196470220247801042256528047)
  ·
    refine ⟨294705330371701563384792071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196470220247801042256528047 294705330371701563384792071)
    ·
      refine ⟨442057995557552345077188107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294705330371701563384792071 442057995557552345077188107)
      ·
        refine ⟨663086993336328517615782161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442057995557552345077188107 663086993336328517615782161)
        ·
          refine ⟨497315245002246388211836621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 663086993336328517615782161 497315245002246388211836621)
          ·
            refine ⟨186493216875842395579438733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 497315245002246388211836621 186493216875842395579438733)
            ·
              refine ⟨69934956328440898342289525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186493216875842395579438733 69934956328440898342289525)
              ·
                refine ⟨6556402155791334219589643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69934956328440898342289525 6556402155791334219589643)
                ·
                  refine ⟨9834603233687001329384465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6556402155791334219589643 9834603233687001329384465)
                  ·
                    refine ⟨7375952425265250997038349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9834603233687001329384465 7375952425265250997038349)
                    ·
                      refine ⟨2765982159474469123889381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7375952425265250997038349 2765982159474469123889381)
                      ·
                        rfl

theorem cell23_5386731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 2, 3].length) (baseStart_5386731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386731 prefixEnd_5386731 := by exact prefixLift 5386731
  have htrace : WordTrace (prefixWord ++ tailWord_5386731) baseStart_5386731 baseEnd_5386731 := by
    simpa [prefixWord, tailWord_5386731, baseEnd_5386731] using wordTrace_append hprefix tailTrace_5386731
  have hstable : (prefixWord ++ tailWord_5386731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386731).length < 2 ^ (prefixWord ++ tailWord_5386731).sum := by decide
  have hdescent : baseEnd_5386731 < baseStart_5386731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386734 : List Nat := [4, 1, 2, 1, 2, 2, 11]
def baseStart_5386734 : Nat := 118140960795 + 5386734 * 2 ^ 59
def prefixEnd_5386734 : Nat := 4983230072969 + 3 ^ 40 * 5386734 * 2
def baseEnd_5386734 : Nat := 34147946912548550767307

theorem tailTrace_5386734 : CollatzResearch.WordTrace tailWord_5386734 prefixEnd_5386734 34147946912548550767307 := by
  unfold tailWord_5386734
  simp only [CollatzResearch.WordTrace]
  refine ⟨24558791208348771721110907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130980219777860115845924837 24558791208348771721110907)
  ·
    refine ⟨36838186812523157581666361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24558791208348771721110907 36838186812523157581666361)
    ·
      refine ⟨27628640109392368186249771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36838186812523157581666361 27628640109392368186249771)
      ·
        refine ⟨41442960164088552279374657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27628640109392368186249771 41442960164088552279374657)
        ·
          refine ⟨31082220123066414209530993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41442960164088552279374657 31082220123066414209530993)
          ·
            refine ⟨23311665092299810657148245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31082220123066414209530993 23311665092299810657148245)
            ·
              refine ⟨34147946912548550767307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23311665092299810657148245 34147946912548550767307)
              ·
                rfl

theorem cell23_5386734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 11].length) (baseStart_5386734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386734 prefixEnd_5386734 := by exact prefixLift 5386734
  have htrace : WordTrace (prefixWord ++ tailWord_5386734) baseStart_5386734 baseEnd_5386734 := by
    simpa [prefixWord, tailWord_5386734, baseEnd_5386734] using wordTrace_append hprefix tailTrace_5386734
  have hstable : (prefixWord ++ tailWord_5386734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386734).length < 2 ^ (prefixWord ++ tailWord_5386734).sum := by decide
  have hdescent : baseEnd_5386734 < baseStart_5386734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386745 : List Nat := [1, 2, 1, 3, 1, 2, 2, 6, 1, 2, 2]
def baseStart_5386745 : Nat := 118140960795 + 5386745 * 2 ^ 59
def prefixEnd_5386745 : Nat := 4983230072969 + 3 ^ 40 * 5386745 * 2
def baseEnd_5386745 : Nat := 2765989348203632069114317

theorem tailTrace_5386745 : CollatzResearch.WordTrace tailWord_5386745 prefixEnd_5386745 2765989348203632069114317 := by
  unfold tailWord_5386745
  simp only [CollatzResearch.WordTrace]
  refine ⟨196470730869750322647537689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130980487246500215098358459 196470730869750322647537689)
  ·
    refine ⟨147353048152312741985653267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196470730869750322647537689 147353048152312741985653267)
    ·
      refine ⟨221029572228469112978479901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147353048152312741985653267 221029572228469112978479901)
      ·
        refine ⟨82886089585675917366929963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221029572228469112978479901 82886089585675917366929963)
        ·
          refine ⟨124329134378513876050394945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82886089585675917366929963 124329134378513876050394945)
          ·
            refine ⟨93246850783885407037796209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124329134378513876050394945 93246850783885407037796209)
            ·
              refine ⟨69935138087914055278347157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93246850783885407037796209 69935138087914055278347157)
              ·
                refine ⟨3278209597870971341172523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69935138087914055278347157 3278209597870971341172523)
                ·
                  refine ⟨4917314396806457011758785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3278209597870971341172523 4917314396806457011758785)
                  ·
                    refine ⟨3687985797604842758819089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4917314396806457011758785 3687985797604842758819089)
                    ·
                      refine ⟨2765989348203632069114317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3687985797604842758819089 2765989348203632069114317)
                      ·
                        rfl

theorem cell23_5386745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 1, 2, 2].length) (baseStart_5386745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386745 prefixEnd_5386745 := by exact prefixLift 5386745
  have htrace : WordTrace (prefixWord ++ tailWord_5386745) baseStart_5386745 baseEnd_5386745 := by
    simpa [prefixWord, tailWord_5386745, baseEnd_5386745] using wordTrace_append hprefix tailTrace_5386745
  have hstable : (prefixWord ++ tailWord_5386745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386745).length < 2 ^ (prefixWord ++ tailWord_5386745).sum := by decide
  have hdescent : baseEnd_5386745 < baseStart_5386745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386761 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 6, 1, 3]
def baseStart_5386761 : Nat := 118140960795 + 5386761 * 2 ^ 59
def prefixEnd_5386761 : Nat := 4983230072969 + 3 ^ 40 * 5386761 * 2
def baseEnd_5386761 : Nat := 2765997563894104006514243

theorem tailTrace_5386761 : CollatzResearch.WordTrace tailWord_5386761 prefixEnd_5386761 2765997563894104006514243 := by
  unfold tailWord_5386761
  simp only [CollatzResearch.WordTrace]
  refine ⟨196471314437692357380120137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130980876291794904920080091 196471314437692357380120137)
  ·
    refine ⟨147353485828269268035090103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196471314437692357380120137 147353485828269268035090103)
    ·
      refine ⟨221030228742403902052635155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147353485828269268035090103 221030228742403902052635155)
      ·
        refine ⟨331545343113605853078952733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221030228742403902052635155 331545343113605853078952733)
        ·
          refine ⟨124329503667602194904607275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 331545343113605853078952733 124329503667602194904607275)
          ·
            refine ⟨186494255501403292356910913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124329503667602194904607275 186494255501403292356910913)
            ·
              refine ⟨139870691626052469267683185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186494255501403292356910913 139870691626052469267683185)
              ·
                refine ⟨104903018719539351950762389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139870691626052469267683185 104903018719539351950762389)
                ·
                  refine ⟨4917329002478407122691987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104903018719539351950762389 4917329002478407122691987)
                  ·
                    refine ⟨7375993503717610684037981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4917329002478407122691987 7375993503717610684037981)
                    ·
                      refine ⟨2765997563894104006514243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7375993503717610684037981 2765997563894104006514243)
                      ·
                        rfl

theorem cell23_5386761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 1, 3].length) (baseStart_5386761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386761 prefixEnd_5386761 := by exact prefixLift 5386761
  have htrace : WordTrace (prefixWord ++ tailWord_5386761) baseStart_5386761 baseEnd_5386761 := by
    simpa [prefixWord, tailWord_5386761, baseEnd_5386761] using wordTrace_append hprefix tailTrace_5386761
  have hstable : (prefixWord ++ tailWord_5386761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386761).length < 2 ^ (prefixWord ++ tailWord_5386761).sum := by decide
  have hdescent : baseEnd_5386761 < baseStart_5386761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386822 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_5386822 : Nat := 118140960795 + 5386822 * 2 ^ 59
def prefixEnd_5386822 : Nat := 4983230072969 + 3 ^ 40 * 5386822 * 2
def baseEnd_5386822 : Nat := 2766028886214028267851463

theorem tailTrace_5386822 : CollatzResearch.WordTrace tailWord_5386822 prefixEnd_5386822 2766028886214028267851463 := by
  unfold tailWord_5386822
  simp only [CollatzResearch.WordTrace]
  refine ⟨6139798102827230149940335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 130982359526980909865393813 6139798102827230149940335)
  ·
    refine ⟨9209697154240845224910503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6139798102827230149940335 9209697154240845224910503)
    ·
      refine ⟨13814545731361267837365755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9209697154240845224910503 13814545731361267837365755)
      ·
        refine ⟨20721818597041901756048633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13814545731361267837365755 20721818597041901756048633)
        ·
          refine ⟨15541363947781426317036475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20721818597041901756048633 15541363947781426317036475)
          ·
            refine ⟨23312045921672139475554713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15541363947781426317036475 23312045921672139475554713)
            ·
              refine ⟨17484034441254104606666035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23312045921672139475554713 17484034441254104606666035)
              ·
                refine ⟨26226051661881156909999053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17484034441254104606666035 26226051661881156909999053)
                ·
                  refine ⟨9834769373205433841249645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26226051661881156909999053 9834769373205433841249645)
                  ·
                    refine ⟨3688038514952037690468617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9834769373205433841249645 3688038514952037690468617)
                    ·
                      refine ⟨2766028886214028267851463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3688038514952037690468617 2766028886214028267851463)
                      ·
                        rfl

theorem cell23_5386822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_5386822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386822 prefixEnd_5386822 := by exact prefixLift 5386822
  have htrace : WordTrace (prefixWord ++ tailWord_5386822) baseStart_5386822 baseEnd_5386822 := by
    simpa [prefixWord, tailWord_5386822, baseEnd_5386822] using wordTrace_append hprefix tailTrace_5386822
  have hstable : (prefixWord ++ tailWord_5386822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386822).length < 2 ^ (prefixWord ++ tailWord_5386822).sum := by decide
  have hdescent : baseEnd_5386822 < baseStart_5386822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386851 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 3]
def baseStart_5386851 : Nat := 118140960795 + 5386851 * 2 ^ 59
def prefixEnd_5386851 : Nat := 4983230072969 + 3 ^ 40 * 5386851 * 2
def baseEnd_5386851 : Nat := 2766043777153008654388829

theorem tailTrace_5386851 : CollatzResearch.WordTrace tailWord_5386851 prefixEnd_5386851 2766043777153008654388829 := by
  unfold tailWord_5386851
  simp only [CollatzResearch.WordTrace]
  refine ⟨196474597007366302750896407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130983064671577535167264271 196474597007366302750896407)
  ·
    refine ⟨294711895511049454126344611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196474597007366302750896407 294711895511049454126344611)
    ·
      refine ⟨442067843266574181189516917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294711895511049454126344611 442067843266574181189516917)
      ·
        refine ⟨41443860306241329486517211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 442067843266574181189516917 41443860306241329486517211)
        ·
          refine ⟨62165790459361994229775817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41443860306241329486517211 62165790459361994229775817)
          ·
            refine ⟨46624342844521495672331863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62165790459361994229775817 46624342844521495672331863)
            ·
              refine ⟨69936514266782243508497795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46624342844521495672331863 69936514266782243508497795)
              ·
                refine ⟨104904771400173365262746693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69936514266782243508497795 104904771400173365262746693)
                ·
                  refine ⟨19669644637532505986765005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104904771400173365262746693 19669644637532505986765005)
                  ·
                    refine ⟨7376116739074689745036877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19669644637532505986765005 7376116739074689745036877)
                    ·
                      refine ⟨2766043777153008654388829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7376116739074689745036877 2766043777153008654388829)
                      ·
                        rfl

theorem cell23_5386851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_5386851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386851 prefixEnd_5386851 := by exact prefixLift 5386851
  have htrace : WordTrace (prefixWord ++ tailWord_5386851) baseStart_5386851 baseEnd_5386851 := by
    simpa [prefixWord, tailWord_5386851, baseEnd_5386851] using wordTrace_append hprefix tailTrace_5386851
  have hstable : (prefixWord ++ tailWord_5386851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386851).length < 2 ^ (prefixWord ++ tailWord_5386851).sum := by decide
  have hdescent : baseEnd_5386851 < baseStart_5386851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386858 : List Nat := [3, 1, 3, 2, 1, 1, 1, 6, 5]
def baseStart_5386858 : Nat := 118140960795 + 5386858 * 2 ^ 59
def prefixEnd_5386858 : Nat := 4983230072969 + 3 ^ 40 * 5386858 * 2
def baseEnd_5386858 : Nat := 307338596835287791889033

theorem tailTrace_5386858 : CollatzResearch.WordTrace tailWord_5386858 prefixEnd_5386858 307338596835287791889033 := by
  unfold tailWord_5386858
  simp only [CollatzResearch.WordTrace]
  refine ⟨49118713079585235736600307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130983234878893961964267485 49118713079585235736600307)
  ·
    refine ⟨73678069619377853604900461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49118713079585235736600307 73678069619377853604900461)
    ·
      refine ⟨27629276107266695101837673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73678069619377853604900461 27629276107266695101837673)
      ·
        refine ⟨20721957080450021326378255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27629276107266695101837673 20721957080450021326378255)
        ·
          refine ⟨31082935620675031989567383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20721957080450021326378255 31082935620675031989567383)
          ·
            refine ⟨46624403431012547984351075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31082935620675031989567383 46624403431012547984351075)
            ·
              refine ⟨69936605146518821976526613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46624403431012547984351075 69936605146518821976526613)
              ·
                refine ⟨3278278366243069780149685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69936605146518821976526613 3278278366243069780149685)
                ·
                  refine ⟨307338596835287791889033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3278278366243069780149685 307338596835287791889033)
                  ·
                    rfl

theorem cell23_5386858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 5].length) (baseStart_5386858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386858 prefixEnd_5386858 := by exact prefixLift 5386858
  have htrace : WordTrace (prefixWord ++ tailWord_5386858) baseStart_5386858 baseEnd_5386858 := by
    simpa [prefixWord, tailWord_5386858, baseEnd_5386858] using wordTrace_append hprefix tailTrace_5386858
  have hstable : (prefixWord ++ tailWord_5386858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386858).length < 2 ^ (prefixWord ++ tailWord_5386858).sum := by decide
  have hdescent : baseEnd_5386858 < baseStart_5386858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386869 : List Nat := [1, 3, 4, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_5386869 : Nat := 118140960795 + 5386869 * 2 ^ 59
def prefixEnd_5386869 : Nat := 4983230072969 + 3 ^ 40 * 5386869 * 2
def baseEnd_5386869 : Nat := 2766053019804789583963747

theorem tailTrace_5386869 : CollatzResearch.WordTrace tailWord_5386869 prefixEnd_5386869 2766053019804789583963747 := by
  unfold tailWord_5386869
  simp only [CollatzResearch.WordTrace]
  refine ⟨196475253521301091825051661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130983502347534061216701107 196475253521301091825051661)
  ·
    refine ⟨73678220070487909434394373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196475253521301091825051661 73678220070487909434394373)
    ·
      refine ⟨13814666263216483018948945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73678220070487909434394373 13814666263216483018948945)
      ·
        refine ⟨10360999697412362264211709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13814666263216483018948945 10360999697412362264211709)
        ·
          refine ⟨3885374886529635849079391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10360999697412362264211709 3885374886529635849079391)
          ·
            refine ⟨5828062329794453773619087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3885374886529635849079391 5828062329794453773619087)
            ·
              refine ⟨8742093494691680660428631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5828062329794453773619087 8742093494691680660428631)
              ·
                refine ⟨13113140242037520990642947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8742093494691680660428631 13113140242037520990642947)
                ·
                  refine ⟨19669710363056281485964421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13113140242037520990642947 19669710363056281485964421)
                  ·
                    refine ⟨3688070693073052778618329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19669710363056281485964421 3688070693073052778618329)
                    ·
                      refine ⟨2766053019804789583963747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3688070693073052778618329 2766053019804789583963747)
                      ·
                        rfl

theorem cell23_5386869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_5386869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386869 prefixEnd_5386869 := by exact prefixLift 5386869
  have htrace : WordTrace (prefixWord ++ tailWord_5386869) baseStart_5386869 baseEnd_5386869 := by
    simpa [prefixWord, tailWord_5386869, baseEnd_5386869] using wordTrace_append hprefix tailTrace_5386869
  have hstable : (prefixWord ++ tailWord_5386869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386869).length < 2 ^ (prefixWord ++ tailWord_5386869).sum := by decide
  have hdescent : baseEnd_5386869 < baseStart_5386869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386908 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_5386908 : Nat := 118140960795 + 5386908 * 2 ^ 59
def prefixEnd_5386908 : Nat := 4983230072969 + 3 ^ 40 * 5386908 * 2
def baseEnd_5386908 : Nat := 2766073045550314931376067

theorem tailTrace_5386908 : CollatzResearch.WordTrace tailWord_5386908 prefixEnd_5386908 2766073045550314931376067 := by
  unfold tailWord_5386908
  simp only [CollatzResearch.WordTrace]
  refine ⟨98238337984079900742860689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130984450645439867657147585 98238337984079900742860689)
  ·
    refine ⟨73678753488059925557145517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98238337984079900742860689 73678753488059925557145517)
    ·
      refine ⟨27629532558022472083929569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73678753488059925557145517 27629532558022472083929569)
      ·
        refine ⟨20722149418516854062947177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27629532558022472083929569 20722149418516854062947177)
        ·
          refine ⟨15541612063887640547210383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20722149418516854062947177 15541612063887640547210383)
          ·
            refine ⟨23312418095831460820815575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15541612063887640547210383 23312418095831460820815575)
            ·
              refine ⟨34968627143747191231223363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23312418095831460820815575 34968627143747191231223363)
              ·
                refine ⟨52452940715620786846835045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34968627143747191231223363 52452940715620786846835045)
                ·
                  refine ⟨9834926384178897533781571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52452940715620786846835045 9834926384178897533781571)
                  ·
                    refine ⟨14752389576268346300672357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9834926384178897533781571 14752389576268346300672357)
                    ·
                      refine ⟨2766073045550314931376067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14752389576268346300672357 2766073045550314931376067)
                      ·
                        rfl

theorem cell23_5386908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_5386908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386908 prefixEnd_5386908 := by exact prefixLift 5386908
  have htrace : WordTrace (prefixWord ++ tailWord_5386908) baseStart_5386908 baseEnd_5386908 := by
    simpa [prefixWord, tailWord_5386908, baseEnd_5386908] using wordTrace_append hprefix tailTrace_5386908
  have hstable : (prefixWord ++ tailWord_5386908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386908).length < 2 ^ (prefixWord ++ tailWord_5386908).sum := by decide
  have hdescent : baseEnd_5386908 < baseStart_5386908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386996 : List Nat := [2, 6, 1, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_5386996 : Nat := 118140960795 + 5386996 * 2 ^ 59
def prefixEnd_5386996 : Nat := 4983230072969 + 3 ^ 40 * 5386996 * 2
def baseEnd_5386996 : Nat := 2766118231847910587075663

theorem tailTrace_5386996 : CollatzResearch.WordTrace tailWord_5386996 prefixEnd_5386996 2766118231847910587075663 := by
  unfold tailWord_5386996
  simp only [CollatzResearch.WordTrace]
  refine ⟨98239942795920496257462421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130986590394560661676616561 98239942795920496257462421)
  ·
    refine ⟨4604997318558773262068551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 98239942795920496257462421 4604997318558773262068551)
    ·
      refine ⟨6907495977838159893102827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4604997318558773262068551 6907495977838159893102827)
      ·
        refine ⟨10361243966757239839654241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6907495977838159893102827 10361243966757239839654241)
        ·
          refine ⟨7770932975067929879740681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10361243966757239839654241 7770932975067929879740681)
          ·
            refine ⟨5828199731300947409805511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7770932975067929879740681 5828199731300947409805511)
            ·
              refine ⟨8742299596951421114708267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5828199731300947409805511 8742299596951421114708267)
              ·
                refine ⟨13113449395427131672062401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8742299596951421114708267 13113449395427131672062401)
                ·
                  refine ⟨9835087046570348754046801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13113449395427131672062401 9835087046570348754046801)
                  ·
                    refine ⟨7376315284927761565535101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9835087046570348754046801 7376315284927761565535101)
                    ·
                      refine ⟨2766118231847910587075663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7376315284927761565535101 2766118231847910587075663)
                      ·
                        rfl

theorem cell23_5386996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_5386996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386996 prefixEnd_5386996 := by exact prefixLift 5386996
  have htrace : WordTrace (prefixWord ++ tailWord_5386996) baseStart_5386996 baseEnd_5386996 := by
    simpa [prefixWord, tailWord_5386996, baseEnd_5386996] using wordTrace_append hprefix tailTrace_5386996
  have hstable : (prefixWord ++ tailWord_5386996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386996).length < 2 ^ (prefixWord ++ tailWord_5386996).sum := by decide
  have hdescent : baseEnd_5386996 < baseStart_5386996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387011 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 6]
def baseStart_5387011 : Nat := 118140960795 + 5387011 * 2 ^ 59
def prefixEnd_5387011 : Nat := 4983230072969 + 3 ^ 40 * 5387011 * 2
def baseEnd_5387011 : Nat := 2766125934057728028388093

theorem tailTrace_5387011 : CollatzResearch.WordTrace tailWord_5387011 prefixEnd_5387011 2766125934057728028388093 := by
  unfold tailWord_5387011
  simp only [CollatzResearch.WordTrace]
  refine ⟨196480432686786650076720887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130986955124524433384480591 196480432686786650076720887)
  ·
    refine ⟨294720649030179975115081331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196480432686786650076720887 294720649030179975115081331)
    ·
      refine ⟨442080973545269962672621997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294720649030179975115081331 442080973545269962672621997)
      ·
        refine ⟨165780365079476236002233249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 442080973545269962672621997 165780365079476236002233249)
        ·
          refine ⟨124335273809607177001674937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165780365079476236002233249 124335273809607177001674937)
          ·
            refine ⟨93251455357205382751256203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124335273809607177001674937 93251455357205382751256203)
            ·
              refine ⟨139877183035808074126884305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93251455357205382751256203 139877183035808074126884305)
              ·
                refine ⟨104907887276856055595163229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139877183035808074126884305 104907887276856055595163229)
                ·
                  refine ⟨39340457728821020848186211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104907887276856055595163229 39340457728821020848186211)
                  ·
                    refine ⟨59010686593231531272279317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39340457728821020848186211 59010686593231531272279317)
                    ·
                      refine ⟨2766125934057728028388093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59010686593231531272279317 2766125934057728028388093)
                      ·
                        rfl

theorem cell23_5387011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_5387011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387011 prefixEnd_5387011 := by exact prefixLift 5387011
  have htrace : WordTrace (prefixWord ++ tailWord_5387011) baseStart_5387011 baseEnd_5387011 := by
    simpa [prefixWord, tailWord_5387011, baseEnd_5387011] using wordTrace_append hprefix tailTrace_5387011
  have hstable : (prefixWord ++ tailWord_5387011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387011).length < 2 ^ (prefixWord ++ tailWord_5387011).sum := by decide
  have hdescent : baseEnd_5387011 < baseStart_5387011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387018 : List Nat := [3, 1, 2, 2, 1, 2, 2, 3, 1, 1, 5]
def baseStart_5387018 : Nat := 118140960795 + 5387018 * 2 ^ 59
def prefixEnd_5387018 : Nat := 4983230072969 + 3 ^ 40 * 5387018 * 2
def baseEnd_5387018 : Nat := 2766129528422309501000561

theorem tailTrace_5387018 : CollatzResearch.WordTrace tailWord_5387018 prefixEnd_5387018 2766129528422309501000561 := by
  unfold tailWord_5387018
  simp only [CollatzResearch.WordTrace]
  refine ⟨49120171999440322568056427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130987125331840860181483805 49120171999440322568056427)
  ·
    refine ⟨73680257999160483852084641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49120171999440322568056427 73680257999160483852084641)
    ·
      refine ⟨55260193499370362889063481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73680257999160483852084641 55260193499370362889063481)
      ·
        refine ⟨41445145124527772166797611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55260193499370362889063481 41445145124527772166797611)
        ·
          refine ⟨62167717686791658250196417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41445145124527772166797611 62167717686791658250196417)
          ·
            refine ⟨46625788265093743687647313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62167717686791658250196417 46625788265093743687647313)
            ·
              refine ⟨34969341198820307765735485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46625788265093743687647313 34969341198820307765735485)
              ·
                refine ⟨13113502949557615412150807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34969341198820307765735485 13113502949557615412150807)
                ·
                  refine ⟨19670254424336423118226211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13113502949557615412150807 19670254424336423118226211)
                  ·
                    refine ⟨29505381636504634677339317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19670254424336423118226211 29505381636504634677339317)
                    ·
                      refine ⟨2766129528422309501000561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29505381636504634677339317 2766129528422309501000561)
                      ·
                        rfl

theorem cell23_5387018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_5387018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387018 prefixEnd_5387018 := by exact prefixLift 5387018
  have htrace : WordTrace (prefixWord ++ tailWord_5387018) baseStart_5387018 baseEnd_5387018 := by
    simpa [prefixWord, tailWord_5387018, baseEnd_5387018] using wordTrace_append hprefix tailTrace_5387018
  have hstable : (prefixWord ++ tailWord_5387018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387018).length < 2 ^ (prefixWord ++ tailWord_5387018).sum := by decide
  have hdescent : baseEnd_5387018 < baseStart_5387018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387025 : List Nat := [1, 2, 2, 1, 1, 3, 5, 2, 2, 4]
def baseStart_5387025 : Nat := 118140960795 + 5387025 * 2 ^ 59
def prefixEnd_5387025 : Nat := 4983230072969 + 3 ^ 40 * 5387025 * 2
def baseEnd_5387025 : Nat := 922044374262296991204343

theorem tailTrace_5387025 : CollatzResearch.WordTrace tailWord_5387025 prefixEnd_5387025 922044374262296991204343 := by
  unfold tailWord_5387025
  simp only [CollatzResearch.WordTrace]
  refine ⟨196480943308735930467730529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130987295539157286978487019 196480943308735930467730529)
  ·
    refine ⟨147360707481551947850797897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196480943308735930467730529 147360707481551947850797897)
    ·
      refine ⟨110520530611163960888098423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147360707481551947850797897 110520530611163960888098423)
      ·
        refine ⟨165780795916745941332147635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110520530611163960888098423 165780795916745941332147635)
        ·
          refine ⟨248671193875118911998221453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165780795916745941332147635 248671193875118911998221453)
          ·
            refine ⟨93251697703169591999333045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248671193875118911998221453 93251697703169591999333045)
            ·
              refine ⟨8742346659672149249937473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93251697703169591999333045 8742346659672149249937473)
              ·
                refine ⟨6556759994754111937453105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8742346659672149249937473 6556759994754111937453105)
                ·
                  refine ⟨4917569996065583953089829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6556759994754111937453105 4917569996065583953089829)
                  ·
                    refine ⟨922044374262296991204343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4917569996065583953089829 922044374262296991204343)
                    ·
                      rfl

theorem cell23_5387025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 4].length) (baseStart_5387025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387025 prefixEnd_5387025 := by exact prefixLift 5387025
  have htrace : WordTrace (prefixWord ++ tailWord_5387025) baseStart_5387025 baseEnd_5387025 := by
    simpa [prefixWord, tailWord_5387025, baseEnd_5387025] using wordTrace_append hprefix tailTrace_5387025
  have hstable : (prefixWord ++ tailWord_5387025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387025).length < 2 ^ (prefixWord ++ tailWord_5387025).sum := by decide
  have hdescent : baseEnd_5387025 < baseStart_5387025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387051 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 4, 7]
def baseStart_5387051 : Nat := 118140960795 + 5387051 * 2 ^ 59
def prefixEnd_5387051 : Nat := 4983230072969 + 3 ^ 40 * 5387051 * 2
def baseEnd_5387051 : Nat := 922048824427969290629303

theorem tailTrace_5387051 : CollatzResearch.WordTrace tailWord_5387051 prefixEnd_5387051 922048824427969290629303 := by
  unfold tailWord_5387051
  simp only [CollatzResearch.WordTrace]
  refine ⟨196481891606641736908177007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130987927737761157938784671 196481891606641736908177007)
  ·
    refine ⟨294722837409962605362265511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196481891606641736908177007 294722837409962605362265511)
    ·
      refine ⟨442084256114943908043398267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294722837409962605362265511 442084256114943908043398267)
      ·
        refine ⟨663126384172415862065097401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442084256114943908043398267 663126384172415862065097401)
        ·
          refine ⟨497344788129311896548823051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 663126384172415862065097401 497344788129311896548823051)
          ·
            refine ⟨746017182193967844823234577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497344788129311896548823051 746017182193967844823234577)
            ·
              refine ⟨559512886645475883617425933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 746017182193967844823234577 559512886645475883617425933)
              ·
                refine ⟨209817332492053456356534725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 559512886645475883617425933 209817332492053456356534725)
                ·
                  refine ⟨39340749842260023066850261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209817332492053456356534725 39340749842260023066850261)
                  ·
                    refine ⟨922048824427969290629303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39340749842260023066850261 922048824427969290629303)
                    ·
                      rfl

theorem cell23_5387051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 7].length) (baseStart_5387051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387051 prefixEnd_5387051 := by exact prefixLift 5387051
  have htrace : WordTrace (prefixWord ++ tailWord_5387051) baseStart_5387051 baseEnd_5387051 := by
    simpa [prefixWord, tailWord_5387051, baseEnd_5387051] using wordTrace_append hprefix tailTrace_5387051
  have hstable : (prefixWord ++ tailWord_5387051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387051).length < 2 ^ (prefixWord ++ tailWord_5387051).sum := by decide
  have hdescent : baseEnd_5387051 < baseStart_5387051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387122 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 6, 2, 2]
def baseStart_5387122 : Nat := 118140960795 + 5387122 * 2 ^ 59
def prefixEnd_5387122 : Nat := 4983230072969 + 3 ^ 40 * 5387122 * 2
def baseEnd_5387122 : Nat := 2766182930410377094100083

theorem tailTrace_5387122 : CollatzResearch.WordTrace tailWord_5387122 prefixEnd_5387122 2766182930410377094100083 := by
  unfold tailWord_5387122
  simp only [CollatzResearch.WordTrace]
  refine ⟨49121120297346129008502905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130989654126256344022674413 49121120297346129008502905)
  ·
    refine ⟨36840840223009596756377179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49121120297346129008502905 36840840223009596756377179)
    ·
      refine ⟨55261260334514395134565769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36840840223009596756377179 55261260334514395134565769)
      ·
        refine ⟨41445945250885796350924327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55261260334514395134565769 41445945250885796350924327)
        ·
          refine ⟨62168917876328694526386491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41445945250885796350924327 62168917876328694526386491)
          ·
            refine ⟨93253376814493041789579737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62168917876328694526386491 93253376814493041789579737)
            ·
              refine ⟨69940032610869781342184803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93253376814493041789579737 69940032610869781342184803)
              ·
                refine ⟨104910048916304672013277205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69940032610869781342184803 104910048916304672013277205)
                ·
                  refine ⟨4917658542951781500622369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104910048916304672013277205 4917658542951781500622369)
                  ·
                    refine ⟨3688243907213836125466777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4917658542951781500622369 3688243907213836125466777)
                    ·
                      refine ⟨2766182930410377094100083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3688243907213836125466777 2766182930410377094100083)
                      ·
                        rfl

theorem cell23_5387122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_5387122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387122 prefixEnd_5387122 := by exact prefixLift 5387122
  have htrace : WordTrace (prefixWord ++ tailWord_5387122) baseStart_5387122 baseEnd_5387122 := by
    simpa [prefixWord, tailWord_5387122, baseEnd_5387122] using wordTrace_append hprefix tailTrace_5387122
  have hstable : (prefixWord ++ tailWord_5387122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387122).length < 2 ^ (prefixWord ++ tailWord_5387122).sum := by decide
  have hdescent : baseEnd_5387122 < baseStart_5387122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387125 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_5387125 : Nat := 118140960795 + 5387125 * 2 ^ 59
def prefixEnd_5387125 : Nat := 4983230072969 + 3 ^ 40 * 5387125 * 2
def baseEnd_5387125 : Nat := 2766184470852340582362569

theorem tailTrace_5387125 : CollatzResearch.WordTrace tailWord_5387125 prefixEnd_5387125 2766184470852340582362569 := by
  unfold tailWord_5387125
  simp only [CollatzResearch.WordTrace]
  refine ⟨196484590608373647546370829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130989727072249098364247219 196484590608373647546370829)
  ·
    refine ⟨73681721478140117829889061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196484590608373647546370829 73681721478140117829889061)
    ·
      refine ⟨13815322777151272093104199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73681721478140117829889061 13815322777151272093104199)
      ·
        refine ⟨20722984165726908139656299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13815322777151272093104199 20722984165726908139656299)
        ·
          refine ⟨31084476248590362209484449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20722984165726908139656299 31084476248590362209484449)
          ·
            refine ⟨23313357186442771657113337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31084476248590362209484449 23313357186442771657113337)
            ·
              refine ⟨17485017889832078742835003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23313357186442771657113337 17485017889832078742835003)
              ·
                refine ⟨26227526834748118114252505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17485017889832078742835003 26227526834748118114252505)
                ·
                  refine ⟨19670645126061088585689379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26227526834748118114252505 19670645126061088585689379)
                  ·
                    refine ⟨29505967689091632878534069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19670645126061088585689379 29505967689091632878534069)
                    ·
                      refine ⟨2766184470852340582362569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29505967689091632878534069 2766184470852340582362569)
                      ·
                        rfl

theorem cell23_5387125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_5387125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387125 prefixEnd_5387125 := by exact prefixLift 5387125
  have htrace : WordTrace (prefixWord ++ tailWord_5387125) baseStart_5387125 baseEnd_5387125 := by
    simpa [prefixWord, tailWord_5387125, baseEnd_5387125] using wordTrace_append hprefix tailTrace_5387125
  have hstable : (prefixWord ++ tailWord_5387125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387125).length < 2 ^ (prefixWord ++ tailWord_5387125).sum := by decide
  have hdescent : baseEnd_5387125 < baseStart_5387125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387139 : List Nat := [1, 1, 1, 3, 4, 1, 4, 2, 2, 2, 2]
def baseStart_5387139 : Nat := 118140960795 + 5387139 * 2 ^ 59
def prefixEnd_5387139 : Nat := 4983230072969 + 3 ^ 40 * 5387139 * 2
def baseEnd_5387139 : Nat := 2766191659581503527587505

theorem tailTrace_5387139 : CollatzResearch.WordTrace tailWord_5387139 prefixEnd_5387139 2766191659581503527587505 := by
  unfold tailWord_5387139
  simp only [CollatzResearch.WordTrace]
  refine ⟨196485101230322927937380471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130990067486881951958253647 196485101230322927937380471)
  ·
    refine ⟨294727651845484391906070707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196485101230322927937380471 294727651845484391906070707)
    ·
      refine ⟨442091477768226587859106061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294727651845484391906070707 442091477768226587859106061)
      ·
        refine ⟨165784304163084970447164773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 442091477768226587859106061 165784304163084970447164773)
        ·
          refine ⟨31084557030578431958843395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165784304163084970447164773 31084557030578431958843395)
          ·
            refine ⟨46626835545867647938265093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31084557030578431958843395 46626835545867647938265093)
            ·
              refine ⟨8742531664850183988424705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46626835545867647938265093 8742531664850183988424705)
              ·
                refine ⟨6556898748637637991318529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8742531664850183988424705 6556898748637637991318529)
                ·
                  refine ⟨4917674061478228493488897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6556898748637637991318529 4917674061478228493488897)
                  ·
                    refine ⟨3688255546108671370116673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4917674061478228493488897 3688255546108671370116673)
                    ·
                      refine ⟨2766191659581503527587505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3688255546108671370116673 2766191659581503527587505)
                      ·
                        rfl

theorem cell23_5387139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 2, 2].length) (baseStart_5387139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387139 prefixEnd_5387139 := by exact prefixLift 5387139
  have htrace : WordTrace (prefixWord ++ tailWord_5387139) baseStart_5387139 baseEnd_5387139 := by
    simpa [prefixWord, tailWord_5387139, baseEnd_5387139] using wordTrace_append hprefix tailTrace_5387139
  have hstable : (prefixWord ++ tailWord_5387139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387139).length < 2 ^ (prefixWord ++ tailWord_5387139).sum := by decide
  have hdescent : baseEnd_5387139 < baseStart_5387139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387168 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 7]
def baseStart_5387168 : Nat := 118140960795 + 5387168 * 2 ^ 59
def prefixEnd_5387168 : Nat := 4983230072969 + 3 ^ 40 * 5387168 * 2
def baseEnd_5387168 : Nat := 2766206550520483914124871

theorem tailTrace_5387168 : CollatzResearch.WordTrace tailWord_5387168 prefixEnd_5387168 2766206550520483914124871 := by
  unfold tailWord_5387168
  simp only [CollatzResearch.WordTrace]
  refine ⟨98243079473608932945093079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130990772631478577260124105 98243079473608932945093079)
  ·
    refine ⟨147364619210413399417639619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98243079473608932945093079 147364619210413399417639619)
    ·
      refine ⟨221046928815620099126459429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147364619210413399417639619 221046928815620099126459429)
      ·
        refine ⟨41446299152928768586211143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221046928815620099126459429 41446299152928768586211143)
        ·
          refine ⟨62169448729393152879316715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41446299152928768586211143 62169448729393152879316715)
          ·
            refine ⟨93254173094089729318975073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62169448729393152879316715 93254173094089729318975073)
            ·
              refine ⟨69940629820567296989231305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93254173094089729318975073 69940629820567296989231305)
              ·
                refine ⟨52455472365425472741923479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69940629820567296989231305 52455472365425472741923479)
                ·
                  refine ⟨78683208548138209112885219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52455472365425472741923479 78683208548138209112885219)
                  ·
                    refine ⟨118024812822207313669327829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78683208548138209112885219 118024812822207313669327829)
                    ·
                      refine ⟨2766206550520483914124871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118024812822207313669327829 2766206550520483914124871)
                      ·
                        rfl

theorem cell23_5387168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_5387168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387168 prefixEnd_5387168 := by exact prefixLift 5387168
  have htrace : WordTrace (prefixWord ++ tailWord_5387168) baseStart_5387168 baseEnd_5387168 := by
    simpa [prefixWord, tailWord_5387168, baseEnd_5387168] using wordTrace_append hprefix tailTrace_5387168
  have hstable : (prefixWord ++ tailWord_5387168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387168).length < 2 ^ (prefixWord ++ tailWord_5387168).sum := by decide
  have hdescent : baseEnd_5387168 < baseStart_5387168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387190 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_5387190 : Nat := 118140960795 + 5387190 * 2 ^ 59
def prefixEnd_5387190 : Nat := 4983230072969 + 3 ^ 40 * 5387190 * 2
def baseEnd_5387190 : Nat := 2766217847094882828049771

theorem tailTrace_5387190 : CollatzResearch.WordTrace tailWord_5387190 prefixEnd_5387190 2766217847094882828049771 := by
  unfold tailWord_5387190
  simp only [CollatzResearch.WordTrace]
  refine ⟨12280435084571135227967939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130991307568758775764991349 12280435084571135227967939)
  ·
    refine ⟨18420652626856702841951909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12280435084571135227967939 18420652626856702841951909)
    ·
      refine ⟨3453872367535631782865983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18420652626856702841951909 3453872367535631782865983)
      ·
        refine ⟨5180808551303447674298975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3453872367535631782865983 5180808551303447674298975)
        ·
          refine ⟨7771212826955171511448463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5180808551303447674298975 7771212826955171511448463)
          ·
            refine ⟨11656819240432757267172695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7771212826955171511448463 11656819240432757267172695)
            ·
              refine ⟨17485228860649135900759043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11656819240432757267172695 17485228860649135900759043)
              ·
                refine ⟨26227843290973703851138565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17485228860649135900759043 26227843290973703851138565)
                ·
                  refine ⟨4917720617057569472088481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26227843290973703851138565 4917720617057569472088481)
                  ·
                    refine ⟨3688290462793177104066361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4917720617057569472088481 3688290462793177104066361)
                    ·
                      refine ⟨2766217847094882828049771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3688290462793177104066361 2766217847094882828049771)
                      ·
                        rfl

theorem cell23_5387190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_5387190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387190 prefixEnd_5387190 := by exact prefixLift 5387190
  have htrace : WordTrace (prefixWord ++ tailWord_5387190) baseStart_5387190 baseEnd_5387190 := by
    simpa [prefixWord, tailWord_5387190, baseEnd_5387190] using wordTrace_append hprefix tailTrace_5387190
  have hstable : (prefixWord ++ tailWord_5387190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387190).length < 2 ^ (prefixWord ++ tailWord_5387190).sum := by decide
  have hdescent : baseEnd_5387190 < baseStart_5387190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387212 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 2, 4, 2]
def baseStart_5387212 : Nat := 118140960795 + 5387212 * 2 ^ 59
def prefixEnd_5387212 : Nat := 4983230072969 + 3 ^ 40 * 5387212 * 2
def baseEnd_5387212 : Nat := 2766229143669281741974669

theorem tailTrace_5387212 : CollatzResearch.WordTrace tailWord_5387212 prefixEnd_5387212 2766229143669281741974669 := by
  unfold tailWord_5387212
  simp only [CollatzResearch.WordTrace]
  refine ⟨98243881879529230702393945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130991842506038974269858593 98243881879529230702393945)
  ·
    refine ⟨73682911409646923026795459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98243881879529230702393945 73682911409646923026795459)
    ·
      refine ⟨110524367114470384540193189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73682911409646923026795459 110524367114470384540193189)
      ·
        refine ⟨20723318833963197101286223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110524367114470384540193189 20723318833963197101286223)
        ·
          refine ⟨31084978250944795651929335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20723318833963197101286223 31084978250944795651929335)
          ·
            refine ⟨46627467376417193477894003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31084978250944795651929335 46627467376417193477894003)
            ·
              refine ⟨69941201064625790216841005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46627467376417193477894003 69941201064625790216841005)
              ·
                refine ⟨26227950399234671331315377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69941201064625790216841005 26227950399234671331315377)
                ·
                  refine ⟨19670962799426003498486533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26227950399234671331315377 19670962799426003498486533)
                  ·
                    refine ⟨3688305524892375655966225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19670962799426003498486533 3688305524892375655966225)
                    ·
                      refine ⟨2766229143669281741974669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3688305524892375655966225 2766229143669281741974669)
                      ·
                        rfl

theorem cell23_5387212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_5387212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387212 prefixEnd_5387212 := by exact prefixLift 5387212
  have htrace : WordTrace (prefixWord ++ tailWord_5387212) baseStart_5387212 baseEnd_5387212 := by
    simpa [prefixWord, tailWord_5387212, baseEnd_5387212] using wordTrace_append hprefix tailTrace_5387212
  have hstable : (prefixWord ++ tailWord_5387212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387212).length < 2 ^ (prefixWord ++ tailWord_5387212).sum := by decide
  have hdescent : baseEnd_5387212 < baseStart_5387212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387215 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 3]
def baseStart_5387215 : Nat := 118140960795 + 5387215 * 2 ^ 59
def prefixEnd_5387215 : Nat := 4983230072969 + 3 ^ 40 * 5387215 * 2
def baseEnd_5387215 : Nat := 2766230684111245230237155

theorem tailTrace_5387215 : CollatzResearch.WordTrace tailWord_5387215 prefixEnd_5387215 2766230684111245230237155 := by
  unfold tailWord_5387215
  simp only [CollatzResearch.WordTrace]
  refine ⟨196487873178047592917147099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130991915452031728611431399 196487873178047592917147099)
  ·
    refine ⟨294731809767071389375720649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196487873178047592917147099 294731809767071389375720649)
    ·
      refine ⟨221048857325303542031790487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294731809767071389375720649 221048857325303542031790487)
      ·
        refine ⟨331573285987955313047685731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221048857325303542031790487 331573285987955313047685731)
        ·
          refine ⟨497359928981932969571528597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331573285987955313047685731 497359928981932969571528597)
          ·
            refine ⟨23313746671028107948665403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 497359928981932969571528597 23313746671028107948665403)
            ·
              refine ⟨34970620006542161922998105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23313746671028107948665403 34970620006542161922998105)
              ·
                refine ⟨26227965004906621442248579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34970620006542161922998105 26227965004906621442248579)
                ·
                  refine ⟨39341947507359932163372869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26227965004906621442248579 39341947507359932163372869)
                  ·
                    refine ⟨7376615157629987280632413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39341947507359932163372869 7376615157629987280632413)
                    ·
                      refine ⟨2766230684111245230237155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7376615157629987280632413 2766230684111245230237155)
                      ·
                        rfl

theorem cell23_5387215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 3].length) (baseStart_5387215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387215 prefixEnd_5387215 := by exact prefixLift 5387215
  have htrace : WordTrace (prefixWord ++ tailWord_5387215) baseStart_5387215 baseEnd_5387215 := by
    simpa [prefixWord, tailWord_5387215, baseEnd_5387215] using wordTrace_append hprefix tailTrace_5387215
  have hstable : (prefixWord ++ tailWord_5387215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387215).length < 2 ^ (prefixWord ++ tailWord_5387215).sum := by decide
  have hdescent : baseEnd_5387215 < baseStart_5387215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387295 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 3, 6]
def baseStart_5387295 : Nat := 118140960795 + 5387295 * 2 ^ 59
def prefixEnd_5387295 : Nat := 4983230072969 + 3 ^ 40 * 5387295 * 2
def baseEnd_5387295 : Nat := 922090587521201639078929

theorem tailTrace_5387295 : CollatzResearch.WordTrace tailWord_5387295 prefixEnd_5387295 922090587521201639078929 := by
  unfold tailWord_5387295
  simp only [CollatzResearch.WordTrace]
  refine ⟨196490791017757766580059339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130993860678505177720039559 196490791017757766580059339)
  ·
    refine ⟨294736186526636649870089009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196490791017757766580059339 294736186526636649870089009)
    ·
      refine ⟨221052139894977487402566757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294736186526636649870089009 221052139894977487402566757)
      ·
        refine ⟨41447276230308278887981267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221052139894977487402566757 41447276230308278887981267)
        ·
          refine ⟨62170914345462418331971901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41447276230308278887981267 62170914345462418331971901)
          ·
            refine ⟨23314092879548406874489463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62170914345462418331971901 23314092879548406874489463)
            ·
              refine ⟨34971139319322610311734195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23314092879548406874489463 34971139319322610311734195)
              ·
                refine ⟨52456708978983915467601293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34971139319322610311734195 52456708978983915467601293)
                ·
                  refine ⟨19671265867118968300350485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52456708978983915467601293 19671265867118968300350485)
                  ·
                    refine ⟨922090587521201639078929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19671265867118968300350485 922090587521201639078929)
                    ·
                      rfl

theorem cell23_5387295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 6].length) (baseStart_5387295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387295 prefixEnd_5387295 := by exact prefixLift 5387295
  have htrace : WordTrace (prefixWord ++ tailWord_5387295) baseStart_5387295 baseEnd_5387295 := by
    simpa [prefixWord, tailWord_5387295, baseEnd_5387295] using wordTrace_append hprefix tailTrace_5387295
  have hstable : (prefixWord ++ tailWord_5387295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387295).length < 2 ^ (prefixWord ++ tailWord_5387295).sum := by decide
  have hdescent : baseEnd_5387295 < baseStart_5387295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387299 : List Nat := [1, 1, 1, 4, 3, 3, 3, 1, 1, 5]
def baseStart_5387299 : Nat := 118140960795 + 5387299 * 2 ^ 59
def prefixEnd_5387299 : Nat := 4983230072969 + 3 ^ 40 * 5387299 * 2
def baseEnd_5387299 : Nat := 922091272162074300528923

theorem tailTrace_5387299 : CollatzResearch.WordTrace tailWord_5387299 prefixEnd_5387299 922091272162074300528923 := by
  unfold tailWord_5387299
  simp only [CollatzResearch.WordTrace]
  refine ⟨196490936909743275263204951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130993957939828850175469967 196490936909743275263204951)
  ·
    refine ⟨294736405364614912894807427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196490936909743275263204951 294736405364614912894807427)
    ·
      refine ⟨442104608046922369342211141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294736405364614912894807427 442104608046922369342211141)
      ·
        refine ⟨82894614008797944251664589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 442104608046922369342211141 82894614008797944251664589)
        ·
          refine ⟨31085480253299229094374221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82894614008797944251664589 31085480253299229094374221)
          ·
            refine ⟨11657055094987210910390333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31085480253299229094374221 11657055094987210910390333)
            ·
              refine ⟨4371395660620204091396375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11657055094987210910390333 4371395660620204091396375)
              ·
                refine ⟨6557093490930306137094563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4371395660620204091396375 6557093490930306137094563)
                ·
                  refine ⟨9835640236395459205641845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6557093490930306137094563 9835640236395459205641845)
                  ·
                    refine ⟨922091272162074300528923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9835640236395459205641845 922091272162074300528923)
                    ·
                      rfl

theorem cell23_5387299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 1, 5].length) (baseStart_5387299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387299 prefixEnd_5387299 := by exact prefixLift 5387299
  have htrace : WordTrace (prefixWord ++ tailWord_5387299) baseStart_5387299 baseEnd_5387299 := by
    simpa [prefixWord, tailWord_5387299, baseEnd_5387299] using wordTrace_append hprefix tailTrace_5387299
  have hstable : (prefixWord ++ tailWord_5387299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387299).length < 2 ^ (prefixWord ++ tailWord_5387299).sum := by decide
  have hdescent : baseEnd_5387299 < baseStart_5387299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387315 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 4]
def baseStart_5387315 : Nat := 118140960795 + 5387315 * 2 ^ 59
def prefixEnd_5387315 : Nat := 4983230072969 + 3 ^ 40 * 5387315 * 2
def baseEnd_5387315 : Nat := 2766282032176694838986695

theorem tailTrace_5387315 : CollatzResearch.WordTrace tailWord_5387315 prefixEnd_5387315 2766282032176694838986695 := by
  unfold tailWord_5387315
  simp only [CollatzResearch.WordTrace]
  refine ⟨196491520477685309995787399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130994346985123539997191599 196491520477685309995787399)
  ·
    refine ⟨294737280716527964993681099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196491520477685309995787399 294737280716527964993681099)
    ·
      refine ⟨442105921074791947490521649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294737280716527964993681099 442105921074791947490521649)
      ·
        refine ⟨331579440806093960617891237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 442105921074791947490521649 331579440806093960617891237)
        ·
          refine ⟨62171145151142617615854607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 331579440806093960617891237 62171145151142617615854607)
          ·
            refine ⟨93256717726713926423781911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62171145151142617615854607 93256717726713926423781911)
            ·
              refine ⟨139885076590070889635672867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93256717726713926423781911 139885076590070889635672867)
              ·
                refine ⟨209827614885106334453509301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139885076590070889635672867 209827614885106334453509301)
                ·
                  refine ⟨19671338895478718855016497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 209827614885106334453509301 19671338895478718855016497)
                  ·
                    refine ⟨14753504171609039141262373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19671338895478718855016497 14753504171609039141262373)
                    ·
                      refine ⟨2766282032176694838986695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14753504171609039141262373 2766282032176694838986695)
                      ·
                        rfl

theorem cell23_5387315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 4].length) (baseStart_5387315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387315 prefixEnd_5387315 := by exact prefixLift 5387315
  have htrace : WordTrace (prefixWord ++ tailWord_5387315) baseStart_5387315 baseEnd_5387315 := by
    simpa [prefixWord, tailWord_5387315, baseEnd_5387315] using wordTrace_append hprefix tailTrace_5387315
  have hstable : (prefixWord ++ tailWord_5387315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387315).length < 2 ^ (prefixWord ++ tailWord_5387315).sum := by decide
  have hdescent : baseEnd_5387315 < baseStart_5387315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387319 : List Nat := [1, 1, 3, 1, 2, 2, 1, 5, 3, 2, 2]
def baseStart_5387319 : Nat := 118140960795 + 5387319 * 2 ^ 59
def prefixEnd_5387319 : Nat := 4983230072969 + 3 ^ 40 * 5387319 * 2
def baseEnd_5387319 : Nat := 2766284086099312823336677

theorem tailTrace_5387319 : CollatzResearch.WordTrace tailWord_5387319 prefixEnd_5387319 2766284086099312823336677 := by
  unfold tailWord_5387319
  simp only [CollatzResearch.WordTrace]
  refine ⟨196491666369670818678933011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130994444246447212452622007 196491666369670818678933011)
  ·
    refine ⟨294737499554506228018399517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196491666369670818678933011 294737499554506228018399517)
    ·
      refine ⟨110526562332939835506899819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294737499554506228018399517 110526562332939835506899819)
      ·
        refine ⟨165789843499409753260349729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110526562332939835506899819 165789843499409753260349729)
        ·
          refine ⟨124342382624557314945262297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165789843499409753260349729 124342382624557314945262297)
          ·
            refine ⟨93256786968417986208946723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124342382624557314945262297 93256786968417986208946723)
            ·
              refine ⟨139885180452626979313420085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93256786968417986208946723 139885180452626979313420085)
              ·
                refine ⟨13114235667433779310633133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139885180452626979313420085 13114235667433779310633133)
                ·
                  refine ⟨4917838375287667241487425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13114235667433779310633133 4917838375287667241487425)
                  ·
                    refine ⟨3688378781465750431115569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4917838375287667241487425 3688378781465750431115569)
                    ·
                      refine ⟨2766284086099312823336677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3688378781465750431115569 2766284086099312823336677)
                      ·
                        rfl

theorem cell23_5387319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 2, 2].length) (baseStart_5387319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387319 prefixEnd_5387319 := by exact prefixLift 5387319
  have htrace : WordTrace (prefixWord ++ tailWord_5387319) baseStart_5387319 baseEnd_5387319 := by
    simpa [prefixWord, tailWord_5387319, baseEnd_5387319] using wordTrace_append hprefix tailTrace_5387319
  have hstable : (prefixWord ++ tailWord_5387319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387319).length < 2 ^ (prefixWord ++ tailWord_5387319).sum := by decide
  have hdescent : baseEnd_5387319 < baseStart_5387319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387322 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3]
def baseStart_5387322 : Nat := 118140960795 + 5387322 * 2 ^ 59
def prefixEnd_5387322 : Nat := 4983230072969 + 3 ^ 40 * 5387322 * 2
def baseEnd_5387322 : Nat := 2766285626541276311599163

theorem tailTrace_5387322 : CollatzResearch.WordTrace tailWord_5387322 prefixEnd_5387322 2766285626541276311599163 := by
  unfold tailWord_5387322
  simp only [CollatzResearch.WordTrace]
  refine ⟨49122943947164987547823055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130994517192439966794194813 49122943947164987547823055)
  ·
    refine ⟨73684415920747481321734583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49122943947164987547823055 73684415920747481321734583)
    ·
      refine ⟨110526623881121221982601875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73684415920747481321734583 110526623881121221982601875)
      ·
        refine ⟨165789935821681832973902813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110526623881121221982601875 165789935821681832973902813)
        ·
          refine ⟨62171225933130687365213555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165789935821681832973902813 62171225933130687365213555)
          ·
            refine ⟨93256838899696031047820333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62171225933130687365213555 93256838899696031047820333)
            ·
              refine ⟨34971314587386011642932625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93256838899696031047820333 34971314587386011642932625)
              ·
                refine ⟨26228485940539508732199469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34971314587386011642932625 26228485940539508732199469)
                ·
                  refine ⟨9835682227702315774574801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26228485940539508732199469 9835682227702315774574801)
                  ·
                    refine ⟨7376761670776736830931101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9835682227702315774574801 7376761670776736830931101)
                    ·
                      refine ⟨2766285626541276311599163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7376761670776736830931101 2766285626541276311599163)
                      ·
                        rfl

theorem cell23_5387322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_5387322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387322 prefixEnd_5387322 := by exact prefixLift 5387322
  have htrace : WordTrace (prefixWord ++ tailWord_5387322) baseStart_5387322 baseEnd_5387322 := by
    simpa [prefixWord, tailWord_5387322, baseEnd_5387322] using wordTrace_append hprefix tailTrace_5387322
  have hstable : (prefixWord ++ tailWord_5387322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387322).length < 2 ^ (prefixWord ++ tailWord_5387322).sum := by decide
  have hdescent : baseEnd_5387322 < baseStart_5387322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387329 : List Nat := [1, 2, 5, 1, 3, 1, 2, 1, 1, 6]
def baseStart_5387329 : Nat := 118140960795 + 5387329 * 2 ^ 59
def prefixEnd_5387329 : Nat := 4983230072969 + 3 ^ 40 * 5387329 * 2
def baseEnd_5387329 : Nat := 922096406968619261403877

theorem tailTrace_5387329 : CollatzResearch.WordTrace tailWord_5387329 prefixEnd_5387329 922096406968619261403877 := by
  unfold tailWord_5387329
  simp only [CollatzResearch.WordTrace]
  refine ⟨196492031099634590386797041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130994687399756393591198027 196492031099634590386797041)
  ·
    refine ⟨147369023324725942790097781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196492031099634590386797041 147369023324725942790097781)
    ·
      refine ⟨13815845936693057136571667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147369023324725942790097781 13815845936693057136571667)
      ·
        refine ⟨20723768905039585704857501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13815845936693057136571667 20723768905039585704857501)
        ·
          refine ⟨7771413339389844639321563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20723768905039585704857501 7771413339389844639321563)
          ·
            refine ⟨11657120009084766958982345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7771413339389844639321563 11657120009084766958982345)
            ·
              refine ⟨8742840006813575219236759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11657120009084766958982345 8742840006813575219236759)
              ·
                refine ⟨13114260010220362828855139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8742840006813575219236759 13114260010220362828855139)
                ·
                  refine ⟨19671390015330544243282709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13114260010220362828855139 19671390015330544243282709)
                  ·
                    refine ⟨922096406968619261403877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19671390015330544243282709 922096406968619261403877)
                    ·
                      rfl

theorem cell23_5387329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_5387329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387329 prefixEnd_5387329 := by exact prefixLift 5387329
  have htrace : WordTrace (prefixWord ++ tailWord_5387329) baseStart_5387329 baseEnd_5387329 := by
    simpa [prefixWord, tailWord_5387329, baseEnd_5387329] using wordTrace_append hprefix tailTrace_5387329
  have hstable : (prefixWord ++ tailWord_5387329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387329).length < 2 ^ (prefixWord ++ tailWord_5387329).sum := by decide
  have hdescent : baseEnd_5387329 < baseStart_5387329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387342 : List Nat := [4, 1, 1, 1, 1, 3, 5, 7]
def baseStart_5387342 : Nat := 118140960795 + 5387342 * 2 ^ 59
def prefixEnd_5387342 : Nat := 4983230072969 + 3 ^ 40 * 5387342 * 2
def baseEnd_5387342 : Nat := 102455403561272823457373

theorem tailTrace_5387342 : CollatzResearch.WordTrace tailWord_5387342 prefixEnd_5387342 102455403561272823457373 := by
  unfold tailWord_5387342
  simp only [CollatzResearch.WordTrace]
  refine ⟨24561563156073436700877535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130995003499058329071346853 24561563156073436700877535)
  ·
    refine ⟨36842344734110155051316303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24561563156073436700877535 36842344734110155051316303)
    ·
      refine ⟨55263517101165232576974455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36842344734110155051316303 55263517101165232576974455)
      ·
        refine ⟨82895275651747848865461683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55263517101165232576974455 82895275651747848865461683)
        ·
          refine ⟨124342913477621773298192525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82895275651747848865461683 124342913477621773298192525)
          ·
            refine ⟨46628592554108164986822197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124342913477621773298192525 46628592554108164986822197)
            ·
              refine ⟨4371430551947640467514581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46628592554108164986822197 4371430551947640467514581)
              ·
                refine ⟨102455403561272823457373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4371430551947640467514581 102455403561272823457373)
                ·
                  rfl

theorem cell23_5387342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 7].length) (baseStart_5387342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387342 prefixEnd_5387342 := by exact prefixLift 5387342
  have htrace : WordTrace (prefixWord ++ tailWord_5387342) baseStart_5387342 baseEnd_5387342 := by
    simpa [prefixWord, tailWord_5387342, baseEnd_5387342] using wordTrace_append hprefix tailTrace_5387342
  have hstable : (prefixWord ++ tailWord_5387342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387342).length < 2 ^ (prefixWord ++ tailWord_5387342).sum := by decide
  have hdescent : baseEnd_5387342 < baseStart_5387342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387350 : List Nat := [5, 2, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_5387350 : Nat := 118140960795 + 5387350 * 2 ^ 59
def prefixEnd_5387350 : Nat := 4983230072969 + 3 ^ 40 * 5387350 * 2
def baseEnd_5387350 : Nat := 922100001333200734016345

theorem tailTrace_5387350 : CollatzResearch.WordTrace tailWord_5387350 prefixEnd_5387350 922100001333200734016345 := by
  unfold tailWord_5387350
  simp only [CollatzResearch.WordTrace]
  refine ⟨12280799814534906935831969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130995198021705673982207669 12280799814534906935831969)
  ·
    refine ⟨9210599860901180201873977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12280799814534906935831969 9210599860901180201873977)
    ·
      refine ⟨6907949895675885151405483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9210599860901180201873977 6907949895675885151405483)
      ·
        refine ⟨10361924843513827727108225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6907949895675885151405483 10361924843513827727108225)
        ·
          refine ⟨7771443632635370795331169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10361924843513827727108225 7771443632635370795331169)
          ·
            refine ⟨5828582724476528096498377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7771443632635370795331169 5828582724476528096498377)
            ·
              refine ⟨4371437043357396072373783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5828582724476528096498377 4371437043357396072373783)
              ·
                refine ⟨6557155565036094108560675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4371437043357396072373783 6557155565036094108560675)
                ·
                  refine ⟨9835733347554141162841013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6557155565036094108560675 9835733347554141162841013)
                  ·
                    refine ⟨922100001333200734016345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9835733347554141162841013 922100001333200734016345)
                    ·
                      rfl

theorem cell23_5387350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_5387350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387350 prefixEnd_5387350 := by exact prefixLift 5387350
  have htrace : WordTrace (prefixWord ++ tailWord_5387350) baseStart_5387350 baseEnd_5387350 := by
    simpa [prefixWord, tailWord_5387350, baseEnd_5387350] using wordTrace_append hprefix tailTrace_5387350
  have hstable : (prefixWord ++ tailWord_5387350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387350).length < 2 ^ (prefixWord ++ tailWord_5387350).sum := by decide
  have hdescent : baseEnd_5387350 < baseStart_5387350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387352 : List Nat := [2, 1, 2, 2, 1, 3, 1, 4, 1, 3, 3]
def baseStart_5387352 : Nat := 118140960795 + 5387352 * 2 ^ 59
def prefixEnd_5387352 : Nat := 4983230072969 + 3 ^ 40 * 5387352 * 2
def baseEnd_5387352 : Nat := 2766301030960911194224025

theorem tailTrace_5387352 : CollatzResearch.WordTrace tailWord_5387352 prefixEnd_5387352 2766301030960911194224025 := by
  unfold tailWord_5387352
  simp only [CollatzResearch.WordTrace]
  refine ⟨98246434989275632657442155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130995246652367510209922873 98246434989275632657442155)
  ·
    refine ⟨147369652483913448986163233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98246434989275632657442155 147369652483913448986163233)
    ·
      refine ⟨110527239362935086739622425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147369652483913448986163233 110527239362935086739622425)
      ·
        refine ⟨82895429522201315054716819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110527239362935086739622425 82895429522201315054716819)
        ·
          refine ⟨124343144283301972582075229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82895429522201315054716819 124343144283301972582075229)
          ·
            refine ⟨46628679106238239718278211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124343144283301972582075229 46628679106238239718278211)
            ·
              refine ⟨69943018659357359577417317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46628679106238239718278211 69943018659357359577417317)
              ·
                refine ⟨13114315998629504920765747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69943018659357359577417317 13114315998629504920765747)
                ·
                  refine ⟨19671473997944257381148621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13114315998629504920765747 19671473997944257381148621)
                  ·
                    refine ⟨7376802749229096517930733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19671473997944257381148621 7376802749229096517930733)
                    ·
                      refine ⟨2766301030960911194224025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7376802749229096517930733 2766301030960911194224025)
                      ·
                        rfl

theorem cell23_5387352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_5387352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387352 prefixEnd_5387352 := by exact prefixLift 5387352
  have htrace : WordTrace (prefixWord ++ tailWord_5387352) baseStart_5387352 baseEnd_5387352 := by
    simpa [prefixWord, tailWord_5387352, baseEnd_5387352] using wordTrace_append hprefix tailTrace_5387352
  have hstable : (prefixWord ++ tailWord_5387352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387352).length < 2 ^ (prefixWord ++ tailWord_5387352).sum := by decide
  have hdescent : baseEnd_5387352 < baseStart_5387352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387369 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 4, 1, 3]
def baseStart_5387369 : Nat := 118140960795 + 5387369 * 2 ^ 59
def prefixEnd_5387369 : Nat := 4983230072969 + 3 ^ 40 * 5387369 * 2
def baseEnd_5387369 : Nat := 2766309760132037627711447

theorem tailTrace_5387369 : CollatzResearch.WordTrace tailWord_5387369 prefixEnd_5387369 2766309760132037627711447 := by
  unfold tailWord_5387369
  simp only [CollatzResearch.WordTrace]
  refine ⟨196493490019489677218253161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130995660012993118145502107 196493490019489677218253161)
  ·
    refine ⟨147370117514617257913689871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196493490019489677218253161 147370117514617257913689871)
    ·
      refine ⟨221055176271925886870534807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147370117514617257913689871 221055176271925886870534807)
      ·
        refine ⟨331582764407888830305802211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221055176271925886870534807 331582764407888830305802211)
        ·
          refine ⟨497374146611833245458703317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331582764407888830305802211 497374146611833245458703317)
          ·
            refine ⟨11657206561214841690438359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 497374146611833245458703317 11657206561214841690438359)
            ·
              refine ⟨17485809841822262535657539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11657206561214841690438359 17485809841822262535657539)
              ·
                refine ⟨26228714762733393803486309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17485809841822262535657539 26228714762733393803486309)
                ·
                  refine ⟨4917884018012511338153683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26228714762733393803486309 4917884018012511338153683)
                  ·
                    refine ⟨7376826027018767007230525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4917884018012511338153683 7376826027018767007230525)
                    ·
                      refine ⟨2766309760132037627711447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7376826027018767007230525 2766309760132037627711447)
                      ·
                        rfl

theorem cell23_5387369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 1, 3].length) (baseStart_5387369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387369 prefixEnd_5387369 := by exact prefixLift 5387369
  have htrace : WordTrace (prefixWord ++ tailWord_5387369) baseStart_5387369 baseEnd_5387369 := by
    simpa [prefixWord, tailWord_5387369, baseEnd_5387369] using wordTrace_append hprefix tailTrace_5387369
  have hstable : (prefixWord ++ tailWord_5387369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387369).length < 2 ^ (prefixWord ++ tailWord_5387369).sum := by decide
  have hdescent : baseEnd_5387369 < baseStart_5387369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387396 : List Nat := [2, 3, 2, 1, 2, 2, 1, 4, 1, 3, 2]
def baseStart_5387396 : Nat := 118140960795 + 5387396 * 2 ^ 59
def prefixEnd_5387396 : Nat := 4983230072969 + 3 ^ 40 * 5387396 * 2
def baseEnd_5387396 : Nat := 2766323624109709022073823

theorem tailTrace_5387396 : CollatzResearch.WordTrace tailWord_5387396 prefixEnd_5387396 2766323624109709022073823 := by
  unfold tailWord_5387396
  simp only [CollatzResearch.WordTrace]
  refine ⟨98247237395195930414743021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130996316526927907219657361 98247237395195930414743021)
  ·
    refine ⟨36842714023198473905528633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98247237395195930414743021 36842714023198473905528633)
    ·
      refine ⟨27632035517398855429146475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36842714023198473905528633 27632035517398855429146475)
      ·
        refine ⟨41448053276098283143719713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27632035517398855429146475 41448053276098283143719713)
        ·
          refine ⟨31086039957073712357789785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41448053276098283143719713 31086039957073712357789785)
          ·
            refine ⟨23314529967805284268342339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31086039957073712357789785 23314529967805284268342339)
            ·
              refine ⟨34971794951707926402513509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23314529967805284268342339 34971794951707926402513509)
              ·
                refine ⟨6557211553445236200471283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34971794951707926402513509 6557211553445236200471283)
                ·
                  refine ⟨9835817330167854300706925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6557211553445236200471283 9835817330167854300706925)
                  ·
                    refine ⟨3688431498812945362765097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9835817330167854300706925 3688431498812945362765097)
                    ·
                      refine ⟨2766323624109709022073823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3688431498812945362765097 2766323624109709022073823)
                      ·
                        rfl

theorem cell23_5387396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_5387396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387396 prefixEnd_5387396 := by exact prefixLift 5387396
  have htrace : WordTrace (prefixWord ++ tailWord_5387396) baseStart_5387396 baseEnd_5387396 := by
    simpa [prefixWord, tailWord_5387396, baseEnd_5387396] using wordTrace_append hprefix tailTrace_5387396
  have hstable : (prefixWord ++ tailWord_5387396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387396).length < 2 ^ (prefixWord ++ tailWord_5387396).sum := by decide
  have hdescent : baseEnd_5387396 < baseStart_5387396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387437 : List Nat := [1, 5, 2, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_5387437 : Nat := 118140960795 + 5387437 * 2 ^ 59
def prefixEnd_5387437 : Nat := 4983230072969 + 3 ^ 40 * 5387437 * 2
def baseEnd_5387437 : Nat := 2766344676816543361661135

theorem tailTrace_5387437 : CollatzResearch.WordTrace tailWord_5387437 prefixEnd_5387437 2766344676816543361661135 := by
  unfold tailWord_5387437
  simp only [CollatzResearch.WordTrace]
  refine ⟨196495970183243324831728565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130997313455495549887819043 196495970183243324831728565)
  ·
    refine ⟨18421497204679061702974553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 196495970183243324831728565 18421497204679061702974553)
    ·
      refine ⟨13816122903509296277230915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18421497204679061702974553 13816122903509296277230915)
      ·
        refine ⟨20724184355263944415846373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13816122903509296277230915 20724184355263944415846373)
        ·
          refine ⟨3885784566611989577971195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20724184355263944415846373 3885784566611989577971195)
          ·
            refine ⟨5828676849917984366956793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3885784566611989577971195 5828676849917984366956793)
            ·
              refine ⟨4371507637438488275217595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5828676849917984366956793 4371507637438488275217595)
              ·
                refine ⟨6557261456157732412826393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4371507637438488275217595 6557261456157732412826393)
                ·
                  refine ⟨4917946092118299309619795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6557261456157732412826393 4917946092118299309619795)
                  ·
                    refine ⟨7376919138177448964429693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4917946092118299309619795 7376919138177448964429693)
                    ·
                      refine ⟨2766344676816543361661135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7376919138177448964429693 2766344676816543361661135)
                      ·
                        rfl

theorem cell23_5387437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_5387437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387437 prefixEnd_5387437 := by exact prefixLift 5387437
  have htrace : WordTrace (prefixWord ++ tailWord_5387437) baseStart_5387437 baseEnd_5387437 := by
    simpa [prefixWord, tailWord_5387437, baseEnd_5387437] using wordTrace_append hprefix tailTrace_5387437
  have hstable : (prefixWord ++ tailWord_5387437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387437).length < 2 ^ (prefixWord ++ tailWord_5387437).sum := by decide
  have hdescent : baseEnd_5387437 < baseStart_5387437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387443 : List Nat := [1, 1, 1, 2, 3, 2, 6, 1, 2, 2, 2]
def baseStart_5387443 : Nat := 118140960795 + 5387443 * 2 ^ 59
def prefixEnd_5387443 : Nat := 4983230072969 + 3 ^ 40 * 5387443 * 2
def baseEnd_5387443 : Nat := 2766347757700470338186107

theorem tailTrace_5387443 : CollatzResearch.WordTrace tailWord_5387443 prefixEnd_5387443 2766347757700470338186107 := by
  unfold tailWord_5387443
  simp only [CollatzResearch.WordTrace]
  refine ⟨196496189021221587856446983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130997459347481058570964655 196496189021221587856446983)
  ·
    refine ⟨294744283531832381784670475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196496189021221587856446983 294744283531832381784670475)
    ·
      refine ⟨442116425297748572677005713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294744283531832381784670475 442116425297748572677005713)
      ·
        refine ⟨331587318973311429507754285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 442116425297748572677005713 331587318973311429507754285)
        ·
          refine ⟨124345244614991786065407857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 331587318973311429507754285 124345244614991786065407857)
          ·
            refine ⟨93258933461243839549055893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124345244614991786065407857 93258933461243839549055893)
            ·
              refine ⟨4371512505995804978861995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 93258933461243839549055893 4371512505995804978861995)
              ·
                refine ⟨6557268758993707468292993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4371512505995804978861995 6557268758993707468292993)
                ·
                  refine ⟨4917951569245280601219745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6557268758993707468292993 4917951569245280601219745)
                  ·
                    refine ⟨3688463676933960450914809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4917951569245280601219745 3688463676933960450914809)
                    ·
                      refine ⟨2766347757700470338186107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3688463676933960450914809 2766347757700470338186107)
                      ·
                        rfl

theorem cell23_5387443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 2, 2, 2].length) (baseStart_5387443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387443 prefixEnd_5387443 := by exact prefixLift 5387443
  have htrace : WordTrace (prefixWord ++ tailWord_5387443) baseStart_5387443 baseEnd_5387443 := by
    simpa [prefixWord, tailWord_5387443, baseEnd_5387443] using wordTrace_append hprefix tailTrace_5387443
  have hstable : (prefixWord ++ tailWord_5387443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387443).length < 2 ^ (prefixWord ++ tailWord_5387443).sum := by decide
  have hdescent : baseEnd_5387443 < baseStart_5387443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387482 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4]
def baseStart_5387482 : Nat := 118140960795 + 5387482 * 2 ^ 59
def prefixEnd_5387482 : Nat := 4983230072969 + 3 ^ 40 * 5387482 * 2
def baseEnd_5387482 : Nat := 2766367783445995685598427

theorem tailTrace_5387482 : CollatzResearch.WordTrace tailWord_5387482 prefixEnd_5387482 2766367783445995685598427 := by
  unfold tailWord_5387482
  simp only [CollatzResearch.WordTrace]
  refine ⟨49124402867020074379279175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130998407645386865011411133 49124402867020074379279175)
  ·
    refine ⟨73686604300530111568918763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49124402867020074379279175 73686604300530111568918763)
    ·
      refine ⟨110529906450795167353378145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73686604300530111568918763 110529906450795167353378145)
      ·
        refine ⟨82897429838096375515033609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110529906450795167353378145 82897429838096375515033609)
        ·
          refine ⟨62173072378572281636275207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82897429838096375515033609 62173072378572281636275207)
          ·
            refine ⟨93259608567858422454412811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62173072378572281636275207 93259608567858422454412811)
            ·
              refine ⟨139889412851787633681619217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93259608567858422454412811 139889412851787633681619217)
              ·
                refine ⟨104917059638840725261214413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139889412851787633681619217 104917059638840725261214413)
                ·
                  refine ⟨39343897364565271972955405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104917059638840725261214413 39343897364565271972955405)
                  ·
                    refine ⟨14753961511711976989858277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39343897364565271972955405 14753961511711976989858277)
                    ·
                      refine ⟨2766367783445995685598427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14753961511711976989858277 2766367783445995685598427)
                      ·
                        rfl

theorem cell23_5387482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_5387482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387482 prefixEnd_5387482 := by exact prefixLift 5387482
  have htrace : WordTrace (prefixWord ++ tailWord_5387482) baseStart_5387482 baseEnd_5387482 := by
    simpa [prefixWord, tailWord_5387482, baseEnd_5387482] using wordTrace_append hprefix tailTrace_5387482
  have hstable : (prefixWord ++ tailWord_5387482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387482).length < 2 ^ (prefixWord ++ tailWord_5387482).sum := by decide
  have hdescent : baseEnd_5387482 < baseStart_5387482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387499 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 1, 6, 2]
def baseStart_5387499 : Nat := 118140960795 + 5387499 * 2 ^ 59
def prefixEnd_5387499 : Nat := 4983230072969 + 3 ^ 40 * 5387499 * 2
def baseEnd_5387499 : Nat := 2766376512617122119085849

theorem tailTrace_5387499 : CollatzResearch.WordTrace tailWord_5387499 prefixEnd_5387499 2766376512617122119085849 := by
  unfold tailWord_5387499
  simp only [CollatzResearch.WordTrace]
  refine ⟨196498231509018709420485551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130998821006012472946990367 196498231509018709420485551)
  ·
    refine ⟨294747347263528064130728327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196498231509018709420485551 294747347263528064130728327)
    ·
      refine ⟨442121020895292096196092491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294747347263528064130728327 442121020895292096196092491)
      ·
        refine ⟨663181531342938144294138737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442121020895292096196092491 663181531342938144294138737)
        ·
          refine ⟨497386148507203608220604053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 663181531342938144294138737 497386148507203608220604053)
          ·
            refine ⟨23314975711275169135340815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 497386148507203608220604053 23314975711275169135340815)
            ·
              refine ⟨34972463566912753703011223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23314975711275169135340815 34972463566912753703011223)
              ·
                refine ⟨52458695350369130554516835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34972463566912753703011223 52458695350369130554516835)
                ·
                  refine ⟨78688043025553695831775253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52458695350369130554516835 78688043025553695831775253)
                  ·
                    refine ⟨3688502016822829492114465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78688043025553695831775253 3688502016822829492114465)
                    ·
                      refine ⟨2766376512617122119085849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3688502016822829492114465 2766376512617122119085849)
                      ·
                        rfl

theorem cell23_5387499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 6, 2].length) (baseStart_5387499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387499 prefixEnd_5387499 := by exact prefixLift 5387499
  have htrace : WordTrace (prefixWord ++ tailWord_5387499) baseStart_5387499 baseEnd_5387499 := by
    simpa [prefixWord, tailWord_5387499, baseEnd_5387499] using wordTrace_append hprefix tailTrace_5387499
  have hstable : (prefixWord ++ tailWord_5387499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387499).length < 2 ^ (prefixWord ++ tailWord_5387499).sum := by decide
  have hdescent : baseEnd_5387499 < baseStart_5387499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387519 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 3]
def baseStart_5387519 : Nat := 118140960795 + 5387519 * 2 ^ 59
def prefixEnd_5387519 : Nat := 4983230072969 + 3 ^ 40 * 5387519 * 2
def baseEnd_5387519 : Nat := 2766386782230212040835757

theorem tailTrace_5387519 : CollatzResearch.WordTrace tailWord_5387519 prefixEnd_5387519 2766386782230212040835757 := by
  unfold tailWord_5387519
  simp only [CollatzResearch.WordTrace]
  refine ⟨196498960968946252836213611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130999307312630835224142407 196498960968946252836213611)
  ·
    refine ⟨294748441453419379254320417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196498960968946252836213611 294748441453419379254320417)
    ·
      refine ⟨221061331090064534440740313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294748441453419379254320417 221061331090064534440740313)
      ·
        refine ⟨165795998317548400830555235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221061331090064534440740313 165795998317548400830555235)
        ·
          refine ⟨248693997476322601245832853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165795998317548400830555235 248693997476322601245832853)
          ·
            refine ⟨11657531131702621933398415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 248693997476322601245832853 11657531131702621933398415)
            ·
              refine ⟨17486296697553932900097623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11657531131702621933398415 17486296697553932900097623)
              ·
                refine ⟨26229445046330899350146435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17486296697553932900097623 26229445046330899350146435)
                ·
                  refine ⟨39344167569496349025219653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26229445046330899350146435 39344167569496349025219653)
                  ·
                    refine ⟨7377031419280565442228685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39344167569496349025219653 7377031419280565442228685)
                    ·
                      refine ⟨2766386782230212040835757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7377031419280565442228685 2766386782230212040835757)
                      ·
                        rfl

theorem cell23_5387519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_5387519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387519 prefixEnd_5387519 := by exact prefixLift 5387519
  have htrace : WordTrace (prefixWord ++ tailWord_5387519) baseStart_5387519 baseEnd_5387519 := by
    simpa [prefixWord, tailWord_5387519, baseEnd_5387519] using wordTrace_append hprefix tailTrace_5387519
  have hstable : (prefixWord ++ tailWord_5387519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387519).length < 2 ^ (prefixWord ++ tailWord_5387519).sum := by decide
  have hdescent : baseEnd_5387519 < baseStart_5387519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387556 : List Nat := [2, 3, 1, 3, 1, 1, 5, 1, 6]
def baseStart_5387556 : Nat := 118140960795 + 5387556 * 2 ^ 59
def prefixEnd_5387556 : Nat := 4983230072969 + 3 ^ 40 * 5387556 * 2
def baseEnd_5387556 : Nat := 307378420112714266230343

theorem tailTrace_5387556 : CollatzResearch.WordTrace tailWord_5387556 prefixEnd_5387556 307378420112714266230343 := by
  unfold tailWord_5387556
  simp only [CollatzResearch.WordTrace]
  refine ⟨98250155234906104077655261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131000206979874805436873681 98250155234906104077655261)
  ·
    refine ⟨36843808213089789029120723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98250155234906104077655261 36843808213089789029120723)
    ·
      refine ⟨55265712319634683543681085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36843808213089789029120723 55265712319634683543681085)
      ·
        refine ⟨20724642119863006328880407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55265712319634683543681085 20724642119863006328880407)
        ·
          refine ⟨31086963179794509493320611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20724642119863006328880407 31086963179794509493320611)
          ·
            refine ⟨46630444769691764239980917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31086963179794509493320611 46630444769691764239980917)
            ·
              refine ⟨4371604197158602897498211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46630444769691764239980917 4371604197158602897498211)
              ·
                refine ⟨6557406295737904346247317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4371604197158602897498211 6557406295737904346247317)
                ·
                  refine ⟨307378420112714266230343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6557406295737904346247317 307378420112714266230343)
                  ·
                    rfl

theorem cell23_5387556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_5387556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387556 prefixEnd_5387556 := by exact prefixLift 5387556
  have htrace : WordTrace (prefixWord ++ tailWord_5387556) baseStart_5387556 baseEnd_5387556 := by
    simpa [prefixWord, tailWord_5387556, baseEnd_5387556] using wordTrace_append hprefix tailTrace_5387556
  have hstable : (prefixWord ++ tailWord_5387556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387556).length < 2 ^ (prefixWord ++ tailWord_5387556).sum := by decide
  have hdescent : baseEnd_5387556 < baseStart_5387556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387576 : List Nat := [2, 1, 2, 1, 3, 1, 1, 5, 2, 3, 2]
def baseStart_5387576 : Nat := 118140960795 + 5387576 * 2 ^ 59
def prefixEnd_5387576 : Nat := 4983230072969 + 3 ^ 40 * 5387576 * 2
def baseEnd_5387576 : Nat := 2766416050627518317822995

theorem tailTrace_5387576 : CollatzResearch.WordTrace tailWord_5387576 prefixEnd_5387576 2766416050627518317822995 := by
  unfold tailWord_5387576
  simp only [CollatzResearch.WordTrace]
  refine ⟨98250519964869875785519291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131000693286493167714025721 98250519964869875785519291)
  ·
    refine ⟨147375779947304813678278937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98250519964869875785519291 147375779947304813678278937)
    ·
      refine ⟨110531834960478610258709203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147375779947304813678278937 110531834960478610258709203)
      ·
        refine ⟨165797752440717915388063805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110531834960478610258709203 165797752440717915388063805)
        ·
          refine ⟨62174157165269218270523927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165797752440717915388063805 62174157165269218270523927)
          ·
            refine ⟨93261235747903827405785891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62174157165269218270523927 93261235747903827405785891)
            ·
              refine ⟨139891853621855741108678837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93261235747903827405785891 139891853621855741108678837)
              ·
                refine ⟨13114861277048975728938641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139891853621855741108678837 13114861277048975728938641)
                ·
                  refine ⟨9836145957786731796703981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13114861277048975728938641 9836145957786731796703981)
                  ·
                    refine ⟨3688554734170024423763993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9836145957786731796703981 3688554734170024423763993)
                    ·
                      refine ⟨2766416050627518317822995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3688554734170024423763993 2766416050627518317822995)
                      ·
                        rfl

theorem cell23_5387576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 2, 3, 2].length) (baseStart_5387576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387576 prefixEnd_5387576 := by exact prefixLift 5387576
  have htrace : WordTrace (prefixWord ++ tailWord_5387576) baseStart_5387576 baseEnd_5387576 := by
    simpa [prefixWord, tailWord_5387576, baseEnd_5387576] using wordTrace_append hprefix tailTrace_5387576
  have hstable : (prefixWord ++ tailWord_5387576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387576).length < 2 ^ (prefixWord ++ tailWord_5387576).sum := by decide
  have hdescent : baseEnd_5387576 < baseStart_5387576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387577 : List Nat := [1, 2, 1, 6, 3, 1, 1, 3, 1, 4]
def baseStart_5387577 : Nat := 118140960795 + 5387577 * 2 ^ 59
def prefixEnd_5387577 : Nat := 4983230072969 + 3 ^ 40 * 5387577 * 2
def baseEnd_5387577 : Nat := 922138854702724271303497

theorem tailTrace_5387577 : CollatzResearch.WordTrace tailWord_5387577 prefixEnd_5387577 922138854702724271303497 := by
  unfold tailWord_5387577
  simp only [CollatzResearch.WordTrace]
  refine ⟨196501076402736128741824985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131000717601824085827883323 196501076402736128741824985)
  ·
    refine ⟨147375807302052096556368739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196501076402736128741824985 147375807302052096556368739)
    ·
      refine ⟨221063710953078144834553109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147375807302052096556368739 221063710953078144834553109)
      ·
        refine ⟨10362361450925538039119677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 221063710953078144834553109 10362361450925538039119677)
        ·
          refine ⟨3885885544097076764669879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10362361450925538039119677 3885885544097076764669879)
          ·
            refine ⟨5828828316145615147004819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3885885544097076764669879 5828828316145615147004819)
            ·
              refine ⟨8743242474218422720507229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5828828316145615147004819 8743242474218422720507229)
              ·
                refine ⟨3278715927831908520190211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8743242474218422720507229 3278715927831908520190211)
                ·
                  refine ⟨4918073891747862780285317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3278715927831908520190211 4918073891747862780285317)
                  ·
                    refine ⟨922138854702724271303497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4918073891747862780285317 922138854702724271303497)
                    ·
                      rfl

theorem cell23_5387577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 1, 4].length) (baseStart_5387577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387577 prefixEnd_5387577 := by exact prefixLift 5387577
  have htrace : WordTrace (prefixWord ++ tailWord_5387577) baseStart_5387577 baseEnd_5387577 := by
    simpa [prefixWord, tailWord_5387577, baseEnd_5387577] using wordTrace_append hprefix tailTrace_5387577
  have hstable : (prefixWord ++ tailWord_5387577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387577).length < 2 ^ (prefixWord ++ tailWord_5387577).sum := by decide
  have hdescent : baseEnd_5387577 < baseStart_5387577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387600 : List Nat := [2, 1, 1, 1, 1, 5, 5, 2, 1, 1, 3]
def baseStart_5387600 : Nat := 118140960795 + 5387600 * 2 ^ 59
def prefixEnd_5387600 : Nat := 4983230072969 + 3 ^ 40 * 5387600 * 2
def baseEnd_5387600 : Nat := 2766428374163226223922885

theorem tailTrace_5387600 : CollatzResearch.WordTrace tailWord_5387600 prefixEnd_5387600 2766428374163226223922885 := by
  unfold tailWord_5387600
  simp only [CollatzResearch.WordTrace]
  refine ⟨98250957640826401834956127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131001276854435202446608169 98250957640826401834956127)
  ·
    refine ⟨147376436461239602752434191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98250957640826401834956127 147376436461239602752434191)
    ·
      refine ⟨221064654691859404128651287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147376436461239602752434191 221064654691859404128651287)
      ·
        refine ⟨331596982037789106192976931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221064654691859404128651287 331596982037789106192976931)
        ·
          refine ⟨497395473056683659289465397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331596982037789106192976931 497395473056683659289465397)
          ·
            refine ⟨46630825599064093058387381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 497395473056683659289465397 46630825599064093058387381)
            ·
              refine ⟨4371639899912258724223817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46630825599064093058387381 4371639899912258724223817)
              ·
                refine ⟨3278729924934194043167863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4371639899912258724223817 3278729924934194043167863)
                ·
                  refine ⟨4918094887401291064751795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3278729924934194043167863 4918094887401291064751795)
                  ·
                    refine ⟨7377142331101936597127693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4918094887401291064751795 7377142331101936597127693)
                    ·
                      refine ⟨2766428374163226223922885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7377142331101936597127693 2766428374163226223922885)
                      ·
                        rfl

theorem cell23_5387600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 1, 1, 3].length) (baseStart_5387600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387600 prefixEnd_5387600 := by exact prefixLift 5387600
  have htrace : WordTrace (prefixWord ++ tailWord_5387600) baseStart_5387600 baseEnd_5387600 := by
    simpa [prefixWord, tailWord_5387600, baseEnd_5387600] using wordTrace_append hprefix tailTrace_5387600
  have hstable : (prefixWord ++ tailWord_5387600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387600).length < 2 ^ (prefixWord ++ tailWord_5387600).sum := by decide
  have hdescent : baseEnd_5387600 < baseStart_5387600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387609 : List Nat := [1, 2, 1, 2, 2, 2, 4, 2, 1, 1, 5]
def baseStart_5387609 : Nat := 118140960795 + 5387609 * 2 ^ 59
def prefixEnd_5387609 : Nat := 4983230072969 + 3 ^ 40 * 5387609 * 2
def baseEnd_5387609 : Nat := 2766432995489116688710343

theorem tailTrace_5387609 : CollatzResearch.WordTrace tailWord_5387609 prefixEnd_5387609 2766432995489116688710343 := by
  unfold tailWord_5387609
  simp only [CollatzResearch.WordTrace]
  refine ⟨196502243538620198206989881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131001495692413465471326587 196502243538620198206989881)
  ·
    refine ⟨147376682653965148655242411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196502243538620198206989881 147376682653965148655242411)
    ·
      refine ⟨221065023980947722982863617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147376682653965148655242411 221065023980947722982863617)
      ·
        refine ⟨165798767985710792237147713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221065023980947722982863617 165798767985710792237147713)
        ·
          refine ⟨124349075989283094177860785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165798767985710792237147713 124349075989283094177860785)
          ·
            refine ⟨93261806991962320633395589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124349075989283094177860785 93261806991962320633395589)
            ·
              refine ⟨17486588810992935118761673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93261806991962320633395589 17486588810992935118761673)
              ·
                refine ⟨13114941608244701339071255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17486588810992935118761673 13114941608244701339071255)
                ·
                  refine ⟨19672412412367052008606883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13114941608244701339071255 19672412412367052008606883)
                  ·
                    refine ⟨29508618618550578012910325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19672412412367052008606883 29508618618550578012910325)
                    ·
                      refine ⟨2766432995489116688710343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29508618618550578012910325 2766432995489116688710343)
                      ·
                        rfl

theorem cell23_5387609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_5387609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387609 prefixEnd_5387609 := by exact prefixLift 5387609
  have htrace : WordTrace (prefixWord ++ tailWord_5387609) baseStart_5387609 baseEnd_5387609 := by
    simpa [prefixWord, tailWord_5387609, baseEnd_5387609] using wordTrace_append hprefix tailTrace_5387609
  have hstable : (prefixWord ++ tailWord_5387609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387609).length < 2 ^ (prefixWord ++ tailWord_5387609).sum := by decide
  have hdescent : baseEnd_5387609 < baseStart_5387609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387619 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 6]
def baseStart_5387619 : Nat := 118140960795 + 5387619 * 2 ^ 59
def prefixEnd_5387619 : Nat := 4983230072969 + 3 ^ 40 * 5387619 * 2
def baseEnd_5387619 : Nat := 2766438130295661649585297

theorem tailTrace_5387619 : CollatzResearch.WordTrace tailWord_5387619 prefixEnd_5387619 2766438130295661649585297 := by
  unfold tailWord_5387619
  simp only [CollatzResearch.WordTrace]
  refine ⟨196502608268583969914853911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131001738845722646609902607 196502608268583969914853911)
  ·
    refine ⟨294753912402875954872280867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196502608268583969914853911 294753912402875954872280867)
    ·
      refine ⟨442130868604313932308421301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294753912402875954872280867 442130868604313932308421301)
      ·
        refine ⟨41449768931654431153914497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 442130868604313932308421301 41449768931654431153914497)
        ·
          refine ⟨31087326698740823365435873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41449768931654431153914497 31087326698740823365435873)
          ·
            refine ⟨23315495024055617524076905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31087326698740823365435873 23315495024055617524076905)
            ·
              refine ⟨17486621268041713143057679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23315495024055617524076905 17486621268041713143057679)
              ·
                refine ⟨26229931902062569714586519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17486621268041713143057679 26229931902062569714586519)
                ·
                  refine ⟨39344897853093854571879779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26229931902062569714586519 39344897853093854571879779)
                  ·
                    refine ⟨59017346779640781857819669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39344897853093854571879779 59017346779640781857819669)
                    ·
                      refine ⟨2766438130295661649585297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59017346779640781857819669 2766438130295661649585297)
                      ·
                        rfl

theorem cell23_5387619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_5387619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387619 prefixEnd_5387619 := by exact prefixLift 5387619
  have htrace : WordTrace (prefixWord ++ tailWord_5387619) baseStart_5387619 baseEnd_5387619 := by
    simpa [prefixWord, tailWord_5387619, baseEnd_5387619] using wordTrace_append hprefix tailTrace_5387619
  have hstable : (prefixWord ++ tailWord_5387619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387619).length < 2 ^ (prefixWord ++ tailWord_5387619).sum := by decide
  have hdescent : baseEnd_5387619 < baseStart_5387619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387629 : List Nat := [1, 5, 1, 1, 1, 3, 2, 9]
def baseStart_5387629 : Nat := 118140960795 + 5387629 * 2 ^ 59
def prefixEnd_5387629 : Nat := 4983230072969 + 3 ^ 40 * 5387629 * 2
def baseEnd_5387629 : Nat := 102460861670452096683713

theorem tailTrace_5387629 : CollatzResearch.WordTrace tailWord_5387629 prefixEnd_5387629 102460861670452096683713 := by
  unfold tailWord_5387629
  simp only [CollatzResearch.WordTrace]
  refine ⟨196502972998547741622717941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131001981999031827748478627 196502972998547741622717941)
  ·
    refine ⟨18422153718613850777129807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 196502972998547741622717941 18422153718613850777129807)
    ·
      refine ⟨27633230577920776165694711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18422153718613850777129807 27633230577920776165694711)
      ·
        refine ⟨41449845866881164248542067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27633230577920776165694711 41449845866881164248542067)
        ·
          refine ⟨62174768800321746372813101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41449845866881164248542067 62174768800321746372813101)
          ·
            refine ⟨23315538300120654889804913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62174768800321746372813101 23315538300120654889804913)
            ·
              refine ⟨17486653725090491167353685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23315538300120654889804913 17486653725090491167353685)
              ·
                refine ⟨102460861670452096683713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17486653725090491167353685 102460861670452096683713)
                ·
                  rfl

theorem cell23_5387629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 9].length) (baseStart_5387629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387629 prefixEnd_5387629 := by exact prefixLift 5387629
  have htrace : WordTrace (prefixWord ++ tailWord_5387629) baseStart_5387629 baseEnd_5387629 := by
    simpa [prefixWord, tailWord_5387629, baseEnd_5387629] using wordTrace_append hprefix tailTrace_5387629
  have hstable : (prefixWord ++ tailWord_5387629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387629).length < 2 ^ (prefixWord ++ tailWord_5387629).sum := by decide
  have hdescent : baseEnd_5387629 < baseStart_5387629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387643 : List Nat := [1, 1, 1, 1, 1, 6, 5, 1, 1, 2, 3]
def baseStart_5387643 : Nat := 118140960795 + 5387643 * 2 ^ 59
def prefixEnd_5387643 : Nat := 4983230072969 + 3 ^ 40 * 5387643 * 2
def baseEnd_5387643 : Nat := 2766450453831369555685187

theorem tailTrace_5387643 : CollatzResearch.WordTrace tailWord_5387643 prefixEnd_5387643 2766450453831369555685187 := by
  unfold tailWord_5387643
  simp only [CollatzResearch.WordTrace]
  refine ⟨196503483620497022013727583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131002322413664681342485055 196503483620497022013727583)
  ·
    refine ⟨294755225430745533020591375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196503483620497022013727583 294755225430745533020591375)
    ·
      refine ⟨442132838146118299530887063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294755225430745533020591375 442132838146118299530887063)
      ·
        refine ⟨663199257219177449296330595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442132838146118299530887063 663199257219177449296330595)
        ·
          refine ⟨994798885828766173944495893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663199257219177449296330595 994798885828766173944495893)
          ·
            refine ⟨46631197773223414403648245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 994798885828766173944495893 46631197773223414403648245)
            ·
              refine ⟨4371674791239695100342023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46631197773223414403648245 4371674791239695100342023)
              ·
                refine ⟨6557512186859542650513035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4371674791239695100342023 6557512186859542650513035)
                ·
                  refine ⟨9836268280289313975769553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6557512186859542650513035 9836268280289313975769553)
                  ·
                    refine ⟨7377201210216985481827165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9836268280289313975769553 7377201210216985481827165)
                    ·
                      refine ⟨2766450453831369555685187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7377201210216985481827165 2766450453831369555685187)
                      ·
                        rfl

theorem cell23_5387643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 1, 2, 3].length) (baseStart_5387643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387643 prefixEnd_5387643 := by exact prefixLift 5387643
  have htrace : WordTrace (prefixWord ++ tailWord_5387643) baseStart_5387643 baseEnd_5387643 := by
    simpa [prefixWord, tailWord_5387643, baseEnd_5387643] using wordTrace_append hprefix tailTrace_5387643
  have hstable : (prefixWord ++ tailWord_5387643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387643).length < 2 ^ (prefixWord ++ tailWord_5387643).sum := by decide
  have hdescent : baseEnd_5387643 < baseStart_5387643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387646 : List Nat := [4, 2, 3, 2, 12]
def baseStart_5387646 : Nat := 118140960795 + 5387646 * 2 ^ 59
def prefixEnd_5387646 : Nat := 4983230072969 + 3 ^ 40 * 5387646 * 2
def baseEnd_5387646 : Nat := 3794858702706904038337

theorem tailTrace_5387646 : CollatzResearch.WordTrace tailWord_5387646 prefixEnd_5387646 3794858702706904038337 := by
  unfold tailWord_5387646
  simp only [CollatzResearch.WordTrace]
  refine ⟨24562949129935769190760849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131002395359657435684057861 24562949129935769190760849)
  ·
    refine ⟨18422211847451826893070637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24562949129935769190760849 18422211847451826893070637)
    ·
      refine ⟨6908329442794435084901489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18422211847451826893070637 6908329442794435084901489)
      ·
        refine ⟨5181247082095826313676117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6908329442794435084901489 5181247082095826313676117)
        ·
          refine ⟨3794858702706904038337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5181247082095826313676117 3794858702706904038337)
          ·
            rfl

theorem cell23_5387646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 12].length) (baseStart_5387646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387646 prefixEnd_5387646 := by exact prefixLift 5387646
  have htrace : WordTrace (prefixWord ++ tailWord_5387646) baseStart_5387646 baseEnd_5387646 := by
    simpa [prefixWord, tailWord_5387646, baseEnd_5387646] using wordTrace_append hprefix tailTrace_5387646
  have hstable : (prefixWord ++ tailWord_5387646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387646).length < 2 ^ (prefixWord ++ tailWord_5387646).sum := by decide
  have hdescent : baseEnd_5387646 < baseStart_5387646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387650 : List Nat := [3, 4, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_5387650 : Nat := 118140960795 + 5387650 * 2 ^ 59
def prefixEnd_5387650 : Nat := 4983230072969 + 3 ^ 40 * 5387650 * 2
def baseEnd_5387650 : Nat := 922151349398650342765885

theorem tailTrace_5387650 : CollatzResearch.WordTrace tailWord_5387650 prefixEnd_5387650 922151349398650342765885 := by
  unfold tailWord_5387650
  simp only [CollatzResearch.WordTrace]
  refine ⟨49125934732867915552308101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131002492620981108139488269 49125934732867915552308101)
  ·
    refine ⟨9211112762412734166057769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49125934732867915552308101 9211112762412734166057769)
    ·
      refine ⟨6908334571809550624543327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9211112762412734166057769 6908334571809550624543327)
      ·
        refine ⟨10362501857714325936814991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6908334571809550624543327 10362501857714325936814991)
        ·
          refine ⟨15543752786571488905222487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10362501857714325936814991 15543752786571488905222487)
          ·
            refine ⟨23315629179857233357833731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15543752786571488905222487 23315629179857233357833731)
            ·
              refine ⟨34973443769785850036750597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23315629179857233357833731 34973443769785850036750597)
              ·
                refine ⟨6557520706834846881890737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34973443769785850036750597 6557520706834846881890737)
                ·
                  refine ⟨4918140530126135161418053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6557520706834846881890737 4918140530126135161418053)
                  ·
                    refine ⟨922151349398650342765885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4918140530126135161418053 922151349398650342765885)
                    ·
                      rfl

theorem cell23_5387650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_5387650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387650 prefixEnd_5387650 := by exact prefixLift 5387650
  have htrace : WordTrace (prefixWord ++ tailWord_5387650) baseStart_5387650 baseEnd_5387650 := by
    simpa [prefixWord, tailWord_5387650, baseEnd_5387650] using wordTrace_append hprefix tailTrace_5387650
  have hstable : (prefixWord ++ tailWord_5387650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387650).length < 2 ^ (prefixWord ++ tailWord_5387650).sum := by decide
  have hdescent : baseEnd_5387650 < baseStart_5387650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387657 : List Nat := [1, 2, 1, 1, 7, 1, 1, 4, 1, 2, 2]
def baseStart_5387657 : Nat := 118140960795 + 5387657 * 2 ^ 59
def prefixEnd_5387657 : Nat := 4983230072969 + 3 ^ 40 * 5387657 * 2
def baseEnd_5387657 : Nat := 2766457642560532500910123

theorem tailTrace_5387657 : CollatzResearch.WordTrace tailWord_5387657 prefixEnd_5387657 2766457642560532500910123 := by
  unfold tailWord_5387657
  simp only [CollatzResearch.WordTrace]
  refine ⟨196503994242446302404737225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131002662828297534936491483 196503994242446302404737225)
  ·
    refine ⟨147377995681834726803552919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196503994242446302404737225 147377995681834726803552919)
    ·
      refine ⟨221066993522752090205329379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147377995681834726803552919 221066993522752090205329379)
      ·
        refine ⟨331600490284128135307994069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221066993522752090205329379 331600490284128135307994069)
        ·
          refine ⟨7771886491034253171281111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 331600490284128135307994069 7771886491034253171281111)
          ·
            refine ⟨11657829736551379756921667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7771886491034253171281111 11657829736551379756921667)
            ·
              refine ⟨17486744604827069635382501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11657829736551379756921667 17486744604827069635382501)
              ·
                refine ⟨3278764613405075556634219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17486744604827069635382501 3278764613405075556634219)
                ·
                  refine ⟨4918146920107613334951329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3278764613405075556634219 4918146920107613334951329)
                  ·
                    refine ⟨3688610190080710001213497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4918146920107613334951329 3688610190080710001213497)
                    ·
                      refine ⟨2766457642560532500910123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3688610190080710001213497 2766457642560532500910123)
                      ·
                        rfl

theorem cell23_5387657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 1, 2, 2].length) (baseStart_5387657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387657 prefixEnd_5387657 := by exact prefixLift 5387657
  have htrace : WordTrace (prefixWord ++ tailWord_5387657) baseStart_5387657 baseEnd_5387657 := by
    simpa [prefixWord, tailWord_5387657, baseEnd_5387657] using wordTrace_append hprefix tailTrace_5387657
  have hstable : (prefixWord ++ tailWord_5387657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387657).length < 2 ^ (prefixWord ++ tailWord_5387657).sum := by decide
  have hdescent : baseEnd_5387657 < baseStart_5387657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387673 : List Nat := [1, 2, 1, 2, 1, 5, 2, 3, 2, 1, 3]
def baseStart_5387673 : Nat := 118140960795 + 5387673 * 2 ^ 59
def prefixEnd_5387673 : Nat := 4983230072969 + 3 ^ 40 * 5387673 * 2
def baseEnd_5387673 : Nat := 2766465858251004438310049

theorem tailTrace_5387673 : CollatzResearch.WordTrace tailWord_5387673 prefixEnd_5387673 2766465858251004438310049 := by
  unfold tailWord_5387673
  simp only [CollatzResearch.WordTrace]
  refine ⟨196504577810388337137319673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131003051873592224758213115 196504577810388337137319673)
  ·
    refine ⟨147378433357791252852989755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196504577810388337137319673 147378433357791252852989755)
    ·
      refine ⟨221067650036686879279484633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147378433357791252852989755 221067650036686879279484633)
      ·
        refine ⟨165800737527515159459613475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221067650036686879279484633 165800737527515159459613475)
        ·
          refine ⟨248701106291272739189420213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165800737527515159459613475 248701106291272739189420213)
          ·
            refine ⟨23315728714806819299008145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 248701106291272739189420213 23315728714806819299008145)
            ·
              refine ⟨17486796536105114474256109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23315728714806819299008145 17486796536105114474256109)
              ·
                refine ⟨6557548701039417927846041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17486796536105114474256109 6557548701039417927846041)
                ·
                  refine ⟨4918161525779563445884531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6557548701039417927846041 4918161525779563445884531)
                  ·
                    refine ⟨7377242288669345168826797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4918161525779563445884531 7377242288669345168826797)
                    ·
                      refine ⟨2766465858251004438310049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7377242288669345168826797 2766465858251004438310049)
                      ·
                        rfl

theorem cell23_5387673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 1, 3].length) (baseStart_5387673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387673 prefixEnd_5387673 := by exact prefixLift 5387673
  have htrace : WordTrace (prefixWord ++ tailWord_5387673) baseStart_5387673 baseEnd_5387673 := by
    simpa [prefixWord, tailWord_5387673, baseEnd_5387673] using wordTrace_append hprefix tailTrace_5387673
  have hstable : (prefixWord ++ tailWord_5387673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387673).length < 2 ^ (prefixWord ++ tailWord_5387673).sum := by decide
  have hdescent : baseEnd_5387673 < baseStart_5387673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387683 : List Nat := [1, 1, 1, 4, 1, 3, 2, 4, 1, 3, 2]
def baseStart_5387683 : Nat := 118140960795 + 5387683 * 2 ^ 59
def prefixEnd_5387683 : Nat := 4983230072969 + 3 ^ 40 * 5387683 * 2
def baseEnd_5387683 : Nat := 2766470993057549399185003

theorem tailTrace_5387683 : CollatzResearch.WordTrace tailWord_5387683 prefixEnd_5387683 2766470993057549399185003 := by
  unfold tailWord_5387683
  simp only [CollatzResearch.WordTrace]
  refine ⟨196504942540352108845183703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131003295026901405896789135 196504942540352108845183703)
  ·
    refine ⟨294757413810528163267775555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196504942540352108845183703 294757413810528163267775555)
    ·
      refine ⟨442136120715792244901663333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294757413810528163267775555 442136120715792244901663333)
      ·
        refine ⟨82900522634211045919061875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 442136120715792244901663333 82900522634211045919061875)
        ·
          refine ⟨124350783951316568878592813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82900522634211045919061875 124350783951316568878592813)
          ·
            refine ⟨46631543981743713329472305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124350783951316568878592813 46631543981743713329472305)
            ·
              refine ⟨34973657986307784997104229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46631543981743713329472305 34973657986307784997104229)
              ·
                refine ⟨6557560872432709686957043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34973657986307784997104229 6557560872432709686957043)
                ·
                  refine ⟨9836341308649064530435565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6557560872432709686957043 9836341308649064530435565)
                  ·
                    refine ⟨3688627990743399198913337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9836341308649064530435565 3688627990743399198913337)
                    ·
                      refine ⟨2766470993057549399185003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3688627990743399198913337 2766470993057549399185003)
                      ·
                        rfl

theorem cell23_5387683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_5387683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387683 prefixEnd_5387683 := by exact prefixLift 5387683
  have htrace : WordTrace (prefixWord ++ tailWord_5387683) baseStart_5387683 baseEnd_5387683 := by
    simpa [prefixWord, tailWord_5387683, baseEnd_5387683] using wordTrace_append hprefix tailTrace_5387683
  have hstable : (prefixWord ++ tailWord_5387683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387683).length < 2 ^ (prefixWord ++ tailWord_5387683).sum := by decide
  have hdescent : baseEnd_5387683 < baseStart_5387683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387696 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 3, 4, 2]
def baseStart_5387696 : Nat := 118140960795 + 5387696 * 2 ^ 59
def prefixEnd_5387696 : Nat := 4983230072969 + 3 ^ 40 * 5387696 * 2
def baseEnd_5387696 : Nat := 2766477668306057848322443

theorem tailTrace_5387696 : CollatzResearch.WordTrace tailWord_5387696 prefixEnd_5387696 2766477668306057848322443 := by
  unfold tailWord_5387696
  simp only [CollatzResearch.WordTrace]
  refine ⟨98252708344652506032703471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131003611126203341376937961 98252708344652506032703471)
  ·
    refine ⟨147379062516978759049055207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98252708344652506032703471 147379062516978759049055207)
    ·
      refine ⟨221068593775468138573582811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147379062516978759049055207 221068593775468138573582811)
      ·
        refine ⟨331602890663202207860374217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221068593775468138573582811 331602890663202207860374217)
        ·
          refine ⟨248702167997401655895280663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331602890663202207860374217 248702167997401655895280663)
          ·
            refine ⟨373053251996102483842920995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248702167997401655895280663 373053251996102483842920995)
            ·
              refine ⟨559579877994153725764381493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373053251996102483842920995 559579877994153725764381493)
              ·
                refine ⟨52460613561951911790410765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 559579877994153725764381493 52460613561951911790410765)
                ·
                  refine ⟨19672730085731966921404037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52460613561951911790410765 19672730085731966921404037)
                  ·
                    refine ⟨3688636891074743797763257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19672730085731966921404037 3688636891074743797763257)
                    ·
                      refine ⟨2766477668306057848322443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3688636891074743797763257 2766477668306057848322443)
                      ·
                        rfl

theorem cell23_5387696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 3, 4, 2].length) (baseStart_5387696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387696 prefixEnd_5387696 := by exact prefixLift 5387696
  have htrace : WordTrace (prefixWord ++ tailWord_5387696) baseStart_5387696 baseEnd_5387696 := by
    simpa [prefixWord, tailWord_5387696, baseEnd_5387696] using wordTrace_append hprefix tailTrace_5387696
  have hstable : (prefixWord ++ tailWord_5387696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387696).length < 2 ^ (prefixWord ++ tailWord_5387696).sum := by decide
  have hdescent : baseEnd_5387696 < baseStart_5387696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387699 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 5]
def baseStart_5387699 : Nat := 118140960795 + 5387699 * 2 ^ 59
def prefixEnd_5387699 : Nat := 4983230072969 + 3 ^ 40 * 5387699 * 2
def baseEnd_5387699 : Nat := 2766479208748021336584929

theorem tailTrace_5387699 : CollatzResearch.WordTrace tailWord_5387699 prefixEnd_5387699 2766479208748021336584929 := by
  unfold tailWord_5387699
  simp only [CollatzResearch.WordTrace]
  refine ⟨196505526108294143577766151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131003684072196095718510767 196505526108294143577766151)
  ·
    refine ⟨294758289162441215366649227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196505526108294143577766151 294758289162441215366649227)
    ·
      refine ⟨442137433743661823049973841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294758289162441215366649227 442137433743661823049973841)
      ·
        refine ⟨331603075307746367287480381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 442137433743661823049973841 331603075307746367287480381)
        ·
          refine ⟨124351153240404887732805143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 331603075307746367287480381 124351153240404887732805143)
          ·
            refine ⟨186526729860607331599207715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124351153240404887732805143 186526729860607331599207715)
            ·
              refine ⟨279790094790910997398811573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186526729860607331599207715 279790094790910997398811573)
              ·
                refine ⟨26230321386647906006138585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 279790094790910997398811573 26230321386647906006138585)
                ·
                  refine ⟨19672741039985929504603939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26230321386647906006138585 19672741039985929504603939)
                  ·
                    refine ⟨29509111559978894256905909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19672741039985929504603939 29509111559978894256905909)
                    ·
                      refine ⟨2766479208748021336584929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29509111559978894256905909 2766479208748021336584929)
                      ·
                        rfl

theorem cell23_5387699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 5].length) (baseStart_5387699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387699 prefixEnd_5387699 := by exact prefixLift 5387699
  have htrace : WordTrace (prefixWord ++ tailWord_5387699) baseStart_5387699 baseEnd_5387699 := by
    simpa [prefixWord, tailWord_5387699, baseEnd_5387699] using wordTrace_append hprefix tailTrace_5387699
  have hstable : (prefixWord ++ tailWord_5387699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387699).length < 2 ^ (prefixWord ++ tailWord_5387699).sum := by decide
  have hdescent : baseEnd_5387699 < baseStart_5387699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387726 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_5387726 : Nat := 118140960795 + 5387726 * 2 ^ 59
def prefixEnd_5387726 : Nat := 4983230072969 + 3 ^ 40 * 5387726 * 2
def baseEnd_5387726 : Nat := 2766493072725692730947305

theorem tailTrace_5387726 : CollatzResearch.WordTrace tailWord_5387726 prefixEnd_5387726 2766493072725692730947305 := by
  unfold tailWord_5387726
  simp only [CollatzResearch.WordTrace]
  refine ⟨24563313859899540898624879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131004340586130884792666021 24563313859899540898624879)
  ·
    refine ⟨36844970789849311347937319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24563313859899540898624879 36844970789849311347937319)
    ·
      refine ⟨55267456184773967021905979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36844970789849311347937319 55267456184773967021905979)
      ·
        refine ⟨82901184277160950532858969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55267456184773967021905979 82901184277160950532858969)
        ·
          refine ⟨62175888207870712899644227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82901184277160950532858969 62175888207870712899644227)
          ·
            refine ⟨93263832311806069349466341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62175888207870712899644227 93263832311806069349466341)
            ·
              refine ⟨17486968558463638003024939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93263832311806069349466341 17486968558463638003024939)
              ·
                refine ⟨26230452837695457004537409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17486968558463638003024939 26230452837695457004537409)
                ·
                  refine ⟨19672839628271592753403057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26230452837695457004537409 19672839628271592753403057)
                  ·
                    refine ⟨14754629721203694565052293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19672839628271592753403057 14754629721203694565052293)
                    ·
                      refine ⟨2766493072725692730947305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14754629721203694565052293 2766493072725692730947305)
                      ·
                        rfl

theorem cell23_5387726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_5387726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387726 prefixEnd_5387726 := by exact prefixLift 5387726
  have htrace : WordTrace (prefixWord ++ tailWord_5387726) baseStart_5387726 baseEnd_5387726 := by
    simpa [prefixWord, tailWord_5387726, baseEnd_5387726] using wordTrace_append hprefix tailTrace_5387726
  have hstable : (prefixWord ++ tailWord_5387726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387726).length < 2 ^ (prefixWord ++ tailWord_5387726).sum := by decide
  have hdescent : baseEnd_5387726 < baseStart_5387726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387779 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 2, 8]
def baseStart_5387779 : Nat := 118140960795 + 5387779 * 2 ^ 59
def prefixEnd_5387779 : Nat := 4983230072969 + 3 ^ 40 * 5387779 * 2
def baseEnd_5387779 : Nat := 922173429066793674528187

theorem tailTrace_5387779 : CollatzResearch.WordTrace tailWord_5387779 prefixEnd_5387779 922173429066793674528187 := by
  unfold tailWord_5387779
  simp only [CollatzResearch.WordTrace]
  refine ⟨196508443948004317240678391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131005629298669544827118927 196508443948004317240678391)
  ·
    refine ⟨294762665922006475861017587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196508443948004317240678391 294762665922006475861017587)
    ·
      refine ⟨442143998883009713791526381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294762665922006475861017587 442143998883009713791526381)
      ·
        refine ⟨165803999581128642671822393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 442143998883009713791526381 165803999581128642671822393)
        ·
          refine ⟨124352999685846482003866795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165803999581128642671822393 124352999685846482003866795)
          ·
            refine ⟨186529499528769723005800193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124352999685846482003866795 186529499528769723005800193)
            ·
              refine ⟨139897124646577292254350145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186529499528769723005800193 139897124646577292254350145)
              ·
                refine ⟨104922843484932969190762609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139897124646577292254350145 104922843484932969190762609)
                ·
                  refine ⟨78692132613699726893071957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104922843484932969190762609 78692132613699726893071957)
                  ·
                    refine ⟨922173429066793674528187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78692132613699726893071957 922173429066793674528187)
                    ·
                      rfl

theorem cell23_5387779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 8].length) (baseStart_5387779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387779 prefixEnd_5387779 := by exact prefixLift 5387779
  have htrace : WordTrace (prefixWord ++ tailWord_5387779) baseStart_5387779 baseEnd_5387779 := by
    simpa [prefixWord, tailWord_5387779, baseEnd_5387779] using wordTrace_append hprefix tailTrace_5387779
  have hstable : (prefixWord ++ tailWord_5387779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387779).length < 2 ^ (prefixWord ++ tailWord_5387779).sum := by decide
  have hdescent : baseEnd_5387779 < baseStart_5387779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387856 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 3, 5]
def baseStart_5387856 : Nat := 118140960795 + 5387856 * 2 ^ 59
def prefixEnd_5387856 : Nat := 4983230072969 + 3 ^ 40 * 5387856 * 2
def baseEnd_5387856 : Nat := 922186608403592407440569

theorem tailTrace_5387856 : CollatzResearch.WordTrace tailWord_5387856 prefixEnd_5387856 922186608403592407440569 := by
  unfold tailWord_5387856
  simp only [CollatzResearch.WordTrace]
  refine ⟨98255626184362679695615711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131007501579150239594154281 98255626184362679695615711)
  ·
    refine ⟨147383439276544019543423567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98255626184362679695615711 147383439276544019543423567)
    ·
      refine ⟨221075158914816029315135351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147383439276544019543423567 221075158914816029315135351)
      ·
        refine ⟨331612738372224043972703027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221075158914816029315135351 331612738372224043972703027)
        ·
          refine ⟨497419107558336065959054541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331612738372224043972703027 497419107558336065959054541)
          ·
            refine ⟨186532165334376024734645453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 497419107558336065959054541 186532165334376024734645453)
            ·
              refine ⟨69949562000391009275492045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186532165334376024734645453 69949562000391009275492045)
              ·
                refine ⟨26231085750146628478309517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69949562000391009275492045 26231085750146628478309517)
                ·
                  refine ⟨9836657156304985679366069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26231085750146628478309517 9836657156304985679366069)
                  ·
                    refine ⟨922186608403592407440569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9836657156304985679366069 922186608403592407440569)
                    ·
                      rfl

theorem cell23_5387856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 3, 5].length) (baseStart_5387856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387856 prefixEnd_5387856 := by exact prefixLift 5387856
  have htrace : WordTrace (prefixWord ++ tailWord_5387856) baseStart_5387856 baseEnd_5387856 := by
    simpa [prefixWord, tailWord_5387856, baseEnd_5387856] using wordTrace_append hprefix tailTrace_5387856
  have hstable : (prefixWord ++ tailWord_5387856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387856).length < 2 ^ (prefixWord ++ tailWord_5387856).sum := by decide
  have hdescent : baseEnd_5387856 < baseStart_5387856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387873 : List Nat := [1, 2, 3, 1, 1, 3, 3, 3, 1, 5]
def baseStart_5387873 : Nat := 118140960795 + 5387873 * 2 ^ 59
def prefixEnd_5387873 : Nat := 4983230072969 + 3 ^ 40 * 5387873 * 2
def baseEnd_5387873 : Nat := 922189518127301218603043

theorem tailTrace_5387873 : CollatzResearch.WordTrace tailWord_5387873 prefixEnd_5387873 922189518127301218603043 := by
  unfold tailWord_5387873
  simp only [CollatzResearch.WordTrace]
  refine ⟨196511872409663771294600273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131007914939775847529733515 196511872409663771294600273)
  ·
    refine ⟨147383904307247828470950205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196511872409663771294600273 147383904307247828470950205)
    ·
      refine ⟨55268964115217935676606327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147383904307247828470950205 55268964115217935676606327)
      ·
        refine ⟨82903446172826903514909491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55268964115217935676606327 82903446172826903514909491)
        ·
          refine ⟨124355169259240355272364237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82903446172826903514909491 124355169259240355272364237)
          ·
            refine ⟨46633188472215133227136589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124355169259240355272364237 46633188472215133227136589)
            ·
              refine ⟨17487445677080674960176221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46633188472215133227136589 17487445677080674960176221)
              ·
                refine ⟨6557792128905253110066083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17487445677080674960176221 6557792128905253110066083)
                ·
                  refine ⟨9836688193357879665099125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6557792128905253110066083 9836688193357879665099125)
                  ·
                    refine ⟨922189518127301218603043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9836688193357879665099125 922189518127301218603043)
                    ·
                      rfl

theorem cell23_5387873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_5387873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387873 prefixEnd_5387873 := by exact prefixLift 5387873
  have htrace : WordTrace (prefixWord ++ tailWord_5387873) baseStart_5387873 baseEnd_5387873 := by
    simpa [prefixWord, tailWord_5387873, baseEnd_5387873] using wordTrace_append hprefix tailTrace_5387873
  have hstable : (prefixWord ++ tailWord_5387873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387873).length < 2 ^ (prefixWord ++ tailWord_5387873).sum := by decide
  have hdescent : baseEnd_5387873 < baseStart_5387873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387913 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 3, 2, 3]
def baseStart_5387913 : Nat := 118140960795 + 5387913 * 2 ^ 59
def prefixEnd_5387913 : Nat := 4983230072969 + 3 ^ 40 * 5387913 * 2
def baseEnd_5387913 : Nat := 2766589093608083499308945

theorem tailTrace_5387913 : CollatzResearch.WordTrace tailWord_5387913 prefixEnd_5387913 2766589093608083499308945 := by
  unfold tailWord_5387913
  simp only [CollatzResearch.WordTrace]
  refine ⟨196513331329518858126056393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131008887553012572084037595 196513331329518858126056393)
  ·
    refine ⟨147384998497139143594542295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196513331329518858126056393 147384998497139143594542295)
    ·
      refine ⟨221077497745708715391813443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147384998497139143594542295 221077497745708715391813443)
      ·
        refine ⟨331616246618563073087720165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221077497745708715391813443 331616246618563073087720165)
        ·
          refine ⟨62178046240980576203947531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 331616246618563073087720165 62178046240980576203947531)
          ·
            refine ⟨93267069361470864305921297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62178046240980576203947531 93267069361470864305921297)
            ·
              refine ⟨69950302021103148229440973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93267069361470864305921297 69950302021103148229440973)
              ·
                refine ⟨26231363257913680586040365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69950302021103148229440973 26231363257913680586040365)
                ·
                  refine ⟨9836761221717630219765137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26231363257913680586040365 9836761221717630219765137)
                  ·
                    refine ⟨7377570916288222664823853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9836761221717630219765137 7377570916288222664823853)
                    ·
                      refine ⟨2766589093608083499308945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7377570916288222664823853 2766589093608083499308945)
                      ·
                        rfl

theorem cell23_5387913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 2, 3].length) (baseStart_5387913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387913 prefixEnd_5387913 := by exact prefixLift 5387913
  have htrace : WordTrace (prefixWord ++ tailWord_5387913) baseStart_5387913 baseEnd_5387913 := by
    simpa [prefixWord, tailWord_5387913, baseEnd_5387913] using wordTrace_append hprefix tailTrace_5387913
  have hstable : (prefixWord ++ tailWord_5387913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387913).length < 2 ^ (prefixWord ++ tailWord_5387913).sum := by decide
  have hdescent : baseEnd_5387913 < baseStart_5387913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387916 : List Nat := [2, 2, 1, 2, 1, 1, 5, 9]
def baseStart_5387916 : Nat := 118140960795 + 5387916 * 2 ^ 59
def prefixEnd_5387916 : Nat := 4983230072969 + 3 ^ 40 * 5387916 * 2
def baseEnd_5387916 : Nat := 102466319779631369910053

theorem tailTrace_5387916 : CollatzResearch.WordTrace tailWord_5387916 prefixEnd_5387916 102466319779631369910053 := by
  unfold tailWord_5387916
  simp only [CollatzResearch.WordTrace]
  refine ⟨98256720374253994819207801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131008960499005326425610401 98256720374253994819207801)
  ·
    refine ⟨73692540280690496114405851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98256720374253994819207801 73692540280690496114405851)
    ·
      refine ⟨110538810421035744171608777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73692540280690496114405851 110538810421035744171608777)
      ·
        refine ⟨82904107815776808128706583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110538810421035744171608777 82904107815776808128706583)
        ·
          refine ⟨124356161723665212193059875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82904107815776808128706583 124356161723665212193059875)
          ·
            refine ⟨186534242585497818289589813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124356161723665212193059875 186534242585497818289589813)
            ·
              refine ⟨17487585242390420464649045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 186534242585497818289589813 17487585242390420464649045)
              ·
                refine ⟨102466319779631369910053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17487585242390420464649045 102466319779631369910053)
                ·
                  rfl

theorem cell23_5387916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 9].length) (baseStart_5387916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387916 prefixEnd_5387916 := by exact prefixLift 5387916
  have htrace : WordTrace (prefixWord ++ tailWord_5387916) baseStart_5387916 baseEnd_5387916 := by
    simpa [prefixWord, tailWord_5387916, baseEnd_5387916] using wordTrace_append hprefix tailTrace_5387916
  have hstable : (prefixWord ++ tailWord_5387916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387916).length < 2 ^ (prefixWord ++ tailWord_5387916).sum := by decide
  have hdescent : baseEnd_5387916 < baseStart_5387916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387938 : List Nat := [3, 3, 1, 4, 1, 1, 3, 2, 1, 1, 3]
def baseStart_5387938 : Nat := 118140960795 + 5387938 * 2 ^ 59
def prefixEnd_5387938 : Nat := 4983230072969 + 3 ^ 40 * 5387938 * 2
def baseEnd_5387938 : Nat := 2766601930624445901496331

theorem tailTrace_5387938 : CollatzResearch.WordTrace tailWord_5387938 prefixEnd_5387938 2766601930624445901496331 := by
  unfold tailWord_5387938
  simp only [CollatzResearch.WordTrace]
  refine ⟨49128560788607071848929117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131009495436285524930477645 49128560788607071848929117)
  ·
    refine ⟨18423210295727651943348419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49128560788607071848929117 18423210295727651943348419)
    ·
      refine ⟨27634815443591477915022629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18423210295727651943348419 27634815443591477915022629)
      ·
        refine ⟨5181527895673402109066743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27634815443591477915022629 5181527895673402109066743)
        ·
          refine ⟨7772291843510103163600115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5181527895673402109066743 7772291843510103163600115)
          ·
            refine ⟨11658437765265154745400173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7772291843510103163600115 11658437765265154745400173)
            ·
              refine ⟨4371914161974433029525065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11658437765265154745400173 4371914161974433029525065)
              ·
                refine ⟨3278935621480824772143799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4371914161974433029525065 3278935621480824772143799)
                ·
                  refine ⟨4918403432221237158215699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3278935621480824772143799 4918403432221237158215699)
                  ·
                    refine ⟨7377605148331855737323549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4918403432221237158215699 7377605148331855737323549)
                    ·
                      refine ⟨2766601930624445901496331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7377605148331855737323549 2766601930624445901496331)
                      ·
                        rfl

theorem cell23_5387938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_5387938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387938 prefixEnd_5387938 := by exact prefixLift 5387938
  have htrace : WordTrace (prefixWord ++ tailWord_5387938) baseStart_5387938 baseEnd_5387938 := by
    simpa [prefixWord, tailWord_5387938, baseEnd_5387938] using wordTrace_append hprefix tailTrace_5387938
  have hstable : (prefixWord ++ tailWord_5387938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387938).length < 2 ^ (prefixWord ++ tailWord_5387938).sum := by decide
  have hdescent : baseEnd_5387938 < baseStart_5387938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387974 : List Nat := [6, 1, 2, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_5387974 : Nat := 118140960795 + 5387974 * 2 ^ 59
def prefixEnd_5387974 : Nat := 4983230072969 + 3 ^ 40 * 5387974 * 2
def baseEnd_5387974 : Nat := 2766620415928007760646165

theorem tailTrace_5387974 : CollatzResearch.WordTrace tailWord_5387974 prefixEnd_5387974 2766620415928007760646165 := by
  unfold tailWord_5387974
  simp only [CollatzResearch.WordTrace]
  refine ⟨6141111130696808298250843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 131010370788198577029351317 6141111130696808298250843)
  ·
    refine ⟨9211666696045212447376265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6141111130696808298250843 9211666696045212447376265)
    ·
      refine ⟨6908750022033909335532199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9211666696045212447376265 6908750022033909335532199)
      ·
        refine ⟨10363125033050864003298299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6908750022033909335532199 10363125033050864003298299)
        ·
          refine ⟨15544687549576296004947449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10363125033050864003298299 15544687549576296004947449)
          ·
            refine ⟨11658515662182222003710587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15544687549576296004947449 11658515662182222003710587)
            ·
              refine ⟨17487773493273333005565881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11658515662182222003710587 17487773493273333005565881)
              ·
                refine ⟨13115830119954999754174411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17487773493273333005565881 13115830119954999754174411)
                ·
                  refine ⟨19673745179932499631261617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13115830119954999754174411 19673745179932499631261617)
                  ·
                    refine ⟨14755308884949374723446213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19673745179932499631261617 14755308884949374723446213)
                    ·
                      refine ⟨2766620415928007760646165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14755308884949374723446213 2766620415928007760646165)
                      ·
                        rfl

theorem cell23_5387974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_5387974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387974 prefixEnd_5387974 := by exact prefixLift 5387974
  have htrace : WordTrace (prefixWord ++ tailWord_5387974) baseStart_5387974 baseEnd_5387974 := by
    simpa [prefixWord, tailWord_5387974, baseEnd_5387974] using wordTrace_append hprefix tailTrace_5387974
  have hstable : (prefixWord ++ tailWord_5387974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387974).length < 2 ^ (prefixWord ++ tailWord_5387974).sum := by decide
  have hdescent : baseEnd_5387974 < baseStart_5387974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5387981 : List Nat := [1, 6, 2, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_5387981 : Nat := 118140960795 + 5387981 * 2 ^ 59
def prefixEnd_5387981 : Nat := 4983230072969 + 3 ^ 40 * 5387981 * 2
def baseEnd_5387981 : Nat := 2766624010292589233258633

theorem tailTrace_5387981 : CollatzResearch.WordTrace tailWord_5387981 prefixEnd_5387981 2766624010292589233258633 := by
  unfold tailWord_5387981
  simp only [CollatzResearch.WordTrace]
  refine ⟨196515811493272505739531797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131010540995515003826354531 196515811493272505739531797)
  ·
    refine ⟨9211678663747148706540553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 196515811493272505739531797 9211678663747148706540553)
    ·
      refine ⟨6908758997810361529905415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9211678663747148706540553 6908758997810361529905415)
      ·
        refine ⟨10363138496715542294858123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6908758997810361529905415 10363138496715542294858123)
        ·
          refine ⟨15544707745073313442287185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10363138496715542294858123 15544707745073313442287185)
          ·
            refine ⟨11658530808804985081715389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15544707745073313442287185 11658530808804985081715389)
            ·
              refine ⟨4371949053301869405643271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11658530808804985081715389 4371949053301869405643271)
              ·
                refine ⟨6557923579952804108464907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4371949053301869405643271 6557923579952804108464907)
                ·
                  refine ⟨9836885369929206162697361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6557923579952804108464907 9836885369929206162697361)
                  ·
                    refine ⟨7377664027446904622023021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9836885369929206162697361 7377664027446904622023021)
                    ·
                      refine ⟨2766624010292589233258633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7377664027446904622023021 2766624010292589233258633)
                      ·
                        rfl

theorem cell23_5387981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_5387981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5387981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5387981 prefixEnd_5387981 := by exact prefixLift 5387981
  have htrace : WordTrace (prefixWord ++ tailWord_5387981) baseStart_5387981 baseEnd_5387981 := by
    simpa [prefixWord, tailWord_5387981, baseEnd_5387981] using wordTrace_append hprefix tailTrace_5387981
  have hstable : (prefixWord ++ tailWord_5387981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5387981).length < 2 ^ (prefixWord ++ tailWord_5387981).sum := by decide
  have hdescent : baseEnd_5387981 < baseStart_5387981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5387981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388017 : List Nat := [1, 2, 2, 2, 2, 4, 2, 1, 1, 4, 2]
def baseStart_5388017 : Nat := 118140960795 + 5388017 * 2 ^ 59
def prefixEnd_5388017 : Nat := 4983230072969 + 3 ^ 40 * 5388017 * 2
def baseEnd_5388017 : Nat := 2766642495596151092408467

theorem tailTrace_5388017 : CollatzResearch.WordTrace tailWord_5388017 prefixEnd_5388017 2766642495596151092408467 := by
  unfold tailWord_5388017
  simp only [CollatzResearch.WordTrace]
  refine ⟨196517124521142083887842305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131011416347428055925228203 196517124521142083887842305)
  ·
    refine ⟨147387843390856562915881729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196517124521142083887842305 147387843390856562915881729)
    ·
      refine ⟨110540882543142422186911297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147387843390856562915881729 110540882543142422186911297)
      ·
        refine ⟨82905661907356816640183473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110540882543142422186911297 82905661907356816640183473)
        ·
          refine ⟨62179246430517612480137605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82905661907356816640183473 62179246430517612480137605)
          ·
            refine ⟨11658608705722052340025801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62179246430517612480137605 11658608705722052340025801)
            ·
              refine ⟨8743956529291539255019351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11658608705722052340025801 8743956529291539255019351)
              ·
                refine ⟨13115934793937308882529027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8743956529291539255019351 13115934793937308882529027)
                ·
                  refine ⟨19673902190905963323793541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13115934793937308882529027 19673902190905963323793541)
                  ·
                    refine ⟨3688856660794868123211289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19673902190905963323793541 3688856660794868123211289)
                    ·
                      refine ⟨2766642495596151092408467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3688856660794868123211289 2766642495596151092408467)
                      ·
                        rfl

theorem cell23_5388017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_5388017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388017 prefixEnd_5388017 := by exact prefixLift 5388017
  have htrace : WordTrace (prefixWord ++ tailWord_5388017) baseStart_5388017 baseEnd_5388017 := by
    simpa [prefixWord, tailWord_5388017, baseEnd_5388017] using wordTrace_append hprefix tailTrace_5388017
  have hstable : (prefixWord ++ tailWord_5388017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388017).length < 2 ^ (prefixWord ++ tailWord_5388017).sum := by decide
  have hdescent : baseEnd_5388017 < baseStart_5388017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388034 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_5388034 : Nat := 118140960795 + 5388034 * 2 ^ 59
def prefixEnd_5388034 : Nat := 4983230072969 + 3 ^ 40 * 5388034 * 2
def baseEnd_5388034 : Nat := 2766651224767277525895889

theorem tailTrace_5388034 : CollatzResearch.WordTrace tailWord_5388034 prefixEnd_5388034 2766651224767277525895889 := by
  unfold tailWord_5388034
  simp only [CollatzResearch.WordTrace]
  refine ⟨49129436140520123947802789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131011829708053663860807437 49129436140520123947802789)
  ·
    refine ⟨9211769276347523240213023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49129436140520123947802789 9211769276347523240213023)
    ·
      refine ⟨13817653914521284860319535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9211769276347523240213023 13817653914521284860319535)
      ·
        refine ⟨20726480871781927290479303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13817653914521284860319535 20726480871781927290479303)
        ·
          refine ⟨31089721307672890935718955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20726480871781927290479303 31089721307672890935718955)
          ·
            refine ⟨46634581961509336403578433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31089721307672890935718955 46634581961509336403578433)
            ·
              refine ⟨34975936471132002302683825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46634581961509336403578433 34975936471132002302683825)
              ·
                refine ⟨26231952353349001727012869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34975936471132002302683825 26231952353349001727012869)
                ·
                  refine ⟨4918491066252937823814913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26231952353349001727012869 4918491066252937823814913)
                  ·
                    refine ⟨3688868299689703367861185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4918491066252937823814913 3688868299689703367861185)
                    ·
                      refine ⟨2766651224767277525895889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3688868299689703367861185 2766651224767277525895889)
                      ·
                        rfl

theorem cell23_5388034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_5388034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388034 prefixEnd_5388034 := by exact prefixLift 5388034
  have htrace : WordTrace (prefixWord ++ tailWord_5388034) baseStart_5388034 baseEnd_5388034 := by
    simpa [prefixWord, tailWord_5388034, baseEnd_5388034] using wordTrace_append hprefix tailTrace_5388034
  have hstable : (prefixWord ++ tailWord_5388034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388034).length < 2 ^ (prefixWord ++ tailWord_5388034).sum := by decide
  have hdescent : baseEnd_5388034 < baseStart_5388034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388063 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 7]
def baseStart_5388063 : Nat := 118140960795 + 5388063 * 2 ^ 59
def prefixEnd_5388063 : Nat := 4983230072969 + 3 ^ 40 * 5388063 * 2
def baseEnd_5388063 : Nat := 2766666115706257912433255

theorem tailTrace_5388063 : CollatzResearch.WordTrace tailWord_5388063 prefixEnd_5388063 2766666115706257912433255 := by
  unfold tailWord_5388063
  simp only [CollatzResearch.WordTrace]
  refine ⟨196518802278975433744016843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131012534852650289162677895 196518802278975433744016843)
  ·
    refine ⟨294778203418463150616025265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196518802278975433744016843 294778203418463150616025265)
    ·
      refine ⟨221083652563847362962018949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294778203418463150616025265 221083652563847362962018949)
      ·
        refine ⟨41453184855721380555378553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221083652563847362962018949 41453184855721380555378553)
        ·
          refine ⟨31089888641791035416533915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41453184855721380555378553 31089888641791035416533915)
          ·
            refine ⟨46634832962686553124800873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31089888641791035416533915 46634832962686553124800873)
            ·
              refine ⟨34976124722014914843600655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46634832962686553124800873 34976124722014914843600655)
              ·
                refine ⟨52464187083022372265400983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34976124722014914843600655 52464187083022372265400983)
                ·
                  refine ⟨78696280624533558398101475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52464187083022372265400983 78696280624533558398101475)
                  ·
                    refine ⟨118044420936800337597152213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78696280624533558398101475 118044420936800337597152213)
                    ·
                      refine ⟨2766666115706257912433255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118044420936800337597152213 2766666115706257912433255)
                      ·
                        rfl

theorem cell23_5388063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_5388063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388063 prefixEnd_5388063 := by exact prefixLift 5388063
  have htrace : WordTrace (prefixWord ++ tailWord_5388063) baseStart_5388063 baseEnd_5388063 := by
    simpa [prefixWord, tailWord_5388063, baseEnd_5388063] using wordTrace_append hprefix tailTrace_5388063
  have hstable : (prefixWord ++ tailWord_5388063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388063).length < 2 ^ (prefixWord ++ tailWord_5388063).sum := by decide
  have hdescent : baseEnd_5388063 < baseStart_5388063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388090 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4]
def baseStart_5388090 : Nat := 118140960795 + 5388090 * 2 ^ 59
def prefixEnd_5388090 : Nat := 4983230072969 + 3 ^ 40 * 5388090 * 2
def baseEnd_5388090 : Nat := 2766679979683929306795631

theorem tailTrace_5388090 : CollatzResearch.WordTrace tailWord_5388090 prefixEnd_5388090 2766679979683929306795631 := by
  unfold tailWord_5388090
  simp only [CollatzResearch.WordTrace]
  refine ⟨49129946762469404338812431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131013191366585078236833149 49129946762469404338812431)
  ·
    refine ⟨73694920143704106508218647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49129946762469404338812431 73694920143704106508218647)
    ·
      refine ⟨110542380215556159762327971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73694920143704106508218647 110542380215556159762327971)
      ·
        refine ⟨165813570323334239643491957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110542380215556159762327971 165813570323334239643491957)
        ·
          refine ⟨15545022217812584966577371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 165813570323334239643491957 15545022217812584966577371)
          ·
            refine ⟨23317533326718877449866057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15545022217812584966577371 23317533326718877449866057)
            ·
              refine ⟨17488149995039158087399543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23317533326718877449866057 17488149995039158087399543)
              ·
                refine ⟨26232224992558737131099315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17488149995039158087399543 26232224992558737131099315)
                ·
                  refine ⟨39348337488838105696648973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26232224992558737131099315 39348337488838105696648973)
                  ·
                    refine ⟨14755626558314289636243365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39348337488838105696648973 14755626558314289636243365)
                    ·
                      refine ⟨2766679979683929306795631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14755626558314289636243365 2766679979683929306795631)
                      ·
                        rfl

theorem cell23_5388090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_5388090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388090 prefixEnd_5388090 := by exact prefixLift 5388090
  have htrace : WordTrace (prefixWord ++ tailWord_5388090) baseStart_5388090 baseEnd_5388090 := by
    simpa [prefixWord, tailWord_5388090, baseEnd_5388090] using wordTrace_append hprefix tailTrace_5388090
  have hstable : (prefixWord ++ tailWord_5388090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388090).length < 2 ^ (prefixWord ++ tailWord_5388090).sum := by decide
  have hdescent : baseEnd_5388090 < baseStart_5388090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388103 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_5388103 : Nat := 118140960795 + 5388103 * 2 ^ 59
def prefixEnd_5388103 : Nat := 4983230072969 + 3 ^ 40 * 5388103 * 2
def baseEnd_5388103 : Nat := 2766686654932437755933071

theorem tailTrace_5388103 : CollatzResearch.WordTrace tailWord_5388103 prefixEnd_5388103 2766686654932437755933071 := by
  unfold tailWord_5388103
  simp only [CollatzResearch.WordTrace]
  refine ⟨196520261198830520575472963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131013507465887013716981975 196520261198830520575472963)
  ·
    refine ⟨294780391798245780863209445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196520261198830520575472963 294780391798245780863209445)
    ·
      refine ⟨55271323462171083911851771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 294780391798245780863209445 55271323462171083911851771)
      ·
        refine ⟨82906985193256625867777657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55271323462171083911851771 82906985193256625867777657)
        ·
          refine ⟨62180238894942469400833243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82906985193256625867777657 62180238894942469400833243)
          ·
            refine ⟨93270358342413704101249865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62180238894942469400833243 93270358342413704101249865)
            ·
              refine ⟨69952768756810278075937399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93270358342413704101249865 69952768756810278075937399)
              ·
                refine ⟨104929153135215417113906099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69952768756810278075937399 104929153135215417113906099)
                ·
                  refine ⟨157393729702823125670859149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104929153135215417113906099 157393729702823125670859149)
                  ·
                    refine ⟨59022648638558672126572181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 157393729702823125670859149 59022648638558672126572181)
                    ·
                      refine ⟨2766686654932437755933071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59022648638558672126572181 2766686654932437755933071)
                      ·
                        rfl

theorem cell23_5388103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_5388103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388103 prefixEnd_5388103 := by exact prefixLift 5388103
  have htrace : WordTrace (prefixWord ++ tailWord_5388103) baseStart_5388103 baseEnd_5388103 := by
    simpa [prefixWord, tailWord_5388103, baseEnd_5388103] using wordTrace_append hprefix tailTrace_5388103
  have hstable : (prefixWord ++ tailWord_5388103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388103).length < 2 ^ (prefixWord ++ tailWord_5388103).sum := by decide
  have hdescent : baseEnd_5388103 < baseStart_5388103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388117 : List Nat := [1, 3, 2, 2, 2, 2, 3, 1, 3, 4]
def baseStart_5388117 : Nat := 118140960795 + 5388117 * 2 ^ 59
def prefixEnd_5388117 : Nat := 4983230072969 + 3 ^ 40 * 5388117 * 2
def baseEnd_5388117 : Nat := 922231281220533567052669

theorem tailTrace_5388117 : CollatzResearch.WordTrace tailWord_5388117 prefixEnd_5388117 922231281220533567052669 := by
  unfold tailWord_5388117
  simp only [CollatzResearch.WordTrace]
  refine ⟨196520771820779800966482605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131013847880519867310988403 196520771820779800966482605)
  ·
    refine ⟨73695289432792425362430977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196520771820779800966482605 73695289432792425362430977)
    ·
      refine ⟨55271467074594319021823233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73695289432792425362430977 55271467074594319021823233)
      ·
        refine ⟨41453600305945739266367425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55271467074594319021823233 41453600305945739266367425)
        ·
          refine ⟨31090200229459304449775569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41453600305945739266367425 31090200229459304449775569)
          ·
            refine ⟨23317650172094478337331677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31090200229459304449775569 23317650172094478337331677)
            ·
              refine ⟨8744118814535429376499379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23317650172094478337331677 8744118814535429376499379)
              ·
                refine ⟨13116178221803144064749069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8744118814535429376499379 13116178221803144064749069)
                ·
                  refine ⟨4918566833176179024280901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13116178221803144064749069 4918566833176179024280901)
                  ·
                    refine ⟨922231281220533567052669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4918566833176179024280901 922231281220533567052669)
                    ·
                      rfl

theorem cell23_5388117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_5388117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388117 prefixEnd_5388117 := by exact prefixLift 5388117
  have htrace : WordTrace (prefixWord ++ tailWord_5388117) baseStart_5388117 baseEnd_5388117 := by
    simpa [prefixWord, tailWord_5388117, baseEnd_5388117] using wordTrace_append hprefix tailTrace_5388117
  have hstable : (prefixWord ++ tailWord_5388117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388117).length < 2 ^ (prefixWord ++ tailWord_5388117).sum := by decide
  have hdescent : baseEnd_5388117 < baseStart_5388117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388168 : List Nat := [2, 1, 3, 3, 3, 2, 2, 2, 1, 4]
def baseStart_5388168 : Nat := 118140960795 + 5388168 * 2 ^ 59
def prefixEnd_5388168 : Nat := 4983230072969 + 3 ^ 40 * 5388168 * 2
def baseEnd_5388168 : Nat := 922240010391660000540091

theorem tailTrace_5388168 : CollatzResearch.WordTrace tailWord_5388168 prefixEnd_5388168 922240010391660000540091 := by
  unfold tailWord_5388168
  simp only [CollatzResearch.WordTrace]
  refine ⟨98261315971797518338294579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131015087962396691117726105 98261315971797518338294579)
  ·
    refine ⟨147391973957696277507441869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98261315971797518338294579 147391973957696277507441869)
    ·
      refine ⟨55271990234136104065290701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147391973957696277507441869 55271990234136104065290701)
      ·
        refine ⟨20726996337801039024484013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55271990234136104065290701 20726996337801039024484013)
        ·
          refine ⟨7772623626675389634181505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20726996337801039024484013 7772623626675389634181505)
          ·
            refine ⟨5829467720006542225636129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7772623626675389634181505 5829467720006542225636129)
            ·
              refine ⟨4372100790004906669227097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5829467720006542225636129 4372100790004906669227097)
              ·
                refine ⟨3279075592503680001920323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4372100790004906669227097 3279075592503680001920323)
                ·
                  refine ⟨4918613388755520002880485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3279075592503680001920323 4918613388755520002880485)
                  ·
                    refine ⟨922240010391660000540091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4918613388755520002880485 922240010391660000540091)
                    ·
                      rfl

theorem cell23_5388168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_5388168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388168 prefixEnd_5388168 := by exact prefixLift 5388168
  have htrace : WordTrace (prefixWord ++ tailWord_5388168) baseStart_5388168 baseEnd_5388168 := by
    simpa [prefixWord, tailWord_5388168, baseEnd_5388168] using wordTrace_append hprefix tailTrace_5388168
  have hstable : (prefixWord ++ tailWord_5388168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388168).length < 2 ^ (prefixWord ++ tailWord_5388168).sum := by decide
  have hdescent : baseEnd_5388168 < baseStart_5388168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388260 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_5388260 : Nat := 118140960795 + 5388260 * 2 ^ 59
def prefixEnd_5388260 : Nat := 4983230072969 + 3 ^ 40 * 5388260 * 2
def baseEnd_5388260 : Nat := 2766767271395193641669849

theorem tailTrace_5388260 : CollatzResearch.WordTrace tailWord_5388260 prefixEnd_5388260 2766767271395193641669849 := by
  unfold tailWord_5388260
  simp only [CollatzResearch.WordTrace]
  refine ⟨98262993729630868194469117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131017324972841157592625489 98262993729630868194469117)
  ·
    refine ⟨36848622648611575572925919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98262993729630868194469117 36848622648611575572925919)
    ·
      refine ⟨55272933972917363359388879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36848622648611575572925919 55272933972917363359388879)
      ·
        refine ⟨82909400959376045039083319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55272933972917363359388879 82909400959376045039083319)
        ·
          refine ⟨124364101439064067558624979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82909400959376045039083319 124364101439064067558624979)
          ·
            refine ⟨186546152158596101337937469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124364101439064067558624979 186546152158596101337937469)
            ·
              refine ⟨69954807059473538001726551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186546152158596101337937469 69954807059473538001726551)
              ·
                refine ⟨104932210589210307002589827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69954807059473538001726551 104932210589210307002589827)
                ·
                  refine ⟨157398315883815460503884741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104932210589210307002589827 157398315883815460503884741)
                  ·
                    refine ⟨29512184228215398844478389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 157398315883815460503884741 29512184228215398844478389)
                    ·
                      refine ⟨2766767271395193641669849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29512184228215398844478389 2766767271395193641669849)
                      ·
                        rfl

theorem cell23_5388260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_5388260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388260 prefixEnd_5388260 := by exact prefixLift 5388260
  have htrace : WordTrace (prefixWord ++ tailWord_5388260) baseStart_5388260 baseEnd_5388260 := by
    simpa [prefixWord, tailWord_5388260, baseEnd_5388260] using wordTrace_append hprefix tailTrace_5388260
  have hstable : (prefixWord ++ tailWord_5388260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388260).length < 2 ^ (prefixWord ++ tailWord_5388260).sum := by decide
  have hdescent : baseEnd_5388260 < baseStart_5388260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388280 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 4, 6]
def baseStart_5388280 : Nat := 118140960795 + 5388280 * 2 ^ 59
def prefixEnd_5388280 : Nat := 4983230072969 + 3 ^ 40 * 5388280 * 2
def baseEnd_5388280 : Nat := 922259180336094521139919

theorem tailTrace_5388280 : CollatzResearch.WordTrace tailWord_5388280 prefixEnd_5388280 922259180336094521139919 := by
  unfold tailWord_5388280
  simp only [CollatzResearch.WordTrace]
  refine ⟨98263358459594639902333147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131017811279459519869777529 98263358459594639902333147)
  ·
    refine ⟨147395037689391959853499721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98263358459594639902333147 147395037689391959853499721)
    ·
      refine ⟨110546278267043969890124791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147395037689391959853499721 110546278267043969890124791)
      ·
        refine ⟨165819417400565954835187187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110546278267043969890124791 165819417400565954835187187)
        ·
          refine ⟨248729126100848932252780781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165819417400565954835187187 248729126100848932252780781)
          ·
            refine ⟨93273422287818349594792793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248729126100848932252780781 93273422287818349594792793)
            ·
              refine ⟨69955066715863762196094595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93273422287818349594792793 69955066715863762196094595)
              ·
                refine ⟨104932600073795643294141893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69955066715863762196094595 104932600073795643294141893)
                ·
                  refine ⟨19674862513836683117651605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104932600073795643294141893 19674862513836683117651605)
                  ·
                    refine ⟨922259180336094521139919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19674862513836683117651605 922259180336094521139919)
                    ·
                      rfl

theorem cell23_5388280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_5388280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388280 prefixEnd_5388280 := by exact prefixLift 5388280
  have htrace : WordTrace (prefixWord ++ tailWord_5388280) baseStart_5388280 baseEnd_5388280 := by
    simpa [prefixWord, tailWord_5388280, baseEnd_5388280] using wordTrace_append hprefix tailTrace_5388280
  have hstable : (prefixWord ++ tailWord_5388280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388280).length < 2 ^ (prefixWord ++ tailWord_5388280).sum := by decide
  have hdescent : baseEnd_5388280 < baseStart_5388280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388321 : List Nat := [1, 2, 3, 2, 4, 1, 1, 2, 1, 4, 2]
def baseStart_5388321 : Nat := 118140960795 + 5388321 * 2 ^ 59
def prefixEnd_5388321 : Nat := 4983230072969 + 3 ^ 40 * 5388321 * 2
def baseEnd_5388321 : Nat := 2766798593715117903007069

theorem tailTrace_5388321 : CollatzResearch.WordTrace tailWord_5388321 prefixEnd_5388321 2766798593715117903007069 := by
  unfold tailWord_5388321
  simp only [CollatzResearch.WordTrace]
  refine ⟨196528212312040743806908817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131018808208027162537939211 196528212312040743806908817)
  ·
    refine ⟨147396159234030557855181613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196528212312040743806908817 147396159234030557855181613)
    ·
      refine ⟨55273559712761459195693105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147396159234030557855181613 55273559712761459195693105)
      ·
        refine ⟨41455169784571094396769829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55273559712761459195693105 41455169784571094396769829)
        ·
          refine ⟨7772844334607080199394343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41455169784571094396769829 7772844334607080199394343)
          ·
            refine ⟨11659266501910620299091515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7772844334607080199394343 11659266501910620299091515)
            ·
              refine ⟨17488899752865930448637273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11659266501910620299091515 17488899752865930448637273)
              ·
                refine ⟨13116674814649447836477955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17488899752865930448637273 13116674814649447836477955)
                ·
                  refine ⟨19675012221974171754716933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13116674814649447836477955 19675012221974171754716933)
                  ·
                    refine ⟨3689064791620157204009425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19675012221974171754716933 3689064791620157204009425)
                    ·
                      refine ⟨2766798593715117903007069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3689064791620157204009425 2766798593715117903007069)
                      ·
                        rfl

theorem cell23_5388321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_5388321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388321 prefixEnd_5388321 := by exact prefixLift 5388321
  have htrace : WordTrace (prefixWord ++ tailWord_5388321) baseStart_5388321 baseEnd_5388321 := by
    simpa [prefixWord, tailWord_5388321, baseEnd_5388321] using wordTrace_append hprefix tailTrace_5388321
  have hstable : (prefixWord ++ tailWord_5388321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388321).length < 2 ^ (prefixWord ++ tailWord_5388321).sum := by decide
  have hdescent : baseEnd_5388321 < baseStart_5388321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388338 : List Nat := [3, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2]
def baseStart_5388338 : Nat := 118140960795 + 5388338 * 2 ^ 59
def prefixEnd_5388338 : Nat := 4983230072969 + 3 ^ 40 * 5388338 * 2
def baseEnd_5388338 : Nat := 2766807322886244336494491

theorem tailTrace_5388338 : CollatzResearch.WordTrace tailWord_5388338 prefixEnd_5388338 2766807322886244336494491 := by
  unfold tailWord_5388338
  simp only [CollatzResearch.WordTrace]
  refine ⟨49132208088244788927569417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131019221568652770473518445 49132208088244788927569417)
  ·
    refine ⟨36849156066183591695677063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49132208088244788927569417 36849156066183591695677063)
    ·
      refine ⟨55273734099275387543515595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36849156066183591695677063 55273734099275387543515595)
      ·
        refine ⟨82910601148913081315273393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55273734099275387543515595 82910601148913081315273393)
        ·
          refine ⟨62182950861684810986455045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82910601148913081315273393 62182950861684810986455045)
          ·
            refine ⟨11659303286565902059960321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62182950861684810986455045 11659303286565902059960321)
            ·
              refine ⟨8744477464924426544970241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11659303286565902059960321 8744477464924426544970241)
              ·
                refine ⟨6558358098693319908727681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8744477464924426544970241 6558358098693319908727681)
                ·
                  refine ⟨4918768574019989931545761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6558358098693319908727681 4918768574019989931545761)
                  ·
                    refine ⟨3689076430514992448659321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4918768574019989931545761 3689076430514992448659321)
                    ·
                      refine ⟨2766807322886244336494491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3689076430514992448659321 2766807322886244336494491)
                      ·
                        rfl

theorem cell23_5388338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_5388338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388338 prefixEnd_5388338 := by exact prefixLift 5388338
  have htrace : WordTrace (prefixWord ++ tailWord_5388338) baseStart_5388338 baseEnd_5388338 := by
    simpa [prefixWord, tailWord_5388338, baseEnd_5388338] using wordTrace_append hprefix tailTrace_5388338
  have hstable : (prefixWord ++ tailWord_5388338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388338).length < 2 ^ (prefixWord ++ tailWord_5388338).sum := by decide
  have hdescent : baseEnd_5388338 < baseStart_5388338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388377 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 1, 3, 4]
def baseStart_5388377 : Nat := 118140960795 + 5388377 * 2 ^ 59
def prefixEnd_5388377 : Nat := 4983230072969 + 3 ^ 40 * 5388377 * 2
def baseEnd_5388377 : Nat := 2766827348631769683906811

theorem tailTrace_5388377 : CollatzResearch.WordTrace tailWord_5388377 prefixEnd_5388377 2766827348631769683906811 := by
  unfold tailWord_5388377
  simp only [CollatzResearch.WordTrace]
  refine ⟨196530254799837865370947385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131020169866558576913964923 196530254799837865370947385)
  ·
    refine ⟨147397691099878399028210539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196530254799837865370947385 147397691099878399028210539)
    ·
      refine ⟨221096536649817598542315809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147397691099878399028210539 221096536649817598542315809)
      ·
        refine ⟨165822402487363198906736857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221096536649817598542315809 165822402487363198906736857)
        ·
          refine ⟨124366801865522399180052643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165822402487363198906736857 124366801865522399180052643)
          ·
            refine ⟨186550202798283598770078965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124366801865522399180052643 186550202798283598770078965)
            ·
              refine ⟨17489081512339087384694903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 186550202798283598770078965 17489081512339087384694903)
              ·
                refine ⟨26233622268508631077042355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17489081512339087384694903 26233622268508631077042355)
                ·
                  refine ⟨39350433402762946615563533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26233622268508631077042355 39350433402762946615563533)
                  ·
                    refine ⟨14756412526036104980836325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39350433402762946615563533 14756412526036104980836325)
                    ·
                      refine ⟨2766827348631769683906811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14756412526036104980836325 2766827348631769683906811)
                      ·
                        rfl

theorem cell23_5388377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_5388377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388377 prefixEnd_5388377 := by exact prefixLift 5388377
  have htrace : WordTrace (prefixWord ++ tailWord_5388377) baseStart_5388377 baseEnd_5388377 := by
    simpa [prefixWord, tailWord_5388377, baseEnd_5388377] using wordTrace_append hprefix tailTrace_5388377
  have hstable : (prefixWord ++ tailWord_5388377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388377).length < 2 ^ (prefixWord ++ tailWord_5388377).sum := by decide
  have hdescent : baseEnd_5388377 < baseStart_5388377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388455 : List Nat := [1, 1, 6, 2, 3, 1, 1, 1, 3, 4]
def baseStart_5388455 : Nat := 118140960795 + 5388455 * 2 ^ 59
def prefixEnd_5388455 : Nat := 4983230072969 + 3 ^ 40 * 5388455 * 2
def baseEnd_5388455 : Nat := 922289133374273459577151

theorem tailTrace_5388455 : CollatzResearch.WordTrace tailWord_5388455 prefixEnd_5388455 922289133374273459577151 := by
  unfold tailWord_5388455
  simp only [CollatzResearch.WordTrace]
  refine ⟨196533099693555284692286819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131022066462370189794857879 196533099693555284692286819)
  ·
    refine ⟨294799649540332927038430229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196533099693555284692286819 294799649540332927038430229)
    ·
      refine ⟨13818733572203105954926417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 294799649540332927038430229 13818733572203105954926417)
      ·
        refine ⟨10364050179152329466194813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13818733572203105954926417 10364050179152329466194813)
        ·
          refine ⟨3886518817182123549823055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10364050179152329466194813 3886518817182123549823055)
          ·
            refine ⟨5829778225773185324734583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3886518817182123549823055 5829778225773185324734583)
            ·
              refine ⟨8744667338659777987101875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5829778225773185324734583 8744667338659777987101875)
              ·
                refine ⟨13117001007989666980652813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8744667338659777987101875 13117001007989666980652813)
                ·
                  refine ⟨4918875377996125117744805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13117001007989666980652813 4918875377996125117744805)
                  ·
                    refine ⟨922289133374273459577151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4918875377996125117744805 922289133374273459577151)
                    ·
                      rfl

theorem cell23_5388455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_5388455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388455 prefixEnd_5388455 := by exact prefixLift 5388455
  have htrace : WordTrace (prefixWord ++ tailWord_5388455) baseStart_5388455 baseEnd_5388455 := by
    simpa [prefixWord, tailWord_5388455, baseEnd_5388455] using wordTrace_append hprefix tailTrace_5388455
  have hstable : (prefixWord ++ tailWord_5388455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388455).length < 2 ^ (prefixWord ++ tailWord_5388455).sum := by decide
  have hdescent : baseEnd_5388455 < baseStart_5388455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388467 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 4]
def baseStart_5388467 : Nat := 118140960795 + 5388467 * 2 ^ 59
def prefixEnd_5388467 : Nat := 4983230072969 + 3 ^ 40 * 5388467 * 2
def baseEnd_5388467 : Nat := 2766873561890674331781397

theorem tailTrace_5388467 : CollatzResearch.WordTrace tailWord_5388467 prefixEnd_5388467 2766873561890674331781397 := by
  unfold tailWord_5388467
  simp only [CollatzResearch.WordTrace]
  refine ⟨196533537369511810741723655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131022358246341207161149103 196533537369511810741723655)
  ·
    refine ⟨294800306054267716112585483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196533537369511810741723655 294800306054267716112585483)
    ·
      refine ⟨442200459081401574168878225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294800306054267716112585483 442200459081401574168878225)
      ·
        refine ⟨331650344311051180626658669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 442200459081401574168878225 331650344311051180626658669)
        ·
          refine ⟨124368879116644192734997001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 331650344311051180626658669 124368879116644192734997001)
          ·
            refine ⟨93276659337483144551247751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124368879116644192734997001 93276659337483144551247751)
            ·
              refine ⟨139914989006224716826871627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93276659337483144551247751 139914989006224716826871627)
              ·
                refine ⟨209872483509337075240307441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139914989006224716826871627 209872483509337075240307441)
                ·
                  refine ⟨157404362632002806430230581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209872483509337075240307441 157404362632002806430230581)
                  ·
                    refine ⟨14756658996750263102834117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 157404362632002806430230581 14756658996750263102834117)
                    ·
                      refine ⟨2766873561890674331781397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14756658996750263102834117 2766873561890674331781397)
                      ·
                        rfl

theorem cell23_5388467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 4].length) (baseStart_5388467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388467 prefixEnd_5388467 := by exact prefixLift 5388467
  have htrace : WordTrace (prefixWord ++ tailWord_5388467) baseStart_5388467 baseEnd_5388467 := by
    simpa [prefixWord, tailWord_5388467, baseEnd_5388467] using wordTrace_append hprefix tailTrace_5388467
  have hstable : (prefixWord ++ tailWord_5388467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388467).length < 2 ^ (prefixWord ++ tailWord_5388467).sum := by decide
  have hdescent : baseEnd_5388467 < baseStart_5388467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388487 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_5388487 : Nat := 118140960795 + 5388487 * 2 ^ 59
def prefixEnd_5388487 : Nat := 4983230072969 + 3 ^ 40 * 5388487 * 2
def baseEnd_5388487 : Nat := 2766883831503764253531305

theorem tailTrace_5388487 : CollatzResearch.WordTrace tailWord_5388487 prefixEnd_5388487 2766883831503764253531305 := by
  unfold tailWord_5388487
  simp only [CollatzResearch.WordTrace]
  refine ⟨196534266829439354157451715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131022844552959569438301143 196534266829439354157451715)
  ·
    refine ⟨294801400244159031236177573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196534266829439354157451715 294801400244159031236177573)
    ·
      refine ⟨55275262545779818356783295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 294801400244159031236177573 55275262545779818356783295)
      ·
        refine ⟨82912893818669727535174943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55275262545779818356783295 82912893818669727535174943)
        ·
          refine ⟨124369340728004591302762415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82912893818669727535174943 124369340728004591302762415)
          ·
            refine ⟨186554011092006886954143623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124369340728004591302762415 186554011092006886954143623)
            ·
              refine ⟨279831016638010330431215435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186554011092006886954143623 279831016638010330431215435)
              ·
                refine ⟨419746524957015495646823153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279831016638010330431215435 419746524957015495646823153)
                ·
                  refine ⟨314809893717761621735117365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 419746524957015495646823153 314809893717761621735117365)
                  ·
                    refine ⟨29513427536040152037667253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 314809893717761621735117365 29513427536040152037667253)
                    ·
                      refine ⟨2766883831503764253531305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29513427536040152037667253 2766883831503764253531305)
                      ·
                        rfl

theorem cell23_5388487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_5388487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388487 prefixEnd_5388487 := by exact prefixLift 5388487
  have htrace : WordTrace (prefixWord ++ tailWord_5388487) baseStart_5388487 baseEnd_5388487 := by
    simpa [prefixWord, tailWord_5388487, baseEnd_5388487] using wordTrace_append hprefix tailTrace_5388487
  have hstable : (prefixWord ++ tailWord_5388487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388487).length < 2 ^ (prefixWord ++ tailWord_5388487).sum := by decide
  have hdescent : baseEnd_5388487 < baseStart_5388487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388494 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 3, 6]
def baseStart_5388494 : Nat := 118140960795 + 5388494 * 2 ^ 59
def prefixEnd_5388494 : Nat := 4983230072969 + 3 ^ 40 * 5388494 * 2
def baseEnd_5388494 : Nat := 922295808622781908714591

theorem tailTrace_5388494 : CollatzResearch.WordTrace tailWord_5388494 prefixEnd_5388494 922295808622781908714591 := by
  unfold tailWord_5388494
  simp only [CollatzResearch.WordTrace]
  refine ⟨24566815267551749294119567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131023014760275996235304357 24566815267551749294119567)
  ·
    refine ⟨36850222901327623941179351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24566815267551749294119567 36850222901327623941179351)
    ·
      refine ⟨55275334351991435911769027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36850222901327623941179351 55275334351991435911769027)
      ·
        refine ⟨82913001527987153867653541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55275334351991435911769027 82913001527987153867653541)
        ·
          refine ⟨15546187786497591350185039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82913001527987153867653541 15546187786497591350185039)
          ·
            refine ⟨23319281679746387025277559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15546187786497591350185039 23319281679746387025277559)
            ·
              refine ⟨34978922519619580537916339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23319281679746387025277559 34978922519619580537916339)
              ·
                refine ⟨52468383779429370806874509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34978922519619580537916339 52468383779429370806874509)
                ·
                  refine ⟨19675643917286014052577941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52468383779429370806874509 19675643917286014052577941)
                  ·
                    refine ⟨922295808622781908714591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19675643917286014052577941 922295808622781908714591)
                    ·
                      rfl

theorem cell23_5388494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_5388494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388494 prefixEnd_5388494 := by exact prefixLift 5388494
  have htrace : WordTrace (prefixWord ++ tailWord_5388494) baseStart_5388494 baseEnd_5388494 := by
    simpa [prefixWord, tailWord_5388494, baseEnd_5388494] using wordTrace_append hprefix tailTrace_5388494
  have hstable : (prefixWord ++ tailWord_5388494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388494).length < 2 ^ (prefixWord ++ tailWord_5388494).sum := by decide
  have hdescent : baseEnd_5388494 < baseStart_5388494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388498 : List Nat := [3, 2, 2, 2, 1, 3, 3, 1, 1, 5]
def baseStart_5388498 : Nat := 118140960795 + 5388498 * 2 ^ 59
def prefixEnd_5388498 : Nat := 4983230072969 + 3 ^ 40 * 5388498 * 2
def baseEnd_5388498 : Nat := 922296493263654570164585

theorem tailTrace_5388498 : CollatzResearch.WordTrace tailWord_5388498 prefixEnd_5388498 922296493263654570164585 := by
  unfold tailWord_5388498
  simp only [CollatzResearch.WordTrace]
  refine ⟨49133667008099875759025537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131023112021599668690734765 49133667008099875759025537)
  ·
    refine ⟨36850250256074906819269153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49133667008099875759025537 36850250256074906819269153)
    ·
      refine ⟨27637687692056180114451865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36850250256074906819269153 27637687692056180114451865)
      ·
        refine ⟨20728265769042135085838899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27637687692056180114451865 20728265769042135085838899)
        ·
          refine ⟨31092398653563202628758349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20728265769042135085838899 31092398653563202628758349)
          ·
            refine ⟨11659649495086200985784381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31092398653563202628758349 11659649495086200985784381)
            ·
              refine ⟨4372368560657325369669143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11659649495086200985784381 4372368560657325369669143)
              ·
                refine ⟨6558552840985988054503715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4372368560657325369669143 6558552840985988054503715)
                ·
                  refine ⟨9837829261478982081755573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6558552840985988054503715 9837829261478982081755573)
                  ·
                    refine ⟨922296493263654570164585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9837829261478982081755573 922296493263654570164585)
                    ·
                      rfl

theorem cell23_5388498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_5388498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388498 prefixEnd_5388498 := by exact prefixLift 5388498
  have htrace : WordTrace (prefixWord ++ tailWord_5388498) baseStart_5388498 baseEnd_5388498 := by
    simpa [prefixWord, tailWord_5388498, baseEnd_5388498] using wordTrace_append hprefix tailTrace_5388498
  have hstable : (prefixWord ++ tailWord_5388498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388498).length < 2 ^ (prefixWord ++ tailWord_5388498).sum := by decide
  have hdescent : baseEnd_5388498 < baseStart_5388498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388552 : List Nat := [2, 1, 3, 2, 3, 2, 2, 3, 1, 2, 2]
def baseStart_5388552 : Nat := 118140960795 + 5388552 * 2 ^ 59
def prefixEnd_5388552 : Nat := 4983230072969 + 3 ^ 40 * 5388552 * 2
def baseEnd_5388552 : Nat := 2766917207746306499218507

theorem tailTrace_5388552 : CollatzResearch.WordTrace tailWord_5388552 prefixEnd_5388552 2766917207746306499218507 := by
  unfold tailWord_5388552
  simp only [CollatzResearch.WordTrace]
  refine ⟨98268318787101935129283955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131024425049469246839045273 98268318787101935129283955)
  ·
    refine ⟨147402478180652902693925933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98268318787101935129283955 147402478180652902693925933)
    ·
      refine ⟨55275929317744838510222225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147402478180652902693925933 55275929317744838510222225)
      ·
        refine ⟨41456946988308628882666669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55275929317744838510222225 41456946988308628882666669)
        ·
          refine ⟨15546355120615735831000001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41456946988308628882666669 15546355120615735831000001)
          ·
            refine ⟨11659766340461801873250001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15546355120615735831000001 11659766340461801873250001)
            ·
              refine ⟨8744824755346351404937501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11659766340461801873250001 8744824755346351404937501)
              ·
                refine ⟨3279309283254881776851563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8744824755346351404937501 3279309283254881776851563)
                ·
                  refine ⟨4918963924882322665277345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3279309283254881776851563 4918963924882322665277345)
                  ·
                    refine ⟨3689222943661741998958009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4918963924882322665277345 3689222943661741998958009)
                    ·
                      refine ⟨2766917207746306499218507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3689222943661741998958009 2766917207746306499218507)
                      ·
                        rfl

theorem cell23_5388552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_5388552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388552 prefixEnd_5388552 := by exact prefixLift 5388552
  have htrace : WordTrace (prefixWord ++ tailWord_5388552) baseStart_5388552 baseEnd_5388552 := by
    simpa [prefixWord, tailWord_5388552, baseEnd_5388552] using wordTrace_append hprefix tailTrace_5388552
  have hstable : (prefixWord ++ tailWord_5388552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388552).length < 2 ^ (prefixWord ++ tailWord_5388552).sum := by decide
  have hdescent : baseEnd_5388552 < baseStart_5388552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388636 : List Nat := [2, 2, 4, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_5388636 : Nat := 118140960795 + 5388636 * 2 ^ 59
def prefixEnd_5388636 : Nat := 4983230072969 + 3 ^ 40 * 5388636 * 2
def baseEnd_5388636 : Nat := 2766960340121284170568121

theorem tailTrace_5388636 : CollatzResearch.WordTrace tailWord_5388636 prefixEnd_5388636 2766960340121284170568121 := by
  unfold tailWord_5388636
  simp only [CollatzResearch.WordTrace]
  refine ⟨98269850652949776302312881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131026467537266368403083841 98269850652949776302312881)
  ·
    refine ⟨73702387989712332226734661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98269850652949776302312881 73702387989712332226734661)
    ·
      refine ⟨13819197748071062292512749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73702387989712332226734661 13819197748071062292512749)
      ·
        refine ⟨5182199155526648359692281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13819197748071062292512749 5182199155526648359692281)
        ·
          refine ⟨3886649366644986269769211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5182199155526648359692281 3886649366644986269769211)
          ·
            refine ⟨5829974049967479404653817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3886649366644986269769211 5829974049967479404653817)
            ·
              refine ⟨4372480537475609553490363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5829974049967479404653817 4372480537475609553490363)
              ·
                refine ⟨6558720806213414330235545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4372480537475609553490363 6558720806213414330235545)
                ·
                  refine ⟨4919040604660060747676659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6558720806213414330235545 4919040604660060747676659)
                  ·
                    refine ⟨7378560906990091121514989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4919040604660060747676659 7378560906990091121514989)
                    ·
                      refine ⟨2766960340121284170568121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7378560906990091121514989 2766960340121284170568121)
                      ·
                        rfl

theorem cell23_5388636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_5388636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388636 prefixEnd_5388636 := by exact prefixLift 5388636
  have htrace : WordTrace (prefixWord ++ tailWord_5388636) baseStart_5388636 baseEnd_5388636 := by
    simpa [prefixWord, tailWord_5388636, baseEnd_5388636] using wordTrace_append hprefix tailTrace_5388636
  have hstable : (prefixWord ++ tailWord_5388636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388636).length < 2 ^ (prefixWord ++ tailWord_5388636).sum := by decide
  have hdescent : baseEnd_5388636 < baseStart_5388636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388642 : List Nat := [3, 3, 2, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_5388642 : Nat := 118140960795 + 5388642 * 2 ^ 59
def prefixEnd_5388642 : Nat := 4983230072969 + 3 ^ 40 * 5388642 * 2
def baseEnd_5388642 : Nat := 2766963421005211147093093

theorem tailTrace_5388642 : CollatzResearch.WordTrace tailWord_5388642 prefixEnd_5388642 2766963421005211147093093 := by
  unfold tailWord_5388642
  simp only [CollatzResearch.WordTrace]
  refine ⟨49134980035969453907336045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131026613429251877086229453 49134980035969453907336045)
  ·
    refine ⟨18425617513488545215251017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49134980035969453907336045 18425617513488545215251017)
    ·
      refine ⟨13819213135116408911438263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18425617513488545215251017 13819213135116408911438263)
      ·
        refine ⟨20728819702674613367157395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13819213135116408911438263 20728819702674613367157395)
        ·
          refine ⟨31093229554011920050736093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20728819702674613367157395 31093229554011920050736093)
          ·
            refine ⟨11659961082754470019026035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31093229554011920050736093 11659961082754470019026035)
            ·
              refine ⟨17489941624131705028539053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11659961082754470019026035 17489941624131705028539053)
              ·
                refine ⟨6558728109049389385702145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17489941624131705028539053 6558728109049389385702145)
                ·
                  refine ⟨4919046081787042039276609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6558728109049389385702145 4919046081787042039276609)
                  ·
                    refine ⟨3689284561340281529457457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4919046081787042039276609 3689284561340281529457457)
                    ·
                      refine ⟨2766963421005211147093093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3689284561340281529457457 2766963421005211147093093)
                      ·
                        rfl

theorem cell23_5388642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_5388642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388642 prefixEnd_5388642 := by exact prefixLift 5388642
  have htrace : WordTrace (prefixWord ++ tailWord_5388642) baseStart_5388642 baseEnd_5388642 := by
    simpa [prefixWord, tailWord_5388642, baseEnd_5388642] using wordTrace_append hprefix tailTrace_5388642
  have hstable : (prefixWord ++ tailWord_5388642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388642).length < 2 ^ (prefixWord ++ tailWord_5388642).sum := by decide
  have hdescent : baseEnd_5388642 < baseStart_5388642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388651 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 2, 5, 2]
def baseStart_5388651 : Nat := 118140960795 + 5388651 * 2 ^ 59
def prefixEnd_5388651 : Nat := 4983230072969 + 3 ^ 40 * 5388651 * 2
def baseEnd_5388651 : Nat := 2766968042331101611880551

theorem tailTrace_5388651 : CollatzResearch.WordTrace tailWord_5388651 prefixEnd_5388651 2766968042331101611880551 := by
  unfold tailWord_5388651
  simp only [CollatzResearch.WordTrace]
  refine ⟨196540248400845210166421807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131026832267230140110947871 196540248400845210166421807)
  ·
    refine ⟨294810372601267815249632711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196540248400845210166421807 294810372601267815249632711)
    ·
      refine ⟨442215558901901722874449067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294810372601267815249632711 442215558901901722874449067)
      ·
        refine ⟨663323338352852584311673601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442215558901901722874449067 663323338352852584311673601)
        ·
          refine ⟨497492503764639438233755201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 663323338352852584311673601 497492503764639438233755201)
          ·
            refine ⟨373119377823479578675316401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497492503764639438233755201 373119377823479578675316401)
            ·
              refine ⟨279839533367609684006487301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373119377823479578675316401 279839533367609684006487301)
              ·
                refine ⟨52469912506426815751216369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 279839533367609684006487301 52469912506426815751216369)
                ·
                  refine ⟨39352434379820111813412277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52469912506426815751216369 39352434379820111813412277)
                  ·
                    refine ⟨3689290723108135482507401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39352434379820111813412277 3689290723108135482507401)
                    ·
                      refine ⟨2766968042331101611880551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3689290723108135482507401 2766968042331101611880551)
                      ·
                        rfl

theorem cell23_5388651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 5, 2].length) (baseStart_5388651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388651 prefixEnd_5388651 := by exact prefixLift 5388651
  have htrace : WordTrace (prefixWord ++ tailWord_5388651) baseStart_5388651 baseEnd_5388651 := by
    simpa [prefixWord, tailWord_5388651, baseEnd_5388651] using wordTrace_append hprefix tailTrace_5388651
  have hstable : (prefixWord ++ tailWord_5388651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388651).length < 2 ^ (prefixWord ++ tailWord_5388651).sum := by decide
  have hdescent : baseEnd_5388651 < baseStart_5388651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388698 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2]
def baseStart_5388698 : Nat := 118140960795 + 5388698 * 2 ^ 59
def prefixEnd_5388698 : Nat := 4983230072969 + 3 ^ 40 * 5388698 * 2
def baseEnd_5388698 : Nat := 2766992175921862927992835

theorem tailTrace_5388698 : CollatzResearch.WordTrace tailWord_5388698 prefixEnd_5388698 2766992175921862927992835 := by
  unfold tailWord_5388698
  simp only [CollatzResearch.WordTrace]
  refine ⟨49135490657918734298345687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131027975087783291462255165 49135490657918734298345687)
  ·
    refine ⟨73703235986878101447518531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49135490657918734298345687 73703235986878101447518531)
    ·
      refine ⟨110554853980317152171277797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73703235986878101447518531 110554853980317152171277797)
      ·
        refine ⟨20729035121309466032114587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110554853980317152171277797 20729035121309466032114587)
        ·
          refine ⟨31093552681964199048171881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20729035121309466032114587 31093552681964199048171881)
          ·
            refine ⟨23320164511473149286128911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31093552681964199048171881 23320164511473149286128911)
            ·
              refine ⟨34980246767209723929193367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23320164511473149286128911 34980246767209723929193367)
              ·
                refine ⟨52470370150814585893790051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34980246767209723929193367 52470370150814585893790051)
                ·
                  refine ⟨78705555226221878840685077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52470370150814585893790051 78705555226221878840685077)
                  ·
                    refine ⟨3689322901229150570657113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78705555226221878840685077 3689322901229150570657113)
                    ·
                      refine ⟨2766992175921862927992835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3689322901229150570657113 2766992175921862927992835)
                      ·
                        rfl

theorem cell23_5388698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_5388698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388698 prefixEnd_5388698 := by exact prefixLift 5388698
  have htrace : WordTrace (prefixWord ++ tailWord_5388698) baseStart_5388698 baseEnd_5388698 := by
    simpa [prefixWord, tailWord_5388698, baseEnd_5388698] using wordTrace_append hprefix tailTrace_5388698
  have hstable : (prefixWord ++ tailWord_5388698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388698).length < 2 ^ (prefixWord ++ tailWord_5388698).sum := by decide
  have hdescent : baseEnd_5388698 < baseStart_5388698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388758 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_5388758 : Nat := 118140960795 + 5388758 * 2 ^ 59
def prefixEnd_5388758 : Nat := 4983230072969 + 3 ^ 40 * 5388758 * 2
def baseEnd_5388758 : Nat := 2767022984761132693242559

theorem tailTrace_5388758 : CollatzResearch.WordTrace tailWord_5388758 prefixEnd_5388758 2767022984761132693242559 := by
  unfold tailWord_5388758
  simp only [CollatzResearch.WordTrace]
  refine ⟨12284009438216097965035433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131029434007638378293711285 12284009438216097965035433)
  ·
    refine ⟨9213007078662073473776575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12284009438216097965035433 9213007078662073473776575)
    ·
      refine ⟨13819510617993110210664863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9213007078662073473776575 13819510617993110210664863)
      ·
        refine ⟨20729265926989665315997295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13819510617993110210664863 20729265926989665315997295)
        ·
          refine ⟨31093898890484497973995943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20729265926989665315997295 31093898890484497973995943)
          ·
            refine ⟨46640848335726746960993915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31093898890484497973995943 46640848335726746960993915)
            ·
              refine ⟨69961272503590120441490873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46640848335726746960993915 69961272503590120441490873)
              ·
                refine ⟨52470954377692590331118155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69961272503590120441490873 52470954377692590331118155)
                ·
                  refine ⟨78706431566538885496677233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52470954377692590331118155 78706431566538885496677233)
                  ·
                    refine ⟨59029823674904164122507925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78706431566538885496677233 59029823674904164122507925)
                    ·
                      refine ⟨2767022984761132693242559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59029823674904164122507925 2767022984761132693242559)
                      ·
                        rfl

theorem cell23_5388758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_5388758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388758 prefixEnd_5388758 := by exact prefixLift 5388758
  have htrace : WordTrace (prefixWord ++ tailWord_5388758) baseStart_5388758 baseEnd_5388758 := by
    simpa [prefixWord, tailWord_5388758, baseEnd_5388758] using wordTrace_append hprefix tailTrace_5388758
  have hstable : (prefixWord ++ tailWord_5388758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388758).length < 2 ^ (prefixWord ++ tailWord_5388758).sum := by decide
  have hdescent : baseEnd_5388758 < baseStart_5388758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388765 : List Nat := [1, 4, 3, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_5388765 : Nat := 118140960795 + 5388765 * 2 ^ 59
def prefixEnd_5388765 : Nat := 4983230072969 + 3 ^ 40 * 5388765 * 2
def baseEnd_5388765 : Nat := 2767026579125714165855027

theorem tailTrace_5388765 : CollatzResearch.WordTrace tailWord_5388765 prefixEnd_5388765 2767026579125714165855027 := by
  unfold tailWord_5388765
  simp only [CollatzResearch.WordTrace]
  refine ⟨196544406322432207636071749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131029604214954805090714499 196544406322432207636071749)
  ·
    refine ⟨36852076185456038931763453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196544406322432207636071749 36852076185456038931763453)
    ·
      refine ⟨13819528569546014599411295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36852076185456038931763453 13819528569546014599411295)
      ·
        refine ⟨20729292854319021899116943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13819528569546014599411295 20729292854319021899116943)
        ·
          refine ⟨31093939281478532848675415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20729292854319021899116943 31093939281478532848675415)
          ·
            refine ⟨46640908922217799273013123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31093939281478532848675415 46640908922217799273013123)
            ·
              refine ⟨69961363383326698909519685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46640908922217799273013123 69961363383326698909519685)
              ·
                refine ⟨13117755634373756045534941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69961363383326698909519685 13117755634373756045534941)
                ·
                  refine ⟨4919158362890158517075603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13117755634373756045534941 4919158362890158517075603)
                  ·
                    refine ⟨7378737544335237775613405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4919158362890158517075603 7378737544335237775613405)
                    ·
                      refine ⟨2767026579125714165855027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7378737544335237775613405 2767026579125714165855027)
                      ·
                        rfl

theorem cell23_5388765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_5388765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388765 prefixEnd_5388765 := by exact prefixLift 5388765
  have htrace : WordTrace (prefixWord ++ tailWord_5388765) baseStart_5388765 baseEnd_5388765 := by
    simpa [prefixWord, tailWord_5388765, baseEnd_5388765] using wordTrace_append hprefix tailTrace_5388765
  have hstable : (prefixWord ++ tailWord_5388765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388765).length < 2 ^ (prefixWord ++ tailWord_5388765).sum := by decide
  have hdescent : baseEnd_5388765 < baseStart_5388765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388768 : List Nat := [2, 1, 1, 3, 1, 1, 6, 2, 1, 5]
def baseStart_5388768 : Nat := 118140960795 + 5388768 * 2 ^ 59
def prefixEnd_5388768 : Nat := 4983230072969 + 3 ^ 40 * 5388768 * 2
def baseEnd_5388768 : Nat := 922342706522559218039171

theorem tailTrace_5388768 : CollatzResearch.WordTrace tailWord_5388768 prefixEnd_5388768 922342706522559218039171 := by
  unfold tailWord_5388768
  simp only [CollatzResearch.WordTrace]
  refine ⟨98272257870710669574215479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131029677160947559432287305 98272257870710669574215479)
  ·
    refine ⟨147408386806066004361323219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98272257870710669574215479 147408386806066004361323219)
    ·
      refine ⟨221112580209099006541984829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147408386806066004361323219 221112580209099006541984829)
      ·
        refine ⟨82917217578412127453244311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221112580209099006541984829 82917217578412127453244311)
        ·
          refine ⟨124375826367618191179866467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82917217578412127453244311 124375826367618191179866467)
          ·
            refine ⟨186563739551427286769799701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124375826367618191179866467 186563739551427286769799701)
            ·
              refine ⟨8745175291473154067334361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 186563739551427286769799701 8745175291473154067334361)
              ·
                refine ⟨6558881468604865550500771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8745175291473154067334361 6558881468604865550500771)
                ·
                  refine ⟨9838322202907298325751157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6558881468604865550500771 9838322202907298325751157)
                  ·
                    refine ⟨922342706522559218039171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9838322202907298325751157 922342706522559218039171)
                    ·
                      rfl

theorem cell23_5388768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 1, 5].length) (baseStart_5388768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388768 prefixEnd_5388768 := by exact prefixLift 5388768
  have htrace : WordTrace (prefixWord ++ tailWord_5388768) baseStart_5388768 baseEnd_5388768 := by
    simpa [prefixWord, tailWord_5388768, baseEnd_5388768] using wordTrace_append hprefix tailTrace_5388768
  have hstable : (prefixWord ++ tailWord_5388768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388768).length < 2 ^ (prefixWord ++ tailWord_5388768).sum := by decide
  have hdescent : baseEnd_5388768 < baseStart_5388768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388775 : List Nat := [1, 1, 5, 2, 1, 1, 2, 3, 2, 3, 2]
def baseStart_5388775 : Nat := 118140960795 + 5388775 * 2 ^ 59
def prefixEnd_5388775 : Nat := 4983230072969 + 3 ^ 40 * 5388775 * 2
def baseEnd_5388775 : Nat := 2767031713932259126729981

theorem tailTrace_5388775 : CollatzResearch.WordTrace tailWord_5388775 prefixEnd_5388775 2767031713932259126729981 := by
  unfold tailWord_5388775
  simp only [CollatzResearch.WordTrace]
  refine ⟨196544771052395979343935779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131029847368263986229290519 196544771052395979343935779)
  ·
    refine ⟨294817156578593969015903669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196544771052395979343935779 294817156578593969015903669)
    ·
      refine ⟨27639108429243184595240969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 294817156578593969015903669 27639108429243184595240969)
      ·
        refine ⟨20729331321932388446430727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27639108429243184595240969 20729331321932388446430727)
        ·
          refine ⟨31093996982898582669646091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20729331321932388446430727 31093996982898582669646091)
          ·
            refine ⟨46640995474347874004469137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31093996982898582669646091 46640995474347874004469137)
            ·
              refine ⟨34980746605760905503351853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46640995474347874004469137 34980746605760905503351853)
              ·
                refine ⟨13117779977160339563756945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34980746605760905503351853 13117779977160339563756945)
                ·
                  refine ⟨9838334982870254672817709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13117779977160339563756945 9838334982870254672817709)
                  ·
                    refine ⟨3689375618576345502306641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9838334982870254672817709 3689375618576345502306641)
                    ·
                      refine ⟨2767031713932259126729981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3689375618576345502306641 2767031713932259126729981)
                      ·
                        rfl

theorem cell23_5388775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_5388775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388775 prefixEnd_5388775 := by exact prefixLift 5388775
  have htrace : WordTrace (prefixWord ++ tailWord_5388775) baseStart_5388775 baseEnd_5388775 := by
    simpa [prefixWord, tailWord_5388775, baseEnd_5388775] using wordTrace_append hprefix tailTrace_5388775
  have hstable : (prefixWord ++ tailWord_5388775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388775).length < 2 ^ (prefixWord ++ tailWord_5388775).sum := by decide
  have hdescent : baseEnd_5388775 < baseStart_5388775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388791 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 3]
def baseStart_5388791 : Nat := 118140960795 + 5388791 * 2 ^ 59
def prefixEnd_5388791 : Nat := 4983230072969 + 3 ^ 40 * 5388791 * 2
def baseEnd_5388791 : Nat := 2767039929622731064129907

theorem tailTrace_5388791 : CollatzResearch.WordTrace tailWord_5388791 prefixEnd_5388791 2767039929622731064129907 := by
  unfold tailWord_5388791
  simp only [CollatzResearch.WordTrace]
  refine ⟨196545354620338014076518227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131030236413558676051012151 196545354620338014076518227)
  ·
    refine ⟨294818031930507021114777341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196545354620338014076518227 294818031930507021114777341)
    ·
      refine ⟨110556761973940132918041503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294818031930507021114777341 110556761973940132918041503)
      ·
        refine ⟨165835142960910199377062255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110556761973940132918041503 165835142960910199377062255)
        ·
          refine ⟨248752714441365299065593383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165835142960910199377062255 248752714441365299065593383)
          ·
            refine ⟨373129071662047948598390075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248752714441365299065593383 373129071662047948598390075)
            ·
              refine ⟨559693607493071922897585113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373129071662047948598390075 559693607493071922897585113)
              ·
                refine ⟨419770205619803942173188835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 559693607493071922897585113 419770205619803942173188835)
                ·
                  refine ⟨629655308429705913259783253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419770205619803942173188835 629655308429705913259783253)
                  ·
                    refine ⟨7378773145660616171013085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 629655308429705913259783253 7378773145660616171013085)
                    ·
                      refine ⟨2767039929622731064129907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7378773145660616171013085 2767039929622731064129907)
                      ·
                        rfl

theorem cell23_5388791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_5388791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388791 prefixEnd_5388791 := by exact prefixLift 5388791
  have htrace : WordTrace (prefixWord ++ tailWord_5388791) baseStart_5388791 baseEnd_5388791 := by
    simpa [prefixWord, tailWord_5388791, baseEnd_5388791] using wordTrace_append hprefix tailTrace_5388791
  have hstable : (prefixWord ++ tailWord_5388791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388791).length < 2 ^ (prefixWord ++ tailWord_5388791).sum := by decide
  have hdescent : baseEnd_5388791 < baseStart_5388791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388806 : List Nat := [6, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_5388806 : Nat := 118140960795 + 5388806 * 2 ^ 59
def prefixEnd_5388806 : Nat := 4983230072969 + 3 ^ 40 * 5388806 * 2
def baseEnd_5388806 : Nat := 307449736870283167271371

theorem tailTrace_5388806 : CollatzResearch.WordTrace tailWord_5388806 prefixEnd_5388806 307449736870283167271371 := by
  unfold tailWord_5388806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6142059428602614738697321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 131030601143522447758876181 6142059428602614738697321)
  ·
    refine ⟨4606544571451961054022991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6142059428602614738697321 4606544571451961054022991)
    ·
      refine ⟨6909816857177941581034487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4606544571451961054022991 6909816857177941581034487)
      ·
        refine ⟨10364725285766912371551731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6909816857177941581034487 10364725285766912371551731)
        ·
          refine ⟨15547087928650368557327597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10364725285766912371551731 15547087928650368557327597)
          ·
            refine ⟨5830157973243888208997849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15547087928650368557327597 5830157973243888208997849)
            ·
              refine ⟨4372618479932916156748387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5830157973243888208997849 4372618479932916156748387)
              ·
                refine ⟨6558927719899374235122581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4372618479932916156748387 6558927719899374235122581)
                ·
                  refine ⟨307449736870283167271371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6558927719899374235122581 307449736870283167271371)
                  ·
                    rfl

theorem cell23_5388806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_5388806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388806 prefixEnd_5388806 := by exact prefixLift 5388806
  have htrace : WordTrace (prefixWord ++ tailWord_5388806) baseStart_5388806 baseEnd_5388806 := by
    simpa [prefixWord, tailWord_5388806, baseEnd_5388806] using wordTrace_append hprefix tailTrace_5388806
  have hstable : (prefixWord ++ tailWord_5388806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388806).length < 2 ^ (prefixWord ++ tailWord_5388806).sum := by decide
  have hdescent : baseEnd_5388806 < baseStart_5388806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388808 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 3, 2, 3]
def baseStart_5388808 : Nat := 118140960795 + 5388808 * 2 ^ 59
def prefixEnd_5388808 : Nat := 4983230072969 + 3 ^ 40 * 5388808 * 2
def baseEnd_5388808 : Nat := 2767048658793857497617329

theorem tailTrace_5388808 : CollatzResearch.WordTrace tailWord_5388808 prefixEnd_5388808 2767048658793857497617329 := by
  unfold tailWord_5388808
  simp only [CollatzResearch.WordTrace]
  refine ⟨98272987330638212989943539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131030649774184283986591385 98272987330638212989943539)
  ·
    refine ⟨147409480995957319484915309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98272987330638212989943539 147409480995957319484915309)
    ·
      refine ⟨55278555373483994806843241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147409480995957319484915309 55278555373483994806843241)
      ·
        refine ⟨41458916530112996105132431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55278555373483994806843241 41458916530112996105132431)
        ·
          refine ⟨62188374795169494157698647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41458916530112996105132431 62188374795169494157698647)
          ·
            refine ⟨93282562192754241236547971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62188374795169494157698647 93282562192754241236547971)
            ·
              refine ⟨139923843289131361854821957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93282562192754241236547971 139923843289131361854821957)
              ·
                refine ⟨26235720616712130347779117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139923843289131361854821957 26235720616712130347779117)
                ·
                  refine ⟨9838395231267048880417169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26235720616712130347779117 9838395231267048880417169)
                  ·
                    refine ⟨7378796423450286660312877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9838395231267048880417169 7378796423450286660312877)
                    ·
                      refine ⟨2767048658793857497617329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7378796423450286660312877 2767048658793857497617329)
                      ·
                        rfl

theorem cell23_5388808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_5388808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388808 prefixEnd_5388808 := by exact prefixLift 5388808
  have htrace : WordTrace (prefixWord ++ tailWord_5388808) baseStart_5388808 baseEnd_5388808 := by
    simpa [prefixWord, tailWord_5388808, baseEnd_5388808] using wordTrace_append hprefix tailTrace_5388808
  have hstable : (prefixWord ++ tailWord_5388808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388808).length < 2 ^ (prefixWord ++ tailWord_5388808).sum := by decide
  have hdescent : baseEnd_5388808 < baseStart_5388808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388811 : List Nat := [1, 1, 1, 1, 7, 1, 1, 10]
def baseStart_5388811 : Nat := 118140960795 + 5388811 * 2 ^ 59
def prefixEnd_5388811 : Nat := 4983230072969 + 3 ^ 40 * 5388811 * 2
def baseEnd_5388811 : Nat := 102483340712437814291845

theorem tailTrace_5388811 : CollatzResearch.WordTrace tailWord_5388811 prefixEnd_5388811 102483340712437814291845 := by
  unfold tailWord_5388811
  simp only [CollatzResearch.WordTrace]
  refine ⟨196546084080265557492246287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131030722720177038328164191 196546084080265557492246287)
  ·
    refine ⟨294819126120398336238369431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196546084080265557492246287 294819126120398336238369431)
    ·
      refine ⟨442228689180597504357554147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294819126120398336238369431 442228689180597504357554147)
      ·
        refine ⟨663343033770896256536331221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442228689180597504357554147 663343033770896256536331221)
        ·
          refine ⟨15547102354005381012570263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 663343033770896256536331221 15547102354005381012570263)
          ·
            refine ⟨23320653531008071518855395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15547102354005381012570263 23320653531008071518855395)
            ·
              refine ⟨34980980296512107278283093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23320653531008071518855395 34980980296512107278283093)
              ·
                refine ⟨102483340712437814291845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34980980296512107278283093 102483340712437814291845)
                ·
                  rfl

theorem cell23_5388811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 10].length) (baseStart_5388811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388811 prefixEnd_5388811 := by exact prefixLift 5388811
  have htrace : WordTrace (prefixWord ++ tailWord_5388811) baseStart_5388811 baseEnd_5388811 := by
    simpa [prefixWord, tailWord_5388811, baseEnd_5388811] using wordTrace_append hprefix tailTrace_5388811
  have hstable : (prefixWord ++ tailWord_5388811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388811).length < 2 ^ (prefixWord ++ tailWord_5388811).sum := by decide
  have hdescent : baseEnd_5388811 < baseStart_5388811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388845 : List Nat := [1, 5, 4, 1, 12]
def baseStart_5388845 : Nat := 118140960795 + 5388845 * 2 ^ 59
def prefixEnd_5388845 : Nat := 4983230072969 + 3 ^ 40 * 5388845 * 2
def baseEnd_5388845 : Nat := 3795703233989127370171

theorem tailTrace_5388845 : CollatzResearch.WordTrace tailWord_5388845 prefixEnd_5388845 3795703233989127370171 := by
  unfold tailWord_5388845
  simp only [CollatzResearch.WordTrace]
  refine ⟨196547324162142381298983989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131031549441428254199322659 196547324162142381298983989)
  ·
    refine ⟨18426311640200848246779749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 196547324162142381298983989 18426311640200848246779749)
    ·
      refine ⟨3454933432537659046271203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18426311640200848246779749 3454933432537659046271203)
      ·
        refine ⟨5182400148806488569406805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3454933432537659046271203 5182400148806488569406805)
        ·
          refine ⟨3795703233989127370171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5182400148806488569406805 3795703233989127370171)
          ·
            rfl

theorem cell23_5388845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 12].length) (baseStart_5388845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388845 prefixEnd_5388845 := by exact prefixLift 5388845
  have htrace : WordTrace (prefixWord ++ tailWord_5388845) baseStart_5388845 baseEnd_5388845 := by
    simpa [prefixWord, tailWord_5388845, baseEnd_5388845] using wordTrace_append hprefix tailTrace_5388845
  have hstable : (prefixWord ++ tailWord_5388845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388845).length < 2 ^ (prefixWord ++ tailWord_5388845).sum := by decide
  have hdescent : baseEnd_5388845 < baseStart_5388845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388862 : List Nat := [4, 2, 1, 4, 1, 2, 1, 8]
def baseStart_5388862 : Nat := 118140960795 + 5388862 * 2 ^ 59
def prefixEnd_5388862 : Nat := 4983230072969 + 3 ^ 40 * 5388862 * 2
def baseEnd_5388862 : Nat := 102484310620340751346003

theorem tailTrace_5388862 : CollatzResearch.WordTrace tailWord_5388862 prefixEnd_5388862 102484310620340751346003 := by
  unfold tailWord_5388862
  simp only [CollatzResearch.WordTrace]
  refine ⟨24568493025385099150294105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131031962802053862134901893 24568493025385099150294105)
  ·
    refine ⟨18426369769038824362720579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24568493025385099150294105 18426369769038824362720579)
    ·
      refine ⟨27639554653558236544080869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18426369769038824362720579 27639554653558236544080869)
      ·
        refine ⟨5182416497542169352015163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27639554653558236544080869 5182416497542169352015163)
        ·
          refine ⟨7773624746313254028022745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5182416497542169352015163 7773624746313254028022745)
          ·
            refine ⟨5830218559734940521017059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7773624746313254028022745 5830218559734940521017059)
            ·
              refine ⟨8745327839602410781525589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5830218559734940521017059 8745327839602410781525589)
              ·
                refine ⟨102484310620340751346003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8745327839602410781525589 102484310620340751346003)
                ·
                  rfl

theorem cell23_5388862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 8].length) (baseStart_5388862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388862 prefixEnd_5388862 := by exact prefixLift 5388862
  have htrace : WordTrace (prefixWord ++ tailWord_5388862) baseStart_5388862 baseEnd_5388862 := by
    simpa [prefixWord, tailWord_5388862, baseEnd_5388862] using wordTrace_append hprefix tailTrace_5388862
  have hstable : (prefixWord ++ tailWord_5388862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388862).length < 2 ^ (prefixWord ++ tailWord_5388862).sum := by decide
  have hdescent : baseEnd_5388862 < baseStart_5388862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388882 : List Nat := [3, 2, 2, 1, 2, 1, 2, 4, 1, 3, 2]
def baseStart_5388882 : Nat := 118140960795 + 5388882 * 2 ^ 59
def prefixEnd_5388882 : Nat := 4983230072969 + 3 ^ 40 * 5388882 * 2
def baseEnd_5388882 : Nat := 2767086656362290208091989

theorem tailTrace_5388882 : CollatzResearch.WordTrace tailWord_5388882 prefixEnd_5388882 2767086656362290208091989 := by
  unfold tailWord_5388882
  simp only [CollatzResearch.WordTrace]
  refine ⟨49137168415752084154520225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131032449108672224412053933 49137168415752084154520225)
  ·
    refine ⟨36852876311814063115890169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49137168415752084154520225 36852876311814063115890169)
    ·
      refine ⟨27639657233860547336917627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36852876311814063115890169 27639657233860547336917627)
      ·
        refine ⟨41459485850790821005376441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27639657233860547336917627 41459485850790821005376441)
        ·
          refine ⟨31094614388093115754032331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41459485850790821005376441 31094614388093115754032331)
          ·
            refine ⟨46641921582139673631048497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31094614388093115754032331 46641921582139673631048497)
            ·
              refine ⟨34981441186604755223286373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46641921582139673631048497 34981441186604755223286373)
              ·
                refine ⟨6559020222488391604366195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34981441186604755223286373 6559020222488391604366195)
                ·
                  refine ⟨9838530333732587406549293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6559020222488391604366195 9838530333732587406549293)
                  ·
                    refine ⟨3689448875149720277455985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9838530333732587406549293 3689448875149720277455985)
                    ·
                      refine ⟨2767086656362290208091989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3689448875149720277455985 2767086656362290208091989)
                      ·
                        rfl

theorem cell23_5388882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_5388882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388882 prefixEnd_5388882 := by exact prefixLift 5388882
  have htrace : WordTrace (prefixWord ++ tailWord_5388882) baseStart_5388882 baseEnd_5388882 := by
    simpa [prefixWord, tailWord_5388882, baseEnd_5388882] using wordTrace_append hprefix tailTrace_5388882
  have hstable : (prefixWord ++ tailWord_5388882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388882).length < 2 ^ (prefixWord ++ tailWord_5388882).sum := by decide
  have hdescent : baseEnd_5388882 < baseStart_5388882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388908 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 4]
def baseStart_5388908 : Nat := 118140960795 + 5388908 * 2 ^ 59
def prefixEnd_5388908 : Nat := 4983230072969 + 3 ^ 40 * 5388908 * 2
def baseEnd_5388908 : Nat := 2767100006859307106366869

theorem tailTrace_5388908 : CollatzResearch.WordTrace tailWord_5388908 prefixEnd_5388908 2767100006859307106366869 := by
  unfold tailWord_5388908
  simp only [CollatzResearch.WordTrace]
  refine ⟨98274810980457071529263689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131033081307276095372351585 98274810980457071529263689)
  ·
    refine ⟨73706108235342803646947767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98274810980457071529263689 73706108235342803646947767)
    ·
      refine ⟨110559162353014205470421651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73706108235342803646947767 110559162353014205470421651)
      ·
        refine ⟨165838743529521308205632477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110559162353014205470421651 165838743529521308205632477)
        ·
          refine ⟨62189528823570490577112179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165838743529521308205632477 62189528823570490577112179)
          ·
            refine ⟨93284293235355735865668269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62189528823570490577112179 93284293235355735865668269)
            ·
              refine ⟨34981609963258400949625601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93284293235355735865668269 34981609963258400949625601)
              ·
                refine ⟨26236207472443800712219201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34981609963258400949625601 26236207472443800712219201)
                ·
                  refine ⟨19677155604332850534164401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26236207472443800712219201 19677155604332850534164401)
                  ·
                    refine ⟨14757866703249637900623301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19677155604332850534164401 14757866703249637900623301)
                    ·
                      refine ⟨2767100006859307106366869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14757866703249637900623301 2767100006859307106366869)
                      ·
                        rfl

theorem cell23_5388908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_5388908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388908 prefixEnd_5388908 := by exact prefixLift 5388908
  have htrace : WordTrace (prefixWord ++ tailWord_5388908) baseStart_5388908 baseEnd_5388908 := by
    simpa [prefixWord, tailWord_5388908, baseEnd_5388908] using wordTrace_append hprefix tailTrace_5388908
  have hstable : (prefixWord ++ tailWord_5388908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388908).length < 2 ^ (prefixWord ++ tailWord_5388908).sum := by decide
  have hdescent : baseEnd_5388908 < baseStart_5388908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5388985 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 1, 6, 2]
def baseStart_5388985 : Nat := 118140960795 + 5388985 * 2 ^ 59
def prefixEnd_5388985 : Nat := 4983230072969 + 3 ^ 40 * 5388985 * 2
def baseEnd_5388985 : Nat := 2767139544869703305104015

theorem tailTrace_5388985 : CollatzResearch.WordTrace tailWord_5388985 prefixEnd_5388985 2767139544869703305104015 := by
  unfold tailWord_5388985
  simp only [CollatzResearch.WordTrace]
  refine ⟨196552430381635185209080409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131034953587756790139386939 196552430381635185209080409)
  ·
    refine ⟨147414322786226388906810307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196552430381635185209080409 147414322786226388906810307)
    ·
      refine ⟨221121484179339583360215461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147414322786226388906810307 221121484179339583360215461)
      ·
        refine ⟨41460278283626171880040399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221121484179339583360215461 41460278283626171880040399)
        ·
          refine ⟨62190417425439257820060599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41460278283626171880040399 62190417425439257820060599)
          ·
            refine ⟨93285626138158886730090899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62190417425439257820060599 93285626138158886730090899)
            ·
              refine ⟨139928439207238330095136349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93285626138158886730090899 139928439207238330095136349)
              ·
                refine ⟨52473164702714373785676131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139928439207238330095136349 52473164702714373785676131)
                ·
                  refine ⟨78709747054071560678514197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52473164702714373785676131 78709747054071560678514197)
                  ·
                    refine ⟨3689519393159604406805353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78709747054071560678514197 3689519393159604406805353)
                    ·
                      refine ⟨2767139544869703305104015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3689519393159604406805353 2767139544869703305104015)
                      ·
                        rfl

theorem cell23_5388985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_5388985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5388985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5388985 prefixEnd_5388985 := by exact prefixLift 5388985
  have htrace : WordTrace (prefixWord ++ tailWord_5388985) baseStart_5388985 baseEnd_5388985 := by
    simpa [prefixWord, tailWord_5388985, baseEnd_5388985] using wordTrace_append hprefix tailTrace_5388985
  have hstable : (prefixWord ++ tailWord_5388985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5388985).length < 2 ^ (prefixWord ++ tailWord_5388985).sum := by decide
  have hdescent : baseEnd_5388985 < baseStart_5388985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5388985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389002 : List Nat := [3, 1, 2, 1, 4, 2, 2, 1, 2, 1, 4]
def baseStart_5389002 : Nat := 118140960795 + 5389002 * 2 ^ 59
def prefixEnd_5389002 : Nat := 4983230072969 + 3 ^ 40 * 5389002 * 2
def baseEnd_5389002 : Nat := 2767148274040829738591437

theorem tailTrace_5389002 : CollatzResearch.WordTrace tailWord_5389002 prefixEnd_5389002 2767148274040829738591437 := by
  unfold tailWord_5389002
  simp only [CollatzResearch.WordTrace]
  refine ⟨49138262605643399278112315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131035366948382398074966173 49138262605643399278112315)
  ·
    refine ⟨73707393908465098917168473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49138262605643399278112315 73707393908465098917168473)
    ·
      refine ⟨55280545431348824187876355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73707393908465098917168473 55280545431348824187876355)
      ·
        refine ⟨82920818147023236281814533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55280545431348824187876355 82920818147023236281814533)
        ·
          refine ⟨15547653402566856802840225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82920818147023236281814533 15547653402566856802840225)
          ·
            refine ⟨11660740051925142602130169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15547653402566856802840225 11660740051925142602130169)
            ·
              refine ⟨8745555038943856951597627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11660740051925142602130169 8745555038943856951597627)
              ·
                refine ⟨13118332558415785427396441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8745555038943856951597627 13118332558415785427396441)
                ·
                  refine ⟨9838749418811839070547331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13118332558415785427396441 9838749418811839070547331)
                  ·
                    refine ⟨14758124128217758605820997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9838749418811839070547331 14758124128217758605820997)
                    ·
                      refine ⟨2767148274040829738591437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14758124128217758605820997 2767148274040829738591437)
                      ·
                        rfl

theorem cell23_5389002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_5389002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389002 prefixEnd_5389002 := by exact prefixLift 5389002
  have htrace : WordTrace (prefixWord ++ tailWord_5389002) baseStart_5389002 baseEnd_5389002 := by
    simpa [prefixWord, tailWord_5389002, baseEnd_5389002] using wordTrace_append hprefix tailTrace_5389002
  have hstable : (prefixWord ++ tailWord_5389002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389002).length < 2 ^ (prefixWord ++ tailWord_5389002).sum := by decide
  have hdescent : baseEnd_5389002 < baseStart_5389002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389025 : List Nat := [1, 2, 3, 1, 4, 1, 1, 4, 6]
def baseStart_5389025 : Nat := 118140960795 + 5389025 * 2 ^ 59
def prefixEnd_5389025 : Nat := 4983230072969 + 3 ^ 40 * 5389025 * 2
def baseEnd_5389025 : Nat := 307462231566209238733759

theorem tailTrace_5389025 : CollatzResearch.WordTrace tailWord_5389025 prefixEnd_5389025 307462231566209238733759 := by
  unfold tailWord_5389025
  simp only [CollatzResearch.WordTrace]
  refine ⟨196553889301490272040536529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131035926200993514693691019 196553889301490272040536529)
  ·
    refine ⟨147415416976117704030402397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196553889301490272040536529 147415416976117704030402397)
    ·
      refine ⟨55280781366044139011400899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147415416976117704030402397 55280781366044139011400899)
      ·
        refine ⟨82921172049066208517101349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55280781366044139011400899 82921172049066208517101349)
        ·
          refine ⟨15547719759199914096956503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82921172049066208517101349 15547719759199914096956503)
          ·
            refine ⟨23321579638799871145434755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15547719759199914096956503 23321579638799871145434755)
            ·
              refine ⟨34982369458199806718152133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23321579638799871145434755 34982369458199806718152133)
              ·
                refine ⟨6559194273412463759653525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34982369458199806718152133 6559194273412463759653525)
                ·
                  refine ⟨307462231566209238733759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6559194273412463759653525 307462231566209238733759)
                  ·
                    rfl

theorem cell23_5389025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 6].length) (baseStart_5389025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389025 prefixEnd_5389025 := by exact prefixLift 5389025
  have htrace : WordTrace (prefixWord ++ tailWord_5389025) baseStart_5389025 baseEnd_5389025 := by
    simpa [prefixWord, tailWord_5389025, baseEnd_5389025] using wordTrace_append hprefix tailTrace_5389025
  have hstable : (prefixWord ++ tailWord_5389025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389025).length < 2 ^ (prefixWord ++ tailWord_5389025).sum := by decide
  have hdescent : baseEnd_5389025 < baseStart_5389025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389029 : List Nat := [1, 3, 1, 4, 1, 3, 1, 4, 1, 4]
def baseStart_5389029 : Nat := 118140960795 + 5389029 * 2 ^ 59
def prefixEnd_5389029 : Nat := 4983230072969 + 3 ^ 40 * 5389029 * 2
def baseEnd_5389029 : Nat := 922387379339500377651271

theorem tailTrace_5389029 : CollatzResearch.WordTrace tailWord_5389029 prefixEnd_5389029 922387379339500377651271 := by
  unfold tailWord_5389029
  simp only [CollatzResearch.WordTrace]
  refine ⟨196554035193475780723682141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131036023462317187149121427 196554035193475780723682141)
  ·
    refine ⟨73707763197553417771380803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196554035193475780723682141 73707763197553417771380803)
    ·
      refine ⟨110561644796330126657071205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73707763197553417771380803 110561644796330126657071205)
      ·
        refine ⟨20730308399311898748200851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110561644796330126657071205 20730308399311898748200851)
        ·
          refine ⟨31095462598967848122301277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20730308399311898748200851 31095462598967848122301277)
          ·
            refine ⟨11660798474612943045862979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31095462598967848122301277 11660798474612943045862979)
            ·
              refine ⟨17491197711919414568794469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11660798474612943045862979 17491197711919414568794469)
              ·
                refine ⟨3279599570984890231648963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17491197711919414568794469 3279599570984890231648963)
                ·
                  refine ⟨4919399356477335347473445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3279599570984890231648963 4919399356477335347473445)
                  ·
                    refine ⟨922387379339500377651271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4919399356477335347473445 922387379339500377651271)
                    ·
                      rfl

theorem cell23_5389029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 1, 4].length) (baseStart_5389029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389029 prefixEnd_5389029 := by exact prefixLift 5389029
  have htrace : WordTrace (prefixWord ++ tailWord_5389029) baseStart_5389029 baseEnd_5389029 := by
    simpa [prefixWord, tailWord_5389029, baseEnd_5389029] using wordTrace_append hprefix tailTrace_5389029
  have hstable : (prefixWord ++ tailWord_5389029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389029).length < 2 ^ (prefixWord ++ tailWord_5389029).sum := by decide
  have hdescent : baseEnd_5389029 < baseStart_5389029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389048 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 2, 1, 7]
def baseStart_5389048 : Nat := 118140960795 + 5389048 * 2 ^ 59
def prefixEnd_5389048 : Nat := 4983230072969 + 3 ^ 40 * 5389048 * 2
def baseEnd_5389048 : Nat := 2767171894150936558616225

theorem tailTrace_5389048 : CollatzResearch.WordTrace tailWord_5389048 prefixEnd_5389048 2767171894150936558616225 := by
  unfold tailWord_5389048
  simp only [CollatzResearch.WordTrace]
  refine ⟨98277364090203473484311899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131036485453604631312415865 98277364090203473484311899)
  ·
    refine ⟨147416046135305210226467849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98277364090203473484311899 147416046135305210226467849)
    ·
      refine ⟨110562034601478907669850887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147416046135305210226467849 110562034601478907669850887)
      ·
        refine ⟨165843051902218361504776331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110562034601478907669850887 165843051902218361504776331)
        ·
          refine ⟨248764577853327542257164497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165843051902218361504776331 248764577853327542257164497)
          ·
            refine ⟨186573433389995656692873373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248764577853327542257164497 186573433389995656692873373)
            ·
              refine ⟨69965037521248371259827515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186573433389995656692873373 69965037521248371259827515)
              ·
                refine ⟨104947556281872556889741273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69965037521248371259827515 104947556281872556889741273)
                ·
                  refine ⟨78710667211404417667305955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104947556281872556889741273 78710667211404417667305955)
                  ·
                    refine ⟨118066000817106626500958933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78710667211404417667305955 118066000817106626500958933)
                    ·
                      refine ⟨2767171894150936558616225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118066000817106626500958933 2767171894150936558616225)
                      ·
                        rfl

theorem cell23_5389048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_5389048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389048 prefixEnd_5389048 := by exact prefixLift 5389048
  have htrace : WordTrace (prefixWord ++ tailWord_5389048) baseStart_5389048 baseEnd_5389048 := by
    simpa [prefixWord, tailWord_5389048, baseEnd_5389048] using wordTrace_append hprefix tailTrace_5389048
  have hstable : (prefixWord ++ tailWord_5389048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389048).length < 2 ^ (prefixWord ++ tailWord_5389048).sum := by decide
  have hdescent : baseEnd_5389048 < baseStart_5389048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389052 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 5, 1, 3]
def baseStart_5389052 : Nat := 118140960795 + 5389052 * 2 ^ 59
def prefixEnd_5389052 : Nat := 4983230072969 + 3 ^ 40 * 5389052 * 2
def baseEnd_5389052 : Nat := 2767173948073554542966207

theorem tailTrace_5389052 : CollatzResearch.WordTrace tailWord_5389052 prefixEnd_5389052 2767173948073554542966207 := by
  unfold tailWord_5389052
  simp only [CollatzResearch.WordTrace]
  refine ⟨98277437036196227825884705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131036582714928303767846273 98277437036196227825884705)
  ·
    refine ⟨73708077777147170869413529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98277437036196227825884705 73708077777147170869413529)
    ·
      refine ⟨55281058332860378152060147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73708077777147170869413529 55281058332860378152060147)
      ·
        refine ⟨82921587499290567228090221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55281058332860378152060147 82921587499290567228090221)
        ·
          refine ⟨31095595312233962710533833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82921587499290567228090221 31095595312233962710533833)
          ·
            refine ⟨23321696484175472032900375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31095595312233962710533833 23321696484175472032900375)
            ·
              refine ⟨34982544726263208049350563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23321696484175472032900375 34982544726263208049350563)
              ·
                refine ⟨52473817089394812074025845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34982544726263208049350563 52473817089394812074025845)
                ·
                  refine ⟨4919420352130763631939923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52473817089394812074025845 4919420352130763631939923)
                  ·
                    refine ⟨7379130528196145447909885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4919420352130763631939923 7379130528196145447909885)
                    ·
                      refine ⟨2767173948073554542966207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7379130528196145447909885 2767173948073554542966207)
                      ·
                        rfl

theorem cell23_5389052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_5389052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389052 prefixEnd_5389052 := by exact prefixLift 5389052
  have htrace : WordTrace (prefixWord ++ tailWord_5389052) baseStart_5389052 baseEnd_5389052 := by
    simpa [prefixWord, tailWord_5389052, baseEnd_5389052] using wordTrace_append hprefix tailTrace_5389052
  have hstable : (prefixWord ++ tailWord_5389052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389052).length < 2 ^ (prefixWord ++ tailWord_5389052).sum := by decide
  have hdescent : baseEnd_5389052 < baseStart_5389052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389055 : List Nat := [1, 1, 2, 2, 1, 3, 1, 6, 1, 5]
def baseStart_5389055 : Nat := 118140960795 + 5389055 * 2 ^ 59
def prefixEnd_5389055 : Nat := 4983230072969 + 3 ^ 40 * 5389055 * 2
def baseEnd_5389055 : Nat := 922391829505172677076231

theorem tailTrace_5389055 : CollatzResearch.WordTrace tailWord_5389055 prefixEnd_5389055 922391829505172677076231 := by
  unfold tailWord_5389055
  simp only [CollatzResearch.WordTrace]
  refine ⟨196554983491381587164128619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131036655660921058109419079 196554983491381587164128619)
  ·
    refine ⟨294832475237072380746192929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196554983491381587164128619 294832475237072380746192929)
    ·
      refine ⟨221124356427804285559644697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294832475237072380746192929 221124356427804285559644697)
      ·
        refine ⟨165843267320853214169733523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221124356427804285559644697 165843267320853214169733523)
        ·
          refine ⟨248764900981279821254600285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165843267320853214169733523 248764900981279821254600285)
          ·
            refine ⟨93286837867979932970475107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248764900981279821254600285 93286837867979932970475107)
            ·
              refine ⟨139930256801969899455712661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93286837867979932970475107 139930256801969899455712661)
              ·
                refine ⟨6559230787592339036986531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 139930256801969899455712661 6559230787592339036986531)
                ·
                  refine ⟨9838846181388508555479797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6559230787592339036986531 9838846181388508555479797)
                  ·
                    refine ⟨922391829505172677076231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9838846181388508555479797 922391829505172677076231)
                    ·
                      rfl

theorem cell23_5389055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 5].length) (baseStart_5389055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389055 prefixEnd_5389055 := by exact prefixLift 5389055
  have htrace : WordTrace (prefixWord ++ tailWord_5389055) baseStart_5389055 baseEnd_5389055 := by
    simpa [prefixWord, tailWord_5389055, baseEnd_5389055] using wordTrace_append hprefix tailTrace_5389055
  have hstable : (prefixWord ++ tailWord_5389055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389055).length < 2 ^ (prefixWord ++ tailWord_5389055).sum := by decide
  have hdescent : baseEnd_5389055 < baseStart_5389055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389105 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 1, 1, 6]
def baseStart_5389105 : Nat := 118140960795 + 5389105 * 2 ^ 59
def prefixEnd_5389105 : Nat := 4983230072969 + 3 ^ 40 * 5389105 * 2
def baseEnd_5389105 : Nat := 2767201162548242835603463

theorem tailTrace_5389105 : CollatzResearch.WordTrace tailWord_5389105 prefixEnd_5389105 2767201162548242835603463 := by
  unfold tailWord_5389105
  simp only [CollatzResearch.WordTrace]
  refine ⟨196556807141200445703448769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131037871427466963802299179 196556807141200445703448769)
  ·
    refine ⟨147417605355900334277586577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196556807141200445703448769 147417605355900334277586577)
    ·
      refine ⟨110563204016925250708189933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147417605355900334277586577 110563204016925250708189933)
      ·
        refine ⟨41461201506346969015571225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110563204016925250708189933 41461201506346969015571225)
        ·
          refine ⟨31095901129760226761678419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41461201506346969015571225 31095901129760226761678419)
          ·
            refine ⟨46643851694640340142517629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31095901129760226761678419 46643851694640340142517629)
            ·
              refine ⟨17491444385490127553444111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46643851694640340142517629 17491444385490127553444111)
              ·
                refine ⟨26237166578235191330166167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17491444385490127553444111 26237166578235191330166167)
                ·
                  refine ⟨39355749867352786995249251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26237166578235191330166167 39355749867352786995249251)
                  ·
                    refine ⟨59033624801029180492873877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39355749867352786995249251 59033624801029180492873877)
                    ·
                      refine ⟨2767201162548242835603463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59033624801029180492873877 2767201162548242835603463)
                      ·
                        rfl

theorem cell23_5389105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_5389105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389105 prefixEnd_5389105 := by exact prefixLift 5389105
  have htrace : WordTrace (prefixWord ++ tailWord_5389105) baseStart_5389105 baseEnd_5389105 := by
    simpa [prefixWord, tailWord_5389105, baseEnd_5389105] using wordTrace_append hprefix tailTrace_5389105
  have hstable : (prefixWord ++ tailWord_5389105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389105).length < 2 ^ (prefixWord ++ tailWord_5389105).sum := by decide
  have hdescent : baseEnd_5389105 < baseStart_5389105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389109 : List Nat := [1, 3, 3, 1, 3, 2, 2, 2, 1, 1, 4]
def baseStart_5389109 : Nat := 118140960795 + 5389109 * 2 ^ 59
def prefixEnd_5389109 : Nat := 4983230072969 + 3 ^ 40 * 5389109 * 2
def baseEnd_5389109 : Nat := 2767203216470860819953445

theorem tailTrace_5389109 : CollatzResearch.WordTrace tailWord_5389109 prefixEnd_5389109 2767203216470860819953445 := by
  unfold tailWord_5389109
  simp only [CollatzResearch.WordTrace]
  refine ⟨196556953033185954386594381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131037968688790636257729587 196556953033185954386594381)
  ·
    refine ⟨73708857387444732894972893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196556953033185954386594381 73708857387444732894972893)
    ·
      refine ⟨27640821520291774835614835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73708857387444732894972893 27640821520291774835614835)
      ·
        refine ⟨41461232280437662253422253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27640821520291774835614835 41461232280437662253422253)
        ·
          refine ⟨15547962105164123345033345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41461232280437662253422253 15547962105164123345033345)
          ·
            refine ⟨11660971578873092508775009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15547962105164123345033345 11660971578873092508775009)
            ·
              refine ⟨8745728684154819381581257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11660971578873092508775009 8745728684154819381581257)
              ·
                refine ⟨6559296513116114536185943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8745728684154819381581257 6559296513116114536185943)
                ·
                  refine ⟨9838944769674171804278915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6559296513116114536185943 9838944769674171804278915)
                  ·
                    refine ⟨14758417154511257706418373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9838944769674171804278915 14758417154511257706418373)
                    ·
                      refine ⟨2767203216470860819953445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14758417154511257706418373 2767203216470860819953445)
                      ·
                        rfl

theorem cell23_5389109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_5389109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389109 prefixEnd_5389109 := by exact prefixLift 5389109
  have htrace : WordTrace (prefixWord ++ tailWord_5389109) baseStart_5389109 baseEnd_5389109 := by
    simpa [prefixWord, tailWord_5389109, baseEnd_5389109] using wordTrace_append hprefix tailTrace_5389109
  have hstable : (prefixWord ++ tailWord_5389109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389109).length < 2 ^ (prefixWord ++ tailWord_5389109).sum := by decide
  have hdescent : baseEnd_5389109 < baseStart_5389109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389165 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_5389165 : Nat := 118140960795 + 5389165 * 2 ^ 59
def prefixEnd_5389165 : Nat := 4983230072969 + 3 ^ 40 * 5389165 * 2
def baseEnd_5389165 : Nat := 2767231971387512600853187

theorem tailTrace_5389165 : CollatzResearch.WordTrace tailWord_5389165 prefixEnd_5389165 2767231971387512600853187 := by
  unfold tailWord_5389165
  simp only [CollatzResearch.WordTrace]
  refine ⟨196558995520983075950632949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131039330347322050633755299 196558995520983075950632949)
  ·
    refine ⟨18427405830092163370371839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 196558995520983075950632949 18427405830092163370371839)
    ·
      refine ⟨27641108745138245055557759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18427405830092163370371839 27641108745138245055557759)
      ·
        refine ⟨41461663117707367583336639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27641108745138245055557759 41461663117707367583336639)
        ·
          refine ⟨62192494676561051375004959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41461663117707367583336639 62192494676561051375004959)
          ·
            refine ⟨93288742014841577062507439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62192494676561051375004959 93288742014841577062507439)
            ·
              refine ⟨139933113022262365593761159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93288742014841577062507439 139933113022262365593761159)
              ·
                refine ⟨209899669533393548390641739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139933113022262365593761159 209899669533393548390641739)
                ·
                  refine ⟨314849504300090322585962609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209899669533393548390641739 314849504300090322585962609)
                  ·
                    refine ⟨236137128225067741939471957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 314849504300090322585962609 236137128225067741939471957)
                    ·
                      refine ⟨2767231971387512600853187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 236137128225067741939471957 2767231971387512600853187)
                      ·
                        rfl

theorem cell23_5389165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_5389165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389165 prefixEnd_5389165 := by exact prefixLift 5389165
  have htrace : WordTrace (prefixWord ++ tailWord_5389165) baseStart_5389165 baseEnd_5389165 := by
    simpa [prefixWord, tailWord_5389165, baseEnd_5389165] using wordTrace_append hprefix tailTrace_5389165
  have hstable : (prefixWord ++ tailWord_5389165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389165).length < 2 ^ (prefixWord ++ tailWord_5389165).sum := by decide
  have hdescent : baseEnd_5389165 < baseStart_5389165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389169 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 3, 3, 2]
def baseStart_5389169 : Nat := 118140960795 + 5389169 * 2 ^ 59
def prefixEnd_5389169 : Nat := 4983230072969 + 3 ^ 40 * 5389169 * 2
def baseEnd_5389169 : Nat := 2767234025310130585203169

theorem tailTrace_5389169 : CollatzResearch.WordTrace tailWord_5389169 prefixEnd_5389169 2767234025310130585203169 := by
  unfold tailWord_5389169
  simp only [CollatzResearch.WordTrace]
  refine ⟨196559141412968584633778561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131039427608645723089185707 196559141412968584633778561)
  ·
    refine ⟨147419356059726438475333921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196559141412968584633778561 147419356059726438475333921)
    ·
      refine ⟨110564517044794828856500441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147419356059726438475333921 110564517044794828856500441)
      ·
        refine ⟨82923387783596121642375331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110564517044794828856500441 82923387783596121642375331)
        ·
          refine ⟨124385081675394182463562997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82923387783596121642375331 124385081675394182463562997)
          ·
            refine ⟨11661101407068204605959031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124385081675394182463562997 11661101407068204605959031)
            ·
              refine ⟨17491652110602306908938547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11661101407068204605959031 17491652110602306908938547)
              ·
                refine ⟨26237478165903460363407821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17491652110602306908938547 26237478165903460363407821)
                ·
                  refine ⟨9839054312213797636277933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26237478165903460363407821 9839054312213797636277933)
                  ·
                    refine ⟨3689645367080174113604225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9839054312213797636277933 3689645367080174113604225)
                    ·
                      refine ⟨2767234025310130585203169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3689645367080174113604225 2767234025310130585203169)
                      ·
                        rfl

theorem cell23_5389169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_5389169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389169 prefixEnd_5389169 := by exact prefixLift 5389169
  have htrace : WordTrace (prefixWord ++ tailWord_5389169) baseStart_5389169 baseEnd_5389169 := by
    simpa [prefixWord, tailWord_5389169, baseEnd_5389169] using wordTrace_append hprefix tailTrace_5389169
  have hstable : (prefixWord ++ tailWord_5389169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389169).length < 2 ^ (prefixWord ++ tailWord_5389169).sum := by decide
  have hdescent : baseEnd_5389169 < baseStart_5389169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389216 : List Nat := [2, 1, 1, 4, 1, 1, 4, 3, 2, 2, 2]
def baseStart_5389216 : Nat := 118140960795 + 5389216 * 2 ^ 59
def prefixEnd_5389216 : Nat := 4983230072969 + 3 ^ 40 * 5389216 * 2
def baseEnd_5389216 : Nat := 2767258158900891901315453

theorem tailTrace_5389216 : CollatzResearch.WordTrace tailWord_5389216 prefixEnd_5389216 2767258158900891901315453 := by
  unfold tailWord_5389216
  simp only [CollatzResearch.WordTrace]
  refine ⟨98280427821899155830369751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131040570429198874440493001 98280427821899155830369751)
  ·
    refine ⟨147420641732848733745554627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98280427821899155830369751 147420641732848733745554627)
    ·
      refine ⟨221130962599273100618331941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147420641732848733745554627 221130962599273100618331941)
      ·
        refine ⟨41462055487363706365937239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221130962599273100618331941 41462055487363706365937239)
        ·
          refine ⟨62193083231045559548905859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41462055487363706365937239 62193083231045559548905859)
          ·
            refine ⟨93289624846568339323358789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62193083231045559548905859 93289624846568339323358789)
            ·
              refine ⟨17491804658731563623129773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93289624846568339323358789 17491804658731563623129773)
              ·
                refine ⟨6559426747024336358673665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17491804658731563623129773 6559426747024336358673665)
                ·
                  refine ⟨4919570060268252269005249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6559426747024336358673665 4919570060268252269005249)
                  ·
                    refine ⟨3689677545201189201753937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4919570060268252269005249 3689677545201189201753937)
                    ·
                      refine ⟨2767258158900891901315453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3689677545201189201753937 2767258158900891901315453)
                      ·
                        rfl

theorem cell23_5389216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_5389216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389216 prefixEnd_5389216 := by exact prefixLift 5389216
  have htrace : WordTrace (prefixWord ++ tailWord_5389216) baseStart_5389216 baseEnd_5389216 := by
    simpa [prefixWord, tailWord_5389216, baseEnd_5389216] using wordTrace_append hprefix tailTrace_5389216
  have hstable : (prefixWord ++ tailWord_5389216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389216).length < 2 ^ (prefixWord ++ tailWord_5389216).sum := by decide
  have hdescent : baseEnd_5389216 < baseStart_5389216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389272 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 1, 3, 4]
def baseStart_5389272 : Nat := 118140960795 + 5389272 * 2 ^ 59
def prefixEnd_5389272 : Nat := 4983230072969 + 3 ^ 40 * 5389272 * 2
def baseEnd_5389272 : Nat := 2767286913817543682215195

theorem tailTrace_5389272 : CollatzResearch.WordTrace tailWord_5389272 prefixEnd_5389272 2767286913817543682215195 := by
  unfold tailWord_5389272
  simp only [CollatzResearch.WordTrace]
  refine ⟨98281449065797716612389035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131041932087730288816518713 98281449065797716612389035)
  ·
    refine ⟨147422173598696574918583553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98281449065797716612389035 147422173598696574918583553)
    ·
      refine ⟨110566630199022431188937665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147422173598696574918583553 110566630199022431188937665)
      ·
        refine ⟨82924972649266823391703249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110566630199022431188937665 82924972649266823391703249)
        ·
          refine ⟨62193729486950117543777437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82924972649266823391703249 62193729486950117543777437)
          ·
            refine ⟨23322648557606294078916539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62193729486950117543777437 23322648557606294078916539)
            ·
              refine ⟨34983972836409441118374809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23322648557606294078916539 34983972836409441118374809)
              ·
                refine ⟨26237979627307080838781107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34983972836409441118374809 26237979627307080838781107)
                ·
                  refine ⟨39356969440960621258171661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26237979627307080838781107 39356969440960621258171661)
                  ·
                    refine ⟨14758863540360232971814373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39356969440960621258171661 14758863540360232971814373)
                    ·
                      refine ⟨2767286913817543682215195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14758863540360232971814373 2767286913817543682215195)
                      ·
                        rfl

theorem cell23_5389272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_5389272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389272 prefixEnd_5389272 := by exact prefixLift 5389272
  have htrace : WordTrace (prefixWord ++ tailWord_5389272) baseStart_5389272 baseEnd_5389272 := by
    simpa [prefixWord, tailWord_5389272, baseEnd_5389272] using wordTrace_append hprefix tailTrace_5389272
  have hstable : (prefixWord ++ tailWord_5389272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389272).length < 2 ^ (prefixWord ++ tailWord_5389272).sum := by decide
  have hdescent : baseEnd_5389272 < baseStart_5389272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389392 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 6]
def baseStart_5389392 : Nat := 118140960795 + 5389392 * 2 ^ 59
def prefixEnd_5389392 : Nat := 4983230072969 + 3 ^ 40 * 5389392 * 2
def baseEnd_5389392 : Nat := 2767348531496083212714643

theorem tailTrace_5389392 : CollatzResearch.WordTrace tailWord_5389392 prefixEnd_5389392 2767348531496083212714643 := by
  unfold tailWord_5389392
  simp only [CollatzResearch.WordTrace]
  refine ⟨98283637445580346859573215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131044849927440462479430953 98283637445580346859573215)
  ·
    refine ⟨147425456168370520289359823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98283637445580346859573215 147425456168370520289359823)
    ·
      refine ⟨221138184252555780434039735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147425456168370520289359823 221138184252555780434039735)
      ·
        refine ⟨331707276378833670651059603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221138184252555780434039735 331707276378833670651059603)
        ·
          refine ⟨497560914568250505976589405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331707276378833670651059603 497560914568250505976589405)
          ·
            refine ⟨186585342963093939741221027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 497560914568250505976589405 186585342963093939741221027)
            ·
              refine ⟨279878014444640909611831541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186585342963093939741221027 279878014444640909611831541)
              ·
                refine ⟨26238563854185085276109207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 279878014444640909611831541 26238563854185085276109207)
                ·
                  refine ⟨39357845781277627914163811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26238563854185085276109207 39357845781277627914163811)
                  ·
                    refine ⟨59036768671916441871245717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39357845781277627914163811 59036768671916441871245717)
                    ·
                      refine ⟨2767348531496083212714643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59036768671916441871245717 2767348531496083212714643)
                      ·
                        rfl

theorem cell23_5389392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_5389392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389392 prefixEnd_5389392 := by exact prefixLift 5389392
  have htrace : WordTrace (prefixWord ++ tailWord_5389392) baseStart_5389392 baseEnd_5389392 := by
    simpa [prefixWord, tailWord_5389392, baseEnd_5389392] using wordTrace_append hprefix tailTrace_5389392
  have hstable : (prefixWord ++ tailWord_5389392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389392).length < 2 ^ (prefixWord ++ tailWord_5389392).sum := by decide
  have hdescent : baseEnd_5389392 < baseStart_5389392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389409 : List Nat := [1, 2, 3, 1, 1, 2, 4, 2, 1, 2, 4]
def baseStart_5389409 : Nat := 118140960795 + 5389409 * 2 ^ 59
def prefixEnd_5389409 : Nat := 4983230072969 + 3 ^ 40 * 5389409 * 2
def baseEnd_5389409 : Nat := 2767357260667209646202065

theorem tailTrace_5389409 : CollatzResearch.WordTrace tailWord_5389409 prefixEnd_5389409 2767357260667209646202065 := by
  unfold tailWord_5389409
  simp only [CollatzResearch.WordTrace]
  refine ⟨196567894932099105622515281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131045263288066070415010187 196567894932099105622515281)
  ·
    refine ⟨147425921199074329216886461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196567894932099105622515281 147425921199074329216886461)
    ·
      refine ⟨55284720449652873456332423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147425921199074329216886461 55284720449652873456332423)
      ·
        refine ⟨82927080674479310184498635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55284720449652873456332423 82927080674479310184498635)
        ·
          refine ⟨124390621011718965276747953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82927080674479310184498635 124390621011718965276747953)
          ·
            refine ⟨93292965758789223957560965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124390621011718965276747953 93292965758789223957560965)
            ·
              refine ⟨17492431079772979492042681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93292965758789223957560965 17492431079772979492042681)
              ·
                refine ⟨13119323309829734619032011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17492431079772979492042681 13119323309829734619032011)
                ·
                  refine ⟨19678984964744601928548017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13119323309829734619032011 19678984964744601928548017)
                  ·
                    refine ⟨14759238723558451446411013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19678984964744601928548017 14759238723558451446411013)
                    ·
                      refine ⟨2767357260667209646202065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14759238723558451446411013 2767357260667209646202065)
                      ·
                        rfl

theorem cell23_5389409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_5389409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389409 prefixEnd_5389409 := by exact prefixLift 5389409
  have htrace : WordTrace (prefixWord ++ tailWord_5389409) baseStart_5389409 baseEnd_5389409 := by
    simpa [prefixWord, tailWord_5389409, baseEnd_5389409] using wordTrace_append hprefix tailTrace_5389409
  have hstable : (prefixWord ++ tailWord_5389409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389409).length < 2 ^ (prefixWord ++ tailWord_5389409).sum := by decide
  have hdescent : baseEnd_5389409 < baseStart_5389409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389410 : List Nat := [3, 3, 2, 2, 1, 3, 2, 1, 1, 5]
def baseStart_5389410 : Nat := 118140960795 + 5389410 * 2 ^ 59
def prefixEnd_5389410 : Nat := 4983230072969 + 3 ^ 40 * 5389410 * 2
def baseEnd_5389410 : Nat := 922452591382621380763187

theorem tailTrace_5389410 : CollatzResearch.WordTrace tailWord_5389410 prefixEnd_5389410 922452591382621380763187 := by
  unfold tailWord_5389410
  simp only [CollatzResearch.WordTrace]
  refine ⟨49141982851273870698325421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131045287603396988528867789 49141982851273870698325421)
  ·
    refine ⟨18428243569227701511872033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49141982851273870698325421 18428243569227701511872033)
    ·
      refine ⟨13821182676920776133904025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18428243569227701511872033 13821182676920776133904025)
      ·
        refine ⟨10365887007690582100428019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13821182676920776133904025 10365887007690582100428019)
        ·
          refine ⟨15548830511535873150642029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10365887007690582100428019 15548830511535873150642029)
          ·
            refine ⟨5830811441825952431490761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15548830511535873150642029 5830811441825952431490761)
            ·
              refine ⟨4373108581369464323618071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5830811441825952431490761 4373108581369464323618071)
              ·
                refine ⟨6559662872054196485427107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4373108581369464323618071 6559662872054196485427107)
                ·
                  refine ⟨9839494308081294728140661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6559662872054196485427107 9839494308081294728140661)
                  ·
                    refine ⟨922452591382621380763187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9839494308081294728140661 922452591382621380763187)
                    ·
                      rfl

theorem cell23_5389410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_5389410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389410 prefixEnd_5389410 := by exact prefixLift 5389410
  have htrace : WordTrace (prefixWord ++ tailWord_5389410) baseStart_5389410 baseEnd_5389410 := by
    simpa [prefixWord, tailWord_5389410, baseEnd_5389410] using wordTrace_append hprefix tailTrace_5389410
  have hstable : (prefixWord ++ tailWord_5389410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389410).length < 2 ^ (prefixWord ++ tailWord_5389410).sum := by decide
  have hdescent : baseEnd_5389410 < baseStart_5389410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389430 : List Nat := [5, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2]
def baseStart_5389430 : Nat := 118140960795 + 5389430 * 2 ^ 59
def prefixEnd_5389430 : Nat := 4983230072969 + 3 ^ 40 * 5389430 * 2
def baseEnd_5389430 : Nat := 2767368043760954064039469

theorem tailTrace_5389430 : CollatzResearch.WordTrace tailWord_5389430 prefixEnd_5389430 2767368043760954064039469 := by
  unfold tailWord_5389430
  simp only [CollatzResearch.WordTrace]
  refine ⟨12285541304063939138064359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131045773910015350806019829 12285541304063939138064359)
  ·
    refine ⟨18428311956095908707096539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12285541304063939138064359 18428311956095908707096539)
    ·
      refine ⟨27642467934143863060644809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18428311956095908707096539 27642467934143863060644809)
      ·
        refine ⟨20731850950607897295483607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27642467934143863060644809 20731850950607897295483607)
        ·
          refine ⟨31097776425911845943225411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20731850950607897295483607 31097776425911845943225411)
          ·
            refine ⟨46646664638867768914838117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31097776425911845943225411 46646664638867768914838117)
            ·
              refine ⟨8746249619787706671532147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46646664638867768914838117 8746249619787706671532147)
              ·
                refine ⟨13119374429681560007298221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8746249619787706671532147 13119374429681560007298221)
                ·
                  refine ⟨4919765411130585002736833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13119374429681560007298221 4919765411130585002736833)
                  ·
                    refine ⟨3689824058347938752052625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4919765411130585002736833 3689824058347938752052625)
                    ·
                      refine ⟨2767368043760954064039469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3689824058347938752052625 2767368043760954064039469)
                      ·
                        rfl

theorem cell23_5389430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_5389430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389430 prefixEnd_5389430 := by exact prefixLift 5389430
  have htrace : WordTrace (prefixWord ++ tailWord_5389430) baseStart_5389430 baseEnd_5389430 := by
    simpa [prefixWord, tailWord_5389430, baseEnd_5389430] using wordTrace_append hprefix tailTrace_5389430
  have hstable : (prefixWord ++ tailWord_5389430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389430).length < 2 ^ (prefixWord ++ tailWord_5389430).sum := by decide
  have hdescent : baseEnd_5389430 < baseStart_5389430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389432 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 1, 9]
def baseStart_5389432 : Nat := 118140960795 + 5389432 * 2 ^ 59
def prefixEnd_5389432 : Nat := 4983230072969 + 3 ^ 40 * 5389432 * 2
def baseEnd_5389432 : Nat := 922456356907421018738153

theorem tailTrace_5389432 : CollatzResearch.WordTrace tailWord_5389432 prefixEnd_5389432 922456356907421018738153 := by
  unfold tailWord_5389432
  simp only [CollatzResearch.WordTrace]
  refine ⟨98284366905507890275301275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131045822540677187033735033 98284366905507890275301275)
  ·
    refine ⟨147426550358261835412951913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98284366905507890275301275 147426550358261835412951913)
    ·
      refine ⟨110569912768696376559713935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147426550358261835412951913 110569912768696376559713935)
      ·
        refine ⟨165854869153044564839570903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110569912768696376559713935 165854869153044564839570903)
        ·
          refine ⟨248782303729566847259356355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165854869153044564839570903 248782303729566847259356355)
          ·
            refine ⟨373173455594350270889034533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248782303729566847259356355 373173455594350270889034533)
            ·
              refine ⟨69970022923940675791693975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 373173455594350270889034533 69970022923940675791693975)
              ·
                refine ⟨104955034385911013687540963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69970022923940675791693975 104955034385911013687540963)
                ·
                  refine ⟨157432551578866520531311445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104955034385911013687540963 157432551578866520531311445)
                  ·
                    refine ⟨922456356907421018738153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 157432551578866520531311445 922456356907421018738153)
                    ·
                      rfl

theorem cell23_5389432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_5389432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389432 prefixEnd_5389432 := by exact prefixLift 5389432
  have htrace : WordTrace (prefixWord ++ tailWord_5389432) baseStart_5389432 baseEnd_5389432 := by
    simpa [prefixWord, tailWord_5389432, baseEnd_5389432] using wordTrace_append hprefix tailTrace_5389432
  have hstable : (prefixWord ++ tailWord_5389432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389432).length < 2 ^ (prefixWord ++ tailWord_5389432).sum := by decide
  have hdescent : baseEnd_5389432 < baseStart_5389432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389473 : List Nat := [1, 2, 3, 3, 1, 1, 1, 5, 1, 3, 2]
def baseStart_5389473 : Nat := 118140960795 + 5389473 * 2 ^ 59
def prefixEnd_5389473 : Nat := 4983230072969 + 3 ^ 40 * 5389473 * 2
def baseEnd_5389473 : Nat := 2767390123429097395801771

theorem tailTrace_5389473 : CollatzResearch.WordTrace tailWord_5389473 prefixEnd_5389473 2767390123429097395801771 := by
  unfold tailWord_5389473
  simp only [CollatzResearch.WordTrace]
  refine ⟨196570229203867244552845073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131046819469244829701896715 196570229203867244552845073)
  ·
    refine ⟨147427671902900433414633805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196570229203867244552845073 147427671902900433414633805)
    ·
      refine ⟨55285376963587662530487677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147427671902900433414633805 55285376963587662530487677)
      ·
        refine ⟨20732016361345373448932879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55285376963587662530487677 20732016361345373448932879)
        ·
          refine ⟨31098024542018060173399319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20732016361345373448932879 31098024542018060173399319)
          ·
            refine ⟨46647036813027090260098979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31098024542018060173399319 46647036813027090260098979)
            ·
              refine ⟨69970555219540635390148469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46647036813027090260098979 69970555219540635390148469)
              ·
                refine ⟨6559739551831934567826419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69970555219540635390148469 6559739551831934567826419)
                ·
                  refine ⟨9839609327747901851739629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6559739551831934567826419 9839609327747901851739629)
                  ·
                    refine ⟨3689853497905463194402361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9839609327747901851739629 3689853497905463194402361)
                    ·
                      refine ⟨2767390123429097395801771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3689853497905463194402361 2767390123429097395801771)
                      ·
                        rfl

theorem cell23_5389473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_5389473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389473 prefixEnd_5389473 := by exact prefixLift 5389473
  have htrace : WordTrace (prefixWord ++ tailWord_5389473) baseStart_5389473 baseEnd_5389473 := by
    simpa [prefixWord, tailWord_5389473, baseEnd_5389473] using wordTrace_append hprefix tailTrace_5389473
  have hstable : (prefixWord ++ tailWord_5389473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389473).length < 2 ^ (prefixWord ++ tailWord_5389473).sum := by decide
  have hdescent : baseEnd_5389473 < baseStart_5389473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389519 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 3]
def baseStart_5389519 : Nat := 118140960795 + 5389519 * 2 ^ 59
def prefixEnd_5389519 : Nat := 4983230072969 + 3 ^ 40 * 5389519 * 2
def baseEnd_5389519 : Nat := 2767413743539204215826559

theorem tailTrace_5389519 : CollatzResearch.WordTrace tailWord_5389519 prefixEnd_5389519 2767413743539204215826559 := by
  unfold tailWord_5389519
  simp only [CollatzResearch.WordTrace]
  refine ⟨196571906961700594409019611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131047937974467062939346407 196571906961700594409019611)
  ·
    refine ⟨294857860442550891613529417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196571906961700594409019611 294857860442550891613529417)
    ·
      refine ⟨221143395331913168710147063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294857860442550891613529417 221143395331913168710147063)
      ·
        refine ⟨331715092997869753065220595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221143395331913168710147063 331715092997869753065220595)
        ·
          refine ⟨497572639496804629597830893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331715092997869753065220595 497572639496804629597830893)
          ·
            refine ⟨186589739811301736099186585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 497572639496804629597830893 186589739811301736099186585)
            ·
              refine ⟨139942304858476302074389939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186589739811301736099186585 139942304858476302074389939)
              ·
                refine ⟨209913457287714453111584909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139942304858476302074389939 209913457287714453111584909)
                ·
                  refine ⟨78717546482892919916844341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209913457287714453111584909 78717546482892919916844341)
                  ·
                    refine ⟨7379769982771211242204157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78717546482892919916844341 7379769982771211242204157)
                    ·
                      refine ⟨2767413743539204215826559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7379769982771211242204157 2767413743539204215826559)
                      ·
                        rfl

theorem cell23_5389519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 3].length) (baseStart_5389519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389519 prefixEnd_5389519 := by exact prefixLift 5389519
  have htrace : WordTrace (prefixWord ++ tailWord_5389519) baseStart_5389519 baseEnd_5389519 := by
    simpa [prefixWord, tailWord_5389519, baseEnd_5389519] using wordTrace_append hprefix tailTrace_5389519
  have hstable : (prefixWord ++ tailWord_5389519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389519).length < 2 ^ (prefixWord ++ tailWord_5389519).sum := by decide
  have hdescent : baseEnd_5389519 < baseStart_5389519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389524 : List Nat := [2, 4, 1, 4, 1, 1, 3, 1, 1, 3, 2]
def baseStart_5389524 : Nat := 118140960795 + 5389524 * 2 ^ 59
def prefixEnd_5389524 : Nat := 4983230072969 + 3 ^ 40 * 5389524 * 2
def baseEnd_5389524 : Nat := 2767416310942476696264037

theorem tailTrace_5389524 : CollatzResearch.WordTrace tailWord_5389524 prefixEnd_5389524 2767416310942476696264037 := by
  unfold tailWord_5389524
  simp only [CollatzResearch.WordTrace]
  refine ⟨98286044663341240131475813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131048059551121653508634417 98286044663341240131475813)
  ·
    refine ⟨18428633374376482524651715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98286044663341240131475813 18428633374376482524651715)
    ·
      refine ⟨27642950061564723786977573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18428633374376482524651715 27642950061564723786977573)
      ·
        refine ⟨5183053136543385710058295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27642950061564723786977573 5183053136543385710058295)
        ·
          refine ⟨7774579704815078565087443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5183053136543385710058295 7774579704815078565087443)
          ·
            refine ⟨11661869557222617847631165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7774579704815078565087443 11661869557222617847631165)
            ·
              refine ⟨4373201083958481692861687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11661869557222617847631165 4373201083958481692861687)
              ·
                refine ⟨6559801625937722539292531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4373201083958481692861687 6559801625937722539292531)
                ·
                  refine ⟨9839702438906583808938797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6559801625937722539292531 9839702438906583808938797)
                  ·
                    refine ⟨3689888414589968928352049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9839702438906583808938797 3689888414589968928352049)
                    ·
                      refine ⟨2767416310942476696264037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3689888414589968928352049 2767416310942476696264037)
                      ·
                        rfl

theorem cell23_5389524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_5389524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389524 prefixEnd_5389524 := by exact prefixLift 5389524
  have htrace : WordTrace (prefixWord ++ tailWord_5389524) baseStart_5389524 baseEnd_5389524 := by
    simpa [prefixWord, tailWord_5389524, baseEnd_5389524] using wordTrace_append hprefix tailTrace_5389524
  have hstable : (prefixWord ++ tailWord_5389524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389524).length < 2 ^ (prefixWord ++ tailWord_5389524).sum := by decide
  have hdescent : baseEnd_5389524 < baseStart_5389524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389559 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 4]
def baseStart_5389559 : Nat := 118140960795 + 5389559 * 2 ^ 59
def prefixEnd_5389559 : Nat := 4983230072969 + 3 ^ 40 * 5389559 * 2
def baseEnd_5389559 : Nat := 2767434282765384059326375

theorem tailTrace_5389559 : CollatzResearch.WordTrace tailWord_5389559 prefixEnd_5389559 2767434282765384059326375 := by
  unfold tailWord_5389559
  simp only [CollatzResearch.WordTrace]
  refine ⟨196573365881555681240475731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131048910587703787493650487 196573365881555681240475731)
  ·
    refine ⟨294860048822333521860713597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196573365881555681240475731 294860048822333521860713597)
    ·
      refine ⟨110572518308375070697767599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294860048822333521860713597 110572518308375070697767599)
      ·
        refine ⟨165858777462562606046651399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110572518308375070697767599 165858777462562606046651399)
        ·
          refine ⟨248788166193843909069977099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165858777462562606046651399 248788166193843909069977099)
          ·
            refine ⟨373182249290765863604965649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248788166193843909069977099 373182249290765863604965649)
            ·
              refine ⟨279886686968074397703724237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373182249290765863604965649 279886686968074397703724237)
              ·
                refine ⟨104957507613027899138896589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 279886686968074397703724237 104957507613027899138896589)
                ·
                  refine ⟨39359065354885462177086221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104957507613027899138896589 39359065354885462177086221)
                  ·
                    refine ⟨14759649508082048316407333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39359065354885462177086221 14759649508082048316407333)
                    ·
                      refine ⟨2767434282765384059326375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14759649508082048316407333 2767434282765384059326375)
                      ·
                        rfl

theorem cell23_5389559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_5389559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389559 prefixEnd_5389559 := by exact prefixLift 5389559
  have htrace : WordTrace (prefixWord ++ tailWord_5389559) baseStart_5389559 baseEnd_5389559 := by
    simpa [prefixWord, tailWord_5389559, baseEnd_5389559] using wordTrace_append hprefix tailTrace_5389559
  have hstable : (prefixWord ++ tailWord_5389559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389559).length < 2 ^ (prefixWord ++ tailWord_5389559).sum := by decide
  have hdescent : baseEnd_5389559 < baseStart_5389559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389603 : List Nat := [1, 1, 1, 4, 2, 4, 2, 1, 3, 4]
def baseStart_5389603 : Nat := 118140960795 + 5389603 * 2 ^ 59
def prefixEnd_5389603 : Nat := 4983230072969 + 3 ^ 40 * 5389603 * 2
def baseEnd_5389603 : Nat := 922485625304727295725391

theorem tailTrace_5389603 : CollatzResearch.WordTrace tailWord_5389603 prefixEnd_5389603 922485625304727295725391 := by
  unfold tailWord_5389603
  simp only [CollatzResearch.WordTrace]
  refine ⟨196574970693396276755077463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131049980462264184503384975 196574970693396276755077463)
  ·
    refine ⟨294862456040094415132616195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196574970693396276755077463 294862456040094415132616195)
    ·
      refine ⟨442293684060141622698924293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294862456040094415132616195 442293684060141622698924293)
      ·
        refine ⟨82930065761276554256048305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 442293684060141622698924293 82930065761276554256048305)
        ·
          refine ⟨62197549320957415692036229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82930065761276554256048305 62197549320957415692036229)
          ·
            refine ⟨11662040497679515442256793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62197549320957415692036229 11662040497679515442256793)
            ·
              refine ⟨8746530373259636581692595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11662040497679515442256793 8746530373259636581692595)
              ·
                refine ⟨13119795559889454872538893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8746530373259636581692595 13119795559889454872538893)
                ·
                  refine ⟨4919923334958545577202085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13119795559889454872538893 4919923334958545577202085)
                  ·
                    refine ⟨922485625304727295725391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4919923334958545577202085 922485625304727295725391)
                    ·
                      rfl

theorem cell23_5389603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 4].length) (baseStart_5389603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389603 prefixEnd_5389603 := by exact prefixLift 5389603
  have htrace : WordTrace (prefixWord ++ tailWord_5389603) baseStart_5389603 baseEnd_5389603 := by
    simpa [prefixWord, tailWord_5389603, baseEnd_5389603] using wordTrace_append hprefix tailTrace_5389603
  have hstable : (prefixWord ++ tailWord_5389603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389603).length < 2 ^ (prefixWord ++ tailWord_5389603).sum := by decide
  have hdescent : baseEnd_5389603 < baseStart_5389603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389610 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_5389610 : Nat := 118140960795 + 5389610 * 2 ^ 59
def prefixEnd_5389610 : Nat := 4983230072969 + 3 ^ 40 * 5389610 * 2
def baseEnd_5389610 : Nat := 2767460470278763359788641

theorem tailTrace_5389610 : CollatzResearch.WordTrace tailWord_5389610 prefixEnd_5389610 2767460470278763359788641 := by
  unfold tailWord_5389610
  simp only [CollatzResearch.WordTrace]
  refine ⟨49143806501092729237645571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131050150669580611300388189 49143806501092729237645571)
  ·
    refine ⟨73715709751639093856468357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49143806501092729237645571 73715709751639093856468357)
    ·
      refine ⟨13821695578432330098087817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73715709751639093856468357 13821695578432330098087817)
      ·
        refine ⟨10366271683824247573565863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13821695578432330098087817 10366271683824247573565863)
        ·
          refine ⟨15549407525736371360348795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10366271683824247573565863 15549407525736371360348795)
          ·
            refine ⟨23324111288604557040523193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15549407525736371360348795 23324111288604557040523193)
            ·
              refine ⟨17493083466453417780392395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23324111288604557040523193 17493083466453417780392395)
              ·
                refine ⟨26239625199680126670588593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17493083466453417780392395 26239625199680126670588593)
                ·
                  refine ⟨19679718899760095002941445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26239625199680126670588593 19679718899760095002941445)
                  ·
                    refine ⟨3689947293705017813051521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19679718899760095002941445 3689947293705017813051521)
                    ·
                      refine ⟨2767460470278763359788641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3689947293705017813051521 2767460470278763359788641)
                      ·
                        rfl

theorem cell23_5389610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_5389610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389610 prefixEnd_5389610 := by exact prefixLift 5389610
  have htrace : WordTrace (prefixWord ++ tailWord_5389610) baseStart_5389610 baseEnd_5389610 := by
    simpa [prefixWord, tailWord_5389610, baseEnd_5389610] using wordTrace_append hprefix tailTrace_5389610
  have hstable : (prefixWord ++ tailWord_5389610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389610).length < 2 ^ (prefixWord ++ tailWord_5389610).sum := by decide
  have hdescent : baseEnd_5389610 < baseStart_5389610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389626 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3]
def baseStart_5389626 : Nat := 118140960795 + 5389626 * 2 ^ 59
def prefixEnd_5389626 : Nat := 4983230072969 + 3 ^ 40 * 5389626 * 2
def baseEnd_5389626 : Nat := 2767468685969235297188567

theorem tailTrace_5389626 : CollatzResearch.WordTrace tailWord_5389626 prefixEnd_5389626 2767468685969235297188567 := by
  unfold tailWord_5389626
  simp only [CollatzResearch.WordTrace]
  refine ⟨49143952393078237920791183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131050539714875301122109821 49143952393078237920791183)
  ·
    refine ⟨73715928589617356881186775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49143952393078237920791183 73715928589617356881186775)
    ·
      refine ⟨110573892884426035321780163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73715928589617356881186775 110573892884426035321780163)
      ·
        refine ⟨165860839326639052982670245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110573892884426035321780163 165860839326639052982670245)
        ·
          refine ⟨31098907373744822434250671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165860839326639052982670245 31098907373744822434250671)
          ·
            refine ⟨46648361060617233651376007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31098907373744822434250671 46648361060617233651376007)
            ·
              refine ⟨69972541590925850477064011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46648361060617233651376007 69972541590925850477064011)
              ·
                refine ⟨104958812386388775715596017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69972541590925850477064011 104958812386388775715596017)
                ·
                  refine ⟨78719109289791581786697013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104958812386388775715596017 78719109289791581786697013)
                  ·
                    refine ⟨7379916495917960792502845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78719109289791581786697013 7379916495917960792502845)
                    ·
                      refine ⟨2767468685969235297188567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7379916495917960792502845 2767468685969235297188567)
                      ·
                        rfl

theorem cell23_5389626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_5389626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389626 prefixEnd_5389626 := by exact prefixLift 5389626
  have htrace : WordTrace (prefixWord ++ tailWord_5389626) baseStart_5389626 baseEnd_5389626 := by
    simpa [prefixWord, tailWord_5389626, baseEnd_5389626] using wordTrace_append hprefix tailTrace_5389626
  have hstable : (prefixWord ++ tailWord_5389626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389626).length < 2 ^ (prefixWord ++ tailWord_5389626).sum := by decide
  have hdescent : baseEnd_5389626 < baseStart_5389626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389697 : List Nat := [1, 2, 4, 3, 2, 1, 3, 1, 1, 5]
def baseStart_5389697 : Nat := 118140960795 + 5389697 * 2 ^ 59
def prefixEnd_5389697 : Nat := 4983230072969 + 3 ^ 40 * 5389697 * 2
def baseEnd_5389697 : Nat := 922501714365234839800247

theorem tailTrace_5389697 : CollatzResearch.WordTrace tailWord_5389697 prefixEnd_5389697 922501714365234839800247 := by
  unfold tailWord_5389697
  simp only [CollatzResearch.WordTrace]
  refine ⟨196578399155055730808999345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131052266103370487205999563 196578399155055730808999345)
  ·
    refine ⟨147433799366291798106749509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196578399155055730808999345 147433799366291798106749509)
    ·
      refine ⟨27643837381179712145015533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147433799366291798106749509 27643837381179712145015533)
      ·
        refine ⟨10366439017942392054380825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27643837381179712145015533 10366439017942392054380825)
        ·
          refine ⟨7774829263456794040785619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10366439017942392054380825 7774829263456794040785619)
          ·
            refine ⟨11662243895185191061178429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7774829263456794040785619 11662243895185191061178429)
            ·
              refine ⟨4373341460694446647941911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11662243895185191061178429 4373341460694446647941911)
              ·
                refine ⟨6560012191041669971912867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4373341460694446647941911 6560012191041669971912867)
                ·
                  refine ⟨9840018286562504957869301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6560012191041669971912867 9840018286562504957869301)
                  ·
                    refine ⟨922501714365234839800247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9840018286562504957869301 922501714365234839800247)
                    ·
                      rfl

theorem cell23_5389697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_5389697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389697 prefixEnd_5389697 := by exact prefixLift 5389697
  have htrace : WordTrace (prefixWord ++ tailWord_5389697) baseStart_5389697 baseEnd_5389697 := by
    simpa [prefixWord, tailWord_5389697, baseEnd_5389697] using wordTrace_append hprefix tailTrace_5389697
  have hstable : (prefixWord ++ tailWord_5389697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389697).length < 2 ^ (prefixWord ++ tailWord_5389697).sum := by decide
  have hdescent : baseEnd_5389697 < baseStart_5389697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389703 : List Nat := [1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 5]
def baseStart_5389703 : Nat := 118140960795 + 5389703 * 2 ^ 59
def prefixEnd_5389703 : Nat := 4983230072969 + 3 ^ 40 * 5389703 * 2
def baseEnd_5389703 : Nat := 2767508223979631495925713

theorem tailTrace_5389703 : CollatzResearch.WordTrace tailWord_5389703 prefixEnd_5389703 2767508223979631495925713 := by
  unfold tailWord_5389703
  simp only [CollatzResearch.WordTrace]
  refine ⟨196578617993033993833717763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131052411995355995889145175 196578617993033993833717763)
  ·
    refine ⟨294867926989550990750576645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196578617993033993833717763 294867926989550990750576645)
    ·
      refine ⟨55287736310540810765733121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 294867926989550990750576645 55287736310540810765733121)
      ·
        refine ⟨41465802232905608074299841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55287736310540810765733121 41465802232905608074299841)
        ·
          refine ⟨31099351674679206055724881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41465802232905608074299841 31099351674679206055724881)
          ·
            refine ⟨23324513756009404541793661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31099351674679206055724881 23324513756009404541793661)
            ·
              refine ⟨8746692658503526703172623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23324513756009404541793661 8746692658503526703172623)
              ·
                refine ⟨13120038987755290054758935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8746692658503526703172623 13120038987755290054758935)
                ·
                  refine ⟨19680058481632935082138403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13120038987755290054758935 19680058481632935082138403)
                  ·
                    refine ⟨29520087722449402623207605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19680058481632935082138403 29520087722449402623207605)
                    ·
                      refine ⟨2767508223979631495925713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29520087722449402623207605 2767508223979631495925713)
                      ·
                        rfl

theorem cell23_5389703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_5389703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389703 prefixEnd_5389703 := by exact prefixLift 5389703
  have htrace : WordTrace (prefixWord ++ tailWord_5389703) baseStart_5389703 baseEnd_5389703 := by
    simpa [prefixWord, tailWord_5389703, baseEnd_5389703] using wordTrace_append hprefix tailTrace_5389703
  have hstable : (prefixWord ++ tailWord_5389703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389703).length < 2 ^ (prefixWord ++ tailWord_5389703).sum := by decide
  have hdescent : baseEnd_5389703 < baseStart_5389703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389730 : List Nat := [3, 3, 1, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_5389730 : Nat := 118140960795 + 5389730 * 2 ^ 59
def prefixEnd_5389730 : Nat := 4983230072969 + 3 ^ 40 * 5389730 * 2
def baseEnd_5389730 : Nat := 2767522087957302890288089

theorem tailTrace_5389730 : CollatzResearch.WordTrace tailWord_5389730 prefixEnd_5389730 2767522087957302890288089 := by
  unfold tailWord_5389730
  simp only [CollatzResearch.WordTrace]
  refine ⟨49144900690984044361237661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131053068509290784963300429 49144900690984044361237661)
  ·
    refine ⟨18429337759119016635464123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49144900690984044361237661 18429337759119016635464123)
    ·
      refine ⟨27644006638678524953196185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18429337759119016635464123 27644006638678524953196185)
      ·
        refine ⟨20733004979008893714897139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27644006638678524953196185 20733004979008893714897139)
        ·
          refine ⟨31099507468513340572345709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20733004979008893714897139 31099507468513340572345709)
          ·
            refine ⟨11662315300692502714629641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31099507468513340572345709 11662315300692502714629641)
            ·
              refine ⟨8746736475519377035972231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11662315300692502714629641 8746736475519377035972231)
              ·
                refine ⟨13120104713279065553958347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8746736475519377035972231 13120104713279065553958347)
                ·
                  refine ⟨19680157069918598330937521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13120104713279065553958347 19680157069918598330937521)
                  ·
                    refine ⟨14760117802438948748203141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19680157069918598330937521 14760117802438948748203141)
                    ·
                      refine ⟨2767522087957302890288089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14760117802438948748203141 2767522087957302890288089)
                      ·
                        rfl

theorem cell23_5389730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_5389730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389730 prefixEnd_5389730 := by exact prefixLift 5389730
  have htrace : WordTrace (prefixWord ++ tailWord_5389730) baseStart_5389730 baseEnd_5389730 := by
    simpa [prefixWord, tailWord_5389730, baseEnd_5389730] using wordTrace_append hprefix tailTrace_5389730
  have hstable : (prefixWord ++ tailWord_5389730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389730).length < 2 ^ (prefixWord ++ tailWord_5389730).sum := by decide
  have hdescent : baseEnd_5389730 < baseStart_5389730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389776 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 5]
def baseStart_5389776 : Nat := 118140960795 + 5389776 * 2 ^ 59
def prefixEnd_5389776 : Nat := 4983230072969 + 3 ^ 40 * 5389776 * 2
def baseEnd_5389776 : Nat := 2767545708067409710312877

theorem tailTrace_5389776 : CollatzResearch.WordTrace tailWord_5389776 prefixEnd_5389776 2767545708067409710312877 := by
  unfold tailWord_5389776
  simp only [CollatzResearch.WordTrace]
  refine ⟨98290640260884763650562591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131054187014513018200750121 98290640260884763650562591)
  ·
    refine ⟨147435960391327145475843887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98290640260884763650562591 147435960391327145475843887)
    ·
      refine ⟨221153940586990718213765831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147435960391327145475843887 221153940586990718213765831)
      ·
        refine ⟨331730910880486077320648747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221153940586990718213765831 331730910880486077320648747)
        ·
          refine ⟨497596366320729115980973121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331730910880486077320648747 497596366320729115980973121)
          ·
            refine ⟨373197274740546836985729841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497596366320729115980973121 373197274740546836985729841)
            ·
              refine ⟨279897956055410127739297381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373197274740546836985729841 279897956055410127739297381)
              ·
                refine ⟨52480866760389398951118259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 279897956055410127739297381 52480866760389398951118259)
                ·
                  refine ⟨78721300140584098426677389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52480866760389398951118259 78721300140584098426677389)
                  ·
                    refine ⟨29520487552719036910004021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78721300140584098426677389 29520487552719036910004021)
                    ·
                      refine ⟨2767545708067409710312877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29520487552719036910004021 2767545708067409710312877)
                      ·
                        rfl

theorem cell23_5389776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_5389776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389776 prefixEnd_5389776 := by exact prefixLift 5389776
  have htrace : WordTrace (prefixWord ++ tailWord_5389776) baseStart_5389776 baseEnd_5389776 := by
    simpa [prefixWord, tailWord_5389776, baseEnd_5389776] using wordTrace_append hprefix tailTrace_5389776
  have hstable : (prefixWord ++ tailWord_5389776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389776).length < 2 ^ (prefixWord ++ tailWord_5389776).sum := by decide
  have hdescent : baseEnd_5389776 < baseStart_5389776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389810 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 2, 1, 5]
def baseStart_5389810 : Nat := 118140960795 + 5389810 * 2 ^ 59
def prefixEnd_5389810 : Nat := 4983230072969 + 3 ^ 40 * 5389810 * 2
def baseEnd_5389810 : Nat := 2767563166409662577287721

theorem tailTrace_5389810 : CollatzResearch.WordTrace tailWord_5389810 prefixEnd_5389810 2767563166409662577287721 := by
  unfold tailWord_5389810
  simp only [CollatzResearch.WordTrace]
  refine ⟨49145630150911587776965721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131055013735764234071908589 49145630150911587776965721)
  ·
    refine ⟨36859222613183690832724291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49145630150911587776965721 36859222613183690832724291)
    ·
      refine ⟨55288833919775536249086437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36859222613183690832724291 55288833919775536249086437)
      ·
        refine ⟨10366656359957913046703707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55288833919775536249086437 10366656359957913046703707)
        ·
          refine ⟨15549984539936869570055561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10366656359957913046703707 15549984539936869570055561)
          ·
            refine ⟨11662488404952652177541671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15549984539936869570055561 11662488404952652177541671)
            ·
              refine ⟨17493732607428978266312507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11662488404952652177541671 17493732607428978266312507)
              ·
                refine ⟨26240598911143467399468761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17493732607428978266312507 26240598911143467399468761)
                ·
                  refine ⟨19680449183357600549601571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26240598911143467399468761 19680449183357600549601571)
                  ·
                    refine ⟨29520673775036400824402357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19680449183357600549601571 29520673775036400824402357)
                    ·
                      refine ⟨2767563166409662577287721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29520673775036400824402357 2767563166409662577287721)
                      ·
                        rfl

theorem cell23_5389810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_5389810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389810 prefixEnd_5389810 := by exact prefixLift 5389810
  have htrace : WordTrace (prefixWord ++ tailWord_5389810) baseStart_5389810 baseEnd_5389810 := by
    simpa [prefixWord, tailWord_5389810, baseEnd_5389810] using wordTrace_append hprefix tailTrace_5389810
  have hstable : (prefixWord ++ tailWord_5389810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389810).length < 2 ^ (prefixWord ++ tailWord_5389810).sum := by decide
  have hdescent : baseEnd_5389810 < baseStart_5389810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389823 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 3]
def baseStart_5389823 : Nat := 118140960795 + 5389823 * 2 ^ 59
def prefixEnd_5389823 : Nat := 4983230072969 + 3 ^ 40 * 5389823 * 2
def baseEnd_5389823 : Nat := 2767569841658171026425161

theorem tailTrace_5389823 : CollatzResearch.WordTrace tailWord_5389823 prefixEnd_5389823 2767569841658171026425161 := by
  unfold tailWord_5389823
  simp only [CollatzResearch.WordTrace]
  refine ⟨196582994752599254328086123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131055329835066169552057415 196582994752599254328086123)
  ·
    refine ⟨294874492128898881492129185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196582994752599254328086123 294874492128898881492129185)
    ·
      refine ⟨221155869096674161119096889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294874492128898881492129185 221155869096674161119096889)
      ·
        refine ⟨165866901822505620839322667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221155869096674161119096889 165866901822505620839322667)
        ·
          refine ⟨248800352733758431258984001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165866901822505620839322667 248800352733758431258984001)
          ·
            refine ⟨186600264550318823444238001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248800352733758431258984001 186600264550318823444238001)
            ·
              refine ⟨139950198412739117583178501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186600264550318823444238001 139950198412739117583178501)
              ·
                refine ⟨26240662202388584546845969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139950198412739117583178501 26240662202388584546845969)
                ·
                  refine ⟨19680496651791438410134477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26240662202388584546845969 19680496651791438410134477)
                  ·
                    refine ⟨7380186244421789403800429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19680496651791438410134477 7380186244421789403800429)
                    ·
                      refine ⟨2767569841658171026425161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7380186244421789403800429 2767569841658171026425161)
                      ·
                        rfl

theorem cell23_5389823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_5389823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389823 prefixEnd_5389823 := by exact prefixLift 5389823
  have htrace : WordTrace (prefixWord ++ tailWord_5389823) baseStart_5389823 baseEnd_5389823 := by
    simpa [prefixWord, tailWord_5389823, baseEnd_5389823] using wordTrace_append hprefix tailTrace_5389823
  have hstable : (prefixWord ++ tailWord_5389823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389823).length < 2 ^ (prefixWord ++ tailWord_5389823).sum := by decide
  have hdescent : baseEnd_5389823 < baseStart_5389823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389853 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_5389853 : Nat := 118140960795 + 5389853 * 2 ^ 59
def prefixEnd_5389853 : Nat := 4983230072969 + 3 ^ 40 * 5389853 * 2
def baseEnd_5389853 : Nat := 2767585246077805909050023

theorem tailTrace_5389853 : CollatzResearch.WordTrace tailWord_5389853 prefixEnd_5389853 2767585246077805909050023 := by
  unfold tailWord_5389853
  simp only [CollatzResearch.WordTrace]
  refine ⟨196584088942490569451678213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131056059294993712967785475 196584088942490569451678213)
  ·
    refine ⟨36859516676716981772189665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196584088942490569451678213 36859516676716981772189665)
    ·
      refine ⟨27644637507537736329142249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36859516676716981772189665 27644637507537736329142249)
      ·
        refine ⟨20733478130653302246856687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27644637507537736329142249 20733478130653302246856687)
        ·
          refine ⟨31100217195979953370285031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20733478130653302246856687 31100217195979953370285031)
          ·
            refine ⟨46650325793969930055427547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31100217195979953370285031 46650325793969930055427547)
            ·
              refine ⟨69975488690954895083141321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46650325793969930055427547 69975488690954895083141321)
              ·
                refine ⟨52481616518216171312355991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69975488690954895083141321 52481616518216171312355991)
                ·
                  refine ⟨78722424777324256968533987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52481616518216171312355991 78722424777324256968533987)
                  ·
                    refine ⟨118083637165986385452800981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78722424777324256968533987 118083637165986385452800981)
                    ·
                      refine ⟨2767585246077805909050023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118083637165986385452800981 2767585246077805909050023)
                      ·
                        rfl

theorem cell23_5389853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_5389853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389853 prefixEnd_5389853 := by exact prefixLift 5389853
  have htrace : WordTrace (prefixWord ++ tailWord_5389853) baseStart_5389853 baseEnd_5389853 := by
    simpa [prefixWord, tailWord_5389853, baseEnd_5389853] using wordTrace_append hprefix tailTrace_5389853
  have hstable : (prefixWord ++ tailWord_5389853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389853).length < 2 ^ (prefixWord ++ tailWord_5389853).sum := by decide
  have hdescent : baseEnd_5389853 < baseStart_5389853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389870 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_5389870 : Nat := 118140960795 + 5389870 * 2 ^ 59
def prefixEnd_5389870 : Nat := 4983230072969 + 3 ^ 40 * 5389870 * 2
def baseEnd_5389870 : Nat := 2767593975248932342537445

theorem tailTrace_5389870 : CollatzResearch.WordTrace tailWord_5389870 prefixEnd_5389870 2767593975248932342537445 := by
  unfold tailWord_5389870
  simp only [CollatzResearch.WordTrace]
  refine ⟨24573088622928622669380883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131056472655619320903364709 24573088622928622669380883)
  ·
    refine ⟨36859632934392934004071325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24573088622928622669380883 36859632934392934004071325)
    ·
      refine ⟨13822362350397350251526747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36859632934392934004071325 13822362350397350251526747)
      ·
        refine ⟨20733543525596025377290121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13822362350397350251526747 20733543525596025377290121)
        ·
          refine ⟨15550157644197019032967591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20733543525596025377290121 15550157644197019032967591)
          ·
            refine ⟨23325236466295528549451387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15550157644197019032967591 23325236466295528549451387)
            ·
              refine ⟨34987854699443292824177081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23325236466295528549451387 34987854699443292824177081)
              ·
                refine ⟨26240891024582469618132811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34987854699443292824177081 26240891024582469618132811)
                ·
                  refine ⟨39361336536873704427199217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26240891024582469618132811 39361336536873704427199217)
                  ·
                    refine ⟨29521002402655278320399413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39361336536873704427199217 29521002402655278320399413)
                    ·
                      refine ⟨2767593975248932342537445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29521002402655278320399413 2767593975248932342537445)
                      ·
                        rfl

theorem cell23_5389870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_5389870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389870 prefixEnd_5389870 := by exact prefixLift 5389870
  have htrace : WordTrace (prefixWord ++ tailWord_5389870) baseStart_5389870 baseEnd_5389870 := by
    simpa [prefixWord, tailWord_5389870, baseEnd_5389870] using wordTrace_append hprefix tailTrace_5389870
  have hstable : (prefixWord ++ tailWord_5389870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389870).length < 2 ^ (prefixWord ++ tailWord_5389870).sum := by decide
  have hdescent : baseEnd_5389870 < baseStart_5389870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389880 : List Nat := [2, 1, 2, 1, 4, 2, 2, 2, 2, 1, 4]
def baseStart_5389880 : Nat := 118140960795 + 5389880 * 2 ^ 59
def prefixEnd_5389880 : Nat := 4983230072969 + 3 ^ 40 * 5389880 * 2
def baseEnd_5389880 : Nat := 2767599110055477303412399

theorem tailTrace_5389880 : CollatzResearch.WordTrace tailWord_5389880 prefixEnd_5389880 2767599110055477303412399 := by
  unfold tailWord_5389880
  simp only [CollatzResearch.WordTrace]
  refine ⟨98292536856696376531455547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131056715808928502041940729 98292536856696376531455547)
  ·
    refine ⟨147438805285044564797183321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98292536856696376531455547 147438805285044564797183321)
    ·
      refine ⟨110579103963783423597887491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147438805285044564797183321 110579103963783423597887491)
      ·
        refine ⟨165868655945675135396831237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110579103963783423597887491 165868655945675135396831237)
        ·
          refine ⟨31100372989814087886905857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165868655945675135396831237 31100372989814087886905857)
          ·
            refine ⟨23325279742360565915179393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31100372989814087886905857 23325279742360565915179393)
            ·
              refine ⟨17493959806770424436384545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23325279742360565915179393 17493959806770424436384545)
              ·
                refine ⟨13120469855077818327288409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17493959806770424436384545 13120469855077818327288409)
                ·
                  refine ⟨9840352391308363745466307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13120469855077818327288409 9840352391308363745466307)
                  ·
                    refine ⟨14760528586962545618199461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9840352391308363745466307 14760528586962545618199461)
                    ·
                      refine ⟨2767599110055477303412399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14760528586962545618199461 2767599110055477303412399)
                      ·
                        rfl

theorem cell23_5389880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_5389880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389880 prefixEnd_5389880 := by exact prefixLift 5389880
  have htrace : WordTrace (prefixWord ++ tailWord_5389880) baseStart_5389880 baseEnd_5389880 := by
    simpa [prefixWord, tailWord_5389880, baseEnd_5389880] using wordTrace_append hprefix tailTrace_5389880
  have hstable : (prefixWord ++ tailWord_5389880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389880).length < 2 ^ (prefixWord ++ tailWord_5389880).sum := by decide
  have hdescent : baseEnd_5389880 < baseStart_5389880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389924 : List Nat := [2, 3, 1, 1, 2, 4, 2, 3, 1, 4]
def baseStart_5389924 : Nat := 118140960795 + 5389924 * 2 ^ 59
def prefixEnd_5389924 : Nat := 4983230072969 + 3 ^ 40 * 5389924 * 2
def baseEnd_5389924 : Nat := 922540567734758377087399

theorem tailTrace_5389924 : CollatzResearch.WordTrace tailWord_5389924 prefixEnd_5389924 922540567734758377087399 := by
  unfold tailWord_5389924
  simp only [CollatzResearch.WordTrace]
  refine ⟨98293339262616674288756413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131057785683488899051675217 98293339262616674288756413)
  ·
    refine ⟨36860002223481252858283655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98293339262616674288756413 36860002223481252858283655)
    ·
      refine ⟨55290003335221879287425483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36860002223481252858283655 55290003335221879287425483)
      ·
        refine ⟨82935005002832818931138225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55290003335221879287425483 82935005002832818931138225)
        ·
          refine ⟨62201253752124614198353669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82935005002832818931138225 62201253752124614198353669)
          ·
            refine ⟨11662735078523365162191313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62201253752124614198353669 11662735078523365162191313)
            ·
              refine ⟨8747051308892523871643485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11662735078523365162191313 8747051308892523871643485)
              ·
                refine ⟨3280144240834696451866307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8747051308892523871643485 3280144240834696451866307)
                ·
                  refine ⟨4920216361252044677799461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3280144240834696451866307 4920216361252044677799461)
                  ·
                    refine ⟨922540567734758377087399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4920216361252044677799461 922540567734758377087399)
                    ·
                      rfl

theorem cell23_5389924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_5389924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389924 prefixEnd_5389924 := by exact prefixLift 5389924
  have htrace : WordTrace (prefixWord ++ tailWord_5389924) baseStart_5389924 baseEnd_5389924 := by
    simpa [prefixWord, tailWord_5389924, baseEnd_5389924] using wordTrace_append hprefix tailTrace_5389924
  have hstable : (prefixWord ++ tailWord_5389924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389924).length < 2 ^ (prefixWord ++ tailWord_5389924).sum := by decide
  have hdescent : baseEnd_5389924 < baseStart_5389924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389947 : List Nat := [1, 1, 1, 1, 1, 4, 6, 1, 3, 1, 3]
def baseStart_5389947 : Nat := 118140960795 + 5389947 * 2 ^ 59
def prefixEnd_5389947 : Nat := 4983230072969 + 3 ^ 40 * 5389947 * 2
def baseEnd_5389947 : Nat := 2767633513259328541274591

theorem tailTrace_5389947 : CollatzResearch.WordTrace tailWord_5389947 prefixEnd_5389947 2767633513259328541274591 := by
  unfold tailWord_5389947
  simp only [CollatzResearch.WordTrace]
  refine ⟨196587517404150023505600095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131058344936100015670400063 196587517404150023505600095)
  ·
    refine ⟨294881276106225035258400143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196587517404150023505600095 294881276106225035258400143)
    ·
      refine ⟨442321914159337552887600215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294881276106225035258400143 442321914159337552887600215)
      ·
        refine ⟨663482871239006329331400323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442321914159337552887600215 663482871239006329331400323)
        ·
          refine ⟨995224306858509493997100485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663482871239006329331400323 995224306858509493997100485)
          ·
            refine ⟨186604557535970530124456341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 995224306858509493997100485 186604557535970530124456341)
            ·
              refine ⟨8747088634498618599583891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 186604557535970530124456341 8747088634498618599583891)
              ·
                refine ⟨13120632951747927899375837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8747088634498618599583891 13120632951747927899375837)
                ·
                  refine ⟨4920237356905472962265939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13120632951747927899375837 4920237356905472962265939)
                  ·
                    refine ⟨7380356035358209443398909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4920237356905472962265939 7380356035358209443398909)
                    ·
                      refine ⟨2767633513259328541274591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7380356035358209443398909 2767633513259328541274591)
                      ·
                        rfl

theorem cell23_5389947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 1, 3].length) (baseStart_5389947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389947 prefixEnd_5389947 := by exact prefixLift 5389947
  have htrace : WordTrace (prefixWord ++ tailWord_5389947) baseStart_5389947 baseEnd_5389947 := by
    simpa [prefixWord, tailWord_5389947, baseEnd_5389947] using wordTrace_append hprefix tailTrace_5389947
  have hstable : (prefixWord ++ tailWord_5389947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389947).length < 2 ^ (prefixWord ++ tailWord_5389947).sum := by decide
  have hdescent : baseEnd_5389947 < baseStart_5389947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389997 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_5389997 : Nat := 118140960795 + 5389997 * 2 ^ 59
def prefixEnd_5389997 : Nat := 4983230072969 + 3 ^ 40 * 5389997 * 2
def baseEnd_5389997 : Nat := 922553062430684448549787

theorem tailTrace_5389997 : CollatzResearch.WordTrace tailWord_5389997 prefixEnd_5389997 922553062430684448549787 := by
  unfold tailWord_5389997
  simp only [CollatzResearch.WordTrace]
  refine ⟨196589341053968882044920245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131059560702645921363280163 196589341053968882044920245)
  ·
    refine ⟨18430250723809582691711273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 196589341053968882044920245 18430250723809582691711273)
    ·
      refine ⟨13822688042857187018783455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18430250723809582691711273 13822688042857187018783455)
      ·
        refine ⟨20734032064285780528175183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13822688042857187018783455 20734032064285780528175183)
        ·
          refine ⟨31101048096428670792262775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20734032064285780528175183 31101048096428670792262775)
          ·
            refine ⟨46651572144643006188394163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31101048096428670792262775 46651572144643006188394163)
            ·
              refine ⟨69977358216964509282591245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46651572144643006188394163 69977358216964509282591245)
              ·
                refine ⟨26241509331361690980971717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69977358216964509282591245 26241509331361690980971717)
                ·
                  refine ⟨4920282999630317058932197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26241509331361690980971717 4920282999630317058932197)
                  ·
                    refine ⟨922553062430684448549787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4920282999630317058932197 922553062430684448549787)
                    ·
                      rfl

theorem cell23_5389997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_5389997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389997 prefixEnd_5389997 := by exact prefixLift 5389997
  have htrace : WordTrace (prefixWord ++ tailWord_5389997) baseStart_5389997 baseEnd_5389997 := by
    simpa [prefixWord, tailWord_5389997, baseEnd_5389997] using wordTrace_append hprefix tailTrace_5389997
  have hstable : (prefixWord ++ tailWord_5389997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389997).length < 2 ^ (prefixWord ++ tailWord_5389997).sum := by decide
  have hdescent : baseEnd_5389997 < baseStart_5389997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5389998 : List Nat := [4, 1, 4, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_5389998 : Nat := 118140960795 + 5389998 * 2 ^ 59
def prefixEnd_5389998 : Nat := 4983230072969 + 3 ^ 40 * 5389998 * 2
def baseEnd_5389998 : Nat := 2767659700772707841736857

theorem tailTrace_5389998 : CollatzResearch.WordTrace tailWord_5389998 prefixEnd_5389998 2767659700772707841736857 := by
  unfold tailWord_5389998
  simp only [CollatzResearch.WordTrace]
  refine ⟨24573672190870657401963331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131059585017976839477137765 24573672190870657401963331)
  ·
    refine ⟨36860508286305986102944997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24573672190870657401963331 36860508286305986102944997)
    ·
      refine ⟨6911345303682372394302187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36860508286305986102944997 6911345303682372394302187)
      ·
        refine ⟨10367017955523558591453281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6911345303682372394302187 10367017955523558591453281)
        ·
          refine ⟨7775263466642668943589961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10367017955523558591453281 7775263466642668943589961)
          ·
            refine ⟨5831447599982001707692471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7775263466642668943589961 5831447599982001707692471)
            ·
              refine ⟨8747171399973002561538707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5831447599982001707692471 8747171399973002561538707)
              ·
                refine ⟨13120757099959503842308061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8747171399973002561538707 13120757099959503842308061)
                ·
                  refine ⟨4920283912484813940865523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13120757099959503842308061 4920283912484813940865523)
                  ·
                    refine ⟨7380425868727220911298285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4920283912484813940865523 7380425868727220911298285)
                    ·
                      refine ⟨2767659700772707841736857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7380425868727220911298285 2767659700772707841736857)
                      ·
                        rfl

theorem cell23_5389998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_5389998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5389998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5389998 prefixEnd_5389998 := by exact prefixLift 5389998
  have htrace : WordTrace (prefixWord ++ tailWord_5389998) baseStart_5389998 baseEnd_5389998 := by
    simpa [prefixWord, tailWord_5389998, baseEnd_5389998] using wordTrace_append hprefix tailTrace_5389998
  have hstable : (prefixWord ++ tailWord_5389998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5389998).length < 2 ^ (prefixWord ++ tailWord_5389998).sum := by decide
  have hdescent : baseEnd_5389998 < baseStart_5389998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5389998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390010 : List Nat := [3, 1, 1, 1, 2, 5, 2, 8]
def baseStart_5390010 : Nat := 118140960795 + 5390010 * 2 ^ 59
def prefixEnd_5390010 : Nat := 4983230072969 + 3 ^ 40 * 5390010 * 2
def baseEnd_5390010 : Nat := 102506143057057844251363

theorem tailTrace_5390010 : CollatzResearch.WordTrace tailWord_5390010 prefixEnd_5390010 102506143057057844251363 := by
  unfold tailWord_5390010
  simp only [CollatzResearch.WordTrace]
  refine ⟨49147453800730446316285871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131059876801947856843428989 49147453800730446316285871)
  ·
    refine ⟨73721180701095669474428807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49147453800730446316285871 73721180701095669474428807)
    ·
      refine ⟨110581771051643504211643211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73721180701095669474428807 110581771051643504211643211)
      ·
        refine ⟨165872656577465256317464817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110581771051643504211643211 165872656577465256317464817)
        ·
          refine ⟨124404492433098942238098613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165872656577465256317464817 124404492433098942238098613)
          ·
            refine ⟨11662921165603025834821745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124404492433098942238098613 11662921165603025834821745)
            ·
              refine ⟨8747190874202269376116309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11662921165603025834821745 8747190874202269376116309)
              ·
                refine ⟨102506143057057844251363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8747190874202269376116309 102506143057057844251363)
                ·
                  rfl

theorem cell23_5390010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 8].length) (baseStart_5390010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390010 prefixEnd_5390010 := by exact prefixLift 5390010
  have htrace : WordTrace (prefixWord ++ tailWord_5390010) baseStart_5390010 baseEnd_5390010 := by
    simpa [prefixWord, tailWord_5390010, baseEnd_5390010] using wordTrace_append hprefix tailTrace_5390010
  have hstable : (prefixWord ++ tailWord_5390010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390010).length < 2 ^ (prefixWord ++ tailWord_5390010).sum := by decide
  have hdescent : baseEnd_5390010 < baseStart_5390010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390014 : List Nat := [4, 2, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_5390014 : Nat := 118140960795 + 5390014 * 2 ^ 59
def prefixEnd_5390014 : Nat := 4983230072969 + 3 ^ 40 * 5390014 * 2
def baseEnd_5390014 : Nat := 922555972154393259712261

theorem tailTrace_5390014 : CollatzResearch.WordTrace tailWord_5390014 prefixEnd_5390014 922555972154393259712261 := by
  unfold tailWord_5390014
  simp only [CollatzResearch.WordTrace]
  refine ⟨24573745136863411743536137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131059974063271529298859397 24573745136863411743536137)
  ·
    refine ⟨18430308852647558807652103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24573745136863411743536137 18430308852647558807652103)
    ·
      refine ⟨27645463278971338211478155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18430308852647558807652103 27645463278971338211478155)
      ·
        refine ⟨41468194918457007317217233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27645463278971338211478155 41468194918457007317217233)
        ·
          refine ⟨31101146188842755487912925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41468194918457007317217233 31101146188842755487912925)
          ·
            refine ⟨11662929820816033307967347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31101146188842755487912925 11662929820816033307967347)
            ·
              refine ⟨17494394731224049961951021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11662929820816033307967347 17494394731224049961951021)
              ·
                refine ⟨6560398024209018735731633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17494394731224049961951021 6560398024209018735731633)
                ·
                  refine ⟨4920298518156764051798725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6560398024209018735731633 4920298518156764051798725)
                  ·
                    refine ⟨922555972154393259712261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4920298518156764051798725 922555972154393259712261)
                    ·
                      rfl

theorem cell23_5390014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_5390014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390014 prefixEnd_5390014 := by exact prefixLift 5390014
  have htrace : WordTrace (prefixWord ++ tailWord_5390014) baseStart_5390014 baseEnd_5390014 := by
    simpa [prefixWord, tailWord_5390014, baseEnd_5390014] using wordTrace_append hprefix tailTrace_5390014
  have hstable : (prefixWord ++ tailWord_5390014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390014).length < 2 ^ (prefixWord ++ tailWord_5390014).sum := by decide
  have hdescent : baseEnd_5390014 < baseStart_5390014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390055 : List Nat := [1, 1, 5, 4, 1, 1, 1, 4, 1, 2, 2]
def baseStart_5390055 : Nat := 118140960795 + 5390055 * 2 ^ 59
def prefixEnd_5390055 : Nat := 4983230072969 + 3 ^ 40 * 5390055 * 2
def baseEnd_5390055 : Nat := 2767688969170014118724095

theorem tailTrace_5390055 : CollatzResearch.WordTrace tailWord_5390055 prefixEnd_5390055 2767688969170014118724095 := by
  unfold tailWord_5390055
  simp only [CollatzResearch.WordTrace]
  refine ⟨196591456487758757950531619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131060970991839171967021079 196591456487758757950531619)
  ·
    refine ⟨294887184731638136925797429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196591456487758757950531619 294887184731638136925797429)
    ·
      refine ⟨27645673568591075336793509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 294887184731638136925797429 27645673568591075336793509)
      ·
        refine ⟨5183563794110826625648783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27645673568591075336793509 5183563794110826625648783)
        ·
          refine ⟨7775345691166239938473175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5183563794110826625648783 7775345691166239938473175)
          ·
            refine ⟨11663018536749359907709763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7775345691166239938473175 11663018536749359907709763)
            ·
              refine ⟨17494527805124039861564645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11663018536749359907709763 17494527805124039861564645)
              ·
                refine ⟨3280223963460757474043371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17494527805124039861564645 3280223963460757474043371)
                ·
                  refine ⟨4920335945191136211065057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3280223963460757474043371 4920335945191136211065057)
                  ·
                    refine ⟨3690251958893352158298793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4920335945191136211065057 3690251958893352158298793)
                    ·
                      refine ⟨2767688969170014118724095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3690251958893352158298793 2767688969170014118724095)
                      ·
                        rfl

theorem cell23_5390055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_5390055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390055 prefixEnd_5390055 := by exact prefixLift 5390055
  have htrace : WordTrace (prefixWord ++ tailWord_5390055) baseStart_5390055 baseEnd_5390055 := by
    simpa [prefixWord, tailWord_5390055, baseEnd_5390055] using wordTrace_append hprefix tailTrace_5390055
  have hstable : (prefixWord ++ tailWord_5390055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390055).length < 2 ^ (prefixWord ++ tailWord_5390055).sum := by decide
  have hdescent : baseEnd_5390055 < baseStart_5390055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390060 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 4]
def baseStart_5390060 : Nat := 118140960795 + 5390060 * 2 ^ 59
def prefixEnd_5390060 : Nat := 4983230072969 + 3 ^ 40 * 5390060 * 2
def baseEnd_5390060 : Nat := 2767691536573286599161571

theorem tailTrace_5390060 : CollatzResearch.WordTrace tailWord_5390060 prefixEnd_5390060 2767691536573286599161571 := by
  unfold tailWord_5390060
  simp only [CollatzResearch.WordTrace]
  refine ⟨98295819426370321902231817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131061092568493762536309089 98295819426370321902231817)
  ·
    refine ⟨73721864569777741426673863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98295819426370321902231817 73721864569777741426673863)
    ·
      refine ⟨110582796854666612140010795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73721864569777741426673863 110582796854666612140010795)
      ·
        refine ⟨165874195281999918210016193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110582796854666612140010795 165874195281999918210016193)
        ·
          refine ⟨124405646461499938657512145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165874195281999918210016193 124405646461499938657512145)
          ·
            refine ⟨93304234846124953993134109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124405646461499938657512145 93304234846124953993134109)
            ·
              refine ⟨34989088067296857747425291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93304234846124953993134109 34989088067296857747425291)
              ·
                refine ⟨52483632100945286621137937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34989088067296857747425291 52483632100945286621137937)
                ·
                  refine ⟨39362724075708964965853453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52483632100945286621137937 39362724075708964965853453)
                  ·
                    refine ⟨14761021528390861862195045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39362724075708964965853453 14761021528390861862195045)
                    ·
                      refine ⟨2767691536573286599161571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14761021528390861862195045 2767691536573286599161571)
                      ·
                        rfl

theorem cell23_5390060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_5390060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390060 prefixEnd_5390060 := by exact prefixLift 5390060
  have htrace : WordTrace (prefixWord ++ tailWord_5390060) baseStart_5390060 baseEnd_5390060 := by
    simpa [prefixWord, tailWord_5390060, baseEnd_5390060] using wordTrace_append hprefix tailTrace_5390060
  have hstable : (prefixWord ++ tailWord_5390060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390060).length < 2 ^ (prefixWord ++ tailWord_5390060).sum := by decide
  have hdescent : baseEnd_5390060 < baseStart_5390060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390094 : List Nat := [4, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2]
def baseStart_5390094 : Nat := 118140960795 + 5390094 * 2 ^ 59
def prefixEnd_5390094 : Nat := 4983230072969 + 3 ^ 40 * 5390094 * 2
def baseEnd_5390094 : Nat := 2767708994915539466136415

theorem tailTrace_5390094 : CollatzResearch.WordTrace tailWord_5390094 prefixEnd_5390094 2767708994915539466136415 := by
  unfold tailWord_5390094
  simp only [CollatzResearch.WordTrace]
  refine ⟨24574109866827183451400167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131061919289744978407467557 24574109866827183451400167)
  ·
    refine ⟨36861164800240775177100251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24574109866827183451400167 36861164800240775177100251)
    ·
      refine ⟨55291747200361162765650377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36861164800240775177100251 55291747200361162765650377)
      ·
        refine ⟨41468810400270872074237783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55291747200361162765650377 41468810400270872074237783)
        ·
          refine ⟨62203215600406308111356675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41468810400270872074237783 62203215600406308111356675)
          ·
            refine ⟨93304823400609462167035013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62203215600406308111356675 93304823400609462167035013)
            ·
              refine ⟨17494654387614274156319065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93304823400609462167035013 17494654387614274156319065)
              ·
                refine ⟨13120990790710705617239299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17494654387614274156319065 13120990790710705617239299)
                ·
                  refine ⟨19681486186066058425858949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13120990790710705617239299 19681486186066058425858949)
                  ·
                    refine ⟨3690278659887385954848553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19681486186066058425858949 3690278659887385954848553)
                    ·
                      refine ⟨2767708994915539466136415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3690278659887385954848553 2767708994915539466136415)
                      ·
                        rfl

theorem cell23_5390094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_5390094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390094 prefixEnd_5390094 := by exact prefixLift 5390094
  have htrace : WordTrace (prefixWord ++ tailWord_5390094) baseStart_5390094 baseEnd_5390094 := by
    simpa [prefixWord, tailWord_5390094, baseEnd_5390094] using wordTrace_append hprefix tailTrace_5390094
  have hstable : (prefixWord ++ tailWord_5390094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390094).length < 2 ^ (prefixWord ++ tailWord_5390094).sum := by decide
  have hdescent : baseEnd_5390094 < baseStart_5390094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390098 : List Nat := [3, 2, 4, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_5390098 : Nat := 118140960795 + 5390098 * 2 ^ 59
def prefixEnd_5390098 : Nat := 4983230072969 + 3 ^ 40 * 5390098 * 2
def baseEnd_5390098 : Nat := 2767711048838157450486397

theorem tailTrace_5390098 : CollatzResearch.WordTrace tailWord_5390098 prefixEnd_5390098 2767711048838157450486397 := by
  unfold tailWord_5390098
  simp only [CollatzResearch.WordTrace]
  refine ⟨49148256206650744073586737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131062016551068650862897965 49148256206650744073586737)
  ·
    refine ⟨36861192154988058055190053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49148256206650744073586737 36861192154988058055190053)
    ·
      refine ⟨6911473529060260885348135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36861192154988058055190053 6911473529060260885348135)
      ·
        refine ⟨10367210293590391328022203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6911473529060260885348135 10367210293590391328022203)
        ·
          refine ⟨15550815440385586992033305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10367210293590391328022203 15550815440385586992033305)
          ·
            refine ⟨11663111580289190244024979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15550815440385586992033305 11663111580289190244024979)
            ·
              refine ⟨17494667370433785366037469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11663111580289190244024979 17494667370433785366037469)
              ·
                refine ⟨6560500263912669512264051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17494667370433785366037469 6560500263912669512264051)
                ·
                  refine ⟨9840750395869004268396077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6560500263912669512264051 9840750395869004268396077)
                  ·
                    refine ⟨3690281398450876600648529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9840750395869004268396077 3690281398450876600648529)
                    ·
                      refine ⟨2767711048838157450486397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3690281398450876600648529 2767711048838157450486397)
                      ·
                        rfl

theorem cell23_5390098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_5390098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390098 prefixEnd_5390098 := by exact prefixLift 5390098
  have htrace : WordTrace (prefixWord ++ tailWord_5390098) baseStart_5390098 baseEnd_5390098 := by
    simpa [prefixWord, tailWord_5390098, baseEnd_5390098] using wordTrace_append hprefix tailTrace_5390098
  have hstable : (prefixWord ++ tailWord_5390098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390098).length < 2 ^ (prefixWord ++ tailWord_5390098).sum := by decide
  have hdescent : baseEnd_5390098 < baseStart_5390098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390117 : List Nat := [1, 3, 1, 2, 3, 3, 2, 1, 7]
def baseStart_5390117 : Nat := 118140960795 + 5390117 * 2 ^ 59
def prefixEnd_5390117 : Nat := 4983230072969 + 3 ^ 40 * 5390117 * 2
def baseEnd_5390117 : Nat := 307524533885621430683201

theorem tailTrace_5390117 : CollatzResearch.WordTrace tailWord_5390117 prefixEnd_5390117 307524533885621430683201 := by
  unfold tailWord_5390117
  simp only [CollatzResearch.WordTrace]
  refine ⟨196593717813534142539288605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131062478542356095026192403 196593717813534142539288605)
  ·
    refine ⟨73722644180075303452233227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196593717813534142539288605 73722644180075303452233227)
    ·
      refine ⟨110583966270112955178349841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73722644180075303452233227 110583966270112955178349841)
      ·
        refine ⟨82937974702584716383762381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110583966270112955178349841 82937974702584716383762381)
        ·
          refine ⟨31101740513469268643910893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82937974702584716383762381 31101740513469268643910893)
          ·
            refine ⟨11663152692550975741466585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31101740513469268643910893 11663152692550975741466585)
            ·
              refine ⟨8747364519413231806099939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11663152692550975741466585 8747364519413231806099939)
              ·
                refine ⟨13121046779119847709149909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8747364519413231806099939 13121046779119847709149909)
                ·
                  refine ⟨307524533885621430683201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13121046779119847709149909 307524533885621430683201)
                  ·
                    rfl

theorem cell23_5390117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 7].length) (baseStart_5390117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390117 prefixEnd_5390117 := by exact prefixLift 5390117
  have htrace : WordTrace (prefixWord ++ tailWord_5390117) baseStart_5390117 baseEnd_5390117 := by
    simpa [prefixWord, tailWord_5390117, baseEnd_5390117] using wordTrace_append hprefix tailTrace_5390117
  have hstable : (prefixWord ++ tailWord_5390117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390117).length < 2 ^ (prefixWord ++ tailWord_5390117).sum := by decide
  have hdescent : baseEnd_5390117 < baseStart_5390117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390134 : List Nat := [5, 1, 2, 2, 1, 1, 2, 2, 7]
def baseStart_5390134 : Nat := 118140960795 + 5390134 * 2 ^ 59
def prefixEnd_5390134 : Nat := 4983230072969 + 3 ^ 40 * 5390134 * 2
def baseEnd_5390134 : Nat := 307525503793524367737359

theorem tailTrace_5390134 : CollatzResearch.WordTrace tailWord_5390134 prefixEnd_5390134 307525503793524367737359 := by
  unfold tailWord_5390134
  simp only [CollatzResearch.WordTrace]
  refine ⟨12287146115904534652666091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131062891902981702961771637 12287146115904534652666091)
  ·
    refine ⟨18430719173856801978999137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12287146115904534652666091 18430719173856801978999137)
    ·
      refine ⟨13823039380392601484249353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18430719173856801978999137 13823039380392601484249353)
      ·
        refine ⟨10367279535294451113187015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13823039380392601484249353 10367279535294451113187015)
        ·
          refine ⟨15550919302941676669780523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10367279535294451113187015 15550919302941676669780523)
          ·
            refine ⟨23326378954412515004670785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15550919302941676669780523 23326378954412515004670785)
            ·
              refine ⟨17494784215809386253503089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23326378954412515004670785 17494784215809386253503089)
              ·
                refine ⟨13121088161857039690127317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17494784215809386253503089 13121088161857039690127317)
                ·
                  refine ⟨307525503793524367737359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13121088161857039690127317 307525503793524367737359)
                  ·
                    rfl

theorem cell23_5390134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_5390134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390134 prefixEnd_5390134 := by exact prefixLift 5390134
  have htrace : WordTrace (prefixWord ++ tailWord_5390134) baseStart_5390134 baseEnd_5390134 := by
    simpa [prefixWord, tailWord_5390134, baseEnd_5390134] using wordTrace_append hprefix tailTrace_5390134
  have hstable : (prefixWord ++ tailWord_5390134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390134).length < 2 ^ (prefixWord ++ tailWord_5390134).sum := by decide
  have hdescent : baseEnd_5390134 < baseStart_5390134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390164 : List Nat := [2, 4, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_5390164 : Nat := 118140960795 + 5390164 * 2 ^ 59
def prefixEnd_5390164 : Nat := 4983230072969 + 3 ^ 40 * 5390164 * 2
def baseEnd_5390164 : Nat := 922581646187118064087031

theorem tailTrace_5390164 : CollatzResearch.WordTrace tailWord_5390164 prefixEnd_5390164 922581646187118064087031 := by
  unfold tailWord_5390164
  simp only [CollatzResearch.WordTrace]
  refine ⟨98297716022181934783124773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131063621362909246377499697 98297716022181934783124773)
  ·
    refine ⟨18430821754159112771835895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98297716022181934783124773 18430821754159112771835895)
    ·
      refine ⟨27646232631238669157753843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18430821754159112771835895 27646232631238669157753843)
      ·
        refine ⟨41469348946858003736630765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27646232631238669157753843 41469348946858003736630765)
        ·
          refine ⟨15551005855071751401236537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41469348946858003736630765 15551005855071751401236537)
          ·
            refine ⟨11663254391303813550927403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15551005855071751401236537 11663254391303813550927403)
            ·
              refine ⟨17494881586955720326391105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11663254391303813550927403 17494881586955720326391105)
              ·
                refine ⟨13121161190216790244793329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17494881586955720326391105 13121161190216790244793329)
                ·
                  refine ⟨9840870892662592683594997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13121161190216790244793329 9840870892662592683594997)
                  ·
                    refine ⟨922581646187118064087031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9840870892662592683594997 922581646187118064087031)
                    ·
                      rfl

theorem cell23_5390164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_5390164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390164 prefixEnd_5390164 := by exact prefixLift 5390164
  have htrace : WordTrace (prefixWord ++ tailWord_5390164) baseStart_5390164 baseEnd_5390164 := by
    simpa [prefixWord, tailWord_5390164, baseEnd_5390164] using wordTrace_append hprefix tailTrace_5390164
  have hstable : (prefixWord ++ tailWord_5390164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390164).length < 2 ^ (prefixWord ++ tailWord_5390164).sum := by decide
  have hdescent : baseEnd_5390164 < baseStart_5390164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390184 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 1, 6, 2]
def baseStart_5390184 : Nat := 118140960795 + 5390184 * 2 ^ 59
def prefixEnd_5390184 : Nat := 4983230072969 + 3 ^ 40 * 5390184 * 2
def baseEnd_5390184 : Nat := 2767755208174444114011001

theorem tailTrace_5390184 : CollatzResearch.WordTrace tailWord_5390184 prefixEnd_5390184 2767755208174444114011001 := by
  unfold tailWord_5390184
  simp only [CollatzResearch.WordTrace]
  refine ⟨98298080752145706490988803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131064107669527608654651737 98298080752145706490988803)
  ·
    refine ⟨147447121128218559736483205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98298080752145706490988803 147447121128218559736483205)
    ·
      refine ⟨27646335211540979950590601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147447121128218559736483205 27646335211540979950590601)
      ·
        refine ⟨20734751408655734962942951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27646335211540979950590601 20734751408655734962942951)
        ·
          refine ⟨31102127112983602444414427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20734751408655734962942951 31102127112983602444414427)
          ·
            refine ⟨46653190669475403666621641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31102127112983602444414427 46653190669475403666621641)
            ·
              refine ⟨34989893002106552749966231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46653190669475403666621641 34989893002106552749966231)
              ·
                refine ⟨52484839503159829124949347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34989893002106552749966231 52484839503159829124949347)
                ·
                  refine ⟨78727259254739743687424021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52484839503159829124949347 78727259254739743687424021)
                  ·
                    refine ⟨3690340277565925485348001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78727259254739743687424021 3690340277565925485348001)
                    ·
                      refine ⟨2767755208174444114011001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3690340277565925485348001 2767755208174444114011001)
                      ·
                        rfl

theorem cell23_5390184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_5390184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390184 prefixEnd_5390184 := by exact prefixLift 5390184
  have htrace : WordTrace (prefixWord ++ tailWord_5390184) baseStart_5390184 baseEnd_5390184 := by
    simpa [prefixWord, tailWord_5390184, baseEnd_5390184] using wordTrace_append hprefix tailTrace_5390184
  have hstable : (prefixWord ++ tailWord_5390184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390184).length < 2 ^ (prefixWord ++ tailWord_5390184).sum := by decide
  have hdescent : baseEnd_5390184 < baseStart_5390184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390187 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 3]
def baseStart_5390187 : Nat := 118140960795 + 5390187 * 2 ^ 59
def prefixEnd_5390187 : Nat := 4983230072969 + 3 ^ 40 * 5390187 * 2
def baseEnd_5390187 : Nat := 2767756748616407602273487

theorem tailTrace_5390187 : CollatzResearch.WordTrace tailWord_5390187 prefixEnd_5390187 2767756748616407602273487 := by
  unfold tailWord_5390187
  simp only [CollatzResearch.WordTrace]
  refine ⟨196596270923280544494336815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131064180615520362996224543 196596270923280544494336815)
  ·
    refine ⟨294894406384920816741505223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196596270923280544494336815 294894406384920816741505223)
    ·
      refine ⟨442341609577381225112257835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294894406384920816741505223 442341609577381225112257835)
      ·
        refine ⟨663512414366071837668386753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442341609577381225112257835 663512414366071837668386753)
        ·
          refine ⟨497634310774553878251290065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 663512414366071837668386753 497634310774553878251290065)
          ·
            refine ⟨373225733080915408688467549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497634310774553878251290065 373225733080915408688467549)
            ·
              refine ⟨139959649905343278258175331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 373225733080915408688467549 139959649905343278258175331)
              ·
                refine ⟨209939474858014917387262997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139959649905343278258175331 209939474858014917387262997)
                ·
                  refine ⟨9840912883969449252527953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 209939474858014917387262997 9840912883969449252527953)
                  ·
                    refine ⟨7380684662977086939395965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9840912883969449252527953 7380684662977086939395965)
                    ·
                      refine ⟨2767756748616407602273487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7380684662977086939395965 2767756748616407602273487)
                      ·
                        rfl

theorem cell23_5390187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 3].length) (baseStart_5390187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390187 prefixEnd_5390187 := by exact prefixLift 5390187
  have htrace : WordTrace (prefixWord ++ tailWord_5390187) baseStart_5390187 baseEnd_5390187 := by
    simpa [prefixWord, tailWord_5390187, baseEnd_5390187] using wordTrace_append hprefix tailTrace_5390187
  have hstable : (prefixWord ++ tailWord_5390187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390187).length < 2 ^ (prefixWord ++ tailWord_5390187).sum := by decide
  have hdescent : baseEnd_5390187 < baseStart_5390187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390228 : List Nat := [2, 4, 2, 1, 1, 3, 1, 4, 1, 4]
def baseStart_5390228 : Nat := 118140960795 + 5390228 * 2 ^ 59
def prefixEnd_5390228 : Nat := 4983230072969 + 3 ^ 40 * 5390228 * 2
def baseEnd_5390228 : Nat := 922592600441080647286933

theorem tailTrace_5390228 : CollatzResearch.WordTrace tailWord_5390228 prefixEnd_5390228 922592600441080647286933 := by
  unfold tailWord_5390228
  simp only [CollatzResearch.WordTrace]
  refine ⟨98298883158066004248289669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131065177544088005664386225 98298883158066004248289669)
  ·
    refine ⟨18431040592137375796554313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98298883158066004248289669 18431040592137375796554313)
    ·
      refine ⟨13823280444103031847415735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18431040592137375796554313 13823280444103031847415735)
      ·
        refine ⟨20734920666154547771123603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13823280444103031847415735 20734920666154547771123603)
        ·
          refine ⟨31102380999231821656685405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20734920666154547771123603 31102380999231821656685405)
          ·
            refine ⟨11663392874711933121257027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31102380999231821656685405 11663392874711933121257027)
            ·
              refine ⟨17495089312067899681885541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11663392874711933121257027 17495089312067899681885541)
              ·
                refine ⟨3280329246012731190353539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17495089312067899681885541 3280329246012731190353539)
                ·
                  refine ⟨4920493869019096785530309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3280329246012731190353539 4920493869019096785530309)
                  ·
                    refine ⟨922592600441080647286933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4920493869019096785530309 922592600441080647286933)
                    ·
                      rfl

theorem cell23_5390228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_5390228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390228 prefixEnd_5390228 := by exact prefixLift 5390228
  have htrace : WordTrace (prefixWord ++ tailWord_5390228) baseStart_5390228 baseEnd_5390228 := by
    simpa [prefixWord, tailWord_5390228, baseEnd_5390228] using wordTrace_append hprefix tailTrace_5390228
  have hstable : (prefixWord ++ tailWord_5390228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390228).length < 2 ^ (prefixWord ++ tailWord_5390228).sum := by decide
  have hdescent : baseEnd_5390228 < baseStart_5390228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390261 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 1, 5, 2]
def baseStart_5390261 : Nat := 118140960795 + 5390261 * 2 ^ 59
def prefixEnd_5390261 : Nat := 4983230072969 + 3 ^ 40 * 5390261 * 2
def baseEnd_5390261 : Nat := 2767794746184840312748147

theorem tailTrace_5390261 : CollatzResearch.WordTrace tailWord_5390261 prefixEnd_5390261 2767794746184840312748147 := by
  unfold tailWord_5390261
  simp only [CollatzResearch.WordTrace]
  refine ⟨196598969925012455132530637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131065979950008303421687091 196598969925012455132530637)
  ·
    refine ⟨73724613721879670674698989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196598969925012455132530637 73724613721879670674698989)
    ·
      refine ⟨27646730145704876503012121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73724613721879670674698989 27646730145704876503012121)
      ·
        refine ⟨20735047609278657377259091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27646730145704876503012121 20735047609278657377259091)
        ·
          refine ⟨31102571413917986065888637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20735047609278657377259091 31102571413917986065888637)
          ·
            refine ⟨11663464280219244774708239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31102571413917986065888637 11663464280219244774708239)
            ·
              refine ⟨17495196420328867162062359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11663464280219244774708239 17495196420328867162062359)
              ·
                refine ⟨26242794630493300743093539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17495196420328867162062359 26242794630493300743093539)
                ·
                  refine ⟨39364191945739951114640309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26242794630493300743093539 39364191945739951114640309)
                  ·
                    refine ⟨3690392994913120416997529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39364191945739951114640309 3690392994913120416997529)
                    ·
                      refine ⟨2767794746184840312748147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3690392994913120416997529 2767794746184840312748147)
                      ·
                        rfl

theorem cell23_5390261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_5390261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390261 prefixEnd_5390261 := by exact prefixLift 5390261
  have htrace : WordTrace (prefixWord ++ tailWord_5390261) baseStart_5390261 baseEnd_5390261 := by
    simpa [prefixWord, tailWord_5390261, baseEnd_5390261] using wordTrace_append hprefix tailTrace_5390261
  have hstable : (prefixWord ++ tailWord_5390261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390261).length < 2 ^ (prefixWord ++ tailWord_5390261).sum := by decide
  have hdescent : baseEnd_5390261 < baseStart_5390261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390287 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 6]
def baseStart_5390287 : Nat := 118140960795 + 5390287 * 2 ^ 59
def prefixEnd_5390287 : Nat := 4983230072969 + 3 ^ 40 * 5390287 * 2
def baseEnd_5390287 : Nat := 2767808096681857211023027

theorem tailTrace_5390287 : CollatzResearch.WordTrace tailWord_5390287 prefixEnd_5390287 2767808096681857211023027 := by
  unfold tailWord_5390287
  simp only [CollatzResearch.WordTrace]
  refine ⟨196599918222918261572977115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131066612148612174381984743 196599918222918261572977115)
  ·
    refine ⟨294899877334377392359465673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196599918222918261572977115 294899877334377392359465673)
    ·
      refine ⟨221174908000783044269599255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294899877334377392359465673 221174908000783044269599255)
      ·
        refine ⟨331762362001174566404398883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221174908000783044269599255 331762362001174566404398883)
        ·
          refine ⟨497643543001761849606598325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331762362001174566404398883 497643543001761849606598325)
          ·
            refine ⟨46654082156415173400618593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 497643543001761849606598325 46654082156415173400618593)
            ·
              refine ⟨34990561617311380050463945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46654082156415173400618593 34990561617311380050463945)
              ·
                refine ⟨26242921212983535037847959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34990561617311380050463945 26242921212983535037847959)
                ·
                  refine ⟨39364381819475302556771939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26242921212983535037847959 39364381819475302556771939)
                  ·
                    refine ⟨59046572729212953835157909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39364381819475302556771939 59046572729212953835157909)
                    ·
                      refine ⟨2767808096681857211023027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59046572729212953835157909 2767808096681857211023027)
                      ·
                        rfl

theorem cell23_5390287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_5390287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390287 prefixEnd_5390287 := by exact prefixLift 5390287
  have htrace : WordTrace (prefixWord ++ tailWord_5390287) baseStart_5390287 baseEnd_5390287 := by
    simpa [prefixWord, tailWord_5390287, baseEnd_5390287] using wordTrace_append hprefix tailTrace_5390287
  have hstable : (prefixWord ++ tailWord_5390287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390287).length < 2 ^ (prefixWord ++ tailWord_5390287).sum := by decide
  have hdescent : baseEnd_5390287 < baseStart_5390287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390341 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 4, 1, 3]
def baseStart_5390341 : Nat := 118140960795 + 5390341 * 2 ^ 59
def prefixEnd_5390341 : Nat := 4983230072969 + 3 ^ 40 * 5390341 * 2
def baseEnd_5390341 : Nat := 2767835824637199999747779

theorem tailTrace_5390341 : CollatzResearch.WordTrace tailWord_5390341 prefixEnd_5390341 2767835824637199999747779 := by
  unfold tailWord_5390341
  simp only [CollatzResearch.WordTrace]
  refine ⟨196601887764722628795442877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131067925176481752530295251 196601887764722628795442877)
  ·
    refine ⟨73725707911770985798291079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196601887764722628795442877 73725707911770985798291079)
    ·
      refine ⟨110588561867656478697436619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73725707911770985798291079 110588561867656478697436619)
      ·
        refine ⟨165882842801484718046154929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110588561867656478697436619 165882842801484718046154929)
        ·
          refine ⟨124412132101113538534616197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165882842801484718046154929 124412132101113538534616197)
          ·
            refine ⟨23327274768958788475240537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124412132101113538534616197 23327274768958788475240537)
            ·
              refine ⟨17495456076719091356430403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23327274768958788475240537 17495456076719091356430403)
              ·
                refine ⟨26243184115078637034645605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17495456076719091356430403 26243184115078637034645605)
                ·
                  refine ⟨4920597021577244443996051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26243184115078637034645605 4920597021577244443996051)
                  ·
                    refine ⟨7380895532365866665994077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4920597021577244443996051 7380895532365866665994077)
                    ·
                      refine ⟨2767835824637199999747779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7380895532365866665994077 2767835824637199999747779)
                      ·
                        rfl

theorem cell23_5390341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 1, 3].length) (baseStart_5390341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390341 prefixEnd_5390341 := by exact prefixLift 5390341
  have htrace : WordTrace (prefixWord ++ tailWord_5390341) baseStart_5390341 baseEnd_5390341 := by
    simpa [prefixWord, tailWord_5390341, baseEnd_5390341] using wordTrace_append hprefix tailTrace_5390341
  have hstable : (prefixWord ++ tailWord_5390341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390341).length < 2 ^ (prefixWord ++ tailWord_5390341).sum := by decide
  have hdescent : baseEnd_5390341 < baseStart_5390341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390377 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 3, 5, 6]
def baseStart_5390377 : Nat := 118140960795 + 5390377 * 2 ^ 59
def prefixEnd_5390377 : Nat := 4983230072969 + 3 ^ 40 * 5390377 * 2
def baseEnd_5390377 : Nat := 2767854309940761858897613

theorem tailTrace_5390377 : CollatzResearch.WordTrace tailWord_5390377 prefixEnd_5390377 2767854309940761858897613 := by
  unfold tailWord_5390377
  simp only [CollatzResearch.WordTrace]
  refine ⟨196603200792592206943753385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131068800528394804629168923 196603200792592206943753385)
  ·
    refine ⟨147452400594444155207815039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196603200792592206943753385 147452400594444155207815039)
    ·
      refine ⟨221178600891666232811722559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147452400594444155207815039 221178600891666232811722559)
      ·
        refine ⟨331767901337499349217583839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221178600891666232811722559 331767901337499349217583839)
        ·
          refine ⟨497651852006249023826375759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331767901337499349217583839 497651852006249023826375759)
          ·
            refine ⟨746477778009373535739563639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497651852006249023826375759 746477778009373535739563639)
            ·
              refine ⟨1119716667014060303609345459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 746477778009373535739563639 1119716667014060303609345459)
              ·
                refine ⟨1679575000521090455414018189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1119716667014060303609345459 1679575000521090455414018189)
                ·
                  refine ⟨629840625195408920780256821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1679575000521090455414018189 629840625195408920780256821)
                  ·
                    refine ⟨59047558612069586323149077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 629840625195408920780256821 59047558612069586323149077)
                    ·
                      refine ⟨2767854309940761858897613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59047558612069586323149077 2767854309940761858897613)
                      ·
                        rfl

theorem cell23_5390377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_5390377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390377 prefixEnd_5390377 := by exact prefixLift 5390377
  have htrace : WordTrace (prefixWord ++ tailWord_5390377) baseStart_5390377 baseEnd_5390377 := by
    simpa [prefixWord, tailWord_5390377, baseEnd_5390377] using wordTrace_append hprefix tailTrace_5390377
  have hstable : (prefixWord ++ tailWord_5390377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390377).length < 2 ^ (prefixWord ++ tailWord_5390377).sum := by decide
  have hdescent : baseEnd_5390377 < baseStart_5390377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390384 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 5]
def baseStart_5390384 : Nat := 118140960795 + 5390384 * 2 ^ 59
def prefixEnd_5390384 : Nat := 4983230072969 + 3 ^ 40 * 5390384 * 2
def baseEnd_5390384 : Nat := 2767857904305343331510081

theorem tailTrace_5390384 : CollatzResearch.WordTrace tailWord_5390384 prefixEnd_5390384 2767857904305343331510081 := by
  unfold tailWord_5390384
  simp only [CollatzResearch.WordTrace]
  refine ⟨98301728051783423569629103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131068970735711231426172137 98301728051783423569629103)
  ·
    refine ⟨147452592077675135354443655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98301728051783423569629103 147452592077675135354443655)
    ·
      refine ⟨221178888116512703031665483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147452592077675135354443655 221178888116512703031665483)
      ·
        refine ⟨331768332174769054547498225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221178888116512703031665483 331768332174769054547498225)
        ·
          refine ⟨248826249131076790910623669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331768332174769054547498225 248826249131076790910623669)
          ·
            refine ⟨23327460856038449147870969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 248826249131076790910623669 23327460856038449147870969)
            ·
              refine ⟨17495595642028836860903227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23327460856038449147870969 17495595642028836860903227)
              ·
                refine ⟨26243393463043255291354841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17495595642028836860903227 26243393463043255291354841)
                ·
                  refine ⟨19682545097282441468516131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26243393463043255291354841 19682545097282441468516131)
                  ·
                    refine ⟨29523817645923662202774197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19682545097282441468516131 29523817645923662202774197)
                    ·
                      refine ⟨2767857904305343331510081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29523817645923662202774197 2767857904305343331510081)
                      ·
                        rfl

theorem cell23_5390384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 5].length) (baseStart_5390384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390384 prefixEnd_5390384 := by exact prefixLift 5390384
  have htrace : WordTrace (prefixWord ++ tailWord_5390384) baseStart_5390384 baseEnd_5390384 := by
    simpa [prefixWord, tailWord_5390384, baseEnd_5390384] using wordTrace_append hprefix tailTrace_5390384
  have hstable : (prefixWord ++ tailWord_5390384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390384).length < 2 ^ (prefixWord ++ tailWord_5390384).sum := by decide
  have hdescent : baseEnd_5390384 < baseStart_5390384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390385 : List Nat := [1, 2, 2, 3, 1, 4, 3, 1, 1, 3, 2]
def baseStart_5390385 : Nat := 118140960795 + 5390385 * 2 ^ 59
def prefixEnd_5390385 : Nat := 4983230072969 + 3 ^ 40 * 5390385 * 2
def baseEnd_5390385 : Nat := 2767858417785997827597577

theorem tailTrace_5390385 : CollatzResearch.WordTrace tailWord_5390385 prefixEnd_5390385 2767858417785997827597577 := by
  unfold tailWord_5390385
  simp only [CollatzResearch.WordTrace]
  refine ⟨196603492576563224310044609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131068995051042149540029739 196603492576563224310044609)
  ·
    refine ⟨147452619432422418232533457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196603492576563224310044609 147452619432422418232533457)
    ·
      refine ⟨110589464574316813674400093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147452619432422418232533457 110589464574316813674400093)
      ·
        refine ⟨41471049215368805127900035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110589464574316813674400093 41471049215368805127900035)
        ·
          refine ⟨62206573823053207691850053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41471049215368805127900035 62206573823053207691850053)
          ·
            refine ⟨11663732591822476442221885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62206573823053207691850053 11663732591822476442221885)
            ·
              refine ⟨4373899721933428665833207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11663732591822476442221885 4373899721933428665833207)
              ·
                refine ⟨6560849582900142998749811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4373899721933428665833207 6560849582900142998749811)
                ·
                  refine ⟨9841274374350214498124717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6560849582900142998749811 9841274374350214498124717)
                  ·
                    refine ⟨3690477890381330436796769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9841274374350214498124717 3690477890381330436796769)
                    ·
                      refine ⟨2767858417785997827597577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3690477890381330436796769 2767858417785997827597577)
                      ·
                        rfl

theorem cell23_5390385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_5390385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390385 prefixEnd_5390385 := by exact prefixLift 5390385
  have htrace : WordTrace (prefixWord ++ tailWord_5390385) baseStart_5390385 baseEnd_5390385 := by
    simpa [prefixWord, tailWord_5390385, baseEnd_5390385] using wordTrace_append hprefix tailTrace_5390385
  have hstable : (prefixWord ++ tailWord_5390385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390385).length < 2 ^ (prefixWord ++ tailWord_5390385).sum := by decide
  have hdescent : baseEnd_5390385 < baseStart_5390385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390394 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4]
def baseStart_5390394 : Nat := 118140960795 + 5390394 * 2 ^ 59
def prefixEnd_5390394 : Nat := 4983230072969 + 3 ^ 40 * 5390394 * 2
def baseEnd_5390394 : Nat := 2767863039111888292385035

theorem tailTrace_5390394 : CollatzResearch.WordTrace tailWord_5390394 prefixEnd_5390394 2767863039111888292385035 := by
  unfold tailWord_5390394
  simp only [CollatzResearch.WordTrace]
  refine ⟨49150955208382654711780559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131069213889020412564748157 49150955208382654711780559)
  ·
    refine ⟨73726432812573982067670839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49150955208382654711780559 73726432812573982067670839)
    ·
      refine ⟨110589649218860973101506259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73726432812573982067670839 110589649218860973101506259)
      ·
        refine ⟨165884473828291459652259389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110589649218860973101506259 165884473828291459652259389)
        ·
          refine ⟨62206677685609297369597271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165884473828291459652259389 62206677685609297369597271)
          ·
            refine ⟨93310016528413946054395907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62206677685609297369597271 93310016528413946054395907)
            ·
              refine ⟨139965024792620919081593861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93310016528413946054395907 139965024792620919081593861)
              ·
                refine ⟨26243442148616422327798849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139965024792620919081593861 26243442148616422327798849)
                ·
                  refine ⟨19682581611462316745849137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26243442148616422327798849 19682581611462316745849137)
                  ·
                    refine ⟨14761936208596737559386853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19682581611462316745849137 14761936208596737559386853)
                    ·
                      refine ⟨2767863039111888292385035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14761936208596737559386853 2767863039111888292385035)
                      ·
                        rfl

theorem cell23_5390394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_5390394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390394 prefixEnd_5390394 := by exact prefixLift 5390394
  have htrace : WordTrace (prefixWord ++ tailWord_5390394) baseStart_5390394 baseEnd_5390394 := by
    simpa [prefixWord, tailWord_5390394, baseEnd_5390394] using wordTrace_append hprefix tailTrace_5390394
  have hstable : (prefixWord ++ tailWord_5390394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390394).length < 2 ^ (prefixWord ++ tailWord_5390394).sum := by decide
  have hdescent : baseEnd_5390394 < baseStart_5390394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390401 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_5390401 : Nat := 118140960795 + 5390401 * 2 ^ 59
def prefixEnd_5390401 : Nat := 4983230072969 + 3 ^ 40 * 5390401 * 2
def baseEnd_5390401 : Nat := 2767866633476469764997503

theorem tailTrace_5390401 : CollatzResearch.WordTrace tailWord_5390401 prefixEnd_5390401 2767866633476469764997503 := by
  unfold tailWord_5390401
  simp only [CollatzResearch.WordTrace]
  refine ⟨196604076144505259042627057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131069384096336839361751371 196604076144505259042627057)
  ·
    refine ⟨147453057108378944281970293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196604076144505259042627057 147453057108378944281970293)
    ·
      refine ⟨13823724103910526026434715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147453057108378944281970293 13823724103910526026434715)
      ·
        refine ⟨20735586155865789039652073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13823724103910526026434715 20735586155865789039652073)
        ·
          refine ⟨15551689616899341779739055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20735586155865789039652073 15551689616899341779739055)
          ·
            refine ⟨23327534425349012669608583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15551689616899341779739055 23327534425349012669608583)
            ·
              refine ⟨34991301638023519004412875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23327534425349012669608583 34991301638023519004412875)
              ·
                refine ⟨52486952457035278506619313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34991301638023519004412875 52486952457035278506619313)
                ·
                  refine ⟨39365214342776458879964485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52486952457035278506619313 39365214342776458879964485)
                  ·
                    refine ⟨7380977689270586039993341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39365214342776458879964485 7380977689270586039993341)
                    ·
                      refine ⟨2767866633476469764997503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7380977689270586039993341 2767866633476469764997503)
                      ·
                        rfl

theorem cell23_5390401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_5390401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390401 prefixEnd_5390401 := by exact prefixLift 5390401
  have htrace : WordTrace (prefixWord ++ tailWord_5390401) baseStart_5390401 baseEnd_5390401 := by
    simpa [prefixWord, tailWord_5390401, baseEnd_5390401] using wordTrace_append hprefix tailTrace_5390401
  have hstable : (prefixWord ++ tailWord_5390401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390401).length < 2 ^ (prefixWord ++ tailWord_5390401).sum := by decide
  have hdescent : baseEnd_5390401 < baseStart_5390401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390528 : List Nat := [2, 1, 1, 2, 5, 1, 4, 1, 6]
def baseStart_5390528 : Nat := 118140960795 + 5390528 * 2 ^ 59
def prefixEnd_5390528 : Nat := 4983230072969 + 3 ^ 40 * 5390528 * 2
def baseEnd_5390528 : Nat := 307547982835510085345491

theorem tailTrace_5390528 : CollatzResearch.WordTrace tailWord_5390528 prefixEnd_5390528 307547982835510085345491 := by
  unfold tailWord_5390528
  simp only [CollatzResearch.WordTrace]
  refine ⟨98304354107522579866250119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131072472143363439821666825 98304354107522579866250119)
  ·
    refine ⟨147456531161283869799375179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98304354107522579866250119 147456531161283869799375179)
    ·
      refine ⟨221184796741925804699062769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147456531161283869799375179 221184796741925804699062769)
      ·
        refine ⟨165888597556444353524297077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221184796741925804699062769 165888597556444353524297077)
        ·
          refine ⟨15552056020916658142902851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 165888597556444353524297077 15552056020916658142902851)
          ·
            refine ⟨23328084031374987214354277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15552056020916658142902851 23328084031374987214354277)
            ·
              refine ⟨4374015755882810102691427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23328084031374987214354277 4374015755882810102691427)
              ·
                refine ⟨6561023633824215154037141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4374015755882810102691427 6561023633824215154037141)
                ·
                  refine ⟨307547982835510085345491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6561023633824215154037141 307547982835510085345491)
                  ·
                    rfl

theorem cell23_5390528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 6].length) (baseStart_5390528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390528 prefixEnd_5390528 := by exact prefixLift 5390528
  have htrace : WordTrace (prefixWord ++ tailWord_5390528) baseStart_5390528 baseEnd_5390528 := by
    simpa [prefixWord, tailWord_5390528, baseEnd_5390528] using wordTrace_append hprefix tailTrace_5390528
  have hstable : (prefixWord ++ tailWord_5390528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390528).length < 2 ^ (prefixWord ++ tailWord_5390528).sum := by decide
  have hdescent : baseEnd_5390528 < baseStart_5390528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390538 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 5, 1, 3]
def baseStart_5390538 : Nat := 118140960795 + 5390538 * 2 ^ 59
def prefixEnd_5390538 : Nat := 4983230072969 + 3 ^ 40 * 5390538 * 2
def baseEnd_5390538 : Nat := 2767936980326135728984373

theorem tailTrace_5390538 : CollatzResearch.WordTrace tailWord_5390538 prefixEnd_5390538 2767936980326135728984373 := by
  unfold tailWord_5390538
  simp only [CollatzResearch.WordTrace]
  refine ⟨49152268236252232860091067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131072715296672620960242845 49152268236252232860091067)
  ·
    refine ⟨73728402354378349290136601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49152268236252232860091067 73728402354378349290136601)
    ·
      refine ⟨55296301765783761967602451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73728402354378349290136601 55296301765783761967602451)
      ·
        refine ⟨82944452648675642951403677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55296301765783761967602451 82944452648675642951403677)
        ·
          refine ⟨31104169743253366106776379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82944452648675642951403677 31104169743253366106776379)
          ·
            refine ⟨46656254614880049160164569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31104169743253366106776379 46656254614880049160164569)
            ·
              refine ⟨34992190961160036870123427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46656254614880049160164569 34992190961160036870123427)
              ·
                refine ⟨52488286441740055305185141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34992190961160036870123427 52488286441740055305185141)
                ·
                  refine ⟨4920776853913130184861107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52488286441740055305185141 4920776853913130184861107)
                  ·
                    refine ⟨7381165280869695277291661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4920776853913130184861107 7381165280869695277291661)
                    ·
                      refine ⟨2767936980326135728984373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7381165280869695277291661 2767936980326135728984373)
                      ·
                        rfl

theorem cell23_5390538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_5390538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390538 prefixEnd_5390538 := by exact prefixLift 5390538
  have htrace : WordTrace (prefixWord ++ tailWord_5390538) baseStart_5390538 baseEnd_5390538 := by
    simpa [prefixWord, tailWord_5390538, baseEnd_5390538] using wordTrace_append hprefix tailTrace_5390538
  have hstable : (prefixWord ++ tailWord_5390538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390538).length < 2 ^ (prefixWord ++ tailWord_5390538).sum := by decide
  have hdescent : baseEnd_5390538 < baseStart_5390538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390565 : List Nat := [1, 3, 1, 4, 2, 1, 2, 2, 2, 3, 2]
def baseStart_5390565 : Nat := 118140960795 + 5390565 * 2 ^ 59
def prefixEnd_5390565 : Nat := 4983230072969 + 3 ^ 40 * 5390565 * 2
def baseEnd_5390565 : Nat := 2767950844303807123346749

theorem tailTrace_5390565 : CollatzResearch.WordTrace tailWord_5390565 prefixEnd_5390565 2767950844303807123346749 := by
  unfold tailWord_5390565
  simp only [CollatzResearch.WordTrace]
  refine ⟨196610057715911115051597149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131073371810607410034398099 196610057715911115051597149)
  ·
    refine ⟨73728771643466668144348931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196610057715911115051597149 73728771643466668144348931)
    ·
      refine ⟨110593157465200002216523397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73728771643466668144348931 110593157465200002216523397)
      ·
        refine ⟨20736217024725000415598137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110593157465200002216523397 20736217024725000415598137)
        ·
          refine ⟨15552162768543750311698603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20736217024725000415598137 15552162768543750311698603)
          ·
            refine ⟨23328244152815625467547905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15552162768543750311698603 23328244152815625467547905)
            ·
              refine ⟨17496183114611719100660929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23328244152815625467547905 17496183114611719100660929)
              ·
                refine ⟨13122137335958789325495697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17496183114611719100660929 13122137335958789325495697)
                ·
                  refine ⟨9841603001969091994121773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13122137335958789325495697 9841603001969091994121773)
                  ·
                    refine ⟨3690601125738409497795665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9841603001969091994121773 3690601125738409497795665)
                    ·
                      refine ⟨2767950844303807123346749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3690601125738409497795665 2767950844303807123346749)
                      ·
                        rfl

theorem cell23_5390565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_5390565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390565 prefixEnd_5390565 := by exact prefixLift 5390565
  have htrace : WordTrace (prefixWord ++ tailWord_5390565) baseStart_5390565 baseEnd_5390565 := by
    simpa [prefixWord, tailWord_5390565, baseEnd_5390565] using wordTrace_append hprefix tailTrace_5390565
  have hstable : (prefixWord ++ tailWord_5390565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390565).length < 2 ^ (prefixWord ++ tailWord_5390565).sum := by decide
  have hdescent : baseEnd_5390565 < baseStart_5390565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390578 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 3, 1, 4]
def baseStart_5390578 : Nat := 118140960795 + 5390578 * 2 ^ 59
def prefixEnd_5390578 : Nat := 4983230072969 + 3 ^ 40 * 5390578 * 2
def baseEnd_5390578 : Nat := 2767957519552315572484189

theorem tailTrace_5390578 : CollatzResearch.WordTrace tailWord_5390578 prefixEnd_5390578 2767957519552315572484189 := by
  unfold tailWord_5390578
  simp only [CollatzResearch.WordTrace]
  refine ⟨49152632966216004567955097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131073687909909345514546925 49152632966216004567955097)
  ·
    refine ⟨36864474724662003425966323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49152632966216004567955097 36864474724662003425966323)
    ·
      refine ⟨55296712086993005138949485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36864474724662003425966323 55296712086993005138949485)
      ·
        refine ⟨20736267032622376927106057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55296712086993005138949485 20736267032622376927106057)
        ·
          refine ⟨15552200274466782695329543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20736267032622376927106057 15552200274466782695329543)
          ·
            refine ⟨23328300411700174042994315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15552200274466782695329543 23328300411700174042994315)
            ·
              refine ⟨34992450617550261064491473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23328300411700174042994315 34992450617550261064491473)
              ·
                refine ⟨26244337963162695798368605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34992450617550261064491473 26244337963162695798368605)
                ·
                  refine ⟨9841626736186010924388227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26244337963162695798368605 9841626736186010924388227)
                  ·
                    refine ⟨14762440104279016386582341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9841626736186010924388227 14762440104279016386582341)
                    ·
                      refine ⟨2767957519552315572484189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14762440104279016386582341 2767957519552315572484189)
                      ·
                        rfl

theorem cell23_5390578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_5390578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390578 prefixEnd_5390578 := by exact prefixLift 5390578
  have htrace : WordTrace (prefixWord ++ tailWord_5390578) baseStart_5390578 baseEnd_5390578 := by
    simpa [prefixWord, tailWord_5390578, baseEnd_5390578] using wordTrace_append hprefix tailTrace_5390578
  have hstable : (prefixWord ++ tailWord_5390578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390578).length < 2 ^ (prefixWord ++ tailWord_5390578).sum := by decide
  have hdescent : baseEnd_5390578 < baseStart_5390578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390588 : List Nat := [2, 2, 2, 1, 4, 2, 2, 1, 1, 6]
def baseStart_5390588 : Nat := 118140960795 + 5390588 * 2 ^ 59
def prefixEnd_5390588 : Nat := 4983230072969 + 3 ^ 40 * 5390588 * 2
def baseEnd_5390588 : Nat := 922654218119620177786381

theorem tailTrace_5390588 : CollatzResearch.WordTrace tailWord_5390588 prefixEnd_5390588 922654218119620177786381 := by
  unfold tailWord_5390588
  simp only [CollatzResearch.WordTrace]
  refine ⟨98305448297413894989842209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131073931063218526653122945 98305448297413894989842209)
  ·
    refine ⟨73729086223060421242381657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98305448297413894989842209 73729086223060421242381657)
    ·
      refine ⟨55296814667295315931786243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73729086223060421242381657 55296814667295315931786243)
      ·
        refine ⟨82945222000942973897679365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55296814667295315931786243 82945222000942973897679365)
        ·
          refine ⟨15552229125176807605814881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82945222000942973897679365 15552229125176807605814881)
          ·
            refine ⟨11664171843882605704361161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15552229125176807605814881 11664171843882605704361161)
            ·
              refine ⟨8748128882911954278270871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11664171843882605704361161 8748128882911954278270871)
              ·
                refine ⟨13122193324367931417406307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8748128882911954278270871 13122193324367931417406307)
                ·
                  refine ⟨19683289986551897126109461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13122193324367931417406307 19683289986551897126109461)
                  ·
                    refine ⟨922654218119620177786381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19683289986551897126109461 922654218119620177786381)
                    ·
                      rfl

theorem cell23_5390588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_5390588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390588 prefixEnd_5390588 := by exact prefixLift 5390588
  have htrace : WordTrace (prefixWord ++ tailWord_5390588) baseStart_5390588 baseEnd_5390588 := by
    simpa [prefixWord, tailWord_5390588, baseEnd_5390588] using wordTrace_append hprefix tailTrace_5390588
  have hstable : (prefixWord ++ tailWord_5390588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390588).length < 2 ^ (prefixWord ++ tailWord_5390588).sum := by decide
  have hdescent : baseEnd_5390588 < baseStart_5390588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390595 : List Nat := [1, 1, 1, 3, 2, 3, 3, 2, 3, 2, 2]
def baseStart_5390595 : Nat := 118140960795 + 5390595 * 2 ^ 59
def prefixEnd_5390595 : Nat := 4983230072969 + 3 ^ 40 * 5390595 * 2
def baseEnd_5390595 : Nat := 2767966248723442005971611

theorem tailTrace_5390595 : CollatzResearch.WordTrace tailWord_5390595 prefixEnd_5390595 2767966248723442005971611 := by
  unfold tailWord_5390595
  simp only [CollatzResearch.WordTrace]
  refine ⟨196611151905802430175189239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131074101270534953450126159 196611151905802430175189239)
  ·
    refine ⟨294916727858703645262783859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196611151905802430175189239 294916727858703645262783859)
    ·
      refine ⟨442375091788055467894175789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294916727858703645262783859 442375091788055467894175789)
      ·
        refine ⟨165890659420520800460315921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 442375091788055467894175789 165890659420520800460315921)
        ·
          refine ⟨124417994565390600345236941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165890659420520800460315921 124417994565390600345236941)
          ·
            refine ⟨46656747962021475129463853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124417994565390600345236941 46656747962021475129463853)
            ·
              refine ⟨17496280485758053173548945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46656747962021475129463853 17496280485758053173548945)
              ·
                refine ⟨13122210364318539880161709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17496280485758053173548945 13122210364318539880161709)
                ·
                  refine ⟨4920828886619452455060641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13122210364318539880161709 4920828886619452455060641)
                  ·
                    refine ⟨3690621664964589341295481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4920828886619452455060641 3690621664964589341295481)
                    ·
                      refine ⟨2767966248723442005971611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3690621664964589341295481 2767966248723442005971611)
                      ·
                        rfl

theorem cell23_5390595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 2, 2].length) (baseStart_5390595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390595 prefixEnd_5390595 := by exact prefixLift 5390595
  have htrace : WordTrace (prefixWord ++ tailWord_5390595) baseStart_5390595 baseEnd_5390595 := by
    simpa [prefixWord, tailWord_5390595, baseEnd_5390595] using wordTrace_append hprefix tailTrace_5390595
  have hstable : (prefixWord ++ tailWord_5390595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390595).length < 2 ^ (prefixWord ++ tailWord_5390595).sum := by decide
  have hdescent : baseEnd_5390595 < baseStart_5390595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390599 : List Nat := [1, 1, 4, 5, 1, 2, 1, 1, 2, 3, 2]
def baseStart_5390599 : Nat := 118140960795 + 5390599 * 2 ^ 59
def prefixEnd_5390599 : Nat := 4983230072969 + 3 ^ 40 * 5390599 * 2
def baseEnd_5390599 : Nat := 2767968302646059990321593

theorem tailTrace_5390599 : CollatzResearch.WordTrace tailWord_5390599 prefixEnd_5390599 2767968302646059990321593 := by
  unfold tailWord_5390599
  simp only [CollatzResearch.WordTrace]
  refine ⟨196611297797787938858334851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131074198531858625905556567 196611297797787938858334851)
  ·
    refine ⟨294916946696681908287502277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196611297797787938858334851 294916946696681908287502277)
    ·
      refine ⟨55296927505627857803906677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 294916946696681908287502277 55296927505627857803906677)
      ·
        refine ⟨5184086953652611669116251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55296927505627857803906677 5184086953652611669116251)
        ·
          refine ⟨7776130430478917503674377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5184086953652611669116251 7776130430478917503674377)
          ·
            refine ⟨5832097822859188127755783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7776130430478917503674377 5832097822859188127755783)
            ·
              refine ⟨8748146734288782191633675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5832097822859188127755783 8748146734288782191633675)
              ·
                refine ⟨13122220101433173287450513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8748146734288782191633675 13122220101433173287450513)
                ·
                  refine ⟨9841665076074879965587885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13122220101433173287450513 9841665076074879965587885)
                  ·
                    refine ⟨3690624403528079987095457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9841665076074879965587885 3690624403528079987095457)
                    ·
                      refine ⟨2767968302646059990321593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3690624403528079987095457 2767968302646059990321593)
                      ·
                        rfl

theorem cell23_5390599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_5390599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390599 prefixEnd_5390599 := by exact prefixLift 5390599
  have htrace : WordTrace (prefixWord ++ tailWord_5390599) baseStart_5390599 baseEnd_5390599 := by
    simpa [prefixWord, tailWord_5390599, baseEnd_5390599] using wordTrace_append hprefix tailTrace_5390599
  have hstable : (prefixWord ++ tailWord_5390599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390599).length < 2 ^ (prefixWord ++ tailWord_5390599).sum := by decide
  have hdescent : baseEnd_5390599 < baseStart_5390599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390615 : List Nat := [1, 1, 3, 4, 1, 3, 1, 3, 1, 2, 3]
def baseStart_5390615 : Nat := 118140960795 + 5390615 * 2 ^ 59
def prefixEnd_5390615 : Nat := 4983230072969 + 3 ^ 40 * 5390615 * 2
def baseEnd_5390615 : Nat := 2767976518336531927721519

theorem tailTrace_5390615 : CollatzResearch.WordTrace tailWord_5390615 prefixEnd_5390615 2767976518336531927721519 := by
  unfold tailWord_5390615
  simp only [CollatzResearch.WordTrace]
  refine ⟨196611881365729973590917299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131074587577153315727278199 196611881365729973590917299)
  ·
    refine ⟨294917822048594960386375949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196611881365729973590917299 294917822048594960386375949)
    ·
      refine ⟨110594183268223110144890981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294917822048594960386375949 110594183268223110144890981)
      ·
        refine ⟨20736409362791833152167059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110594183268223110144890981 20736409362791833152167059)
        ·
          refine ⟨31104614044187749728250589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20736409362791833152167059 31104614044187749728250589)
          ·
            refine ⟨11664230266570406148093971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31104614044187749728250589 11664230266570406148093971)
            ·
              refine ⟨17496345399855609222140957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11664230266570406148093971 17496345399855609222140957)
              ·
                refine ⟨6561129524945853458302859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17496345399855609222140957 6561129524945853458302859)
                ·
                  refine ⟨9841694287418780187454289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6561129524945853458302859 9841694287418780187454289)
                  ·
                    refine ⟨7381270715564085140590717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9841694287418780187454289 7381270715564085140590717)
                    ·
                      refine ⟨2767976518336531927721519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7381270715564085140590717 2767976518336531927721519)
                      ·
                        rfl

theorem cell23_5390615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_5390615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390615 prefixEnd_5390615 := by exact prefixLift 5390615
  have htrace : WordTrace (prefixWord ++ tailWord_5390615) baseStart_5390615 baseEnd_5390615 := by
    simpa [prefixWord, tailWord_5390615, baseEnd_5390615] using wordTrace_append hprefix tailTrace_5390615
  have hstable : (prefixWord ++ tailWord_5390615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390615).length < 2 ^ (prefixWord ++ tailWord_5390615).sum := by decide
  have hdescent : baseEnd_5390615 < baseStart_5390615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390622 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_5390622 : Nat := 118140960795 + 5390622 * 2 ^ 59
def prefixEnd_5390622 : Nat := 4983230072969 + 3 ^ 40 * 5390622 * 2
def baseEnd_5390622 : Nat := 922660037567037800111329

theorem tailTrace_5390622 : CollatzResearch.WordTrace tailWord_5390622 prefixEnd_5390622 922660037567037800111329 := by
  unfold tailWord_5390622
  simp only [CollatzResearch.WordTrace]
  refine ⟨24576517084588076723302765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131074757784469742524281413 24576517084588076723302765)
  ·
    refine ⟨9216193906720528771238537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24576517084588076723302765 9216193906720528771238537)
    ·
      refine ⟨6912145430040396578428903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9216193906720528771238537 6912145430040396578428903)
      ·
        refine ⟨10368218145060594867643355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6912145430040396578428903 10368218145060594867643355)
        ·
          refine ⟨15552327217590892301465033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10368218145060594867643355 15552327217590892301465033)
          ·
            refine ⟨11664245413193169226098775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15552327217590892301465033 11664245413193169226098775)
            ·
              refine ⟨17496368119789753839148163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11664245413193169226098775 17496368119789753839148163)
              ·
                refine ⟨26244552179684630758722245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17496368119789753839148163 26244552179684630758722245)
                ·
                  refine ⟨4920853533690868267260421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26244552179684630758722245 4920853533690868267260421)
                  ·
                    refine ⟨922660037567037800111329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4920853533690868267260421 922660037567037800111329)
                    ·
                      rfl

theorem cell23_5390622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_5390622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390622 prefixEnd_5390622 := by exact prefixLift 5390622
  have htrace : WordTrace (prefixWord ++ tailWord_5390622) baseStart_5390622 baseEnd_5390622 := by
    simpa [prefixWord, tailWord_5390622, baseEnd_5390622] using wordTrace_append hprefix tailTrace_5390622
  have hstable : (prefixWord ++ tailWord_5390622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390622).length < 2 ^ (prefixWord ++ tailWord_5390622).sum := by decide
  have hdescent : baseEnd_5390622 < baseStart_5390622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390642 : List Nat := [3, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4]
def baseStart_5390642 : Nat := 118140960795 + 5390642 * 2 ^ 59
def prefixEnd_5390642 : Nat := 4983230072969 + 3 ^ 40 * 5390642 * 2
def baseEnd_5390642 : Nat := 2767990382314203322083895

theorem tailTrace_5390642 : CollatzResearch.WordTrace tailWord_5390642 prefixEnd_5390642 2767990382314203322083895 := by
  unfold tailWord_5390642
  simp only [CollatzResearch.WordTrace]
  refine ⟨49153216534158039300537545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131075244091088104801433453 49153216534158039300537545)
  ·
    refine ⟨36864912400618529475403159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49153216534158039300537545 36864912400618529475403159)
    ·
      refine ⟨55297368600927794213104739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36864912400618529475403159 55297368600927794213104739)
      ·
        refine ⟨82946052901391691319657109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55297368600927794213104739 82946052901391691319657109)
        ·
          refine ⟨3888096229752735530608927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82946052901391691319657109 3888096229752735530608927)
          ·
            refine ⟨5832144344629103295913391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3888096229752735530608927 5832144344629103295913391)
            ·
              refine ⟨8748216516943654943870087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5832144344629103295913391 8748216516943654943870087)
              ·
                refine ⟨13122324775415482415805131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8748216516943654943870087 13122324775415482415805131)
                ·
                  refine ⟨19683487163123223623707697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13122324775415482415805131 19683487163123223623707697)
                  ·
                    refine ⟨14762615372342417717780773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19683487163123223623707697 14762615372342417717780773)
                    ·
                      refine ⟨2767990382314203322083895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14762615372342417717780773 2767990382314203322083895)
                      ·
                        rfl

theorem cell23_5390642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_5390642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390642 prefixEnd_5390642 := by exact prefixLift 5390642
  have htrace : WordTrace (prefixWord ++ tailWord_5390642) baseStart_5390642 baseEnd_5390642 := by
    simpa [prefixWord, tailWord_5390642, baseEnd_5390642] using wordTrace_append hprefix tailTrace_5390642
  have hstable : (prefixWord ++ tailWord_5390642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390642).length < 2 ^ (prefixWord ++ tailWord_5390642).sum := by decide
  have hdescent : baseEnd_5390642 < baseStart_5390642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390775 : List Nat := [1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 4]
def baseStart_5390775 : Nat := 118140960795 + 5390775 * 2 ^ 59
def prefixEnd_5390775 : Nat := 4983230072969 + 3 ^ 40 * 5390775 * 2
def baseEnd_5390775 : Nat := 2768058675241251301720783

theorem tailTrace_5390775 : CollatzResearch.WordTrace tailWord_5390775 prefixEnd_5390775 2768058675241251301720783 := by
  unfold tailWord_5390775
  simp only [CollatzResearch.WordTrace]
  refine ⟨196617717045150320916741779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131078478030100213944494519 196617717045150320916741779)
  ·
    refine ⟨294926575567725481375112669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196617717045150320916741779 294926575567725481375112669)
    ·
      refine ⟨110597465837897055515667251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294926575567725481375112669 110597465837897055515667251)
      ·
        refine ⟨165896198756845583273500877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110597465837897055515667251 165896198756845583273500877)
        ·
          refine ⟨62211074533817093727562829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165896198756845583273500877 62211074533817093727562829)
          ·
            refine ⟨23329152950181410147836061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62211074533817093727562829 23329152950181410147836061)
            ·
              refine ⟨8748432356318028805438523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23329152950181410147836061 8748432356318028805438523)
              ·
                refine ⟨13122648534477043208157785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8748432356318028805438523 13122648534477043208157785)
                ·
                  refine ⟨9841986400857782406118339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13122648534477043208157785 9841986400857782406118339)
                  ·
                    refine ⟨14762979601286673609177509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9841986400857782406118339 14762979601286673609177509)
                    ·
                      refine ⟨2768058675241251301720783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14762979601286673609177509 2768058675241251301720783)
                      ·
                        rfl

theorem cell23_5390775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_5390775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390775 prefixEnd_5390775 := by exact prefixLift 5390775
  have htrace : WordTrace (prefixWord ++ tailWord_5390775) baseStart_5390775 baseEnd_5390775 := by
    simpa [prefixWord, tailWord_5390775, baseEnd_5390775] using wordTrace_append hprefix tailTrace_5390775
  have hstable : (prefixWord ++ tailWord_5390775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390775).length < 2 ^ (prefixWord ++ tailWord_5390775).sum := by decide
  have hdescent : baseEnd_5390775 < baseStart_5390775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390825 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 5, 1, 3]
def baseStart_5390825 : Nat := 118140960795 + 5390825 * 2 ^ 59
def prefixEnd_5390825 : Nat := 4983230072969 + 3 ^ 40 * 5390825 * 2
def baseEnd_5390825 : Nat := 2768084349273976106095553

theorem tailTrace_5390825 : CollatzResearch.WordTrace tailWord_5390825 prefixEnd_5390825 2768084349273976106095553 := by
  unfold tailWord_5390825
  simp only [CollatzResearch.WordTrace]
  refine ⟨196619540694969179456061929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131079693796646119637374619 196619540694969179456061929)
  ·
    refine ⟨147464655521226884592046447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196619540694969179456061929 147464655521226884592046447)
    ·
      refine ⟨221196983281840326888069671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147464655521226884592046447 221196983281840326888069671)
      ·
        refine ⟨331795474922760490332104507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221196983281840326888069671 331795474922760490332104507)
        ·
          refine ⟨497693212384140735498156761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331795474922760490332104507 497693212384140735498156761)
          ·
            refine ⟨373269909288105551623617571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497693212384140735498156761 373269909288105551623617571)
            ·
              refine ⟨559904863932158327435426357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373269909288105551623617571 559904863932158327435426357)
              ·
                refine ⟨52491080993639843197071221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 559904863932158327435426357 52491080993639843197071221)
                ·
                  refine ⟨4921038843153735299725427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52491080993639843197071221 4921038843153735299725427)
                  ·
                    refine ⟨7381558264730602949588141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4921038843153735299725427 7381558264730602949588141)
                    ·
                      refine ⟨2768084349273976106095553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7381558264730602949588141 2768084349273976106095553)
                      ·
                        rfl

theorem cell23_5390825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 1, 3].length) (baseStart_5390825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390825 prefixEnd_5390825 := by exact prefixLift 5390825
  have htrace : WordTrace (prefixWord ++ tailWord_5390825) baseStart_5390825 baseEnd_5390825 := by
    simpa [prefixWord, tailWord_5390825, baseEnd_5390825] using wordTrace_append hprefix tailTrace_5390825
  have hstable : (prefixWord ++ tailWord_5390825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390825).length < 2 ^ (prefixWord ++ tailWord_5390825).sum := by decide
  have hdescent : baseEnd_5390825 < baseStart_5390825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390835 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 1, 5, 2]
def baseStart_5390835 : Nat := 118140960795 + 5390835 * 2 ^ 59
def prefixEnd_5390835 : Nat := 4983230072969 + 3 ^ 40 * 5390835 * 2
def baseEnd_5390835 : Nat := 2768089484080521066970507

theorem tailTrace_5390835 : CollatzResearch.WordTrace tailWord_5390835 prefixEnd_5390835 2768089484080521066970507 := by
  unfold tailWord_5390835
  simp only [CollatzResearch.WordTrace]
  refine ⟨196619905424932951163925959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131079936949955300775950639 196619905424932951163925959)
  ·
    refine ⟨294929858137399426745888939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196619905424932951163925959 294929858137399426745888939)
    ·
      refine ⟨442394787206099140118833409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294929858137399426745888939 442394787206099140118833409)
      ·
        refine ⟨331796090404574355089125057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 442394787206099140118833409 331796090404574355089125057)
        ·
          refine ⟨248847067803430766316843793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331796090404574355089125057 248847067803430766316843793)
          ·
            refine ⟨186635300852573074737632845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248847067803430766316843793 186635300852573074737632845)
            ·
              refine ⟨69988237819714903026612317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186635300852573074737632845 69988237819714903026612317)
              ·
                refine ⟨26245589182393088634979619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69988237819714903026612317 26245589182393088634979619)
                ·
                  refine ⟨39368383773589632952469429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26245589182393088634979619 39368383773589632952469429)
                  ·
                    refine ⟨3690785978774028089294009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39368383773589632952469429 3690785978774028089294009)
                    ·
                      refine ⟨2768089484080521066970507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3690785978774028089294009 2768089484080521066970507)
                      ·
                        rfl

theorem cell23_5390835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 5, 2].length) (baseStart_5390835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390835 prefixEnd_5390835 := by exact prefixLift 5390835
  have htrace : WordTrace (prefixWord ++ tailWord_5390835) baseStart_5390835 baseEnd_5390835 := by
    simpa [prefixWord, tailWord_5390835, baseEnd_5390835] using wordTrace_append hprefix tailTrace_5390835
  have hstable : (prefixWord ++ tailWord_5390835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390835).length < 2 ^ (prefixWord ++ tailWord_5390835).sum := by decide
  have hdescent : baseEnd_5390835 < baseStart_5390835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390845 : List Nat := [1, 4, 1, 1, 1, 3, 1, 5, 1, 5]
def baseStart_5390845 : Nat := 118140960795 + 5390845 * 2 ^ 59
def prefixEnd_5390845 : Nat := 4983230072969 + 3 ^ 40 * 5390845 * 2
def baseEnd_5390845 : Nat := 922698206295688675948487

theorem tailTrace_5390845 : CollatzResearch.WordTrace tailWord_5390845 prefixEnd_5390845 922698206295688675948487 := by
  unfold tailWord_5390845
  simp only [CollatzResearch.WordTrace]
  refine ⟨196620270154896722871789989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131080180103264481914526659 196620270154896722871789989)
  ·
    refine ⟨36866300654043135538460623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196620270154896722871789989 36866300654043135538460623)
    ·
      refine ⟨55299450981064703307690935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36866300654043135538460623 55299450981064703307690935)
      ·
        refine ⟨82949176471597054961536403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55299450981064703307690935 82949176471597054961536403)
        ·
          refine ⟨124423764707395582442304605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82949176471597054961536403 124423764707395582442304605)
          ·
            refine ⟨46658911765273343415864227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124423764707395582442304605 46658911765273343415864227)
            ·
              refine ⟨69988367647910015123796341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46658911765273343415864227 69988367647910015123796341)
              ·
                refine ⟨6561409466991563917855907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69988367647910015123796341 6561409466991563917855907)
                ·
                  refine ⟨9842114200487345876783861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6561409466991563917855907 9842114200487345876783861)
                  ·
                    refine ⟨922698206295688675948487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9842114200487345876783861 922698206295688675948487)
                    ·
                      rfl

theorem cell23_5390845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_5390845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390845 prefixEnd_5390845 := by exact prefixLift 5390845
  have htrace : WordTrace (prefixWord ++ tailWord_5390845) baseStart_5390845 baseEnd_5390845 := by
    simpa [prefixWord, tailWord_5390845, baseEnd_5390845] using wordTrace_append hprefix tailTrace_5390845
  have hstable : (prefixWord ++ tailWord_5390845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390845).length < 2 ^ (prefixWord ++ tailWord_5390845).sum := by decide
  have hdescent : baseEnd_5390845 < baseStart_5390845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390859 : List Nat := [1, 1, 1, 1, 7, 3, 1, 1, 3, 1, 3]
def baseStart_5390859 : Nat := 118140960795 + 5390859 * 2 ^ 59
def prefixEnd_5390859 : Nat := 4983230072969 + 3 ^ 40 * 5390859 * 2
def baseEnd_5390859 : Nat := 2768101807616228973070397

theorem tailTrace_5390859 : CollatzResearch.WordTrace tailWord_5390859 prefixEnd_5390859 2768101807616228973070397 := by
  unfold tailWord_5390859
  simp only [CollatzResearch.WordTrace]
  refine ⟨196620780776846003262799631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131080520517897335508533087 196620780776846003262799631)
  ·
    refine ⟨294931171165269004894199447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196620780776846003262799631 294931171165269004894199447)
    ·
      refine ⟨442396756747903507341299171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294931171165269004894199447 442396756747903507341299171)
      ·
        refine ⟨663595135121855261011948757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442396756747903507341299171 663595135121855261011948757)
        ·
          refine ⟨15553010979418482679967549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 663595135121855261011948757 15553010979418482679967549)
          ·
            refine ⟨5832379117281931004987831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15553010979418482679967549 5832379117281931004987831)
            ·
              refine ⟨8748568675922896507481747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5832379117281931004987831 8748568675922896507481747)
              ·
                refine ⟨13122853013884344761222621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8748568675922896507481747 13122853013884344761222621)
                ·
                  refine ⟨4921069880206629285458483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13122853013884344761222621 4921069880206629285458483)
                  ·
                    refine ⟨7381604820309943928187725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4921069880206629285458483 7381604820309943928187725)
                    ·
                      refine ⟨2768101807616228973070397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7381604820309943928187725 2768101807616228973070397)
                      ·
                        rfl

theorem cell23_5390859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 1, 3].length) (baseStart_5390859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390859 prefixEnd_5390859 := by exact prefixLift 5390859
  have htrace : WordTrace (prefixWord ++ tailWord_5390859) baseStart_5390859 baseEnd_5390859 := by
    simpa [prefixWord, tailWord_5390859, baseEnd_5390859] using wordTrace_append hprefix tailTrace_5390859
  have hstable : (prefixWord ++ tailWord_5390859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390859).length < 2 ^ (prefixWord ++ tailWord_5390859).sum := by decide
  have hdescent : baseEnd_5390859 < baseStart_5390859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390865 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 2, 6, 2]
def baseStart_5390865 : Nat := 118140960795 + 5390865 * 2 ^ 59
def prefixEnd_5390865 : Nat := 4983230072969 + 3 ^ 40 * 5390865 * 2
def baseEnd_5390865 : Nat := 2768104888500155949595369

theorem tailTrace_5390865 : CollatzResearch.WordTrace tailWord_5390865 prefixEnd_5390865 2768104888500155949595369 := by
  unfold tailWord_5390865
  simp only [CollatzResearch.WordTrace]
  refine ⟨196620999614824266287518049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131080666409882844191678699 196620999614824266287518049)
  ·
    refine ⟨147465749711118199715638537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196620999614824266287518049 147465749711118199715638537)
    ·
      refine ⟨110599312283338649786728903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147465749711118199715638537 110599312283338649786728903)
      ·
        refine ⟨165898968425007974680093355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110599312283338649786728903 165898968425007974680093355)
        ·
          refine ⟨248848452637511962020140033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165898968425007974680093355 248848452637511962020140033)
          ·
            refine ⟨186636339478133971515105025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248848452637511962020140033 186636339478133971515105025)
            ·
              refine ⟨139977254608600478636328769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186636339478133971515105025 139977254608600478636328769)
              ·
                refine ⟨104982940956450358977246577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139977254608600478636328769 104982940956450358977246577)
                ·
                  refine ⟨78737205717337769232934933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104982940956450358977246577 78737205717337769232934933)
                  ·
                    refine ⟨3690806518000207932793825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78737205717337769232934933 3690806518000207932793825)
                    ·
                      refine ⟨2768104888500155949595369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3690806518000207932793825 2768104888500155949595369)
                      ·
                        rfl

theorem cell23_5390865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 6, 2].length) (baseStart_5390865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390865 prefixEnd_5390865 := by exact prefixLift 5390865
  have htrace : WordTrace (prefixWord ++ tailWord_5390865) baseStart_5390865 baseEnd_5390865 := by
    simpa [prefixWord, tailWord_5390865, baseEnd_5390865] using wordTrace_append hprefix tailTrace_5390865
  have hstable : (prefixWord ++ tailWord_5390865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390865).length < 2 ^ (prefixWord ++ tailWord_5390865).sum := by decide
  have hdescent : baseEnd_5390865 < baseStart_5390865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390909 : List Nat := [1, 4, 1, 3, 2, 2, 2, 2, 2, 4]
def baseStart_5390909 : Nat := 118140960795 + 5390909 * 2 ^ 59
def prefixEnd_5390909 : Nat := 4983230072969 + 3 ^ 40 * 5390909 * 2
def baseEnd_5390909 : Nat := 922709160549651259148389

theorem tailTrace_5390909 : CollatzResearch.WordTrace tailWord_5390909 prefixEnd_5390909 922709160549651259148389 := by
  unfold tailWord_5390909
  simp only [CollatzResearch.WordTrace]
  refine ⟨196622604426664861802119781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131081736284443241201413187 196622604426664861802119781)
  ·
    refine ⟨36866738329999661587897459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196622604426664861802119781 36866738329999661587897459)
    ·
      refine ⟨55300107494999492381846189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36866738329999661587897459 55300107494999492381846189)
      ·
        refine ⟨20737540310624809643192321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55300107494999492381846189 20737540310624809643192321)
        ·
          refine ⟨15553155232968607232394241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20737540310624809643192321 15553155232968607232394241)
          ·
            refine ⟨11664866424726455424295681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15553155232968607232394241 11664866424726455424295681)
            ·
              refine ⟨8748649818544841568221761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11664866424726455424295681 8748649818544841568221761)
              ·
                refine ⟨6561487363908631176166321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8748649818544841568221761 6561487363908631176166321)
                ·
                  refine ⟨4921115522931473382124741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6561487363908631176166321 4921115522931473382124741)
                  ·
                    refine ⟨922709160549651259148389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4921115522931473382124741 922709160549651259148389)
                    ·
                      rfl

theorem cell23_5390909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_5390909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390909 prefixEnd_5390909 := by exact prefixLift 5390909
  have htrace : WordTrace (prefixWord ++ tailWord_5390909) baseStart_5390909 baseEnd_5390909 := by
    simpa [prefixWord, tailWord_5390909, baseEnd_5390909] using wordTrace_append hprefix tailTrace_5390909
  have hstable : (prefixWord ++ tailWord_5390909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390909).length < 2 ^ (prefixWord ++ tailWord_5390909).sum := by decide
  have hdescent : baseEnd_5390909 < baseStart_5390909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390932 : List Nat := [2, 4, 1, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_5390932 : Nat := 118140960795 + 5390932 * 2 ^ 59
def prefixEnd_5390932 : Nat := 4983230072969 + 3 ^ 40 * 5390932 * 2
def baseEnd_5390932 : Nat := 2768139291704007187457561

theorem tailTrace_5390932 : CollatzResearch.WordTrace tailWord_5390932 prefixEnd_5390932 2768139291704007187457561 := by
  unfold tailWord_5390932
  simp only [CollatzResearch.WordTrace]
  refine ⟨98311721652790768365103525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131082295537054357820138033 98311721652790768365103525)
  ·
    refine ⟨18433447809898269068456911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98311721652790768365103525 18433447809898269068456911)
    ·
      refine ⟨27650171714847403602685367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18433447809898269068456911 27650171714847403602685367)
      ·
        refine ⟨41475257572271105404028051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27650171714847403602685367 41475257572271105404028051)
        ·
          refine ⟨62212886358406658106042077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41475257572271105404028051 62212886358406658106042077)
          ·
            refine ⟨23329832384402496789765779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62212886358406658106042077 23329832384402496789765779)
            ·
              refine ⟨34994748576603745184648669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23329832384402496789765779 34994748576603745184648669)
              ·
                refine ⟨13123030716226404444243251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34994748576603745184648669 13123030716226404444243251)
                ·
                  refine ⟨19684546074339606666364877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13123030716226404444243251 19684546074339606666364877)
                  ·
                    refine ⟨7381704777877352499886829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19684546074339606666364877 7381704777877352499886829)
                    ·
                      refine ⟨2768139291704007187457561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7381704777877352499886829 2768139291704007187457561)
                      ·
                        rfl

theorem cell23_5390932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_5390932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390932 prefixEnd_5390932 := by exact prefixLift 5390932
  have htrace : WordTrace (prefixWord ++ tailWord_5390932) baseStart_5390932 baseEnd_5390932 := by
    simpa [prefixWord, tailWord_5390932, baseEnd_5390932] using wordTrace_append hprefix tailTrace_5390932
  have hstable : (prefixWord ++ tailWord_5390932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390932).length < 2 ^ (prefixWord ++ tailWord_5390932).sum := by decide
  have hdescent : baseEnd_5390932 < baseStart_5390932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390966 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3]
def baseStart_5390966 : Nat := 118140960795 + 5390966 * 2 ^ 59
def prefixEnd_5390966 : Nat := 4983230072969 + 3 ^ 40 * 5390966 * 2
def baseEnd_5390966 : Nat := 2768156750046260054432405

theorem tailTrace_5390966 : CollatzResearch.WordTrace tailWord_5390966 prefixEnd_5390966 2768156750046260054432405 := by
  unfold tailWord_5390966
  simp only [CollatzResearch.WordTrace]
  refine ⟨12289042711716147533559047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131083122258305573691296501 12289042711716147533559047)
  ·
    refine ⟨18433564067574221300338571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12289042711716147533559047 18433564067574221300338571)
    ·
      refine ⟨27650346101361331950507857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18433564067574221300338571 27650346101361331950507857)
      ·
        refine ⟨20737759576020998962880893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27650346101361331950507857 20737759576020998962880893)
        ·
          refine ⟨7776659841007874611080335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20737759576020998962880893 7776659841007874611080335)
          ·
            refine ⟨11664989761511811916620503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7776659841007874611080335 11664989761511811916620503)
            ·
              refine ⟨17497484642267717874930755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11664989761511811916620503 17497484642267717874930755)
              ·
                refine ⟨26246226963401576812396133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17497484642267717874930755 26246226963401576812396133)
                ·
                  refine ⟨4921167555637795652324275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26246226963401576812396133 4921167555637795652324275)
                  ·
                    refine ⟨7381751333456693478486413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4921167555637795652324275 7381751333456693478486413)
                    ·
                      refine ⟨2768156750046260054432405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7381751333456693478486413 2768156750046260054432405)
                      ·
                        rfl

theorem cell23_5390966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_5390966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390966 prefixEnd_5390966 := by exact prefixLift 5390966
  have htrace : WordTrace (prefixWord ++ tailWord_5390966) baseStart_5390966 baseEnd_5390966 := by
    simpa [prefixWord, tailWord_5390966, baseEnd_5390966] using wordTrace_append hprefix tailTrace_5390966
  have hstable : (prefixWord ++ tailWord_5390966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390966).length < 2 ^ (prefixWord ++ tailWord_5390966).sum := by decide
  have hdescent : baseEnd_5390966 < baseStart_5390966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390972 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 3, 4, 2]
def baseStart_5390972 : Nat := 118140960795 + 5390972 * 2 ^ 59
def prefixEnd_5390972 : Nat := 4983230072969 + 3 ^ 40 * 5390972 * 2
def baseEnd_5390972 : Nat := 2768159830930187030957377

theorem tailTrace_5390972 : CollatzResearch.WordTrace tailWord_5390972 prefixEnd_5390972 2768159830930187030957377 := by
  unfold tailWord_5390972
  simp only [CollatzResearch.WordTrace]
  refine ⟨98312451112718311780831585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131083268150291082374442113 98312451112718311780831585)
  ·
    refine ⟨73734338334538733835623689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98312451112718311780831585 73734338334538733835623689)
    ·
      refine ⟨55300753750904050376717767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73734338334538733835623689 55300753750904050376717767)
      ·
        refine ⟨82951130626356075565076651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55300753750904050376717767 82951130626356075565076651)
        ·
          refine ⟨124426695939534113347614977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82951130626356075565076651 124426695939534113347614977)
          ·
            refine ⟨93320021954650585010711233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124426695939534113347614977 93320021954650585010711233)
            ·
              refine ⟨69990016465987938758033425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93320021954650585010711233 69990016465987938758033425)
              ·
                refine ⟨52492512349490954068525069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69990016465987938758033425 52492512349490954068525069)
                ·
                  refine ⟨19684692131059107775696901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52492512349490954068525069 19684692131059107775696901)
                  ·
                    refine ⟨3690879774573582707943169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19684692131059107775696901 3690879774573582707943169)
                    ·
                      refine ⟨2768159830930187030957377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3690879774573582707943169 2768159830930187030957377)
                      ·
                        rfl

theorem cell23_5390972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_5390972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390972 prefixEnd_5390972 := by exact prefixLift 5390972
  have htrace : WordTrace (prefixWord ++ tailWord_5390972) baseStart_5390972 baseEnd_5390972 := by
    simpa [prefixWord, tailWord_5390972, baseEnd_5390972] using wordTrace_append hprefix tailTrace_5390972
  have hstable : (prefixWord ++ tailWord_5390972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390972).length < 2 ^ (prefixWord ++ tailWord_5390972).sum := by decide
  have hdescent : baseEnd_5390972 < baseStart_5390972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5390975 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 3]
def baseStart_5390975 : Nat := 118140960795 + 5390975 * 2 ^ 59
def prefixEnd_5390975 : Nat := 4983230072969 + 3 ^ 40 * 5390975 * 2
def baseEnd_5390975 : Nat := 2768161371372150519219863

theorem tailTrace_5390975 : CollatzResearch.WordTrace tailWord_5390975 prefixEnd_5390975 2768161371372150519219863 := by
  unfold tailWord_5390975
  simp only [CollatzResearch.WordTrace]
  refine ⟨196625011644425755074022379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131083341096283836716014919 196625011644425755074022379)
  ·
    refine ⟨294937517466638632611033569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196625011644425755074022379 294937517466638632611033569)
    ·
      refine ⟨221203138099978974458275177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294937517466638632611033569 221203138099978974458275177)
      ·
        refine ⟨165902353574984230843706383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221203138099978974458275177 165902353574984230843706383)
        ·
          refine ⟨248853530362476346265559575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165902353574984230843706383 248853530362476346265559575)
          ·
            refine ⟨373280295543714519398339363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248853530362476346265559575 373280295543714519398339363)
            ·
              refine ⟨559920443315571779097509045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373280295543714519398339363 559920443315571779097509045)
              ·
                refine ⟨52492541560834854290391473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 559920443315571779097509045 52492541560834854290391473)
                ·
                  refine ⟨39369406170626140717793605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52492541560834854290391473 39369406170626140717793605)
                  ·
                    refine ⟨7381763656992401384586301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39369406170626140717793605 7381763656992401384586301)
                    ·
                      refine ⟨2768161371372150519219863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7381763656992401384586301 2768161371372150519219863)
                      ·
                        rfl

theorem cell23_5390975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_5390975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5390975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5390975 prefixEnd_5390975 := by exact prefixLift 5390975
  have htrace : WordTrace (prefixWord ++ tailWord_5390975) baseStart_5390975 baseEnd_5390975 := by
    simpa [prefixWord, tailWord_5390975, baseEnd_5390975] using wordTrace_append hprefix tailTrace_5390975
  have hstable : (prefixWord ++ tailWord_5390975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5390975).length < 2 ^ (prefixWord ++ tailWord_5390975).sum := by decide
  have hdescent : baseEnd_5390975 < baseStart_5390975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5390975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391006 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_5391006 : Nat := 118140960795 + 5391006 * 2 ^ 59
def prefixEnd_5391006 : Nat := 4983230072969 + 3 ^ 40 * 5391006 * 2
def baseEnd_5391006 : Nat := 2768177289272439897932221

theorem tailTrace_5391006 : CollatzResearch.WordTrace tailWord_5391006 prefixEnd_5391006 2768177289272439897932221 := by
  unfold tailWord_5391006
  simp only [CollatzResearch.WordTrace]
  refine ⟨24578267788414180921050109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131084094871542298245600581 24578267788414180921050109)
  ·
    refine ⟨9216850420655317845393791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24578267788414180921050109 9216850420655317845393791)
    ·
      refine ⟨13825275630982976768090687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9216850420655317845393791 13825275630982976768090687)
      ·
        refine ⟨20737913446474465152136031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13825275630982976768090687 20737913446474465152136031)
        ·
          refine ⟨31106870169711697728204047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20737913446474465152136031 31106870169711697728204047)
          ·
            refine ⟨46660305254567546592306071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31106870169711697728204047 46660305254567546592306071)
            ·
              refine ⟨69990457881851319888459107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46660305254567546592306071 69990457881851319888459107)
              ·
                refine ⟨104985686822776979832688661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69990457881851319888459107 104985686822776979832688661)
                ·
                  refine ⟨4921204069817670929657281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104985686822776979832688661 4921204069817670929657281)
                  ·
                    refine ⟨3690903052363253197242961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4921204069817670929657281 3690903052363253197242961)
                    ·
                      refine ⟨2768177289272439897932221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3690903052363253197242961 2768177289272439897932221)
                      ·
                        rfl

theorem cell23_5391006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_5391006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391006 prefixEnd_5391006 := by exact prefixLift 5391006
  have htrace : WordTrace (prefixWord ++ tailWord_5391006) baseStart_5391006 baseEnd_5391006 := by
    simpa [prefixWord, tailWord_5391006, baseEnd_5391006] using wordTrace_append hprefix tailTrace_5391006
  have hstable : (prefixWord ++ tailWord_5391006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391006).length < 2 ^ (prefixWord ++ tailWord_5391006).sum := by decide
  have hdescent : baseEnd_5391006 < baseStart_5391006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391029 : List Nat := [1, 3, 3, 3, 1, 3, 1, 1, 7]
def baseStart_5391029 : Nat := 118140960795 + 5391029 * 2 ^ 59
def prefixEnd_5391029 : Nat := 4983230072969 + 3 ^ 40 * 5391029 * 2
def baseEnd_5391029 : Nat := 307576566591943700882735

theorem tailTrace_5391029 : CollatzResearch.WordTrace tailWord_5391029 prefixEnd_5391029 307576566591943700882735 := by
  unfold tailWord_5391029
  simp only [CollatzResearch.WordTrace]
  refine ⟨196626981186230122296488141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131084654124153414864325427 196626981186230122296488141)
  ·
    refine ⟨73735117944836295861183053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196626981186230122296488141 73735117944836295861183053)
    ·
      refine ⟨27650669229313610947943645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73735117944836295861183053 27650669229313610947943645)
      ·
        refine ⟨10369000960992604105478867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27650669229313610947943645 10369000960992604105478867)
        ·
          refine ⟨15553501441488906158218301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10369000960992604105478867 15553501441488906158218301)
          ·
            refine ⟨5832563040558339809331863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15553501441488906158218301 5832563040558339809331863)
            ·
              refine ⟨8748844560837509713997795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5832563040558339809331863 8748844560837509713997795)
              ·
                refine ⟨13123266841256264570996693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8748844560837509713997795 13123266841256264570996693)
                ·
                  refine ⟨307576566591943700882735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13123266841256264570996693 307576566591943700882735)
                  ·
                    rfl

theorem cell23_5391029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 7].length) (baseStart_5391029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391029 prefixEnd_5391029 := by exact prefixLift 5391029
  have htrace : WordTrace (prefixWord ++ tailWord_5391029) baseStart_5391029 baseEnd_5391029 := by
    simpa [prefixWord, tailWord_5391029, baseEnd_5391029] using wordTrace_append hprefix tailTrace_5391029
  have hstable : (prefixWord ++ tailWord_5391029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391029).length < 2 ^ (prefixWord ++ tailWord_5391029).sum := by decide
  have hdescent : baseEnd_5391029 < baseStart_5391029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391082 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_5391082 : Nat := 118140960795 + 5391082 * 2 ^ 59
def prefixEnd_5391082 : Nat := 4983230072969 + 3 ^ 40 * 5391082 * 2
def baseEnd_5391082 : Nat := 2768216313802181600581871

theorem tailTrace_5391082 : CollatzResearch.WordTrace tailWord_5391082 prefixEnd_5391082 2768216313802181600581871 := by
  unfold tailWord_5391082
  simp only [CollatzResearch.WordTrace]
  refine ⟨49157228563759528087041875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131085942836692074898778333 49157228563759528087041875)
  ·
    refine ⟨73735842845639292130562813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49157228563759528087041875 73735842845639292130562813)
    ·
      refine ⟨27650941067114734548961055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73735842845639292130562813 27650941067114734548961055)
      ·
        refine ⟨41476411600672101823441583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27650941067114734548961055 41476411600672101823441583)
        ·
          refine ⟨62214617401008152735162375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41476411600672101823441583 62214617401008152735162375)
          ·
            refine ⟨93321926101512229102743563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62214617401008152735162375 93321926101512229102743563)
            ·
              refine ⟨139982889152268343654115345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93321926101512229102743563 139982889152268343654115345)
              ·
                refine ⟨104987166864201257740586509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139982889152268343654115345 104987166864201257740586509)
                ·
                  refine ⟨39370187574075471652719941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104987166864201257740586509 39370187574075471652719941)
                  ·
                    refine ⟨7381910170139150934884989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39370187574075471652719941 7381910170139150934884989)
                    ·
                      refine ⟨2768216313802181600581871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7381910170139150934884989 2768216313802181600581871)
                      ·
                        rfl

theorem cell23_5391082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_5391082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391082 prefixEnd_5391082 := by exact prefixLift 5391082
  have htrace : WordTrace (prefixWord ++ tailWord_5391082) baseStart_5391082 baseEnd_5391082 := by
    simpa [prefixWord, tailWord_5391082, baseEnd_5391082] using wordTrace_append hprefix tailTrace_5391082
  have hstable : (prefixWord ++ tailWord_5391082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391082).length < 2 ^ (prefixWord ++ tailWord_5391082).sum := by decide
  have hdescent : baseEnd_5391082 < baseStart_5391082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391106 : List Nat := [3, 4, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_5391106 : Nat := 118140960795 + 5391106 * 2 ^ 59
def prefixEnd_5391106 : Nat := 4983230072969 + 3 ^ 40 * 5391106 * 2
def baseEnd_5391106 : Nat := 922742879112629835560587

theorem tailTrace_5391106 : CollatzResearch.WordTrace tailWord_5391106 prefixEnd_5391106 922742879112629835560587 := by
  unfold tailWord_5391106
  simp only [CollatzResearch.WordTrace]
  refine ⟨49157447401737791111760293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131086526404634109631360781 49157447401737791111760293)
  ·
    refine ⟨9217021387825835833455055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49157447401737791111760293 9217021387825835833455055)
    ·
      refine ⟨13825532081738753750182583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9217021387825835833455055 13825532081738753750182583)
      ·
        refine ⟨20738298122608130625273875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13825532081738753750182583 20738298122608130625273875)
        ·
          refine ⟨31107447183912195937910813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20738298122608130625273875 31107447183912195937910813)
          ·
            refine ⟨11665292693967073476716555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31107447183912195937910813 11665292693967073476716555)
            ·
              refine ⟨17497939040950610215074833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11665292693967073476716555 17497939040950610215074833)
              ·
                refine ⟨13123454280712957661306125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17497939040950610215074833 13123454280712957661306125)
                ·
                  refine ⟨4921295355267359122989797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13123454280712957661306125 4921295355267359122989797)
                  ·
                    refine ⟨922742879112629835560587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4921295355267359122989797 922742879112629835560587)
                    ·
                      rfl

theorem cell23_5391106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_5391106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391106 prefixEnd_5391106 := by exact prefixLift 5391106
  have htrace : WordTrace (prefixWord ++ tailWord_5391106) baseStart_5391106 baseEnd_5391106 := by
    simpa [prefixWord, tailWord_5391106, baseEnd_5391106] using wordTrace_append hprefix tailTrace_5391106
  have hstable : (prefixWord ++ tailWord_5391106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391106).length < 2 ^ (prefixWord ++ tailWord_5391106).sum := by decide
  have hdescent : baseEnd_5391106 < baseStart_5391106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391139 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 4, 3, 2]
def baseStart_5391139 : Nat := 118140960795 + 5391139 * 2 ^ 59
def prefixEnd_5391139 : Nat := 4983230072969 + 3 ^ 40 * 5391139 * 2
def baseEnd_5391139 : Nat := 2768245582199487877569109

theorem tailTrace_5391139 : CollatzResearch.WordTrace tailWord_5391139 prefixEnd_5391139 2768245582199487877569109 := by
  unfold tailWord_5391139
  simp only [CollatzResearch.WordTrace]
  refine ⟨196630993215831611082992471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131087328810554407388661647 196630993215831611082992471)
  ·
    refine ⟨294946489823747416624488707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196630993215831611082992471 294946489823747416624488707)
    ·
      refine ⟨442419734735621124936733061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294946489823747416624488707 442419734735621124936733061)
      ·
        refine ⟨82953700262928960925637449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 442419734735621124936733061 82953700262928960925637449)
        ·
          refine ⟨62215275197196720694228087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82953700262928960925637449 62215275197196720694228087)
          ·
            refine ⟨93322912795795081041342131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62215275197196720694228087 93322912795795081041342131)
            ·
              refine ⟨139984369193692621562013197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93322912795795081041342131 139984369193692621562013197)
              ·
                refine ⟨52494138447634733085754949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139984369193692621562013197 52494138447634733085754949)
                ·
                  refine ⟨9842650958931512453579053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52494138447634733085754949 9842650958931512453579053)
                  ·
                    refine ⟨3690994109599317170092145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9842650958931512453579053 3690994109599317170092145)
                    ·
                      refine ⟨2768245582199487877569109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3690994109599317170092145 2768245582199487877569109)
                      ·
                        rfl

theorem cell23_5391139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_5391139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391139 prefixEnd_5391139 := by exact prefixLift 5391139
  have htrace : WordTrace (prefixWord ++ tailWord_5391139) baseStart_5391139 baseEnd_5391139 := by
    simpa [prefixWord, tailWord_5391139, baseEnd_5391139] using wordTrace_append hprefix tailTrace_5391139
  have hstable : (prefixWord ++ tailWord_5391139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391139).length < 2 ^ (prefixWord ++ tailWord_5391139).sum := by decide
  have hdescent : baseEnd_5391139 < baseStart_5391139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391152 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 4]
def baseStart_5391152 : Nat := 118140960795 + 5391152 * 2 ^ 59
def prefixEnd_5391152 : Nat := 4983230072969 + 3 ^ 40 * 5391152 * 2
def baseEnd_5391152 : Nat := 2768252257447996326706549

theorem tailTrace_5391152 : CollatzResearch.WordTrace tailWord_5391152 prefixEnd_5391152 2768252257447996326706549 := by
  unfold tailWord_5391152
  simp only [CollatzResearch.WordTrace]
  refine ⟨98315733682392257151607855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131087644909856342868810473 98315733682392257151607855)
  ·
    refine ⟨147473600523588385727411783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98315733682392257151607855 147473600523588385727411783)
    ·
      refine ⟨221210400785382578591117675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147473600523588385727411783 221210400785382578591117675)
      ·
        refine ⟨331815601178073867886676513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221210400785382578591117675 331815601178073867886676513)
        ·
          refine ⟨248861700883555400915007385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331815601178073867886676513 248861700883555400915007385)
          ·
            refine ⟨186646275662666550686255539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248861700883555400915007385 186646275662666550686255539)
            ·
              refine ⟨279969413493999826029383309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186646275662666550686255539 279969413493999826029383309)
              ·
                refine ⟨104988530060249934761018741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 279969413493999826029383309 104988530060249934761018741)
                ·
                  refine ⟨9842674693148431383845507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104988530060249934761018741 9842674693148431383845507)
                  ·
                    refine ⟨14764012039722647075768261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9842674693148431383845507 14764012039722647075768261)
                    ·
                      refine ⟨2768252257447996326706549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14764012039722647075768261 2768252257447996326706549)
                      ·
                        rfl

theorem cell23_5391152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 4].length) (baseStart_5391152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391152 prefixEnd_5391152 := by exact prefixLift 5391152
  have htrace : WordTrace (prefixWord ++ tailWord_5391152) baseStart_5391152 baseEnd_5391152 := by
    simpa [prefixWord, tailWord_5391152, baseEnd_5391152] using wordTrace_append hprefix tailTrace_5391152
  have hstable : (prefixWord ++ tailWord_5391152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391152).length < 2 ^ (prefixWord ++ tailWord_5391152).sum := by decide
  have hdescent : baseEnd_5391152 < baseStart_5391152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391174 : List Nat := [6, 1, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_5391174 : Nat := 118140960795 + 5391174 * 2 ^ 59
def prefixEnd_5391174 : Nat := 4983230072969 + 3 ^ 40 * 5391174 * 2
def baseEnd_5391174 : Nat := 922754518007465080210483

theorem tailTrace_5391174 : CollatzResearch.WordTrace tailWord_5391174 prefixEnd_5391174 922754518007465080210483 := by
  unfold tailWord_5391174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6144758430334525376891143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 131088179847136541373677717 6144758430334525376891143)
  ·
    refine ⟨9217137645501788065336715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6144758430334525376891143 9217137645501788065336715)
    ·
      refine ⟨13825706468252682098005073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9217137645501788065336715 13825706468252682098005073)
      ·
        refine ⟨10369279851189511573503805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13825706468252682098005073 10369279851189511573503805)
        ·
          refine ⟨3888479944196066840063927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10369279851189511573503805 3888479944196066840063927)
          ·
            refine ⟨5832719916294100260095891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3888479944196066840063927 5832719916294100260095891)
            ·
              refine ⟨8749079874441150390143837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5832719916294100260095891 8749079874441150390143837)
              ·
                refine ⟨3280904952915431396303939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8749079874441150390143837 3280904952915431396303939)
                ·
                  refine ⟨4921357429373147094455909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3280904952915431396303939 4921357429373147094455909)
                  ·
                    refine ⟨922754518007465080210483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4921357429373147094455909 922754518007465080210483)
                    ·
                      rfl

theorem cell23_5391174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_5391174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391174 prefixEnd_5391174 := by exact prefixLift 5391174
  have htrace : WordTrace (prefixWord ++ tailWord_5391174) baseStart_5391174 baseEnd_5391174 := by
    simpa [prefixWord, tailWord_5391174, baseEnd_5391174] using wordTrace_append hprefix tailTrace_5391174
  have hstable : (prefixWord ++ tailWord_5391174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391174).length < 2 ^ (prefixWord ++ tailWord_5391174).sum := by decide
  have hdescent : baseEnd_5391174 < baseStart_5391174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391180 : List Nat := [2, 2, 1, 3, 3, 3, 1, 3, 1, 1, 3]
def baseStart_5391180 : Nat := 118140960795 + 5391180 * 2 ^ 59
def prefixEnd_5391180 : Nat := 4983230072969 + 3 ^ 40 * 5391180 * 2
def baseEnd_5391180 : Nat := 2768266634906322217156421

theorem tailTrace_5391180 : CollatzResearch.WordTrace tailWord_5391180 prefixEnd_5391180 2768266634906322217156421 := by
  unfold tailWord_5391180
  simp only [CollatzResearch.WordTrace]
  refine ⟨98316244304341537542617497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131088325739122050056823329 98316244304341537542617497)
  ·
    refine ⟨73737183228256153156963123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98316244304341537542617497 73737183228256153156963123)
    ·
      refine ⟨110605774842384229735444685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73737183228256153156963123 110605774842384229735444685)
      ·
        refine ⟨41477165565894086150791757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110605774842384229735444685 41477165565894086150791757)
        ·
          refine ⟨15553937087210282306546909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41477165565894086150791757 15553937087210282306546909)
          ·
            refine ⟨5832726407703855864955091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15553937087210282306546909 5832726407703855864955091)
            ·
              refine ⟨8749089611555783797432637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5832726407703855864955091 8749089611555783797432637)
              ·
                refine ⟨3280908604333418924037239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8749089611555783797432637 3280908604333418924037239)
                ·
                  refine ⟨4921362906500128386055859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3280908604333418924037239 4921362906500128386055859)
                  ·
                    refine ⟨7382044359750192579083789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4921362906500128386055859 7382044359750192579083789)
                    ·
                      refine ⟨2768266634906322217156421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7382044359750192579083789 2768266634906322217156421)
                      ·
                        rfl

theorem cell23_5391180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_5391180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391180 prefixEnd_5391180 := by exact prefixLift 5391180
  have htrace : WordTrace (prefixWord ++ tailWord_5391180) baseStart_5391180 baseEnd_5391180 := by
    simpa [prefixWord, tailWord_5391180, baseEnd_5391180] using wordTrace_append hprefix tailTrace_5391180
  have hstable : (prefixWord ++ tailWord_5391180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391180).length < 2 ^ (prefixWord ++ tailWord_5391180).sum := by decide
  have hdescent : baseEnd_5391180 < baseStart_5391180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391189 : List Nat := [1, 3, 2, 2, 2, 1, 4, 1, 1, 1, 5]
def baseStart_5391189 : Nat := 118140960795 + 5391189 * 2 ^ 59
def prefixEnd_5391189 : Nat := 4983230072969 + 3 ^ 40 * 5391189 * 2
def baseEnd_5391189 : Nat := 2768271256232212681943879

theorem tailTrace_5391189 : CollatzResearch.WordTrace tailWord_5391189 prefixEnd_5391189 2768271256232212681943879 := by
  unfold tailWord_5391189
  simp only [CollatzResearch.WordTrace]
  refine ⟨196632816865650469622312621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131088544577100313081541747 196632816865650469622312621)
  ·
    refine ⟨73737306324618926108367233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196632816865650469622312621 73737306324618926108367233)
    ·
      refine ⟨55302979743464194581275425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73737306324618926108367233 55302979743464194581275425)
      ·
        refine ⟨41477234807598145935956569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55302979743464194581275425 41477234807598145935956569)
        ·
          refine ⟨31107926105698609451967427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41477234807598145935956569 31107926105698609451967427)
          ·
            refine ⟨46661889158547914177951141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31107926105698609451967427 46661889158547914177951141)
            ·
              refine ⟨8749104217227733908365839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46661889158547914177951141 8749104217227733908365839)
              ·
                refine ⟨13123656325841600862548759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8749104217227733908365839 13123656325841600862548759)
                ·
                  refine ⟨19685484488762401293823139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13123656325841600862548759 19685484488762401293823139)
                  ·
                    refine ⟨29528226733143601940734709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19685484488762401293823139 29528226733143601940734709)
                    ·
                      refine ⟨2768271256232212681943879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29528226733143601940734709 2768271256232212681943879)
                      ·
                        rfl

theorem cell23_5391189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_5391189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391189 prefixEnd_5391189 := by exact prefixLift 5391189
  have htrace : WordTrace (prefixWord ++ tailWord_5391189) baseStart_5391189 baseEnd_5391189 := by
    simpa [prefixWord, tailWord_5391189, baseEnd_5391189] using wordTrace_append hprefix tailTrace_5391189
  have hstable : (prefixWord ++ tailWord_5391189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391189).length < 2 ^ (prefixWord ++ tailWord_5391189).sum := by decide
  have hdescent : baseEnd_5391189 < baseStart_5391189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391196 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 4, 4]
def baseStart_5391196 : Nat := 118140960795 + 5391196 * 2 ^ 59
def prefixEnd_5391196 : Nat := 4983230072969 + 3 ^ 40 * 5391196 * 2
def baseEnd_5391196 : Nat := 922758283532264718185449

theorem tailTrace_5391196 : CollatzResearch.WordTrace tailWord_5391196 prefixEnd_5391196 922758283532264718185449 := by
  unfold tailWord_5391196
  simp only [CollatzResearch.WordTrace]
  refine ⟨98316536088312554908908721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131088714784416739878544961 98316536088312554908908721)
  ·
    refine ⟨73737402066234416181681541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98316536088312554908908721 73737402066234416181681541)
    ·
      refine ⟨13825762887418953034065289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73737402066234416181681541 13825762887418953034065289)
      ·
        refine ⟨10369322165564214775548967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13825762887418953034065289 10369322165564214775548967)
        ·
          refine ⟨15553983248346322163323451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10369322165564214775548967 15553983248346322163323451)
          ·
            refine ⟨23330974872519483244985177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15553983248346322163323451 23330974872519483244985177)
            ·
              refine ⟨17498231154389612433738883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23330974872519483244985177 17498231154389612433738883)
              ·
                refine ⟨26247346731584418650608325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17498231154389612433738883 26247346731584418650608325)
                ·
                  refine ⟨4921377512172078496989061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26247346731584418650608325 4921377512172078496989061)
                  ·
                    refine ⟨922758283532264718185449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4921377512172078496989061 922758283532264718185449)
                    ·
                      rfl

theorem cell23_5391196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_5391196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391196 prefixEnd_5391196 := by exact prefixLift 5391196
  have htrace : WordTrace (prefixWord ++ tailWord_5391196) baseStart_5391196 baseEnd_5391196 := by
    simpa [prefixWord, tailWord_5391196, baseEnd_5391196] using wordTrace_append hprefix tailTrace_5391196
  have hstable : (prefixWord ++ tailWord_5391196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391196).length < 2 ^ (prefixWord ++ tailWord_5391196).sum := by decide
  have hdescent : baseEnd_5391196 < baseStart_5391196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391203 : List Nat := [1, 1, 1, 5, 3, 1, 3, 1, 3, 2, 2]
def baseStart_5391203 : Nat := 118140960795 + 5391203 * 2 ^ 59
def prefixEnd_5391203 : Nat := 4983230072969 + 3 ^ 40 * 5391203 * 2
def baseEnd_5391203 : Nat := 2768278444961375627168815

theorem tailTrace_5391203 : CollatzResearch.WordTrace tailWord_5391203 prefixEnd_5391203 2768278444961375627168815 := by
  unfold tailWord_5391203
  simp only [CollatzResearch.WordTrace]
  refine ⟨196633327487599750013322263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131088884991733166675548175 196633327487599750013322263)
  ·
    refine ⟨294949991231399625019983395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196633327487599750013322263 294949991231399625019983395)
    ·
      refine ⟨442424986847099437529975093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294949991231399625019983395 442424986847099437529975093)
      ·
        refine ⟨41477342516915572268435165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 442424986847099437529975093 41477342516915572268435165)
        ·
          refine ⟨15554003443843339600663187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41477342516915572268435165 15554003443843339600663187)
          ·
            refine ⟨23331005165765009400994781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15554003443843339600663187 23331005165765009400994781)
            ·
              refine ⟨8749126937161878525373043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23331005165765009400994781 8749126937161878525373043)
              ·
                refine ⟨13123690405742817788059565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8749126937161878525373043 13123690405742817788059565)
                ·
                  refine ⟨4921383902153556670522337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13123690405742817788059565 4921383902153556670522337)
                  ·
                    refine ⟨3691037926615167502891753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4921383902153556670522337 3691037926615167502891753)
                    ·
                      refine ⟨2768278444961375627168815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3691037926615167502891753 2768278444961375627168815)
                      ·
                        rfl

theorem cell23_5391203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_5391203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391203 prefixEnd_5391203 := by exact prefixLift 5391203
  have htrace : WordTrace (prefixWord ++ tailWord_5391203) baseStart_5391203 baseEnd_5391203 := by
    simpa [prefixWord, tailWord_5391203, baseEnd_5391203] using wordTrace_append hprefix tailTrace_5391203
  have hstable : (prefixWord ++ tailWord_5391203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391203).length < 2 ^ (prefixWord ++ tailWord_5391203).sum := by decide
  have hdescent : baseEnd_5391203 < baseStart_5391203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391212 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 6]
def baseStart_5391212 : Nat := 118140960795 + 5391212 * 2 ^ 59
def prefixEnd_5391212 : Nat := 4983230072969 + 3 ^ 40 * 5391212 * 2
def baseEnd_5391212 : Nat := 2768283066287266091956273

theorem tailTrace_5391212 : CollatzResearch.WordTrace tailWord_5391212 prefixEnd_5391212 2768283066287266091956273 := by
  unfold tailWord_5391212
  simp only [CollatzResearch.WordTrace]
  refine ⟨98316827872283572275199945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131089103829711429700266593 98316827872283572275199945)
  ·
    refine ⟨73737620904212679206399959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98316827872283572275199945 73737620904212679206399959)
    ·
      refine ⟨110606431356319018809599939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73737620904212679206399959 110606431356319018809599939)
      ·
        refine ⟨165909647034478528214399909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110606431356319018809599939 165909647034478528214399909)
        ·
          refine ⟨31108058818964724040199983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165909647034478528214399909 31108058818964724040199983)
          ·
            refine ⟨46662088228447086060299975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31108058818964724040199983 46662088228447086060299975)
            ·
              refine ⟨69993132342670629090449963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46662088228447086060299975 69993132342670629090449963)
              ·
                refine ⟨104989698514005943635674945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69993132342670629090449963 104989698514005943635674945)
                ·
                  refine ⟨78742273885504457726756209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104989698514005943635674945 78742273885504457726756209)
                  ·
                    refine ⟨59056705414128343295067157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78742273885504457726756209 59056705414128343295067157)
                    ·
                      refine ⟨2768283066287266091956273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59056705414128343295067157 2768283066287266091956273)
                      ·
                        rfl

theorem cell23_5391212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_5391212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391212 prefixEnd_5391212 := by exact prefixLift 5391212
  have htrace : WordTrace (prefixWord ++ tailWord_5391212) baseStart_5391212 baseEnd_5391212 := by
    simpa [prefixWord, tailWord_5391212, baseEnd_5391212] using wordTrace_append hprefix tailTrace_5391212
  have hstable : (prefixWord ++ tailWord_5391212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391212).length < 2 ^ (prefixWord ++ tailWord_5391212).sum := by decide
  have hdescent : baseEnd_5391212 < baseStart_5391212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391232 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 5]
def baseStart_5391232 : Nat := 118140960795 + 5391232 * 2 ^ 59
def prefixEnd_5391232 : Nat := 4983230072969 + 3 ^ 40 * 5391232 * 2
def baseEnd_5391232 : Nat := 2768293335900356013706181

theorem tailTrace_5391232 : CollatzResearch.WordTrace tailWord_5391232 prefixEnd_5391232 2768293335900356013706181 := by
  unfold tailWord_5391232
  simp only [CollatzResearch.WordTrace]
  refine ⟨98317192602247343983063975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131089590136329791977418633 98317192602247343983063975)
  ·
    refine ⟨147475788903371015974595963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98317192602247343983063975 147475788903371015974595963)
    ·
      refine ⟨221213683355056523961893945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147475788903371015974595963 221213683355056523961893945)
      ·
        refine ⟨165910262516292392971420459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221213683355056523961893945 165910262516292392971420459)
        ·
          refine ⟨248865393774438589457130689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165910262516292392971420459 248865393774438589457130689)
          ·
            refine ⟨186649045330828942092848017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248865393774438589457130689 186649045330828942092848017)
            ·
              refine ⟨139986783998121706569636013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186649045330828942092848017 139986783998121706569636013)
              ·
                refine ⟨52495043999295639963613505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139986783998121706569636013 52495043999295639963613505)
                ·
                  refine ⟨39371282999471729972710129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52495043999295639963613505 39371282999471729972710129)
                  ·
                    refine ⟨29528462249603797479532597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39371282999471729972710129 29528462249603797479532597)
                    ·
                      refine ⟨2768293335900356013706181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29528462249603797479532597 2768293335900356013706181)
                      ·
                        rfl

theorem cell23_5391232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_5391232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391232 prefixEnd_5391232 := by exact prefixLift 5391232
  have htrace : WordTrace (prefixWord ++ tailWord_5391232) baseStart_5391232 baseEnd_5391232 := by
    simpa [prefixWord, tailWord_5391232, baseEnd_5391232] using wordTrace_append hprefix tailTrace_5391232
  have hstable : (prefixWord ++ tailWord_5391232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391232).length < 2 ^ (prefixWord ++ tailWord_5391232).sum := by decide
  have hdescent : baseEnd_5391232 < baseStart_5391232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391253 : List Nat := [1, 3, 2, 1, 1, 5, 2, 2, 2, 1, 3]
def baseStart_5391253 : Nat := 118140960795 + 5391253 * 2 ^ 59
def prefixEnd_5391253 : Nat := 4983230072969 + 3 ^ 40 * 5391253 * 2
def baseEnd_5391253 : Nat := 2768304118994100431543585

theorem tailTrace_5391253 : CollatzResearch.WordTrace tailWord_5391253 prefixEnd_5391253 2768304118994100431543585 := by
  unfold tailWord_5391253
  simp only [CollatzResearch.WordTrace]
  refine ⟨196635151137418608552642413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131090100758279072368428275 196635151137418608552642413)
  ·
    refine ⟨73738181676531978207240905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196635151137418608552642413 73738181676531978207240905)
    ·
      refine ⟨55303636257398983655430679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73738181676531978207240905 55303636257398983655430679)
      ·
        refine ⟨82955454386098475483146019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55303636257398983655430679 82955454386098475483146019)
        ·
          refine ⟨124433181579147713224719029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82955454386098475483146019 124433181579147713224719029)
          ·
            refine ⟨11665610773045098114817409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124433181579147713224719029 11665610773045098114817409)
            ·
              refine ⟨8749208079783823586113057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11665610773045098114817409 8749208079783823586113057)
              ·
                refine ⟨6561906059837867689584793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8749208079783823586113057 6561906059837867689584793)
                ·
                  refine ⟨4921429544878400767188595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6561906059837867689584793 4921429544878400767188595)
                  ·
                    refine ⟨7382144317317601150782893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4921429544878400767188595 7382144317317601150782893)
                    ·
                      refine ⟨2768304118994100431543585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7382144317317601150782893 2768304118994100431543585)
                      ·
                        rfl

theorem cell23_5391253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_5391253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391253 prefixEnd_5391253 := by exact prefixLift 5391253
  have htrace : WordTrace (prefixWord ++ tailWord_5391253) baseStart_5391253 baseEnd_5391253 := by
    simpa [prefixWord, tailWord_5391253, baseEnd_5391253] using wordTrace_append hprefix tailTrace_5391253
  have hstable : (prefixWord ++ tailWord_5391253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391253).length < 2 ^ (prefixWord ++ tailWord_5391253).sum := by decide
  have hdescent : baseEnd_5391253 < baseStart_5391253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391310 : List Nat := [4, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2]
def baseStart_5391310 : Nat := 118140960795 + 5391310 * 2 ^ 59
def prefixEnd_5391310 : Nat := 4983230072969 + 3 ^ 40 * 5391310 * 2
def baseEnd_5391310 : Nat := 2768333387391406708530823

theorem tailTrace_5391310 : CollatzResearch.WordTrace tailWord_5391310 prefixEnd_5391310 2768333387391406708530823 := by
  unfold tailWord_5391310
  simp only [CollatzResearch.WordTrace]
  refine ⟨24579653762276513410933423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131091486732141404858311589 24579653762276513410933423)
  ·
    refine ⟨36869480643414770116400135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24579653762276513410933423 36869480643414770116400135)
    ·
      refine ⟨55304220965122155174600203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36869480643414770116400135 55304220965122155174600203)
      ·
        refine ⟨82956331447683232761900305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55304220965122155174600203 82956331447683232761900305)
        ·
          refine ⟨62217248585762424571425229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82956331447683232761900305 62217248585762424571425229)
          ·
            refine ⟨23331468219660909214284461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62217248585762424571425229 23331468219660909214284461)
            ·
              refine ⟨8749300582372840955356673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23331468219660909214284461 8749300582372840955356673)
              ·
                refine ⟨6561975436779630716517505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8749300582372840955356673 6561975436779630716517505)
                ·
                  refine ⟨4921481577584723037388129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6561975436779630716517505 4921481577584723037388129)
                  ·
                    refine ⟨3691111183188542278041097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4921481577584723037388129 3691111183188542278041097)
                    ·
                      refine ⟨2768333387391406708530823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3691111183188542278041097 2768333387391406708530823)
                      ·
                        rfl

theorem cell23_5391310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_5391310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391310 prefixEnd_5391310 := by exact prefixLift 5391310
  have htrace : WordTrace (prefixWord ++ tailWord_5391310) baseStart_5391310 baseEnd_5391310 := by
    simpa [prefixWord, tailWord_5391310, baseEnd_5391310] using wordTrace_append hprefix tailTrace_5391310
  have hstable : (prefixWord ++ tailWord_5391310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391310).length < 2 ^ (prefixWord ++ tailWord_5391310).sum := by decide
  have hdescent : baseEnd_5391310 < baseStart_5391310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391316 : List Nat := [2, 4, 1, 2, 1, 3, 2, 1, 7]
def baseStart_5391316 : Nat := 118140960795 + 5391316 * 2 ^ 59
def prefixEnd_5391316 : Nat := 4983230072969 + 3 ^ 40 * 5391316 * 2
def baseEnd_5391316 : Nat := 307592940919481520561755

theorem tailTrace_5391316 : CollatzResearch.WordTrace tailWord_5391316 prefixEnd_5391316 307592940919481520561755 := by
  unfold tailWord_5391316
  simp only [CollatzResearch.WordTrace]
  refine ⟨98318724468095185156092901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131091632624126913541457201 98318724468095185156092901)
  ·
    refine ⟨18434760837767847216767419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98318724468095185156092901 18434760837767847216767419)
    ·
      refine ⟨27652141256651770825151129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18434760837767847216767419 27652141256651770825151129)
      ·
        refine ⟨20739105942488828118863347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27652141256651770825151129 20739105942488828118863347)
        ·
          refine ⟨31108658913733242178295021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20739105942488828118863347 31108658913733242178295021)
          ·
            refine ⟨11665747092649965816860633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31108658913733242178295021 11665747092649965816860633)
            ·
              refine ⟨8749310319487474362645475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11665747092649965816860633 8749310319487474362645475)
              ·
                refine ⟨13123965479231211543968213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8749310319487474362645475 13123965479231211543968213)
                ·
                  refine ⟨307592940919481520561755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13123965479231211543968213 307592940919481520561755)
                  ·
                    rfl

theorem cell23_5391316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_5391316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391316 prefixEnd_5391316 := by exact prefixLift 5391316
  have htrace : WordTrace (prefixWord ++ tailWord_5391316) baseStart_5391316 baseEnd_5391316 := by
    simpa [prefixWord, tailWord_5391316, baseEnd_5391316] using wordTrace_append hprefix tailTrace_5391316
  have hstable : (prefixWord ++ tailWord_5391316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391316).length < 2 ^ (prefixWord ++ tailWord_5391316).sum := by decide
  have hdescent : baseEnd_5391316 < baseStart_5391316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391327 : List Nat := [1, 1, 2, 3, 5, 1, 3, 1, 2, 2, 2]
def baseStart_5391327 : Nat := 118140960795 + 5391327 * 2 ^ 59
def prefixEnd_5391327 : Nat := 4983230072969 + 3 ^ 40 * 5391327 * 2
def baseEnd_5391327 : Nat := 2768342116562533142018245

theorem tailTrace_5391327 : CollatzResearch.WordTrace tailWord_5391327 prefixEnd_5391327 2768342116562533142018245 := by
  unfold tailWord_5391327
  simp only [CollatzResearch.WordTrace]
  refine ⟨196637850139150519190836235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131091900092767012793890823 196637850139150519190836235)
  ·
    refine ⟨294956775208725778786254353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196637850139150519190836235 294956775208725778786254353)
    ·
      refine ⟨221217581406544334089690765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294956775208725778786254353 221217581406544334089690765)
      ·
        refine ⟨82956593027454125283634037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221217581406544334089690765 82956593027454125283634037)
        ·
          refine ⟨7777180596323824245340691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82956593027454125283634037 7777180596323824245340691)
          ·
            refine ⟨11665770894485736368011037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7777180596323824245340691 11665770894485736368011037)
            ·
              refine ⟨4374664085432151138004139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11665770894485736368011037 4374664085432151138004139)
              ·
                refine ⟨6561996128148226707006209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4374664085432151138004139 6561996128148226707006209)
                ·
                  refine ⟨4921497096111170030254657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6561996128148226707006209 4921497096111170030254657)
                  ·
                    refine ⟨3691122822083377522690993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4921497096111170030254657 3691122822083377522690993)
                    ·
                      refine ⟨2768342116562533142018245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3691122822083377522690993 2768342116562533142018245)
                      ·
                        rfl

theorem cell23_5391327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_5391327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391327 prefixEnd_5391327 := by exact prefixLift 5391327
  have htrace : WordTrace (prefixWord ++ tailWord_5391327) baseStart_5391327 baseEnd_5391327 := by
    simpa [prefixWord, tailWord_5391327, baseEnd_5391327] using wordTrace_append hprefix tailTrace_5391327
  have hstable : (prefixWord ++ tailWord_5391327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391327).length < 2 ^ (prefixWord ++ tailWord_5391327).sum := by decide
  have hdescent : baseEnd_5391327 < baseStart_5391327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391336 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 2, 5, 2]
def baseStart_5391336 : Nat := 118140960795 + 5391336 * 2 ^ 59
def prefixEnd_5391336 : Nat := 4983230072969 + 3 ^ 40 * 5391336 * 2
def baseEnd_5391336 : Nat := 2768346737888423606805703

theorem tailTrace_5391336 : CollatzResearch.WordTrace tailWord_5391336 prefixEnd_5391336 2768346737888423606805703 := by
  unfold tailWord_5391336
  simp only [CollatzResearch.WordTrace]
  refine ⟨98319089198058956863956931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131092118930745275818609241 98319089198058956863956931)
  ·
    refine ⟨147478633797088435295935397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98319089198058956863956931 147478633797088435295935397)
    ·
      refine ⟨27652243836954081617987887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147478633797088435295935397 27652243836954081617987887)
      ·
        refine ⟨41478365755431122426981831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27652243836954081617987887 41478365755431122426981831)
        ·
          refine ⟨62217548633146683640472747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41478365755431122426981831 62217548633146683640472747)
          ·
            refine ⟨93326322949720025460709121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62217548633146683640472747 93326322949720025460709121)
            ·
              refine ⟨69994742212290019095531841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93326322949720025460709121 69994742212290019095531841)
              ·
                refine ⟨52496056659217514321648881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69994742212290019095531841 52496056659217514321648881)
                ·
                  refine ⟨39372042494413135741236661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52496056659217514321648881 39372042494413135741236661)
                  ·
                    refine ⟨3691128983851231475740937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39372042494413135741236661 3691128983851231475740937)
                    ·
                      refine ⟨2768346737888423606805703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3691128983851231475740937 2768346737888423606805703)
                      ·
                        rfl

theorem cell23_5391336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_5391336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391336 prefixEnd_5391336 := by exact prefixLift 5391336
  have htrace : WordTrace (prefixWord ++ tailWord_5391336) baseStart_5391336 baseEnd_5391336 := by
    simpa [prefixWord, tailWord_5391336, baseEnd_5391336] using wordTrace_append hprefix tailTrace_5391336
  have hstable : (prefixWord ++ tailWord_5391336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391336).length < 2 ^ (prefixWord ++ tailWord_5391336).sum := by decide
  have hdescent : baseEnd_5391336 < baseStart_5391336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391350 : List Nat := [5, 1, 1, 1, 3, 3, 1, 3, 5]
def baseStart_5391350 : Nat := 118140960795 + 5391350 * 2 ^ 59
def prefixEnd_5391350 : Nat := 4983230072969 + 3 ^ 40 * 5391350 * 2
def baseEnd_5391350 : Nat := 307594880735287394670071

theorem tailTrace_5391350 : CollatzResearch.WordTrace tailWord_5391350 prefixEnd_5391350 307594880735287394670071 := by
  unfold tailWord_5391350
  simp only [CollatzResearch.WordTrace]
  refine ⟨12289918063629199632432719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131092459345378129412615669 12289918063629199632432719)
  ·
    refine ⟨18434877095443799448649079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12289918063629199632432719 18434877095443799448649079)
    ·
      refine ⟨27652315643165699172973619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18434877095443799448649079 27652315643165699172973619)
      ·
        refine ⟨41478473464748548759460429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27652315643165699172973619 41478473464748548759460429)
        ·
          refine ⟨15554427549280705784797661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41478473464748548759460429 15554427549280705784797661)
          ·
            refine ⟨5832910330980264669299123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15554427549280705784797661 5832910330980264669299123)
            ·
              refine ⟨8749365496470397003948685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5832910330980264669299123 8749365496470397003948685)
              ·
                refine ⟨3281012061176398876480757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8749365496470397003948685 3281012061176398876480757)
                ·
                  refine ⟨307594880735287394670071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3281012061176398876480757 307594880735287394670071)
                  ·
                    rfl

theorem cell23_5391350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_5391350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391350 prefixEnd_5391350 := by exact prefixLift 5391350
  have htrace : WordTrace (prefixWord ++ tailWord_5391350) baseStart_5391350 baseEnd_5391350 := by
    simpa [prefixWord, tailWord_5391350, baseEnd_5391350] using wordTrace_append hprefix tailTrace_5391350
  have hstable : (prefixWord ++ tailWord_5391350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391350).length < 2 ^ (prefixWord ++ tailWord_5391350).sum := by decide
  have hdescent : baseEnd_5391350 < baseStart_5391350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391378 : List Nat := [3, 2, 5, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_5391378 : Nat := 118140960795 + 5391378 * 2 ^ 59
def prefixEnd_5391378 : Nat := 4983230072969 + 3 ^ 40 * 5391378 * 2
def baseEnd_5391378 : Nat := 2768368304075912442480511

theorem tailTrace_5391378 : CollatzResearch.WordTrace tailWord_5391378 prefixEnd_5391378 2768368304075912442480511 := by
  unfold tailWord_5391378
  simp only [CollatzResearch.WordTrace]
  refine ⟨49159927565491438725235697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131093140174643836600628525 49159927565491438725235697)
  ·
    refine ⟨36869945674118579043926773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49159927565491438725235697 36869945674118579043926773)
    ·
      refine ⟨3456557406948616785368135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36869945674118579043926773 3456557406948616785368135)
      ·
        refine ⟨5184836110422925178052203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3456557406948616785368135 5184836110422925178052203)
        ·
          refine ⟨7777254165634387767078305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5184836110422925178052203 7777254165634387767078305)
          ·
            refine ⟨5832940624225790825308729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7777254165634387767078305 5832940624225790825308729)
            ·
              refine ⟨4374705468169343118981547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5832940624225790825308729 4374705468169343118981547)
              ·
                refine ⟨6562058202254014678472321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4374705468169343118981547 6562058202254014678472321)
                ·
                  refine ⟨4921543651690511008854241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6562058202254014678472321 4921543651690511008854241)
                  ·
                    refine ⟨3691157738767883256640681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4921543651690511008854241 3691157738767883256640681)
                    ·
                      refine ⟨2768368304075912442480511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3691157738767883256640681 2768368304075912442480511)
                      ·
                        rfl

theorem cell23_5391378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_5391378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391378 prefixEnd_5391378 := by exact prefixLift 5391378
  have htrace : WordTrace (prefixWord ++ tailWord_5391378) baseStart_5391378 baseEnd_5391378 := by
    simpa [prefixWord, tailWord_5391378, baseEnd_5391378] using wordTrace_append hprefix tailTrace_5391378
  have hstable : (prefixWord ++ tailWord_5391378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391378).length < 2 ^ (prefixWord ++ tailWord_5391378).sum := by decide
  have hdescent : baseEnd_5391378 < baseStart_5391378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391386 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3]
def baseStart_5391386 : Nat := 118140960795 + 5391386 * 2 ^ 59
def prefixEnd_5391386 : Nat := 4983230072969 + 3 ^ 40 * 5391386 * 2
def baseEnd_5391386 : Nat := 2768372411921148411180473

theorem tailTrace_5391386 : CollatzResearch.WordTrace tailWord_5391386 prefixEnd_5391386 2768372411921148411180473 := by
  unfold tailWord_5391386
  simp only [CollatzResearch.WordTrace]
  refine ⟨49160000511484193066808503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131093334697291181511489341 49160000511484193066808503)
  ·
    refine ⟨73740000767226289600212755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49160000511484193066808503 73740000767226289600212755)
    ·
      refine ⟨110610001150839434400319133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73740000767226289600212755 110610001150839434400319133)
      ·
        refine ⟨41478750431564787900119675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110610001150839434400319133 41478750431564787900119675)
        ·
          refine ⟨62218125647347181850179513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41478750431564787900119675 62218125647347181850179513)
          ·
            refine ⟨46663594235510386387634635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62218125647347181850179513 46663594235510386387634635)
            ·
              refine ⟨69995391353265579581451953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46663594235510386387634635 69995391353265579581451953)
              ·
                refine ⟨52496543514949184686088965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69995391353265579581451953 52496543514949184686088965)
                ·
                  refine ⟨9843101909052972128641681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52496543514949184686088965 9843101909052972128641681)
                  ·
                    refine ⟨7382326431789729096481261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9843101909052972128641681 7382326431789729096481261)
                    ·
                      refine ⟨2768372411921148411180473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7382326431789729096481261 2768372411921148411180473)
                      ·
                        rfl

theorem cell23_5391386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_5391386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391386 prefixEnd_5391386 := by exact prefixLift 5391386
  have htrace : WordTrace (prefixWord ++ tailWord_5391386) baseStart_5391386 baseEnd_5391386 := by
    simpa [prefixWord, tailWord_5391386, baseEnd_5391386] using wordTrace_append hprefix tailTrace_5391386
  have hstable : (prefixWord ++ tailWord_5391386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391386).length < 2 ^ (prefixWord ++ tailWord_5391386).sum := by decide
  have hdescent : baseEnd_5391386 < baseStart_5391386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391419 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 7, 5]
def baseStart_5391419 : Nat := 118140960795 + 5391419 * 2 ^ 59
def prefixEnd_5391419 : Nat := 4983230072969 + 3 ^ 40 * 5391419 * 2
def baseEnd_5391419 : Nat := 922796452260915594022607

theorem tailTrace_5391419 : CollatzResearch.WordTrace tailWord_5391419 prefixEnd_5391419 922796452260915594022607 := by
  unfold tailWord_5391419
  simp only [CollatzResearch.WordTrace]
  refine ⟨196641205654817218903185311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131094137103211479268790207 196641205654817218903185311)
  ·
    refine ⟨294961808482225828354777967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196641205654817218903185311 294961808482225828354777967)
    ·
      refine ⟨442442712723338742532166951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294961808482225828354777967 442442712723338742532166951)
      ·
        refine ⟨663664069085008113798250427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442442712723338742532166951 663664069085008113798250427)
        ·
          refine ⟨995496103627512170697375641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663664069085008113798250427 995496103627512170697375641)
          ·
            refine ⟨746622077720634128023031731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 995496103627512170697375641 746622077720634128023031731)
            ·
              refine ⟨1119933116580951192034547597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 746622077720634128023031731 1119933116580951192034547597)
              ·
                refine ⟨419974918717856697012955349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1119933116580951192034547597 419974918717856697012955349)
                ·
                  refine ⟨9843162157449766336241141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 419974918717856697012955349 9843162157449766336241141)
                  ·
                    refine ⟨922796452260915594022607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9843162157449766336241141 922796452260915594022607)
                    ·
                      rfl

theorem cell23_5391419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 5].length) (baseStart_5391419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391419 prefixEnd_5391419 := by exact prefixLift 5391419
  have htrace : WordTrace (prefixWord ++ tailWord_5391419) baseStart_5391419 baseEnd_5391419 := by
    simpa [prefixWord, tailWord_5391419, baseEnd_5391419] using wordTrace_append hprefix tailTrace_5391419
  have hstable : (prefixWord ++ tailWord_5391419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391419).length < 2 ^ (prefixWord ++ tailWord_5391419).sum := by decide
  have hdescent : baseEnd_5391419 < baseStart_5391419 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391439 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 4]
def baseStart_5391439 : Nat := 118140960795 + 5391439 * 2 ^ 59
def prefixEnd_5391439 : Nat := 4983230072969 + 3 ^ 40 * 5391439 * 2
def baseEnd_5391439 : Nat := 2768399626395836703817729

theorem tailTrace_5391439 : CollatzResearch.WordTrace tailWord_5391439 prefixEnd_5391439 2768399626395836703817729 := by
  unfold tailWord_5391439
  simp only [CollatzResearch.WordTrace]
  refine ⟨196641935114744762318913371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131094623409829841545942247 196641935114744762318913371)
  ·
    refine ⟨294962902672117143478370057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196641935114744762318913371 294962902672117143478370057)
    ·
      refine ⟨221222177004087857608777543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294962902672117143478370057 221222177004087857608777543)
      ·
        refine ⟨331833265506131786413166315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221222177004087857608777543 331833265506131786413166315)
        ·
          refine ⟨497749898259197679619749473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331833265506131786413166315 497749898259197679619749473)
          ·
            refine ⟨373312423694398259714812105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497749898259197679619749473 373312423694398259714812105)
            ·
              refine ⟨279984317770798694786109079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373312423694398259714812105 279984317770798694786109079)
              ·
                refine ⟨419976476656198042179163619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279984317770798694786109079 419976476656198042179163619)
                ·
                  refine ⟨629964714984297063268745429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419976476656198042179163619 629964714984297063268745429)
                  ·
                    refine ⟨14764798007444462420361221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 629964714984297063268745429 14764798007444462420361221)
                    ·
                      refine ⟨2768399626395836703817729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14764798007444462420361221 2768399626395836703817729)
                      ·
                        rfl

theorem cell23_5391439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 4].length) (baseStart_5391439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391439 prefixEnd_5391439 := by exact prefixLift 5391439
  have htrace : WordTrace (prefixWord ++ tailWord_5391439) baseStart_5391439 baseEnd_5391439 := by
    simpa [prefixWord, tailWord_5391439, baseEnd_5391439] using wordTrace_append hprefix tailTrace_5391439
  have hstable : (prefixWord ++ tailWord_5391439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391439).length < 2 ^ (prefixWord ++ tailWord_5391439).sum := by decide
  have hdescent : baseEnd_5391439 < baseStart_5391439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391454 : List Nat := [4, 4, 1, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_5391454 : Nat := 118140960795 + 5391454 * 2 ^ 59
def prefixEnd_5391454 : Nat := 4983230072969 + 3 ^ 40 * 5391454 * 2
def baseEnd_5391454 : Nat := 2768407328605654145130161

theorem tailTrace_5391454 : CollatzResearch.WordTrace tailWord_5391454 prefixEnd_5391454 2768407328605654145130161 := by
  unfold tailWord_5391454
  simp only [CollatzResearch.WordTrace]
  refine ⟨24580310276211302485088677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131094988139793613253806277 24580310276211302485088677)
  ·
    refine ⟨4608808176789619215954127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24580310276211302485088677 4608808176789619215954127)
    ·
      refine ⟨6913212265184428823931191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4608808176789619215954127 6913212265184428823931191)
      ·
        refine ⟨10369818397776643235896787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6913212265184428823931191 10369818397776643235896787)
        ·
          refine ⟨15554727596664964853845181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10369818397776643235896787 15554727596664964853845181)
          ·
            refine ⟨5833022848749361820191943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15554727596664964853845181 5833022848749361820191943)
            ·
              refine ⟨8749534273124042730287915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5833022848749361820191943 8749534273124042730287915)
              ·
                refine ⟨13124301409686064095431873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8749534273124042730287915 13124301409686064095431873)
                ·
                  refine ⟨9843226057264548071573905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13124301409686064095431873 9843226057264548071573905)
                  ·
                    refine ⟨7382419542948411053680429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9843226057264548071573905 7382419542948411053680429)
                    ·
                      refine ⟨2768407328605654145130161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7382419542948411053680429 2768407328605654145130161)
                      ·
                        rfl

theorem cell23_5391454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_5391454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391454 prefixEnd_5391454 := by exact prefixLift 5391454
  have htrace : WordTrace (prefixWord ++ tailWord_5391454) baseStart_5391454 baseEnd_5391454 := by
    simpa [prefixWord, tailWord_5391454, baseEnd_5391454] using wordTrace_append hprefix tailTrace_5391454
  have hstable : (prefixWord ++ tailWord_5391454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391454).length < 2 ^ (prefixWord ++ tailWord_5391454).sum := by decide
  have hdescent : baseEnd_5391454 < baseStart_5391454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391456 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 4]
def baseStart_5391456 : Nat := 118140960795 + 5391456 * 2 ^ 59
def prefixEnd_5391456 : Nat := 4983230072969 + 3 ^ 40 * 5391456 * 2
def baseEnd_5391456 : Nat := 2768408355566963137305151

theorem tailTrace_5391456 : CollatzResearch.WordTrace tailWord_5391456 prefixEnd_5391456 2768408355566963137305151 := by
  unfold tailWord_5391456
  simp only [CollatzResearch.WordTrace]
  refine ⟨98321277577841587111141111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131095036770455449481521481 98321277577841587111141111)
  ·
    refine ⟨147481916366762380666711667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98321277577841587111141111 147481916366762380666711667)
    ·
      refine ⟨221222874550143571000067501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147481916366762380666711667 221222874550143571000067501)
      ·
        refine ⟨82958577956303839125025313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221222874550143571000067501 82958577956303839125025313)
        ·
          refine ⟨62218933467227879343768985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82958577956303839125025313 62218933467227879343768985)
          ·
            refine ⟨46664200100420909507826739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62218933467227879343768985 46664200100420909507826739)
            ·
              refine ⟨69996300150631364261740109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46664200100420909507826739 69996300150631364261740109)
              ·
                refine ⟨26248612556486761598152541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69996300150631364261740109 26248612556486761598152541)
                ·
                  refine ⟨9843229708682535599307203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26248612556486761598152541 9843229708682535599307203)
                  ·
                    refine ⟨14764844563023803398960805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9843229708682535599307203 14764844563023803398960805)
                    ·
                      refine ⟨2768408355566963137305151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14764844563023803398960805 2768408355566963137305151)
                      ·
                        rfl

theorem cell23_5391456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_5391456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391456 prefixEnd_5391456 := by exact prefixLift 5391456
  have htrace : WordTrace (prefixWord ++ tailWord_5391456) baseStart_5391456 baseEnd_5391456 := by
    simpa [prefixWord, tailWord_5391456, baseEnd_5391456] using wordTrace_append hprefix tailTrace_5391456
  have hstable : (prefixWord ++ tailWord_5391456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391456).length < 2 ^ (prefixWord ++ tailWord_5391456).sum := by decide
  have hdescent : baseEnd_5391456 < baseStart_5391456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391470 : List Nat := [4, 1, 2, 2, 1, 2, 4, 1, 1, 5]
def baseStart_5391470 : Nat := 118140960795 + 5391470 * 2 ^ 59
def prefixEnd_5391470 : Nat := 4983230072969 + 3 ^ 40 * 5391470 * 2
def baseEnd_5391470 : Nat := 922805181432042027510029

theorem tailTrace_5391470 : CollatzResearch.WordTrace tailWord_5391470 prefixEnd_5391470 922805181432042027510029 := by
  unfold tailWord_5391470
  simp only [CollatzResearch.WordTrace]
  refine ⟨24580383222204056826661483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131095377185088303075527909 24580383222204056826661483)
  ·
    refine ⟨36870574833306085239992225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24580383222204056826661483 36870574833306085239992225)
    ·
      refine ⟨27652931124979563929994169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36870574833306085239992225 27652931124979563929994169)
      ·
        refine ⟨20739698343734672947495627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27652931124979563929994169 20739698343734672947495627)
        ·
          refine ⟨31109547515602009421243441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20739698343734672947495627 31109547515602009421243441)
          ·
            refine ⟨23332160636701507065932581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31109547515602009421243441 23332160636701507065932581)
            ·
              refine ⟨4374780119381532574862359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23332160636701507065932581 4374780119381532574862359)
              ·
                refine ⟨6562170179072298862293539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4374780119381532574862359 6562170179072298862293539)
                ·
                  refine ⟨9843255268608448293440309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6562170179072298862293539 9843255268608448293440309)
                  ·
                    refine ⟨922805181432042027510029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9843255268608448293440309 922805181432042027510029)
                    ·
                      rfl

theorem cell23_5391470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_5391470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391470 prefixEnd_5391470 := by exact prefixLift 5391470
  have htrace : WordTrace (prefixWord ++ tailWord_5391470) baseStart_5391470 baseEnd_5391470 := by
    simpa [prefixWord, tailWord_5391470, baseEnd_5391470] using wordTrace_append hprefix tailTrace_5391470
  have hstable : (prefixWord ++ tailWord_5391470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391470).length < 2 ^ (prefixWord ++ tailWord_5391470).sum := by decide
  have hdescent : baseEnd_5391470 < baseStart_5391470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391479 : List Nat := [1, 1, 3, 1, 1, 4, 12]
def baseStart_5391479 : Nat := 118140960795 + 5391479 * 2 ^ 59
def prefixEnd_5391479 : Nat := 4983230072969 + 3 ^ 40 * 5391479 * 2
def baseEnd_5391479 : Nat := 34178026736074278361945

theorem tailTrace_5391479 : CollatzResearch.WordTrace tailWord_5391479 prefixEnd_5391479 34178026736074278361945 := by
  unfold tailWord_5391479
  simp only [CollatzResearch.WordTrace]
  refine ⟨196643394034599849150369491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131095596023066566100246327 196643394034599849150369491)
  ·
    refine ⟨294965091051899773725554237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196643394034599849150369491 294965091051899773725554237)
    ·
      refine ⟨110611909144462415147082839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294965091051899773725554237 110611909144462415147082839)
      ·
        refine ⟨165917863716693622720624259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110611909144462415147082839 165917863716693622720624259)
        ·
          refine ⟨248876795575040434080936389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165917863716693622720624259 248876795575040434080936389)
          ·
            refine ⟨46664399170320081390175573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 248876795575040434080936389 46664399170320081390175573)
            ·
              refine ⟨34178026736074278361945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 46664399170320081390175573 34178026736074278361945)
              ·
                rfl

theorem cell23_5391479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 12].length) (baseStart_5391479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391479 prefixEnd_5391479 := by exact prefixLift 5391479
  have htrace : WordTrace (prefixWord ++ tailWord_5391479) baseStart_5391479 baseEnd_5391479 := by
    simpa [prefixWord, tailWord_5391479, baseEnd_5391479] using wordTrace_append hprefix tailTrace_5391479
  have hstable : (prefixWord ++ tailWord_5391479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391479).length < 2 ^ (prefixWord ++ tailWord_5391479).sum := by decide
  have hdescent : baseEnd_5391479 < baseStart_5391479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391493 : List Nat := [1, 3, 1, 1, 6, 1, 1, 2, 1, 1, 5]
def baseStart_5391493 : Nat := 118140960795 + 5391493 * 2 ^ 59
def prefixEnd_5391493 : Nat := 4983230072969 + 3 ^ 40 * 5391493 * 2
def baseEnd_5391493 : Nat := 2768427354351179492542481

theorem tailTrace_5391493 : CollatzResearch.WordTrace tailWord_5391493 prefixEnd_5391493 2768427354351179492542481 := by
  unfold tailWord_5391493
  simp only [CollatzResearch.WordTrace]
  refine ⟨196643904656549129541379133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131095936437699419694252755 196643904656549129541379133)
  ·
    refine ⟨73741464246205923578017175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196643904656549129541379133 73741464246205923578017175)
    ·
      refine ⟨110612196369308885367025763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73741464246205923578017175 110612196369308885367025763)
      ·
        refine ⟨165918294553963328050538645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110612196369308885367025763 165918294553963328050538645)
        ·
          refine ⟨7777420057217031002368999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 165918294553963328050538645 7777420057217031002368999)
          ·
            refine ⟨11666130085825546503553499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7777420057217031002368999 11666130085825546503553499)
            ·
              refine ⟨17499195128738319755330249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11666130085825546503553499 17499195128738319755330249)
              ·
                refine ⟨13124396346553739816497687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17499195128738319755330249 13124396346553739816497687)
                ·
                  refine ⟨19686594519830609724746531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13124396346553739816497687 19686594519830609724746531)
                  ·
                    refine ⟨29529891779745914587119797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19686594519830609724746531 29529891779745914587119797)
                    ·
                      refine ⟨2768427354351179492542481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29529891779745914587119797 2768427354351179492542481)
                      ·
                        rfl

theorem cell23_5391493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_5391493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391493 prefixEnd_5391493 := by exact prefixLift 5391493
  have htrace : WordTrace (prefixWord ++ tailWord_5391493) baseStart_5391493 baseEnd_5391493 := by
    simpa [prefixWord, tailWord_5391493, baseEnd_5391493] using wordTrace_append hprefix tailTrace_5391493
  have hstable : (prefixWord ++ tailWord_5391493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391493).length < 2 ^ (prefixWord ++ tailWord_5391493).sum := by decide
  have hdescent : baseEnd_5391493 < baseStart_5391493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391524 : List Nat := [2, 3, 1, 2, 3, 1, 3, 3, 1, 2, 2]
def baseStart_5391524 : Nat := 118140960795 + 5391524 * 2 ^ 59
def prefixEnd_5391524 : Nat := 4983230072969 + 3 ^ 40 * 5391524 * 2
def baseEnd_5391524 : Nat := 2768443272251468871254839

theorem tailTrace_5391524 : CollatzResearch.WordTrace tailWord_5391524 prefixEnd_5391524 2768443272251468871254839 := by
  unfold tailWord_5391524
  simp only [CollatzResearch.WordTrace]
  refine ⟨98322517659718410917878813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131096690212957881223838417 98322517659718410917878813)
  ·
    refine ⟨36870944122394404094204555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98322517659718410917878813 36870944122394404094204555)
    ·
      refine ⟨55306416183591606141306833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36870944122394404094204555 55306416183591606141306833)
      ·
        refine ⟨41479812137693704605980125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55306416183591606141306833 41479812137693704605980125)
        ·
          refine ⟨15554929551635139227242547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41479812137693704605980125 15554929551635139227242547)
          ·
            refine ⟨23332394327452708840863821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15554929551635139227242547 23332394327452708840863821)
            ·
              refine ⟨8749647872794765815323933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23332394327452708840863821 8749647872794765815323933)
              ·
                refine ⟨3281117952298037180746475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8749647872794765815323933 3281117952298037180746475)
                ·
                  refine ⟨4921676928447055771119713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3281117952298037180746475 4921676928447055771119713)
                  ·
                    refine ⟨3691257696335291828339785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4921676928447055771119713 3691257696335291828339785)
                    ·
                      refine ⟨2768443272251468871254839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3691257696335291828339785 2768443272251468871254839)
                      ·
                        rfl

theorem cell23_5391524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_5391524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391524 prefixEnd_5391524 := by exact prefixLift 5391524
  have htrace : WordTrace (prefixWord ++ tailWord_5391524) baseStart_5391524 baseEnd_5391524 := by
    simpa [prefixWord, tailWord_5391524, baseEnd_5391524] using wordTrace_append hprefix tailTrace_5391524
  have hstable : (prefixWord ++ tailWord_5391524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391524).length < 2 ^ (prefixWord ++ tailWord_5391524).sum := by decide
  have hdescent : baseEnd_5391524 < baseStart_5391524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391546 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4]
def baseStart_5391546 : Nat := 118140960795 + 5391546 * 2 ^ 59
def prefixEnd_5391546 : Nat := 4983230072969 + 3 ^ 40 * 5391546 * 2
def baseEnd_5391546 : Nat := 2768454568825867785179737

theorem tailTrace_5391546 : CollatzResearch.WordTrace tailWord_5391546 prefixEnd_5391546 2768454568825867785179737 := by
  unfold tailWord_5391546
  simp only [CollatzResearch.WordTrace]
  refine ⟨49161459431339279898264623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131097225150238079728705661 49161459431339279898264623)
  ·
    refine ⟨73742189147008919847396935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49161459431339279898264623 73742189147008919847396935)
    ·
      refine ⟨110613283720513379771095403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73742189147008919847396935 110613283720513379771095403)
      ·
        refine ⟨165919925580770069656643105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110613283720513379771095403 165919925580770069656643105)
        ·
          refine ⟨124439944185577552242482329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165919925580770069656643105 124439944185577552242482329)
          ·
            refine ⟨93329958139183164181861747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124439944185577552242482329 93329958139183164181861747)
            ·
              refine ⟨139994937208774746272792621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93329958139183164181861747 139994937208774746272792621)
              ·
                refine ⟨52498101453290529852297233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139994937208774746272792621 52498101453290529852297233)
                ·
                  refine ⟨39373576089967897389222925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52498101453290529852297233 39373576089967897389222925)
                  ·
                    refine ⟨14765091033737961520958597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39373576089967897389222925 14765091033737961520958597)
                    ·
                      refine ⟨2768454568825867785179737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14765091033737961520958597 2768454568825867785179737)
                      ·
                        rfl

theorem cell23_5391546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_5391546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391546 prefixEnd_5391546 := by exact prefixLift 5391546
  have htrace : WordTrace (prefixWord ++ tailWord_5391546) baseStart_5391546 baseEnd_5391546 := by
    simpa [prefixWord, tailWord_5391546, baseEnd_5391546] using wordTrace_append hprefix tailTrace_5391546
  have hstable : (prefixWord ++ tailWord_5391546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391546).length < 2 ^ (prefixWord ++ tailWord_5391546).sum := by decide
  have hdescent : baseEnd_5391546 < baseStart_5391546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391558 : List Nat := [6, 1, 2, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_5391558 : Nat := 118140960795 + 5391558 * 2 ^ 59
def prefixEnd_5391558 : Nat := 4983230072969 + 3 ^ 40 * 5391558 * 2
def baseEnd_5391558 : Nat := 2768460730593721738229683

theorem tailTrace_5391558 : CollatzResearch.WordTrace tailWord_5391558 prefixEnd_5391558 2768460730593721738229683 := by
  unfold tailWord_5391558
  simp only [CollatzResearch.WordTrace]
  refine ⟨6145196106291051426327979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 131097516934209097094996885 6145196106291051426327979)
  ·
    refine ⟨9217794159436577139491969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6145196106291051426327979 9217794159436577139491969)
    ·
      refine ⟨6913345619577432854618977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9217794159436577139491969 6913345619577432854618977)
      ·
        refine ⟨5185009214683074640964233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6913345619577432854618977 5185009214683074640964233)
        ·
          refine ⟨3888756911012305980723175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5185009214683074640964233 3888756911012305980723175)
          ·
            refine ⟨5833135366518458971084763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3888756911012305980723175 5833135366518458971084763)
            ·
              refine ⟨8749703049777688456627145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5833135366518458971084763 8749703049777688456627145)
              ·
                refine ⟨6562277287333266342470359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8749703049777688456627145 6562277287333266342470359)
                ·
                  refine ⟨9843415930999899513705539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6562277287333266342470359 9843415930999899513705539)
                  ·
                    refine ⟨14765123896499849270558309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9843415930999899513705539 14765123896499849270558309)
                    ·
                      refine ⟨2768460730593721738229683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14765123896499849270558309 2768460730593721738229683)
                      ·
                        rfl

theorem cell23_5391558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_5391558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391558 prefixEnd_5391558 := by exact prefixLift 5391558
  have htrace : WordTrace (prefixWord ++ tailWord_5391558) baseStart_5391558 baseEnd_5391558 := by
    simpa [prefixWord, tailWord_5391558, baseEnd_5391558] using wordTrace_append hprefix tailTrace_5391558
  have hstable : (prefixWord ++ tailWord_5391558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391558).length < 2 ^ (prefixWord ++ tailWord_5391558).sum := by decide
  have hdescent : baseEnd_5391558 < baseStart_5391558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391614 : List Nat := [4, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_5391614 : Nat := 118140960795 + 5391614 * 2 ^ 59
def prefixEnd_5391614 : Nat := 4983230072969 + 3 ^ 40 * 5391614 * 2
def baseEnd_5391614 : Nat := 2768489485510373519129425

theorem tailTrace_5391614 : CollatzResearch.WordTrace tailWord_5391614 prefixEnd_5391614 2768489485510373519129425 := by
  unfold tailWord_5391614
  simp only [CollatzResearch.WordTrace]
  refine ⟨24581039736138845900816737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131098878592740511471022597 24581039736138845900816737)
  ·
    refine ⟨18435779802104134425612553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24581039736138845900816737 18435779802104134425612553)
    ·
      refine ⟨13826834851578100819209415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18435779802104134425612553 13826834851578100819209415)
      ·
        refine ⟨20740252277367151228814123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13826834851578100819209415 20740252277367151228814123)
        ·
          refine ⟨31110378416050726843221185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20740252277367151228814123 31110378416050726843221185)
          ·
            refine ⟨23332783812038045132415889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31110378416050726843221185 23332783812038045132415889)
            ·
              refine ⟨17499587859028533849311917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23332783812038045132415889 17499587859028533849311917)
              ·
                refine ⟨6562345447135700193491969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17499587859028533849311917 6562345447135700193491969)
                ·
                  refine ⟨4921759085351775145118977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6562345447135700193491969 4921759085351775145118977)
                  ·
                    refine ⟨3691319314013831358839233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4921759085351775145118977 3691319314013831358839233)
                    ·
                      refine ⟨2768489485510373519129425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3691319314013831358839233 2768489485510373519129425)
                      ·
                        rfl

theorem cell23_5391614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_5391614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391614 prefixEnd_5391614 := by exact prefixLift 5391614
  have htrace : WordTrace (prefixWord ++ tailWord_5391614) baseStart_5391614 baseEnd_5391614 := by
    simpa [prefixWord, tailWord_5391614, baseEnd_5391614] using wordTrace_append hprefix tailTrace_5391614
  have hstable : (prefixWord ++ tailWord_5391614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391614).length < 2 ^ (prefixWord ++ tailWord_5391614).sum := by decide
  have hdescent : baseEnd_5391614 < baseStart_5391614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391616 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 1, 7]
def baseStart_5391616 : Nat := 118140960795 + 5391616 * 2 ^ 59
def prefixEnd_5391616 : Nat := 4983230072969 + 3 ^ 40 * 5391616 * 2
def baseEnd_5391616 : Nat := 922830170823894170434805

theorem tailTrace_5391616 : CollatzResearch.WordTrace tailWord_5391616 prefixEnd_5391616 922830170823894170434805 := by
  unfold tailWord_5391616
  simp only [CollatzResearch.WordTrace]
  refine ⟨98324195417551760774053351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131098927223402347698737801 98324195417551760774053351)
  ·
    refine ⟨147486293126327641161080027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98324195417551760774053351 147486293126327641161080027)
    ·
      refine ⟨221229439689491461741620041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147486293126327641161080027 221229439689491461741620041)
      ·
        refine ⟨165922079767118596306215031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221229439689491461741620041 165922079767118596306215031)
        ·
          refine ⟨248883119650677894459322547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165922079767118596306215031 248883119650677894459322547)
          ·
            refine ⟨373324679476016841688983821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248883119650677894459322547 373324679476016841688983821)
            ·
              refine ⟨139996754803506315633368933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 373324679476016841688983821 139996754803506315633368933)
              ·
                refine ⟨26249391525657434181256675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139996754803506315633368933 26249391525657434181256675)
                ·
                  refine ⟨39374087288486151271885013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26249391525657434181256675 39374087288486151271885013)
                  ·
                    refine ⟨922830170823894170434805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39374087288486151271885013 922830170823894170434805)
                    ·
                      rfl

theorem cell23_5391616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 1, 7].length) (baseStart_5391616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391616 prefixEnd_5391616 := by exact prefixLift 5391616
  have htrace : WordTrace (prefixWord ++ tailWord_5391616) baseStart_5391616 baseEnd_5391616 := by
    simpa [prefixWord, tailWord_5391616, baseEnd_5391616] using wordTrace_append hprefix tailTrace_5391616
  have hstable : (prefixWord ++ tailWord_5391616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391616).length < 2 ^ (prefixWord ++ tailWord_5391616).sum := by decide
  have hdescent : baseEnd_5391616 < baseStart_5391616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391747 : List Nat := [1, 1, 1, 3, 5, 1, 1, 3, 2, 3, 2]
def baseStart_5391747 : Nat := 118140960795 + 5391747 * 2 ^ 59
def prefixEnd_5391747 : Nat := 4983230072969 + 3 ^ 40 * 5391747 * 2
def baseEnd_5391747 : Nat := 2768557778437421498766313

theorem tailTrace_5391747 : CollatzResearch.WordTrace tailWord_5391747 prefixEnd_5391747 2768557778437421498766313 := by
  unfold tailWord_5391747
  simp only [CollatzResearch.WordTrace]
  refine ⟨196653168797628930921125495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131102112531752620614083663 196653168797628930921125495)
  ·
    refine ⟨294979753196443396381688243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196653168797628930921125495 294979753196443396381688243)
    ·
      refine ⟨442469629794665094572532365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294979753196443396381688243 442469629794665094572532365)
      ·
        refine ⟨165926111172999410464699637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 442469629794665094572532365 165926111172999410464699637)
        ·
          refine ⟨15555572922468694731065591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 165926111172999410464699637 15555572922468694731065591)
          ·
            refine ⟨23333359383703042096598387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15555572922468694731065591 23333359383703042096598387)
            ·
              refine ⟨35000039075554563144897581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23333359383703042096598387 35000039075554563144897581)
              ·
                refine ⟨13125014653332961179336593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35000039075554563144897581 13125014653332961179336593)
                ·
                  refine ⟨9843760989999720884502445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13125014653332961179336593 9843760989999720884502445)
                  ·
                    refine ⟨3691410371249895331688417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9843760989999720884502445 3691410371249895331688417)
                    ·
                      refine ⟨2768557778437421498766313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3691410371249895331688417 2768557778437421498766313)
                      ·
                        rfl

theorem cell23_5391747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 3, 2].length) (baseStart_5391747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391747 prefixEnd_5391747 := by exact prefixLift 5391747
  have htrace : WordTrace (prefixWord ++ tailWord_5391747) baseStart_5391747 baseEnd_5391747 := by
    simpa [prefixWord, tailWord_5391747, baseEnd_5391747] using wordTrace_append hprefix tailTrace_5391747
  have hstable : (prefixWord ++ tailWord_5391747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391747).length < 2 ^ (prefixWord ++ tailWord_5391747).sum := by decide
  have hdescent : baseEnd_5391747 < baseStart_5391747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391764 : List Nat := [2, 4, 2, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_5391764 : Nat := 118140960795 + 5391764 * 2 ^ 59
def prefixEnd_5391764 : Nat := 4983230072969 + 3 ^ 40 * 5391764 * 2
def baseEnd_5391764 : Nat := 2768566507608547932253735

theorem tailTrace_5391764 : CollatzResearch.WordTrace tailWord_5391764 prefixEnd_5391764 2768566507608547932253735 := by
  unfold tailWord_5391764
  simp only [CollatzResearch.WordTrace]
  refine ⟨98326894419283671412247173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131102525892378228549662897 98326894419283671412247173)
  ·
    refine ⟨18436292703615688389796345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98326894419283671412247173 18436292703615688389796345)
    ·
      refine ⟨13827219527711766292347259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18436292703615688389796345 13827219527711766292347259)
      ·
        refine ⟨20740829291567649438520889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13827219527711766292347259 20740829291567649438520889)
        ·
          refine ⟨15555621968675737078890667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20740829291567649438520889 15555621968675737078890667)
          ·
            refine ⟨23333432953013605618336001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15555621968675737078890667 23333432953013605618336001)
            ·
              refine ⟨17500074714760204213752001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23333432953013605618336001 17500074714760204213752001)
              ·
                refine ⟨13125056036070153160314001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17500074714760204213752001 13125056036070153160314001)
                ·
                  refine ⟨9843792027052614870235501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13125056036070153160314001 9843792027052614870235501)
                  ·
                    refine ⟨3691422010144730576338313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9843792027052614870235501 3691422010144730576338313)
                    ·
                      refine ⟨2768566507608547932253735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3691422010144730576338313 2768566507608547932253735)
                      ·
                        rfl

theorem cell23_5391764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_5391764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391764 prefixEnd_5391764 := by exact prefixLift 5391764
  have htrace : WordTrace (prefixWord ++ tailWord_5391764) baseStart_5391764 baseEnd_5391764 := by
    simpa [prefixWord, tailWord_5391764, baseEnd_5391764] using wordTrace_append hprefix tailTrace_5391764
  have hstable : (prefixWord ++ tailWord_5391764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391764).length < 2 ^ (prefixWord ++ tailWord_5391764).sum := by decide
  have hdescent : baseEnd_5391764 < baseStart_5391764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391797 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_5391797 : Nat := 118140960795 + 5391797 * 2 ^ 59
def prefixEnd_5391797 : Nat := 4983230072969 + 3 ^ 40 * 5391797 * 2
def baseEnd_5391797 : Nat := 2768583452470146303141083

theorem tailTrace_5391797 : CollatzResearch.WordTrace tailWord_5391797 prefixEnd_5391797 2768583452470146303141083 := by
  unfold tailWord_5391797
  simp only [CollatzResearch.WordTrace]
  refine ⟨196654992447447789460445645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131103328298298526306963763 196654992447447789460445645)
  ·
    refine ⟨73745622167792921047667117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196654992447447789460445645 73745622167792921047667117)
    ·
      refine ⟨27654608312922345392875169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73745622167792921047667117 27654608312922345392875169)
      ·
        refine ⟨20740956234691759044656377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27654608312922345392875169 20740956234691759044656377)
        ·
          refine ⟨15555717176018819283492283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20740956234691759044656377 15555717176018819283492283)
          ·
            refine ⟨23333575764028228925238425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15555717176018819283492283 23333575764028228925238425)
            ·
              refine ⟨17500181823021171693928819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23333575764028228925238425 17500181823021171693928819)
              ·
                refine ⟨26250272734531757540893229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17500181823021171693928819 26250272734531757540893229)
                ·
                  refine ⟨9843852275449409077834961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26250272734531757540893229 9843852275449409077834961)
                  ·
                    refine ⟨7382889206587056808376221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9843852275449409077834961 7382889206587056808376221)
                    ·
                      refine ⟨2768583452470146303141083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7382889206587056808376221 2768583452470146303141083)
                      ·
                        rfl

theorem cell23_5391797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_5391797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391797 prefixEnd_5391797 := by exact prefixLift 5391797
  have htrace : WordTrace (prefixWord ++ tailWord_5391797) baseStart_5391797 baseEnd_5391797 := by
    simpa [prefixWord, tailWord_5391797, baseEnd_5391797] using wordTrace_append hprefix tailTrace_5391797
  have hstable : (prefixWord ++ tailWord_5391797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391797).length < 2 ^ (prefixWord ++ tailWord_5391797).sum := by decide
  have hdescent : baseEnd_5391797 < baseStart_5391797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391880 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_5391880 : Nat := 118140960795 + 5391880 * 2 ^ 59
def prefixEnd_5391880 : Nat := 4983230072969 + 3 ^ 40 * 5391880 * 2
def baseEnd_5391880 : Nat := 2768626071364469478403201

theorem tailTrace_5391880 : CollatzResearch.WordTrace tailWord_5391880 prefixEnd_5391880 2768626071364469478403201 := by
  unfold tailWord_5391880
  simp only [CollatzResearch.WordTrace]
  refine ⟨98329009853073547317858547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131105346470764729757144729 98329009853073547317858547)
  ·
    refine ⟨147493514779610320976787821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98329009853073547317858547 147493514779610320976787821)
    ·
      refine ⟨55310068042353870366295433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147493514779610320976787821 55310068042353870366295433)
      ·
        refine ⟨41482551031765402774721575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55310068042353870366295433 41482551031765402774721575)
        ·
          refine ⟨62223826547648104162082363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41482551031765402774721575 62223826547648104162082363)
          ·
            refine ⟨93335739821472156243123545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62223826547648104162082363 93335739821472156243123545)
            ·
              refine ⟨70001804866104117182342659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93335739821472156243123545 70001804866104117182342659)
              ·
                refine ⟨105002707299156175773513989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70001804866104117182342659 105002707299156175773513989)
                ·
                  refine ⟨19688007618591782957533873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105002707299156175773513989 19688007618591782957533873)
                  ·
                    refine ⟨14766005713943837218150405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19688007618591782957533873 14766005713943837218150405)
                    ·
                      refine ⟨2768626071364469478403201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14766005713943837218150405 2768626071364469478403201)
                      ·
                        rfl

theorem cell23_5391880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_5391880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391880 prefixEnd_5391880 := by exact prefixLift 5391880
  have htrace : WordTrace (prefixWord ++ tailWord_5391880) baseStart_5391880 baseEnd_5391880 := by
    simpa [prefixWord, tailWord_5391880, baseEnd_5391880] using wordTrace_append hprefix tailTrace_5391880
  have hstable : (prefixWord ++ tailWord_5391880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391880).length < 2 ^ (prefixWord ++ tailWord_5391880).sum := by decide
  have hdescent : baseEnd_5391880 < baseStart_5391880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391901 : List Nat := [1, 4, 2, 2, 1, 1, 3, 3, 2, 2, 2]
def baseStart_5391901 : Nat := 118140960795 + 5391901 * 2 ^ 59
def prefixEnd_5391901 : Nat := 4983230072969 + 3 ^ 40 * 5391901 * 2
def baseEnd_5391901 : Nat := 2768636854458213896240605

theorem tailTrace_5391901 : CollatzResearch.WordTrace tailWord_5391901 prefixEnd_5391901 2768636854458213896240605 := by
  unfold tailWord_5391901
  simp only [CollatzResearch.WordTrace]
  refine ⟨196658785639071015222231557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131105857092714010148154371 196658785639071015222231557)
  ·
    refine ⟨36873522307325815354168417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196658785639071015222231557 36873522307325815354168417)
    ·
      refine ⟨27655141730494361515626313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36873522307325815354168417 27655141730494361515626313)
      ·
        refine ⟨20741356297870771136719735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27655141730494361515626313 20741356297870771136719735)
        ·
          refine ⟨31112034446806156705079603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20741356297870771136719735 31112034446806156705079603)
          ·
            refine ⟨46668051670209235057619405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31112034446806156705079603 46668051670209235057619405)
            ·
              refine ⟨17500519376328463146607277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46668051670209235057619405 17500519376328463146607277)
              ·
                refine ⟨6562694766123173679977729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17500519376328463146607277 6562694766123173679977729)
                ·
                  refine ⟨4922021074592380259983297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6562694766123173679977729 4922021074592380259983297)
                  ·
                    refine ⟨3691515805944285194987473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4922021074592380259983297 3691515805944285194987473)
                    ·
                      refine ⟨2768636854458213896240605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3691515805944285194987473 2768636854458213896240605)
                      ·
                        rfl

theorem cell23_5391901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_5391901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391901 prefixEnd_5391901 := by exact prefixLift 5391901
  have htrace : WordTrace (prefixWord ++ tailWord_5391901) baseStart_5391901 baseEnd_5391901 := by
    simpa [prefixWord, tailWord_5391901, baseEnd_5391901] using wordTrace_append hprefix tailTrace_5391901
  have hstable : (prefixWord ++ tailWord_5391901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391901).length < 2 ^ (prefixWord ++ tailWord_5391901).sum := by decide
  have hdescent : baseEnd_5391901 < baseStart_5391901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391930 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5]
def baseStart_5391930 : Nat := 118140960795 + 5391930 * 2 ^ 59
def prefixEnd_5391930 : Nat := 4983230072969 + 3 ^ 40 * 5391930 * 2
def baseEnd_5391930 : Nat := 2768651745397194282777971

theorem tailTrace_5391930 : CollatzResearch.WordTrace tailWord_5391930 prefixEnd_5391930 2768651745397194282777971 := by
  unfold tailWord_5391930
  simp only [CollatzResearch.WordTrace]
  refine ⟨49164960838991488293759311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131106562237310635450024829 49164960838991488293759311)
  ·
    refine ⟨73747441258487232440638967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49164960838991488293759311 73747441258487232440638967)
    ·
      refine ⟨110621161887730848660958451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73747441258487232440638967 110621161887730848660958451)
      ·
        refine ⟨165931742831596272991437677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110621161887730848660958451 165931742831596272991437677)
        ·
          refine ⟨62224403561848602371789129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165931742831596272991437677 62224403561848602371789129)
          ·
            refine ⟨46668302671386451778841847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62224403561848602371789129 46668302671386451778841847)
            ·
              refine ⟨70002454007079677668262771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46668302671386451778841847 70002454007079677668262771)
              ·
                refine ⟨105003681010619516502394157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70002454007079677668262771 105003681010619516502394157)
                ·
                  refine ⟨39376380378982318688397809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105003681010619516502394157 39376380378982318688397809)
                  ·
                    refine ⟨29532285284236739016298357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39376380378982318688397809 29532285284236739016298357)
                    ·
                      refine ⟨2768651745397194282777971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29532285284236739016298357 2768651745397194282777971)
                      ·
                        rfl

theorem cell23_5391930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_5391930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391930 prefixEnd_5391930 := by exact prefixLift 5391930
  have htrace : WordTrace (prefixWord ++ tailWord_5391930) baseStart_5391930 baseEnd_5391930 := by
    simpa [prefixWord, tailWord_5391930, baseEnd_5391930] using wordTrace_append hprefix tailTrace_5391930
  have hstable : (prefixWord ++ tailWord_5391930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391930).length < 2 ^ (prefixWord ++ tailWord_5391930).sum := by decide
  have hdescent : baseEnd_5391930 < baseStart_5391930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391937 : List Nat := [1, 2, 5, 1, 1, 1, 1, 4, 2, 5]
def baseStart_5391937 : Nat := 118140960795 + 5391937 * 2 ^ 59
def prefixEnd_5391937 : Nat := 4983230072969 + 3 ^ 40 * 5391937 * 2
def baseEnd_5391937 : Nat := 922885113253925251796813

theorem tailTrace_5391937 : CollatzResearch.WordTrace tailWord_5391937 prefixEnd_5391937 922885113253925251796813 := by
  unfold tailWord_5391937
  simp only [CollatzResearch.WordTrace]
  refine ⟨196660098666940593370542065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131106732444627062247028043 196660098666940593370542065)
  ·
    refine ⟨147495074000205445027906549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196660098666940593370542065 147495074000205445027906549)
    ·
      refine ⟨13827663187519260471366239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147495074000205445027906549 13827663187519260471366239)
      ·
        refine ⟨20741494781278890707049359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13827663187519260471366239 20741494781278890707049359)
        ·
          refine ⟨31112242171918336060574039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20741494781278890707049359 31112242171918336060574039)
          ·
            refine ⟨46668363257877504090861059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31112242171918336060574039 46668363257877504090861059)
            ·
              refine ⟨70002544886816256136291589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46668363257877504090861059 70002544886816256136291589)
              ·
                refine ⟨13125477166278048025554673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70002544886816256136291589 13125477166278048025554673)
                ·
                  refine ⟨9844107874708536019166005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13125477166278048025554673 9844107874708536019166005)
                  ·
                    refine ⟨922885113253925251796813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9844107874708536019166005 922885113253925251796813)
                    ·
                      rfl

theorem cell23_5391937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_5391937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391937 prefixEnd_5391937 := by exact prefixLift 5391937
  have htrace : WordTrace (prefixWord ++ tailWord_5391937) baseStart_5391937 baseEnd_5391937 := by
    simpa [prefixWord, tailWord_5391937, baseEnd_5391937] using wordTrace_append hprefix tailTrace_5391937
  have hstable : (prefixWord ++ tailWord_5391937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391937).length < 2 ^ (prefixWord ++ tailWord_5391937).sum := by decide
  have hdescent : baseEnd_5391937 < baseStart_5391937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391950 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 2, 8]
def baseStart_5391950 : Nat := 118140960795 + 5391950 * 2 ^ 59
def prefixEnd_5391950 : Nat := 4983230072969 + 3 ^ 40 * 5391950 * 2
def baseEnd_5391950 : Nat := 922887338336761401509293

theorem tailTrace_5391950 : CollatzResearch.WordTrace tailWord_5391950 prefixEnd_5391950 922887338336761401509293 := by
  unfold tailWord_5391950
  simp only [CollatzResearch.WordTrace]
  refine ⟨24582571601986687073845663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131107048543928997727176869 24582571601986687073845663)
  ·
    refine ⟨36873857402980030610768495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24582571601986687073845663 36873857402980030610768495)
    ·
      refine ⟨55310786104470045916152743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36873857402980030610768495 55310786104470045916152743)
      ·
        refine ⟨82966179156705068874229115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55310786104470045916152743 82966179156705068874229115)
        ·
          refine ⟨124449268735057603311343673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82966179156705068874229115 124449268735057603311343673)
          ·
            refine ⟨93336951551293202483507755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124449268735057603311343673 93336951551293202483507755)
            ·
              refine ⟨140005427326939803725261633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93336951551293202483507755 140005427326939803725261633)
              ·
                refine ⟨105004070495204852793946225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140005427326939803725261633 105004070495204852793946225)
                ·
                  refine ⟨78753052871403639595459669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105004070495204852793946225 78753052871403639595459669)
                  ·
                    refine ⟨922887338336761401509293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78753052871403639595459669 922887338336761401509293)
                    ·
                      rfl

theorem cell23_5391950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_5391950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391950 prefixEnd_5391950 := by exact prefixLift 5391950
  have htrace : WordTrace (prefixWord ++ tailWord_5391950) baseStart_5391950 baseEnd_5391950 := by
    simpa [prefixWord, tailWord_5391950, baseEnd_5391950] using wordTrace_append hprefix tailTrace_5391950
  have hstable : (prefixWord ++ tailWord_5391950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391950).length < 2 ^ (prefixWord ++ tailWord_5391950).sum := by decide
  have hdescent : baseEnd_5391950 < baseStart_5391950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391980 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 8]
def baseStart_5391980 : Nat := 118140960795 + 5391980 * 2 ^ 59
def prefixEnd_5391980 : Nat := 4983230072969 + 3 ^ 40 * 5391980 * 2
def baseEnd_5391980 : Nat := 307630824381102120794749

theorem tailTrace_5391980 : CollatzResearch.WordTrace tailWord_5391980 prefixEnd_5391980 307630824381102120794749 := by
  unfold tailWord_5391980
  simp only [CollatzResearch.WordTrace]
  refine ⟨98330833502892405857178697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131107778003856541142904929 98330833502892405857178697)
  ·
    refine ⟨73748125127169304392884023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98330833502892405857178697 73748125127169304392884023)
    ·
      refine ⟨110622187690753956589326035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73748125127169304392884023 110622187690753956589326035)
      ·
        refine ⟨165933281536130934883989053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110622187690753956589326035 165933281536130934883989053)
        ·
          refine ⟨62224980576049100581495895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165933281536130934883989053 62224980576049100581495895)
          ·
            refine ⟨93337470864073650872243843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62224980576049100581495895 93337470864073650872243843)
            ·
              refine ⟨140006206296110476308365765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93337470864073650872243843 140006206296110476308365765)
              ·
                refine ⟨26251163680520714307818581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140006206296110476308365765 26251163680520714307818581)
                ·
                  refine ⟨307630824381102120794749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26251163680520714307818581 307630824381102120794749)
                  ·
                    rfl

theorem cell23_5391980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 8].length) (baseStart_5391980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391980 prefixEnd_5391980 := by exact prefixLift 5391980
  have htrace : WordTrace (prefixWord ++ tailWord_5391980) baseStart_5391980 baseEnd_5391980 := by
    simpa [prefixWord, tailWord_5391980, baseEnd_5391980] using wordTrace_append hprefix tailTrace_5391980
  have hstable : (prefixWord ++ tailWord_5391980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391980).length < 2 ^ (prefixWord ++ tailWord_5391980).sum := by decide
  have hdescent : baseEnd_5391980 < baseStart_5391980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5391997 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 8]
def baseStart_5391997 : Nat := 118140960795 + 5391997 * 2 ^ 59
def prefixEnd_5391997 : Nat := 4983230072969 + 3 ^ 40 * 5391997 * 2
def baseEnd_5391997 : Nat := 307631794289005057848907

theorem tailTrace_5391997 : CollatzResearch.WordTrace tailWord_5391997 prefixEnd_5391997 307631794289005057848907 := by
  unfold tailWord_5391997
  simp only [CollatzResearch.WordTrace]
  refine ⟨196662287046723223617726245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131108191364482149078484163 196662287046723223617726245)
  ·
    refine ⟨36874178821260604428323671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196662287046723223617726245 36874178821260604428323671)
    ·
      refine ⟨55311268231890906642485507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36874178821260604428323671 55311268231890906642485507)
      ·
        refine ⟨82966902347836359963728261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55311268231890906642485507 82966902347836359963728261)
        ·
          refine ⟨15556294190219317493199049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82966902347836359963728261 15556294190219317493199049)
          ·
            refine ⟨11667220642664488119899287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15556294190219317493199049 11667220642664488119899287)
            ·
              refine ⟨17500830963996732179848931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11667220642664488119899287 17500830963996732179848931)
              ·
                refine ⟨26251246445995098269773397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17500830963996732179848931 26251246445995098269773397)
                ·
                  refine ⟨307631794289005057848907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26251246445995098269773397 307631794289005057848907)
                  ·
                    rfl

theorem cell23_5391997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_5391997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5391997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5391997 prefixEnd_5391997 := by exact prefixLift 5391997
  have htrace : WordTrace (prefixWord ++ tailWord_5391997) baseStart_5391997 baseEnd_5391997 := by
    simpa [prefixWord, tailWord_5391997, baseEnd_5391997] using wordTrace_append hprefix tailTrace_5391997
  have hstable : (prefixWord ++ tailWord_5391997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5391997).length < 2 ^ (prefixWord ++ tailWord_5391997).sum := by decide
  have hdescent : baseEnd_5391997 < baseStart_5391997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5391997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392000 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 8]
def baseStart_5392000 : Nat := 118140960795 + 5392000 * 2 ^ 59
def prefixEnd_5392000 : Nat := 4983230072969 + 3 ^ 40 * 5392000 * 2
def baseEnd_5392000 : Nat := 2768687689043009008902649

theorem tailTrace_5392000 : CollatzResearch.WordTrace tailWord_5392000 prefixEnd_5392000 2768687689043009008902649 := by
  unfold tailWord_5392000
  simp only [CollatzResearch.WordTrace]
  refine ⟨98331198232856177565042727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131108264310474903420056969 98331198232856177565042727)
  ·
    refine ⟨147496797349284266347564091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98331198232856177565042727 147496797349284266347564091)
    ·
      refine ⟨221245196023926399521346137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147496797349284266347564091 221245196023926399521346137)
      ·
        refine ⟨165933897017944799641009603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221245196023926399521346137 165933897017944799641009603)
        ·
          refine ⟨248900845526917199461514405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165933897017944799641009603 248900845526917199461514405)
          ·
            refine ⟨46668908536296974899033951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 248900845526917199461514405 46668908536296974899033951)
            ·
              refine ⟨70003362804445462348550927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46668908536296974899033951 70003362804445462348550927)
              ·
                refine ⟨105005044206668193522826391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70003362804445462348550927 105005044206668193522826391)
                ·
                  refine ⟨157507566310002290284239587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105005044206668193522826391 157507566310002290284239587)
                  ·
                    refine ⟨236261349465003435426359381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 157507566310002290284239587 236261349465003435426359381)
                    ·
                      refine ⟨2768687689043009008902649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 236261349465003435426359381 2768687689043009008902649)
                      ·
                        rfl

theorem cell23_5392000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_5392000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392000 prefixEnd_5392000 := by exact prefixLift 5392000
  have htrace : WordTrace (prefixWord ++ tailWord_5392000) baseStart_5392000 baseEnd_5392000 := by
    simpa [prefixWord, tailWord_5392000, baseEnd_5392000] using wordTrace_append hprefix tailTrace_5392000
  have hstable : (prefixWord ++ tailWord_5392000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392000).length < 2 ^ (prefixWord ++ tailWord_5392000).sum := by decide
  have hdescent : baseEnd_5392000 < baseStart_5392000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392001 : List Nat := [1, 2, 4, 2, 1, 2, 2, 4, 1, 4]
def baseStart_5392001 : Nat := 118140960795 + 5392001 * 2 ^ 59
def prefixEnd_5392001 : Nat := 4983230072969 + 3 ^ 40 * 5392001 * 2
def baseEnd_5392001 : Nat := 922896067507887834996715

theorem tailTrace_5392001 : CollatzResearch.WordTrace tailWord_5392001 prefixEnd_5392001 922896067507887834996715 := by
  unfold tailWord_5392001
  simp only [CollatzResearch.WordTrace]
  refine ⟨196662432938708732300871857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131108288625805821533914571 196662432938708732300871857)
  ·
    refine ⟨147496824704031549225653893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196662432938708732300871857 147496824704031549225653893)
    ·
      refine ⟨27655654632005915479810105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147496824704031549225653893 27655654632005915479810105)
      ·
        refine ⟨20741740974004436609857579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27655654632005915479810105 20741740974004436609857579)
        ·
          refine ⟨31112611461006654914786369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20741740974004436609857579 31112611461006654914786369)
          ·
            refine ⟨23334458595754991186089777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31112611461006654914786369 23334458595754991186089777)
            ·
              refine ⟨17500843946816243389567333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23334458595754991186089777 17500843946816243389567333)
              ·
                refine ⟨3281408240028045635543875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17500843946816243389567333 3281408240028045635543875)
                ·
                  refine ⟨4922112360042068453315813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3281408240028045635543875 4922112360042068453315813)
                  ·
                    refine ⟨922896067507887834996715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4922112360042068453315813 922896067507887834996715)
                    ·
                      rfl

theorem cell23_5392001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_5392001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392001 prefixEnd_5392001 := by exact prefixLift 5392001
  have htrace : WordTrace (prefixWord ++ tailWord_5392001) baseStart_5392001 baseEnd_5392001 := by
    simpa [prefixWord, tailWord_5392001, baseEnd_5392001] using wordTrace_append hprefix tailTrace_5392001
  have hstable : (prefixWord ++ tailWord_5392001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392001).length < 2 ^ (prefixWord ++ tailWord_5392001).sum := by decide
  have hdescent : baseEnd_5392001 < baseStart_5392001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392081 : List Nat := [1, 2, 2, 1, 2, 6, 1, 2, 1, 1, 4]
def baseStart_5392081 : Nat := 118140960795 + 5392081 * 2 ^ 59
def prefixEnd_5392081 : Nat := 4983230072969 + 3 ^ 40 * 5392081 * 2
def baseEnd_5392081 : Nat := 2768729280976023191989777

theorem tailTrace_5392081 : CollatzResearch.WordTrace tailWord_5392081 prefixEnd_5392081 2768729280976023191989777 := by
  unfold tailWord_5392081
  simp only [CollatzResearch.WordTrace]
  refine ⟨196665350778418905963784097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131110233852279270642522731 196665350778418905963784097)
  ·
    refine ⟨147499013083814179472838073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196665350778418905963784097 147499013083814179472838073)
    ·
      refine ⟨110624259812860634604628555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147499013083814179472838073 110624259812860634604628555)
      ·
        refine ⟨165936389719290951906942833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110624259812860634604628555 165936389719290951906942833)
        ·
          refine ⟨124452292289468213930207125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165936389719290951906942833 124452292289468213930207125)
          ·
            refine ⟨5833701201068822527978459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 124452292289468213930207125 5833701201068822527978459)
            ·
              refine ⟨8750551801603233791967689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5833701201068822527978459 8750551801603233791967689)
              ·
                refine ⟨6562913851202425343975767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8750551801603233791967689 6562913851202425343975767)
                ·
                  refine ⟨9844370776803638015963651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6562913851202425343975767 9844370776803638015963651)
                  ·
                    refine ⟨14766556165205457023945477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9844370776803638015963651 14766556165205457023945477)
                    ·
                      refine ⟨2768729280976023191989777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14766556165205457023945477 2768729280976023191989777)
                      ·
                        rfl

theorem cell23_5392081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 1, 4].length) (baseStart_5392081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392081 prefixEnd_5392081 := by exact prefixLift 5392081
  have htrace : WordTrace (prefixWord ++ tailWord_5392081) baseStart_5392081 baseEnd_5392081 := by
    simpa [prefixWord, tailWord_5392081, baseEnd_5392081] using wordTrace_append hprefix tailTrace_5392081
  have hstable : (prefixWord ++ tailWord_5392081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392081).length < 2 ^ (prefixWord ++ tailWord_5392081).sum := by decide
  have hdescent : baseEnd_5392081 < baseStart_5392081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392114 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 3, 3, 3]
def baseStart_5392114 : Nat := 118140960795 + 5392114 * 2 ^ 59
def prefixEnd_5392114 : Nat := 4983230072969 + 3 ^ 40 * 5392114 * 2
def baseEnd_5392114 : Nat := 2768746225837621562877125

theorem tailTrace_5392114 : CollatzResearch.WordTrace tailWord_5392114 prefixEnd_5392114 2768746225837621562877125 := by
  unfold tailWord_5392114
  simp only [CollatzResearch.WordTrace]
  refine ⟨49166638596824838149933849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131111036258199568399823597 49166638596824838149933849)
  ·
    refine ⟨36874978947618628612450387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49166638596824838149933849 36874978947618628612450387)
    ·
      refine ⟨55312468421427942918675581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36874978947618628612450387 55312468421427942918675581)
      ·
        refine ⟨20742175658035478594503343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55312468421427942918675581 20742175658035478594503343)
        ·
          refine ⟨31113263487053217891755015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20742175658035478594503343 31113263487053217891755015)
          ·
            refine ⟨46669895230579826837632523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31113263487053217891755015 46669895230579826837632523)
            ·
              refine ⟨70004842845869740256448785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46669895230579826837632523 70004842845869740256448785)
              ·
                refine ⟨52503632134402305192336589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70004842845869740256448785 52503632134402305192336589)
                ·
                  refine ⟨19688862050400864447126221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52503632134402305192336589 19688862050400864447126221)
                  ·
                    refine ⟨7383323268900324167672333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19688862050400864447126221 7383323268900324167672333)
                    ·
                      refine ⟨2768746225837621562877125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7383323268900324167672333 2768746225837621562877125)
                      ·
                        rfl

theorem cell23_5392114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_5392114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392114 prefixEnd_5392114 := by exact prefixLift 5392114
  have htrace : WordTrace (prefixWord ++ tailWord_5392114) baseStart_5392114 baseEnd_5392114 := by
    simpa [prefixWord, tailWord_5392114, baseEnd_5392114] using wordTrace_append hprefix tailTrace_5392114
  have hstable : (prefixWord ++ tailWord_5392114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392114).length < 2 ^ (prefixWord ++ tailWord_5392114).sum := by decide
  have hdescent : baseEnd_5392114 < baseStart_5392114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392115 : List Nat := [1, 1, 1, 2, 2, 3, 6, 2, 1, 2, 2]
def baseStart_5392115 : Nat := 118140960795 + 5392115 * 2 ^ 59
def prefixEnd_5392115 : Nat := 4983230072969 + 3 ^ 40 * 5392115 * 2
def baseEnd_5392115 : Nat := 2768746739318276058964621

theorem tailTrace_5392115 : CollatzResearch.WordTrace tailWord_5392115 prefixEnd_5392115 2768746739318276058964621 := by
  unfold tailWord_5392115
  simp only [CollatzResearch.WordTrace]
  refine ⟨196666590860295729770521799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131111060573530486513681199 196666590860295729770521799)
  ·
    refine ⟨294999886290443594655782699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196666590860295729770521799 294999886290443594655782699)
    ·
      refine ⟨442499829435665391983674049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294999886290443594655782699 442499829435665391983674049)
      ·
        refine ⟨331874872076749043987755537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 442499829435665391983674049 331874872076749043987755537)
        ·
          refine ⟨248906154057561782990816653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331874872076749043987755537 248906154057561782990816653)
          ·
            refine ⟨93339807771585668621556245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248906154057561782990816653 93339807771585668621556245)
            ·
              refine ⟨4375303489293078216635449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 93339807771585668621556245 4375303489293078216635449)
              ·
                refine ⟨3281477616969808662476587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4375303489293078216635449 3281477616969808662476587)
                ·
                  refine ⟨4922216425454712993714881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3281477616969808662476587 4922216425454712993714881)
                  ·
                    refine ⟨3691662319091034745286161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4922216425454712993714881 3691662319091034745286161)
                    ·
                      refine ⟨2768746739318276058964621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3691662319091034745286161 2768746739318276058964621)
                      ·
                        rfl

theorem cell23_5392115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 1, 2, 2].length) (baseStart_5392115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392115 prefixEnd_5392115 := by exact prefixLift 5392115
  have htrace : WordTrace (prefixWord ++ tailWord_5392115) baseStart_5392115 baseEnd_5392115 := by
    simpa [prefixWord, tailWord_5392115, baseEnd_5392115] using wordTrace_append hprefix tailTrace_5392115
  have hstable : (prefixWord ++ tailWord_5392115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392115).length < 2 ^ (prefixWord ++ tailWord_5392115).sum := by decide
  have hdescent : baseEnd_5392115 < baseStart_5392115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392131 : List Nat := [1, 1, 1, 3, 2, 2, 4, 3, 2, 1, 3]
def baseStart_5392131 : Nat := 118140960795 + 5392131 * 2 ^ 59
def prefixEnd_5392131 : Nat := 4983230072969 + 3 ^ 40 * 5392131 * 2
def baseEnd_5392131 : Nat := 2768754955008747996364547

theorem tailTrace_5392131 : CollatzResearch.WordTrace tailWord_5392131 prefixEnd_5392131 2768754955008747996364547 := by
  unfold tailWord_5392131
  simp only [CollatzResearch.WordTrace]
  refine ⟨196667174428237764503104247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131111449618825176335402831 196667174428237764503104247)
  ·
    refine ⟨295000761642356646754656371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196667174428237764503104247 295000761642356646754656371)
    ·
      refine ⟨442501142463534970131984557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295000761642356646754656371 442501142463534970131984557)
      ·
        refine ⟨165937928423825613799494209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 442501142463534970131984557 165937928423825613799494209)
        ·
          refine ⟨124453446317869210349620657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165937928423825613799494209 124453446317869210349620657)
          ·
            refine ⟨93340084738401907762215493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124453446317869210349620657 93340084738401907762215493)
            ·
              refine ⟨17501265888450357705415405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93340084738401907762215493 17501265888450357705415405)
              ·
                refine ⟨6562974708168884139530777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17501265888450357705415405 6562974708168884139530777)
                ·
                  refine ⟨4922231031126663104648083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6562974708168884139530777 4922231031126663104648083)
                  ·
                    refine ⟨7383346546689994656972125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4922231031126663104648083 7383346546689994656972125)
                    ·
                      refine ⟨2768754955008747996364547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7383346546689994656972125 2768754955008747996364547)
                      ·
                        rfl

theorem cell23_5392131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 1, 3].length) (baseStart_5392131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392131 prefixEnd_5392131 := by exact prefixLift 5392131
  have htrace : WordTrace (prefixWord ++ tailWord_5392131) baseStart_5392131 baseEnd_5392131 := by
    simpa [prefixWord, tailWord_5392131, baseEnd_5392131] using wordTrace_append hprefix tailTrace_5392131
  have hstable : (prefixWord ++ tailWord_5392131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392131).length < 2 ^ (prefixWord ++ tailWord_5392131).sum := by decide
  have hdescent : baseEnd_5392131 < baseStart_5392131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392137 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 4, 3, 4]
def baseStart_5392137 : Nat := 118140960795 + 5392137 * 2 ^ 59
def prefixEnd_5392137 : Nat := 4983230072969 + 3 ^ 40 * 5392137 * 2
def baseEnd_5392137 : Nat := 2768758035892674972889519

theorem tailTrace_5392137 : CollatzResearch.WordTrace tailWord_5392137 prefixEnd_5392137 2768758035892674972889519 := by
  unfold tailWord_5392137
  simp only [CollatzResearch.WordTrace]
  refine ⟨196667393266216027527822665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131111595510810685018548443 196667393266216027527822665)
  ·
    refine ⟨147500544949662020645866999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196667393266216027527822665 147500544949662020645866999)
    ·
      refine ⟨221250817424493030968800499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147500544949662020645866999 221250817424493030968800499)
      ·
        refine ⟨331876226136739546453200749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221250817424493030968800499 331876226136739546453200749)
        ·
          refine ⟨124453584801277329919950281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 331876226136739546453200749 124453584801277329919950281)
          ·
            refine ⟨93340188600957997439962711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124453584801277329919950281 93340188600957997439962711)
            ·
              refine ⟨140010282901436996159944067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93340188600957997439962711 140010282901436996159944067)
              ·
                refine ⟨210015424352155494239916101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140010282901436996159944067 210015424352155494239916101)
                ·
                  refine ⟨39377892066029155169984269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 210015424352155494239916101 39377892066029155169984269)
                  ·
                    refine ⟨14766709524760933188744101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39377892066029155169984269 14766709524760933188744101)
                    ·
                      refine ⟨2768758035892674972889519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14766709524760933188744101 2768758035892674972889519)
                      ·
                        rfl

theorem cell23_5392137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 3, 4].length) (baseStart_5392137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392137 prefixEnd_5392137 := by exact prefixLift 5392137
  have htrace : WordTrace (prefixWord ++ tailWord_5392137) baseStart_5392137 baseEnd_5392137 := by
    simpa [prefixWord, tailWord_5392137, baseEnd_5392137] using wordTrace_append hprefix tailTrace_5392137
  have hstable : (prefixWord ++ tailWord_5392137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392137).length < 2 ^ (prefixWord ++ tailWord_5392137).sum := by decide
  have hdescent : baseEnd_5392137 < baseStart_5392137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392164 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 2, 6]
def baseStart_5392164 : Nat := 118140960795 + 5392164 * 2 ^ 59
def prefixEnd_5392164 : Nat := 4983230072969 + 3 ^ 40 * 5392164 * 2
def baseEnd_5392164 : Nat := 922923966623448789083965

theorem tailTrace_5392164 : CollatzResearch.WordTrace tailWord_5392164 prefixEnd_5392164 922923966623448789083965 := by
  unfold tailWord_5392164
  simp only [CollatzResearch.WordTrace]
  refine ⟨98334189018559105569527773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131112252024745474092703697 98334189018559105569527773)
  ·
    refine ⟨36875320881959664588572915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98334189018559105569527773 36875320881959664588572915)
    ·
      refine ⟨55312981322939496882859373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36875320881959664588572915 55312981322939496882859373)
      ·
        refine ⟨20742367996102311331072265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55312981322939496882859373 20742367996102311331072265)
        ·
          refine ⟨15556775997076733498304199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20742367996102311331072265 15556775997076733498304199)
          ·
            refine ⟨23335163995615100247456299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15556775997076733498304199 23335163995615100247456299)
            ·
              refine ⟨35002745993422650371184449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23335163995615100247456299 35002745993422650371184449)
              ·
                refine ⟨26252059495066987778388337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35002745993422650371184449 26252059495066987778388337)
                ·
                  refine ⟨19689044621300240833791253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26252059495066987778388337 19689044621300240833791253)
                  ·
                    refine ⟨922923966623448789083965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19689044621300240833791253 922923966623448789083965)
                    ·
                      rfl

theorem cell23_5392164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_5392164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392164 prefixEnd_5392164 := by exact prefixLift 5392164
  have htrace : WordTrace (prefixWord ++ tailWord_5392164) baseStart_5392164 baseEnd_5392164 := by
    simpa [prefixWord, tailWord_5392164, baseEnd_5392164] using wordTrace_append hprefix tailTrace_5392164
  have hstable : (prefixWord ++ tailWord_5392164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392164).length < 2 ^ (prefixWord ++ tailWord_5392164).sum := by decide
  have hdescent : baseEnd_5392164 < baseStart_5392164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392182 : List Nat := [5, 1, 2, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_5392182 : Nat := 118140960795 + 5392182 * 2 ^ 59
def prefixEnd_5392182 : Nat := 4983230072969 + 3 ^ 40 * 5392182 * 2
def baseEnd_5392182 : Nat := 2768781142522127296826813

theorem tailTrace_5392182 : CollatzResearch.WordTrace tailWord_5392182 prefixEnd_5392182 2768781142522127296826813 := by
  unfold tailWord_5392182
  simp only [CollatzResearch.WordTrace]
  refine ⟨12291814659440812513325675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131112689700702000142140533 12291814659440812513325675)
  ·
    refine ⟨18437721989161218769988513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12291814659440812513325675 18437721989161218769988513)
    ·
      refine ⟨13828291491870914077491385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18437721989161218769988513 13828291491870914077491385)
      ·
        refine ⟨10371218618903185558118539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13828291491870914077491385 10371218618903185558118539)
        ·
          refine ⟨15556827928354778337177809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10371218618903185558118539 15556827928354778337177809)
          ·
            refine ⟨11667620946266083752883357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15556827928354778337177809 11667620946266083752883357)
            ·
              refine ⟨4375357854849781407331259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11667620946266083752883357 4375357854849781407331259)
              ·
                refine ⟨6563036782274672110996889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4375357854849781407331259 6563036782274672110996889)
                ·
                  refine ⟨4922277586706004083247667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6563036782274672110996889 4922277586706004083247667)
                  ·
                    refine ⟨7383416380059006124871501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4922277586706004083247667 7383416380059006124871501)
                    ·
                      refine ⟨2768781142522127296826813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7383416380059006124871501 2768781142522127296826813)
                      ·
                        rfl

theorem cell23_5392182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_5392182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392182 prefixEnd_5392182 := by exact prefixLift 5392182
  have htrace : WordTrace (prefixWord ++ tailWord_5392182) baseStart_5392182 baseEnd_5392182 := by
    simpa [prefixWord, tailWord_5392182, baseEnd_5392182] using wordTrace_append hprefix tailTrace_5392182
  have hstable : (prefixWord ++ tailWord_5392182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392182).length < 2 ^ (prefixWord ++ tailWord_5392182).sum := by decide
  have hdescent : baseEnd_5392182 < baseStart_5392182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392184 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 2, 2, 4]
def baseStart_5392184 : Nat := 118140960795 + 5392184 * 2 ^ 59
def prefixEnd_5392184 : Nat := 4983230072969 + 3 ^ 40 * 5392184 * 2
def baseEnd_5392184 : Nat := 2768782169483436289001803

theorem tailTrace_5392184 : CollatzResearch.WordTrace tailWord_5392184 prefixEnd_5392184 2768782169483436289001803 := by
  unfold tailWord_5392184
  simp only [CollatzResearch.WordTrace]
  refine ⟨98334553748522877277391803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131112738331363836369855737 98334553748522877277391803)
  ·
    refine ⟨147501830622784315916087705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98334553748522877277391803 147501830622784315916087705)
    ·
      refine ⟨110626372967088236937065779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147501830622784315916087705 110626372967088236937065779)
      ·
        refine ⟨165939559450632355405598669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110626372967088236937065779 165939559450632355405598669)
        ·
          refine ⟨62227334793987133277099501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165939559450632355405598669 62227334793987133277099501)
          ·
            refine ⟨23335250547745174978912313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62227334793987133277099501 23335250547745174978912313)
            ·
              refine ⟨17501437910808881234184235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23335250547745174978912313 17501437910808881234184235)
              ·
                refine ⟨26252156866213321851276353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17501437910808881234184235 26252156866213321851276353)
                ·
                  refine ⟨19689117649659991388457265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26252156866213321851276353 19689117649659991388457265)
                  ·
                    refine ⟨14766838237244993541342949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19689117649659991388457265 14766838237244993541342949)
                    ·
                      refine ⟨2768782169483436289001803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14766838237244993541342949 2768782169483436289001803)
                      ·
                        rfl

theorem cell23_5392184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_5392184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392184 prefixEnd_5392184 := by exact prefixLift 5392184
  have htrace : WordTrace (prefixWord ++ tailWord_5392184) baseStart_5392184 baseEnd_5392184 := by
    simpa [prefixWord, tailWord_5392184, baseEnd_5392184] using wordTrace_append hprefix tailTrace_5392184
  have hstable : (prefixWord ++ tailWord_5392184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392184).length < 2 ^ (prefixWord ++ tailWord_5392184).sum := by decide
  have hdescent : baseEnd_5392184 < baseStart_5392184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392188 : List Nat := [2, 2, 2, 2, 1, 1, 2, 5, 2, 2, 2]
def baseStart_5392188 : Nat := 118140960795 + 5392188 * 2 ^ 59
def prefixEnd_5392188 : Nat := 4983230072969 + 3 ^ 40 * 5392188 * 2
def baseEnd_5392188 : Nat := 2768784223406054273351785

theorem tailTrace_5392188 : CollatzResearch.WordTrace tailWord_5392188 prefixEnd_5392188 2768784223406054273351785 := by
  unfold tailWord_5392188
  simp only [CollatzResearch.WordTrace]
  refine ⟨98334626694515631618964609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131112835592687508825286145 98334626694515631618964609)
  ·
    refine ⟨73750970020886723714223457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98334626694515631618964609 73750970020886723714223457)
    ·
      refine ⟨55313227515665042785667593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73750970020886723714223457 55313227515665042785667593)
      ·
        refine ⟨41484920636748782089250695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55313227515665042785667593 41484920636748782089250695)
        ·
          refine ⟨62227380955123173133876043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41484920636748782089250695 62227380955123173133876043)
          ·
            refine ⟨93341071432684759700814065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62227380955123173133876043 93341071432684759700814065)
            ·
              refine ⟨70005803574513569775610549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93341071432684759700814065 70005803574513569775610549)
              ·
                refine ⟨6563044085110647166463489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70005803574513569775610549 6563044085110647166463489)
                ·
                  refine ⟨4922283063832985374847617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6563044085110647166463489 4922283063832985374847617)
                  ·
                    refine ⟨3691712297874739031135713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4922283063832985374847617 3691712297874739031135713)
                    ·
                      refine ⟨2768784223406054273351785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3691712297874739031135713 2768784223406054273351785)
                      ·
                        rfl

theorem cell23_5392188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_5392188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392188 prefixEnd_5392188 := by exact prefixLift 5392188
  have htrace : WordTrace (prefixWord ++ tailWord_5392188) baseStart_5392188 baseEnd_5392188 := by
    simpa [prefixWord, tailWord_5392188, baseEnd_5392188] using wordTrace_append hprefix tailTrace_5392188
  have hstable : (prefixWord ++ tailWord_5392188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392188).length < 2 ^ (prefixWord ++ tailWord_5392188).sum := by decide
  have hdescent : baseEnd_5392188 < baseStart_5392188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392205 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_5392205 : Nat := 118140960795 + 5392205 * 2 ^ 59
def prefixEnd_5392205 : Nat := 4983230072969 + 3 ^ 40 * 5392205 * 2
def baseEnd_5392205 : Nat := 2768792952577180706839207

theorem tailTrace_5392205 : CollatzResearch.WordTrace tailWord_5392205 prefixEnd_5392205 2768792952577180706839207 := by
  unfold tailWord_5392205
  simp only [CollatzResearch.WordTrace]
  refine ⟨196669873429969675141298069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131113248953313116760865379 196669873429969675141298069)
  ·
    refine ⟨9218900317029828522248347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 196669873429969675141298069 9218900317029828522248347)
    ·
      refine ⟨13828350475544742783372521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9218900317029828522248347 13828350475544742783372521)
      ·
        refine ⟨10371262856658557087529391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13828350475544742783372521 10371262856658557087529391)
        ·
          refine ⟨15556894284987835631294087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10371262856658557087529391 15556894284987835631294087)
          ·
            refine ⟨23335341427481753446941131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15556894284987835631294087 23335341427481753446941131)
            ·
              refine ⟨35003012141222630170411697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23335341427481753446941131 35003012141222630170411697)
              ·
                refine ⟨26252259105916972627808773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35003012141222630170411697 26252259105916972627808773)
                ·
                  refine ⟨4922298582359432367714145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26252259105916972627808773 4922298582359432367714145)
                  ·
                    refine ⟨3691723936769574275785609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4922298582359432367714145 3691723936769574275785609)
                    ·
                      refine ⟨2768792952577180706839207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3691723936769574275785609 2768792952577180706839207)
                      ·
                        rfl

theorem cell23_5392205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_5392205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392205 prefixEnd_5392205 := by exact prefixLift 5392205
  have htrace : WordTrace (prefixWord ++ tailWord_5392205) baseStart_5392205 baseEnd_5392205 := by
    simpa [prefixWord, tailWord_5392205, baseEnd_5392205] using wordTrace_append hprefix tailTrace_5392205
  have hstable : (prefixWord ++ tailWord_5392205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392205).length < 2 ^ (prefixWord ++ tailWord_5392205).sum := by decide
  have hdescent : baseEnd_5392205 < baseStart_5392205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392224 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 4, 5]
def baseStart_5392224 : Nat := 118140960795 + 5392224 * 2 ^ 59
def prefixEnd_5392224 : Nat := 4983230072969 + 3 ^ 40 * 5392224 * 2
def baseEnd_5392224 : Nat := 922934236236538710833873

theorem tailTrace_5392224 : CollatzResearch.WordTrace tailWord_5392224 prefixEnd_5392224 922934236236538710833873 := by
  unfold tailWord_5392224
  simp only [CollatzResearch.WordTrace]
  refine ⟨98335283208450420693119863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131113710944600560924159817 98335283208450420693119863)
  ·
    refine ⟨147502924812675631039679795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98335283208450420693119863 147502924812675631039679795)
    ·
      refine ⟨221254387219013446559519693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147502924812675631039679795 221254387219013446559519693)
      ·
        refine ⟨82970395207130042459819885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221254387219013446559519693 82970395207130042459819885)
        ·
          refine ⟨31113898202673765922432457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82970395207130042459819885 31113898202673765922432457)
          ·
            refine ⟨23335423652005324441824343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31113898202673765922432457 23335423652005324441824343)
            ·
              refine ⟨35003135478007986662736515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23335423652005324441824343 35003135478007986662736515)
              ·
                refine ⟨52504703217011979994104773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35003135478007986662736515 52504703217011979994104773)
                ·
                  refine ⟨9844631853189746248894645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52504703217011979994104773 9844631853189746248894645)
                  ·
                    refine ⟨922934236236538710833873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9844631853189746248894645 922934236236538710833873)
                    ·
                      rfl

theorem cell23_5392224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 4, 5].length) (baseStart_5392224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392224 prefixEnd_5392224 := by exact prefixLift 5392224
  have htrace : WordTrace (prefixWord ++ tailWord_5392224) baseStart_5392224 baseEnd_5392224 := by
    simpa [prefixWord, tailWord_5392224, baseEnd_5392224] using wordTrace_append hprefix tailTrace_5392224
  have hstable : (prefixWord ++ tailWord_5392224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392224).length < 2 ^ (prefixWord ++ tailWord_5392224).sum := by decide
  have hdescent : baseEnd_5392224 < baseStart_5392224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392228 : List Nat := [2, 3, 1, 1, 6, 1, 1, 1, 7]
def baseStart_5392228 : Nat := 118140960795 + 5392228 * 2 ^ 59
def prefixEnd_5392228 : Nat := 4983230072969 + 3 ^ 40 * 5392228 * 2
def baseEnd_5392228 : Nat := 307644973625803790761289

theorem tailTrace_5392228 : CollatzResearch.WordTrace tailWord_5392228 prefixEnd_5392228 307644973625803790761289 := by
  unfold tailWord_5392228
  simp only [CollatzResearch.WordTrace]
  refine ⟨98335356154443175034692669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131113808205924233379590225 98335356154443175034692669)
  ·
    refine ⟨36875758557916190638009751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98335356154443175034692669 36875758557916190638009751)
    ·
      refine ⟨55313637836874285957014627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36875758557916190638009751 55313637836874285957014627)
      ·
        refine ⟨82970456755311428935521941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55313637836874285957014627 82970456755311428935521941)
        ·
          refine ⟨3889240160405223231352591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82970456755311428935521941 3889240160405223231352591)
          ·
            refine ⟨5833860240607834847028887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3889240160405223231352591 5833860240607834847028887)
            ·
              refine ⟨8750790360911752270543331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5833860240607834847028887 8750790360911752270543331)
              ·
                refine ⟨13126185541367628405814997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8750790360911752270543331 13126185541367628405814997)
                ·
                  refine ⟨307644973625803790761289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13126185541367628405814997 307644973625803790761289)
                  ·
                    rfl

theorem cell23_5392228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_5392228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392228 prefixEnd_5392228 := by exact prefixLift 5392228
  have htrace : WordTrace (prefixWord ++ tailWord_5392228) baseStart_5392228 baseEnd_5392228 := by
    simpa [prefixWord, tailWord_5392228, baseEnd_5392228] using wordTrace_append hprefix tailTrace_5392228
  have hstable : (prefixWord ++ tailWord_5392228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392228).length < 2 ^ (prefixWord ++ tailWord_5392228).sum := by decide
  have hdescent : baseEnd_5392228 < baseStart_5392228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392231 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 2, 5, 2]
def baseStart_5392231 : Nat := 118140960795 + 5392231 * 2 ^ 59
def prefixEnd_5392231 : Nat := 4983230072969 + 3 ^ 40 * 5392231 * 2
def baseEnd_5392231 : Nat := 2768806303074197605114087

theorem tailTrace_5392231 : CollatzResearch.WordTrace tailWord_5392231 prefixEnd_5392231 2768806303074197605114087 := by
  unfold tailWord_5392231
  simp only [CollatzResearch.WordTrace]
  refine ⟨196670821727875481581744547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131113881151916987721163031 196670821727875481581744547)
  ·
    refine ⟨295006232591813222372616821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196670821727875481581744547 295006232591813222372616821)
    ·
      refine ⟨27656834305482489597432827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 295006232591813222372616821 27656834305482489597432827)
      ·
        refine ⟨41485251458223734396149241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27656834305482489597432827 41485251458223734396149241)
        ·
          refine ⟨31113938593667800797111931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41485251458223734396149241 31113938593667800797111931)
          ·
            refine ⟨46670907890501701195667897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31113938593667800797111931 46670907890501701195667897)
            ·
              refine ⟨35003180917876275896750923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46670907890501701195667897 35003180917876275896750923)
              ·
                refine ⟨52504771376814413845126385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35003180917876275896750923 52504771376814413845126385)
                ·
                  refine ⟨39378578532610810383844789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52504771376814413845126385 39378578532610810383844789)
                  ·
                    refine ⟨3691741737432263473485449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39378578532610810383844789 3691741737432263473485449)
                    ·
                      refine ⟨2768806303074197605114087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3691741737432263473485449 2768806303074197605114087)
                      ·
                        rfl

theorem cell23_5392231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_5392231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392231 prefixEnd_5392231 := by exact prefixLift 5392231
  have htrace : WordTrace (prefixWord ++ tailWord_5392231) baseStart_5392231 baseEnd_5392231 := by
    simpa [prefixWord, tailWord_5392231, baseEnd_5392231] using wordTrace_append hprefix tailTrace_5392231
  have hstable : (prefixWord ++ tailWord_5392231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392231).length < 2 ^ (prefixWord ++ tailWord_5392231).sum := by decide
  have hdescent : baseEnd_5392231 < baseStart_5392231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392261 : List Nat := [1, 3, 1, 1, 3, 2, 4, 1, 2, 1, 4]
def baseStart_5392261 : Nat := 118140960795 + 5392261 * 2 ^ 59
def prefixEnd_5392261 : Nat := 4983230072969 + 3 ^ 40 * 5392261 * 2
def baseEnd_5392261 : Nat := 2768821707493832487738949

theorem tailTrace_5392261 : CollatzResearch.WordTrace tailWord_5392261 prefixEnd_5392261 2768821707493832487738949 := by
  unfold tailWord_5392261
  simp only [CollatzResearch.WordTrace]
  refine ⟨196671915917766796705336637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131114610611844531136891091 196671915917766796705336637)
  ·
    refine ⟨73751968469162548764501239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196671915917766796705336637 73751968469162548764501239)
    ·
      refine ⟨110627952703743823146751859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73751968469162548764501239 110627952703743823146751859)
      ·
        refine ⟨165941929055615734720127789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110627952703743823146751859 165941929055615734720127789)
        ·
          refine ⟨62228223395855900520047921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165941929055615734720127789 62228223395855900520047921)
          ·
            refine ⟨46671167546891925390035941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62228223395855900520047921 46671167546891925390035941)
            ·
              refine ⟨8750843915042236010631739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46671167546891925390035941 8750843915042236010631739)
              ·
                refine ⟨13126265872563354015947609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8750843915042236010631739 13126265872563354015947609)
                ·
                  refine ⟨9844699404422515511960707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13126265872563354015947609 9844699404422515511960707)
                  ·
                    refine ⟨14767049106633773267941061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9844699404422515511960707 14767049106633773267941061)
                    ·
                      refine ⟨2768821707493832487738949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14767049106633773267941061 2768821707493832487738949)
                      ·
                        rfl

theorem cell23_5392261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_5392261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392261 prefixEnd_5392261 := by exact prefixLift 5392261
  have htrace : WordTrace (prefixWord ++ tailWord_5392261) baseStart_5392261 baseEnd_5392261 := by
    simpa [prefixWord, tailWord_5392261, baseEnd_5392261] using wordTrace_append hprefix tailTrace_5392261
  have hstable : (prefixWord ++ tailWord_5392261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392261).length < 2 ^ (prefixWord ++ tailWord_5392261).sum := by decide
  have hdescent : baseEnd_5392261 < baseStart_5392261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392281 : List Nat := [1, 2, 1, 2, 1, 3, 4, 2, 2, 2, 3]
def baseStart_5392281 : Nat := 118140960795 + 5392281 * 2 ^ 59
def prefixEnd_5392281 : Nat := 4983230072969 + 3 ^ 40 * 5392281 * 2
def baseEnd_5392281 : Nat := 2768831977106922409488857

theorem tailTrace_5392281 : CollatzResearch.WordTrace tailWord_5392281 prefixEnd_5392281 2768831977106922409488857 := by
  unfold tailWord_5392281
  simp only [CollatzResearch.WordTrace]
  refine ⟨196672645377694340121064697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131115096918462893414043131 196672645377694340121064697)
  ·
    refine ⟨147504484033270755090798523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196672645377694340121064697 147504484033270755090798523)
    ·
      refine ⟨221256726049906132636197785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147504484033270755090798523 221256726049906132636197785)
      ·
        refine ⟨165942544537429599477148339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221256726049906132636197785 165942544537429599477148339)
        ·
          refine ⟨248913816806144399215722509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165942544537429599477148339 248913816806144399215722509)
          ·
            refine ⟨93342681302304149705895941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248913816806144399215722509 93342681302304149705895941)
            ·
              refine ⟨17501752744182028069855489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93342681302304149705895941 17501752744182028069855489)
              ·
                refine ⟨13126314558136521052391617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17501752744182028069855489 13126314558136521052391617)
                ·
                  refine ⟨9844735918602390789293713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13126314558136521052391617 9844735918602390789293713)
                  ·
                    refine ⟨7383551938951793091970285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9844735918602390789293713 7383551938951793091970285)
                    ·
                      refine ⟨2768831977106922409488857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7383551938951793091970285 2768831977106922409488857)
                      ·
                        rfl

theorem cell23_5392281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_5392281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392281 prefixEnd_5392281 := by exact prefixLift 5392281
  have htrace : WordTrace (prefixWord ++ tailWord_5392281) baseStart_5392281 baseEnd_5392281 := by
    simpa [prefixWord, tailWord_5392281, baseEnd_5392281] using wordTrace_append hprefix tailTrace_5392281
  have hstable : (prefixWord ++ tailWord_5392281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392281).length < 2 ^ (prefixWord ++ tailWord_5392281).sum := by decide
  have hdescent : baseEnd_5392281 < baseStart_5392281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392331 : List Nat := [1, 1, 1, 1, 3, 4, 3, 3, 1, 5]
def baseStart_5392331 : Nat := 118140960795 + 5392331 * 2 ^ 59
def prefixEnd_5392331 : Nat := 4983230072969 + 3 ^ 40 * 5392331 * 2
def baseEnd_5392331 : Nat := 922952550379882404621209

theorem tailTrace_5392331 : CollatzResearch.WordTrace tailWord_5392331 prefixEnd_5392331 922952550379882404621209 := by
  unfold tailWord_5392331
  simp only [CollatzResearch.WordTrace]
  refine ⟨196674469027513198660384847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131116312685008799106923231 196674469027513198660384847)
  ·
    refine ⟨295011703541269797990577271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196674469027513198660384847 295011703541269797990577271)
    ·
      refine ⟨442517555311904696985865907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295011703541269797990577271 442517555311904696985865907)
      ·
        refine ⟨663776332967857045478798861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442517555311904696985865907 663776332967857045478798861)
        ·
          refine ⟨248916124862946392054549573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 663776332967857045478798861 248916124862946392054549573)
          ·
            refine ⟨46671773411802448510228045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 248916124862946392054549573 46671773411802448510228045)
            ·
              refine ⟨17501915029425918191335517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46671773411802448510228045 17501915029425918191335517)
              ·
                refine ⟨6563218136034719321750819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17501915029425918191335517 6563218136034719321750819)
                ·
                  refine ⟨9844827204052078982626229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6563218136034719321750819 9844827204052078982626229)
                  ·
                    refine ⟨922952550379882404621209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9844827204052078982626229 922952550379882404621209)
                    ·
                      rfl

theorem cell23_5392331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 5].length) (baseStart_5392331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392331 prefixEnd_5392331 := by exact prefixLift 5392331
  have htrace : WordTrace (prefixWord ++ tailWord_5392331) baseStart_5392331 baseEnd_5392331 := by
    simpa [prefixWord, tailWord_5392331, baseEnd_5392331] using wordTrace_append hprefix tailTrace_5392331
  have hstable : (prefixWord ++ tailWord_5392331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392331).length < 2 ^ (prefixWord ++ tailWord_5392331).sum := by decide
  have hdescent : baseEnd_5392331 < baseStart_5392331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392345 : List Nat := [1, 2, 1, 2, 6, 1, 2, 1, 3, 1, 3]
def baseStart_5392345 : Nat := 118140960795 + 5392345 * 2 ^ 59
def prefixEnd_5392345 : Nat := 4983230072969 + 3 ^ 40 * 5392345 * 2
def baseEnd_5392345 : Nat := 2768864839868810159088563

theorem tailTrace_5392345 : CollatzResearch.WordTrace tailWord_5392345 prefixEnd_5392345 2768864839868810159088563 := by
  unfold tailWord_5392345
  simp only [CollatzResearch.WordTrace]
  refine ⟨196674979649462479051394489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131116653099641652700929659 196674979649462479051394489)
  ·
    refine ⟨147506234737096859288545867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196674979649462479051394489 147506234737096859288545867)
    ·
      refine ⟨221259352105645288932818801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147506234737096859288545867 221259352105645288932818801)
      ·
        refine ⟨165944514079233966699614101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221259352105645288932818801 165944514079233966699614101)
        ·
          refine ⟨7778649097464092189044411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 165944514079233966699614101 7778649097464092189044411)
          ·
            refine ⟨11667973646196138283566617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7778649097464092189044411 11667973646196138283566617)
            ·
              refine ⟨8750980234647103712674963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11667973646196138283566617 8750980234647103712674963)
              ·
                refine ⟨13126470351970655569012445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8750980234647103712674963 13126470351970655569012445)
                ·
                  refine ⟨4922426381988995838379667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13126470351970655569012445 4922426381988995838379667)
                  ·
                    refine ⟨7383639572983493757569501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4922426381988995838379667 7383639572983493757569501)
                    ·
                      refine ⟨2768864839868810159088563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7383639572983493757569501 2768864839868810159088563)
                      ·
                        rfl

theorem cell23_5392345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 1, 3].length) (baseStart_5392345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392345 prefixEnd_5392345 := by exact prefixLift 5392345
  have htrace : WordTrace (prefixWord ++ tailWord_5392345) baseStart_5392345 baseEnd_5392345 := by
    simpa [prefixWord, tailWord_5392345, baseEnd_5392345] using wordTrace_append hprefix tailTrace_5392345
  have hstable : (prefixWord ++ tailWord_5392345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392345).length < 2 ^ (prefixWord ++ tailWord_5392345).sum := by decide
  have hdescent : baseEnd_5392345 < baseStart_5392345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392371 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 3]
def baseStart_5392371 : Nat := 118140960795 + 5392371 * 2 ^ 59
def prefixEnd_5392371 : Nat := 4983230072969 + 3 ^ 40 * 5392371 * 2
def baseEnd_5392371 : Nat := 2768878190365827057363443

theorem tailTrace_5392371 : CollatzResearch.WordTrace tailWord_5392371 prefixEnd_5392371 2768878190365827057363443 := by
  unfold tailWord_5392371
  simp only [CollatzResearch.WordTrace]
  refine ⟨196675927947368285491840967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131117285298245523661227311 196675927947368285491840967)
  ·
    refine ⟨295013891921052428237761451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196675927947368285491840967 295013891921052428237761451)
    ·
      refine ⟨442520837881578642356642177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295013891921052428237761451 442520837881578642356642177)
      ·
        refine ⟨331890628411183981767481633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 442520837881578642356642177 331890628411183981767481633)
        ·
          refine ⟨248917971308387986325611225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331890628411183981767481633 248917971308387986325611225)
          ·
            refine ⟨186688478481290989744208419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248917971308387986325611225 186688478481290989744208419)
            ·
              refine ⟨280032717721936484616312629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186688478481290989744208419 280032717721936484616312629)
              ·
                refine ⟨26253067286431545432779309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 280032717721936484616312629 26253067286431545432779309)
                ·
                  refine ⟨9844900232411829537292241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26253067286431545432779309 9844900232411829537292241)
                  ·
                    refine ⟨7383675174308872152969181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9844900232411829537292241 7383675174308872152969181)
                    ·
                      refine ⟨2768878190365827057363443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7383675174308872152969181 2768878190365827057363443)
                      ·
                        rfl

theorem cell23_5392371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 3].length) (baseStart_5392371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392371 prefixEnd_5392371 := by exact prefixLift 5392371
  have htrace : WordTrace (prefixWord ++ tailWord_5392371) baseStart_5392371 baseEnd_5392371 := by
    simpa [prefixWord, tailWord_5392371, baseEnd_5392371] using wordTrace_append hprefix tailTrace_5392371
  have hstable : (prefixWord ++ tailWord_5392371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392371).length < 2 ^ (prefixWord ++ tailWord_5392371).sum := by decide
  have hdescent : baseEnd_5392371 < baseStart_5392371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392381 : List Nat := [1, 4, 1, 1, 1, 2, 2, 4, 1, 2, 4]
def baseStart_5392381 : Nat := 118140960795 + 5392381 * 2 ^ 59
def prefixEnd_5392381 : Nat := 4983230072969 + 3 ^ 40 * 5392381 * 2
def baseEnd_5392381 : Nat := 2768883325172372018238397

theorem tailTrace_5392381 : CollatzResearch.WordTrace tailWord_5392381 prefixEnd_5392381 2768883325172372018238397 := by
  unfold tailWord_5392381
  simp only [CollatzResearch.WordTrace]
  refine ⟨196676292677332057199704997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131117528451554704799803331 196676292677332057199704997)
  ·
    refine ⟨36876804876999760724944687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196676292677332057199704997 36876804876999760724944687)
    ·
      refine ⟨55315207315499641087417031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36876804876999760724944687 55315207315499641087417031)
      ·
        refine ⟨82972810973249461631125547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55315207315499641087417031 82972810973249461631125547)
        ·
          refine ⟨124459216459874192446688321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82972810973249461631125547 124459216459874192446688321)
          ·
            refine ⟨93344412344905644335016241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124459216459874192446688321 93344412344905644335016241)
            ·
              refine ⟨70008309258679233251262181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93344412344905644335016241 70008309258679233251262181)
              ·
                refine ⟨13126557986002356234611659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70008309258679233251262181 13126557986002356234611659)
                ·
                  refine ⟨19689836979003534351917489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13126557986002356234611659 19689836979003534351917489)
                  ·
                    refine ⟨14767377734252650763938117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19689836979003534351917489 14767377734252650763938117)
                    ·
                      refine ⟨2768883325172372018238397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14767377734252650763938117 2768883325172372018238397)
                      ·
                        rfl

theorem cell23_5392381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_5392381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392381 prefixEnd_5392381 := by exact prefixLift 5392381
  have htrace : WordTrace (prefixWord ++ tailWord_5392381) baseStart_5392381 baseEnd_5392381 := by
    simpa [prefixWord, tailWord_5392381, baseEnd_5392381] using wordTrace_append hprefix tailTrace_5392381
  have hstable : (prefixWord ++ tailWord_5392381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392381).length < 2 ^ (prefixWord ++ tailWord_5392381).sum := by decide
  have hdescent : baseEnd_5392381 < baseStart_5392381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392391 : List Nat := [1, 1, 4, 3, 1, 4, 9]
def baseStart_5392391 : Nat := 118140960795 + 5392391 * 2 ^ 59
def prefixEnd_5392391 : Nat := 4983230072969 + 3 ^ 40 * 5392391 * 2
def baseEnd_5392391 : Nat := 34183808147887863939671

theorem tailTrace_5392391 : CollatzResearch.WordTrace tailWord_5392391 prefixEnd_5392391 34183808147887863939671 := by
  unfold tailWord_5392391
  simp only [CollatzResearch.WordTrace]
  refine ⟨196676657407295828907569027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131117771604863885938379351 196676657407295828907569027)
  ·
    refine ⟨295014986110943743361353541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196676657407295828907569027 295014986110943743361353541)
    ·
      refine ⟨55315309895801951880253789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 295014986110943743361353541 55315309895801951880253789)
      ·
        refine ⟨20743241210925731955095171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55315309895801951880253789 20743241210925731955095171)
        ·
          refine ⟨31114861816388597932642757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20743241210925731955095171 31114861816388597932642757)
          ·
            refine ⟨5834036590572862112370517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31114861816388597932642757 5834036590572862112370517)
            ·
              refine ⟨34183808147887863939671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5834036590572862112370517 34183808147887863939671)
              ·
                rfl

theorem cell23_5392391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 9].length) (baseStart_5392391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392391 prefixEnd_5392391 := by exact prefixLift 5392391
  have htrace : WordTrace (prefixWord ++ tailWord_5392391) baseStart_5392391 baseEnd_5392391 := by
    simpa [prefixWord, tailWord_5392391, baseEnd_5392391] using wordTrace_append hprefix tailTrace_5392391
  have hstable : (prefixWord ++ tailWord_5392391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392391).length < 2 ^ (prefixWord ++ tailWord_5392391).sum := by decide
  have hdescent : baseEnd_5392391 < baseStart_5392391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392412 : List Nat := [2, 2, 3, 1, 3, 3, 2, 1, 2, 4]
def baseStart_5392412 : Nat := 118140960795 + 5392412 * 2 ^ 59
def prefixEnd_5392412 : Nat := 4983230072969 + 3 ^ 40 * 5392412 * 2
def baseEnd_5392412 : Nat := 922966414357553798983585

theorem tailTrace_5392412 : CollatzResearch.WordTrace tailWord_5392412 prefixEnd_5392412 922966414357553798983585 := by
  unfold tailWord_5392412
  simp only [CollatzResearch.WordTrace]
  refine ⟨98338711670109874747041745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131118282226813166329388993 98338711670109874747041745)
  ·
    refine ⟨73754033752582406060281309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98338711670109874747041745 73754033752582406060281309)
    ·
      refine ⟨27657762657218402272605491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73754033752582406060281309 27657762657218402272605491)
      ·
        refine ⟨41486643985827603408908237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27657762657218402272605491 41486643985827603408908237)
        ·
          refine ⟨15557491494685351278340589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41486643985827603408908237 15557491494685351278340589)
          ·
            refine ⟨5834059310507006729377721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15557491494685351278340589 5834059310507006729377721)
            ·
              refine ⟨4375544482880255047033291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5834059310507006729377721 4375544482880255047033291)
              ·
                refine ⟨6563316724320382570549937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4375544482880255047033291 6563316724320382570549937)
                ·
                  refine ⟨4922487543240286927912453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6563316724320382570549937 4922487543240286927912453)
                  ·
                    refine ⟨922966414357553798983585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4922487543240286927912453 922966414357553798983585)
                    ·
                      rfl

theorem cell23_5392412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_5392412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392412 prefixEnd_5392412 := by exact prefixLift 5392412
  have htrace : WordTrace (prefixWord ++ tailWord_5392412) baseStart_5392412 baseEnd_5392412 := by
    simpa [prefixWord, tailWord_5392412, baseEnd_5392412] using wordTrace_append hprefix tailTrace_5392412
  have hstable : (prefixWord ++ tailWord_5392412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392412).length < 2 ^ (prefixWord ++ tailWord_5392412).sum := by decide
  have hdescent : baseEnd_5392412 < baseStart_5392412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392418 : List Nat := [3, 3, 1, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_5392418 : Nat := 118140960795 + 5392418 * 2 ^ 59
def prefixEnd_5392418 : Nat := 4983230072969 + 3 ^ 40 * 5392418 * 2
def baseEnd_5392418 : Nat := 2768902323956588373475727

theorem tailTrace_5392418 : CollatzResearch.WordTrace tailWord_5392418 prefixEnd_5392418 2768902323956588373475727 := by
  unfold tailWord_5392418
  simp only [CollatzResearch.WordTrace]
  refine ⟨49169410544549503129700477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131118428118798675012534605 49169410544549503129700477)
  ·
    refine ⟨18438528954206063673637679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49169410544549503129700477 18438528954206063673637679)
    ·
      refine ⟨27657793431309095510456519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18438528954206063673637679 27657793431309095510456519)
      ·
        refine ⟨41486690146963643265684779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27657793431309095510456519 41486690146963643265684779)
        ·
          refine ⟨62230035220445464898527169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41486690146963643265684779 62230035220445464898527169)
          ·
            refine ⟨46672526415334098673895377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62230035220445464898527169 46672526415334098673895377)
            ·
              refine ⟨35004394811500574005421533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46672526415334098673895377 35004394811500574005421533)
              ·
                refine ⟨13126648054312715252033075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35004394811500574005421533 13126648054312715252033075)
                ·
                  refine ⟨19689972081469072878049613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13126648054312715252033075 19689972081469072878049613)
                  ·
                    refine ⟨7383739530550902329268605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19689972081469072878049613 7383739530550902329268605)
                    ·
                      refine ⟨2768902323956588373475727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7383739530550902329268605 2768902323956588373475727)
                      ·
                        rfl

theorem cell23_5392418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_5392418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392418 prefixEnd_5392418 := by exact prefixLift 5392418
  have htrace : WordTrace (prefixWord ++ tailWord_5392418) baseStart_5392418 baseEnd_5392418 := by
    simpa [prefixWord, tailWord_5392418, baseEnd_5392418] using wordTrace_append hprefix tailTrace_5392418
  have hstable : (prefixWord ++ tailWord_5392418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392418).length < 2 ^ (prefixWord ++ tailWord_5392418).sum := by decide
  have hdescent : baseEnd_5392418 < baseStart_5392418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392458 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 5, 4, 2]
def baseStart_5392458 : Nat := 118140960795 + 5392458 * 2 ^ 59
def prefixEnd_5392458 : Nat := 4983230072969 + 3 ^ 40 * 5392458 * 2
def baseEnd_5392458 : Nat := 2768922863182768216975543

theorem tailTrace_5392458 : CollatzResearch.WordTrace tailWord_5392458 prefixEnd_5392458 2768922863182768216975543 := by
  unfold tailWord_5392458
  simp only [CollatzResearch.WordTrace]
  refine ⟨49169775274513274837564507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131119400732035399566838685 49169775274513274837564507)
  ·
    refine ⟨73754662911769912256346761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49169775274513274837564507 73754662911769912256346761)
    ·
      refine ⟨55315997183827434192260071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73754662911769912256346761 55315997183827434192260071)
      ·
        refine ⟨82973995775741151288390107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55315997183827434192260071 82973995775741151288390107)
        ·
          refine ⟨124460993663611726932585161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82973995775741151288390107 124460993663611726932585161)
          ·
            refine ⟨93345745247708795199438871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124460993663611726932585161 93345745247708795199438871)
            ·
              refine ⟨140018617871563192799158307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93345745247708795199438871 140018617871563192799158307)
              ·
                refine ⟨210027926807344789198737461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140018617871563192799158307 210027926807344789198737461)
                ·
                  refine ⟨19690118138188573987381637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 210027926807344789198737461 19690118138188573987381637)
                  ·
                    refine ⟨3691897150910357622634057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19690118138188573987381637 3691897150910357622634057)
                    ·
                      refine ⟨2768922863182768216975543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3691897150910357622634057 2768922863182768216975543)
                      ·
                        rfl

theorem cell23_5392458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_5392458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392458 prefixEnd_5392458 := by exact prefixLift 5392458
  have htrace : WordTrace (prefixWord ++ tailWord_5392458) baseStart_5392458 baseEnd_5392458 := by
    simpa [prefixWord, tailWord_5392458, baseEnd_5392458] using wordTrace_append hprefix tailTrace_5392458
  have hstable : (prefixWord ++ tailWord_5392458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392458).length < 2 ^ (prefixWord ++ tailWord_5392458).sum := by decide
  have hdescent : baseEnd_5392458 < baseStart_5392458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392471 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 4]
def baseStart_5392471 : Nat := 118140960795 + 5392471 * 2 ^ 59
def prefixEnd_5392471 : Nat := 4983230072969 + 3 ^ 40 * 5392471 * 2
def baseEnd_5392471 : Nat := 2768929538431276666112983

theorem tailTrace_5392471 : CollatzResearch.WordTrace tailWord_5392471 prefixEnd_5392471 2768929538431276666112983 := by
  unfold tailWord_5392471
  simp only [CollatzResearch.WordTrace]
  refine ⟨196679575247006002570481267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131119716831337335046987511 196679575247006002570481267)
  ·
    refine ⟨295019362870509003855721901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196679575247006002570481267 295019362870509003855721901)
    ·
      refine ⟨110632261076440876445895713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295019362870509003855721901 110632261076440876445895713)
      ·
        refine ⟨82974195807330657334421785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110632261076440876445895713 82974195807330657334421785)
        ·
          refine ⟨62230646855497993000816339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82974195807330657334421785 62230646855497993000816339)
          ·
            refine ⟨93345970283246989501224509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62230646855497993000816339 93345970283246989501224509)
            ·
              refine ⟨35004738856217621062959191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93345970283246989501224509 35004738856217621062959191)
              ·
                refine ⟨52507108284326431594438787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35004738856217621062959191 52507108284326431594438787)
                ·
                  refine ⟨78760662426489647391658181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52507108284326431594438787 78760662426489647391658181)
                  ·
                    refine ⟨14767624204966808885935909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78760662426489647391658181 14767624204966808885935909)
                    ·
                      refine ⟨2768929538431276666112983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14767624204966808885935909 2768929538431276666112983)
                      ·
                        rfl

theorem cell23_5392471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_5392471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392471 prefixEnd_5392471 := by exact prefixLift 5392471
  have htrace : WordTrace (prefixWord ++ tailWord_5392471) baseStart_5392471 baseEnd_5392471 := by
    simpa [prefixWord, tailWord_5392471, baseEnd_5392471] using wordTrace_append hprefix tailTrace_5392471
  have hstable : (prefixWord ++ tailWord_5392471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392471).length < 2 ^ (prefixWord ++ tailWord_5392471).sum := by decide
  have hdescent : baseEnd_5392471 < baseStart_5392471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
