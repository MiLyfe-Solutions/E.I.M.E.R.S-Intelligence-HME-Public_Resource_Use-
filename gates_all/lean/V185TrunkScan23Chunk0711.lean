import V185TrunkScan23Chunk0710

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4203397 : List Nat := [1, 3, 1, 1, 3, 4, 2, 1, 1, 1, 5]
def baseStart_4203397 : Nat := 118140960795 + 4203397 * 2 ^ 59
def prefixEnd_4203397 : Nat := 4983230072969 + 3 ^ 40 * 4203397 * 2
def baseEnd_4203397 : Nat := 2158363042666995923606435

theorem tailTrace_4203397 : CollatzResearch.WordTrace tailWord_4203397 prefixEnd_4203397 2158363042666995923606435 := by
  unfold tailWord_4203397
  simp only [CollatzResearch.WordTrace]
  refine ⟨153310483552818026899120445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102206989035212017932746963 153310483552818026899120445)
  ·
    refine ⟨57491431332306760087170167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153310483552818026899120445 57491431332306760087170167)
    ·
      refine ⟨86237146998460140130755251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57491431332306760087170167 86237146998460140130755251)
      ·
        refine ⟨129355720497690210196132877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86237146998460140130755251 129355720497690210196132877)
        ·
          refine ⟨48508395186633828823549829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129355720497690210196132877 48508395186633828823549829)
          ·
            refine ⟨9095324097493842904415593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48508395186633828823549829 9095324097493842904415593)
            ·
              refine ⟨6821493073120382178311695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9095324097493842904415593 6821493073120382178311695)
              ·
                refine ⟨10232239609680573267467543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6821493073120382178311695 10232239609680573267467543)
                ·
                  refine ⟨15348359414520859901201315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10232239609680573267467543 15348359414520859901201315)
                  ·
                    refine ⟨23022539121781289851801973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15348359414520859901201315 23022539121781289851801973)
                    ·
                      refine ⟨2158363042666995923606435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23022539121781289851801973 2158363042666995923606435)
                      ·
                        rfl

theorem cell23_4203397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_4203397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203397 prefixEnd_4203397 := by exact prefixLift 4203397
  have htrace : WordTrace (prefixWord ++ tailWord_4203397) baseStart_4203397 baseEnd_4203397 := by
    simpa [prefixWord, tailWord_4203397, baseEnd_4203397] using wordTrace_append hprefix tailTrace_4203397
  have hstable : (prefixWord ++ tailWord_4203397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203397).length < 2 ^ (prefixWord ++ tailWord_4203397).sum := by decide
  have hdescent : baseEnd_4203397 < baseStart_4203397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203400 : List Nat := [2, 1, 3, 3, 2, 1, 11]
def baseStart_4203400 : Nat := 118140960795 + 4203400 * 2 ^ 59
def prefixEnd_4203400 : Nat := 4983230072969 + 3 ^ 40 * 4203400 * 2
def baseEnd_4203400 : Nat := 26646476334678511257641

theorem tailTrace_4203400 : CollatzResearch.WordTrace tailWord_4203400 prefixEnd_4203400 26646476334678511257641 := by
  unfold tailWord_4203400
  simp only [CollatzResearch.WordTrace]
  refine ⟨76655296485903579205739827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102207061981204772274319769 76655296485903579205739827)
  ·
    refine ⟨114982944728855368808609741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76655296485903579205739827 114982944728855368808609741)
    ·
      refine ⟨43118604273320763303228653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114982944728855368808609741 43118604273320763303228653)
      ·
        refine ⟨16169476602495286238710745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43118604273320763303228653 16169476602495286238710745)
        ·
          refine ⟨12127107451871464679033059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16169476602495286238710745 12127107451871464679033059)
          ·
            refine ⟨18190661177807197018549589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12127107451871464679033059 18190661177807197018549589)
            ·
              refine ⟨26646476334678511257641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18190661177807197018549589 26646476334678511257641)
              ·
                rfl

theorem cell23_4203400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 11].length) (baseStart_4203400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203400 prefixEnd_4203400 := by exact prefixLift 4203400
  have htrace : WordTrace (prefixWord ++ tailWord_4203400) baseStart_4203400 baseEnd_4203400 := by
    simpa [prefixWord, tailWord_4203400, baseEnd_4203400] using wordTrace_append hprefix tailTrace_4203400
  have hstable : (prefixWord ++ tailWord_4203400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203400).length < 2 ^ (prefixWord ++ tailWord_4203400).sum := by decide
  have hdescent : baseEnd_4203400 < baseStart_4203400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203478 : List Nat := [5, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_4203478 : Nat := 118140960795 + 4203478 * 2 ^ 59
def prefixEnd_4203478 : Nat := 4983230072969 + 3 ^ 40 * 4203478 * 2
def baseEnd_4203478 : Nat := 2158404634600010106693563

theorem tailTrace_4203478 : CollatzResearch.WordTrace tailWord_4203478 prefixEnd_4203478 2158404634600010106693563 := by
  unfold tailWord_4203478
  simp only [CollatzResearch.WordTrace]
  refine ⟨9582089866595286108301193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102208958577016385155212725 9582089866595286108301193)
  ·
    refine ⟨7186567399946464581225895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9582089866595286108301193 7186567399946464581225895)
    ·
      refine ⟨10779851099919696871838843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7186567399946464581225895 10779851099919696871838843)
      ·
        refine ⟨16169776649879545307758265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10779851099919696871838843 16169776649879545307758265)
        ·
          refine ⟨12127332487409658980818699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16169776649879545307758265 12127332487409658980818699)
          ·
            refine ⟨18190998731114488471228049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12127332487409658980818699 18190998731114488471228049)
            ·
              refine ⟨13643249048335866353421037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18190998731114488471228049 13643249048335866353421037)
              ·
                refine ⟨5116218393125949882532889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13643249048335866353421037 5116218393125949882532889)
                ·
                  refine ⟨3837163794844462411899667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5116218393125949882532889 3837163794844462411899667)
                  ·
                    refine ⟨5755745692266693617849501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3837163794844462411899667 5755745692266693617849501)
                    ·
                      refine ⟨2158404634600010106693563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5755745692266693617849501 2158404634600010106693563)
                      ·
                        rfl

theorem cell23_4203478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_4203478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203478 prefixEnd_4203478 := by exact prefixLift 4203478
  have htrace : WordTrace (prefixWord ++ tailWord_4203478) baseStart_4203478 baseEnd_4203478 := by
    simpa [prefixWord, tailWord_4203478, baseEnd_4203478] using wordTrace_append hprefix tailTrace_4203478
  have hstable : (prefixWord ++ tailWord_4203478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203478).length < 2 ^ (prefixWord ++ tailWord_4203478).sum := by decide
  have hdescent : baseEnd_4203478 < baseStart_4203478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203500 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 7]
def baseStart_4203500 : Nat := 118140960795 + 4203500 * 2 ^ 59
def prefixEnd_4203500 : Nat := 4983230072969 + 3 ^ 40 * 4203500 * 2
def baseEnd_4203500 : Nat := 2158415931174409020618461

theorem tailTrace_4203500 : CollatzResearch.WordTrace tailWord_4203500 prefixEnd_4203500 2158415931174409020618461 := by
  unfold tailWord_4203500
  simp only [CollatzResearch.WordTrace]
  refine ⟨76657120135722437745059977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102209493514296583660079969 76657120135722437745059977)
  ·
    refine ⟨57492840101791828308794983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76657120135722437745059977 57492840101791828308794983)
    ·
      refine ⟨86239260152687742463192475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57492840101791828308794983 86239260152687742463192475)
      ·
        refine ⟨129358890229031613694788713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86239260152687742463192475 129358890229031613694788713)
        ·
          refine ⟨97019167671773710271091535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129358890229031613694788713 97019167671773710271091535)
          ·
            refine ⟨145528751507660565406637303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97019167671773710271091535 145528751507660565406637303)
            ·
              refine ⟨218293127261490848109955955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145528751507660565406637303 218293127261490848109955955)
              ·
                refine ⟨327439690892236272164933933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218293127261490848109955955 327439690892236272164933933)
                ·
                  refine ⟨122789884084588602061850225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327439690892236272164933933 122789884084588602061850225)
                  ·
                    refine ⟨92092413063441451546387669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122789884084588602061850225 92092413063441451546387669)
                    ·
                      refine ⟨2158415931174409020618461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92092413063441451546387669 2158415931174409020618461)
                      ·
                        rfl

theorem cell23_4203500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_4203500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203500 prefixEnd_4203500 := by exact prefixLift 4203500
  have htrace : WordTrace (prefixWord ++ tailWord_4203500) baseStart_4203500 baseEnd_4203500 := by
    simpa [prefixWord, tailWord_4203500, baseEnd_4203500] using wordTrace_append hprefix tailTrace_4203500
  have hstable : (prefixWord ++ tailWord_4203500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203500).length < 2 ^ (prefixWord ++ tailWord_4203500).sum := by decide
  have hdescent : baseEnd_4203500 < baseStart_4203500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203534 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3]
def baseStart_4203534 : Nat := 118140960795 + 4203534 * 2 ^ 59
def prefixEnd_4203534 : Nat := 4983230072969 + 3 ^ 40 * 4203534 * 2
def baseEnd_4203534 : Nat := 2158433389516661887593305

theorem tailTrace_4203534 : CollatzResearch.WordTrace tailWord_4203534 prefixEnd_4203534 2158433389516661887593305 := by
  unfold tailWord_4203534
  simp only [CollatzResearch.WordTrace]
  refine ⟨19164435044165212412107207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102210320235547799531238437 19164435044165212412107207)
  ·
    refine ⟨28746652566247818618160811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19164435044165212412107207 28746652566247818618160811)
    ·
      refine ⟨43119978849371727927241217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28746652566247818618160811 43119978849371727927241217)
      ·
        refine ⟨32339984137028795945430913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43119978849371727927241217 32339984137028795945430913)
        ·
          refine ⟨24254988102771596959073185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32339984137028795945430913 24254988102771596959073185)
          ·
            refine ⟨18191241077078697719304889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24254988102771596959073185 18191241077078697719304889)
            ·
              refine ⟨13643430807809023289478667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18191241077078697719304889 13643430807809023289478667)
              ·
                refine ⟨20465146211713534934218001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13643430807809023289478667 20465146211713534934218001)
                ·
                  refine ⟨15348859658785151200663501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20465146211713534934218001 15348859658785151200663501)
                  ·
                    refine ⟨5755822372044431700248813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15348859658785151200663501 5755822372044431700248813)
                    ·
                      refine ⟨2158433389516661887593305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5755822372044431700248813 2158433389516661887593305)
                      ·
                        rfl

theorem cell23_4203534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_4203534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203534 prefixEnd_4203534 := by exact prefixLift 4203534
  have htrace : WordTrace (prefixWord ++ tailWord_4203534) baseStart_4203534 baseEnd_4203534 := by
    simpa [prefixWord, tailWord_4203534, baseEnd_4203534] using wordTrace_append hprefix tailTrace_4203534
  have hstable : (prefixWord ++ tailWord_4203534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203534).length < 2 ^ (prefixWord ++ tailWord_4203534).sum := by decide
  have hdescent : baseEnd_4203534 < baseStart_4203534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203557 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 1, 3, 4]
def baseStart_4203557 : Nat := 118140960795 + 4203557 * 2 ^ 59
def prefixEnd_4203557 : Nat := 4983230072969 + 3 ^ 40 * 4203557 * 2
def baseEnd_4203557 : Nat := 2158445199571715297605699

theorem tailTrace_4203557 : CollatzResearch.WordTrace tailWord_4203557 prefixEnd_4203557 2158445199571715297605699 := by
  unfold tailWord_4203557
  simp only [CollatzResearch.WordTrace]
  refine ⟨153316319232238374224944925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102210879488158916149963283 153316319232238374224944925)
  ·
    refine ⟨57493619712089390334354347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153316319232238374224944925 57493619712089390334354347)
    ·
      refine ⟨86240429568134085501531521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57493619712089390334354347 86240429568134085501531521)
      ·
        refine ⟨64680322176100564126148641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86240429568134085501531521 64680322176100564126148641)
        ·
          refine ⟨48510241632075423094611481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64680322176100564126148641 48510241632075423094611481)
          ·
            refine ⟨36382681224056567320958611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48510241632075423094611481 36382681224056567320958611)
            ·
              refine ⟨54574021836084850981437917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36382681224056567320958611 54574021836084850981437917)
              ·
                refine ⟨20465258188531819118039219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54574021836084850981437917 20465258188531819118039219)
                ·
                  refine ⟨30697887282797728677058829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20465258188531819118039219 30697887282797728677058829)
                  ·
                    refine ⟨11511707731049148253897061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30697887282797728677058829 11511707731049148253897061)
                    ·
                      refine ⟨2158445199571715297605699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11511707731049148253897061 2158445199571715297605699)
                      ·
                        rfl

theorem cell23_4203557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_4203557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203557 prefixEnd_4203557 := by exact prefixLift 4203557
  have htrace : WordTrace (prefixWord ++ tailWord_4203557) baseStart_4203557 baseEnd_4203557 := by
    simpa [prefixWord, tailWord_4203557, baseEnd_4203557] using wordTrace_append hprefix tailTrace_4203557
  have hstable : (prefixWord ++ tailWord_4203557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203557).length < 2 ^ (prefixWord ++ tailWord_4203557).sum := by decide
  have hdescent : baseEnd_4203557 < baseStart_4203557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203664 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 1, 8, 2]
def baseStart_4203664 : Nat := 118140960795 + 4203664 * 2 ^ 59
def prefixEnd_4203664 : Nat := 4983230072969 + 3 ^ 40 * 4203664 * 2
def baseEnd_4203664 : Nat := 2158500142001746378967707

theorem tailTrace_4203664 : CollatzResearch.WordTrace tailWord_4203664 prefixEnd_4203664 2158500142001746378967707 := by
  unfold tailWord_4203664
  simp only [CollatzResearch.WordTrace]
  refine ⟨76660110921425365749545023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102213481228567154332726697 76660110921425365749545023)
  ·
    refine ⟨114990166382138048624317535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76660110921425365749545023 114990166382138048624317535)
    ·
      refine ⟨172485249573207072936476303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114990166382138048624317535 172485249573207072936476303)
      ·
        refine ⟨258727874359810609404714455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172485249573207072936476303 258727874359810609404714455)
        ·
          refine ⟨388091811539715914107071683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258727874359810609404714455 388091811539715914107071683)
          ·
            refine ⟨582137717309573871160607525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388091811539715914107071683 582137717309573871160607525)
            ·
              refine ⟨109150821995545100842613911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 582137717309573871160607525 109150821995545100842613911)
              ·
                refine ⟨163726232993317651263920867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109150821995545100842613911 163726232993317651263920867)
                ·
                  refine ⟨245589349489976476895881301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163726232993317651263920867 245589349489976476895881301)
                  ·
                    refine ⟨2878000189335661838623609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 245589349489976476895881301 2878000189335661838623609)
                    ·
                      refine ⟨2158500142001746378967707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2878000189335661838623609 2158500142001746378967707)
                      ·
                        rfl

theorem cell23_4203664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 8, 2].length) (baseStart_4203664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203664 prefixEnd_4203664 := by exact prefixLift 4203664
  have htrace : WordTrace (prefixWord ++ tailWord_4203664) baseStart_4203664 baseEnd_4203664 := by
    simpa [prefixWord, tailWord_4203664, baseEnd_4203664] using wordTrace_append hprefix tailTrace_4203664
  have hstable : (prefixWord ++ tailWord_4203664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203664).length < 2 ^ (prefixWord ++ tailWord_4203664).sum := by decide
  have hdescent : baseEnd_4203664 < baseStart_4203664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203678 : List Nat := [4, 3, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_4203678 : Nat := 118140960795 + 4203678 * 2 ^ 59
def prefixEnd_4203678 : Nat := 4983230072969 + 3 ^ 40 * 4203678 * 2
def baseEnd_4203678 : Nat := 719502443576969774730881

theorem tailTrace_4203678 : CollatzResearch.WordTrace tailWord_4203678 prefixEnd_4203678 719502443576969774730881 := by
  unfold tailWord_4203678
  simp only [CollatzResearch.WordTrace]
  refine ⟨19165091558100001486262461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102213821643200007926733125 19165091558100001486262461)
  ·
    refine ⟨7186909334287500557348423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19165091558100001486262461 7186909334287500557348423)
    ·
      refine ⟨10780364001431250836022635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7186909334287500557348423 10780364001431250836022635)
      ·
        refine ⟨16170546002146876254033953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10780364001431250836022635 16170546002146876254033953)
        ·
          refine ⟨12127909501610157190525465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16170546002146876254033953 12127909501610157190525465)
          ·
            refine ⟨9095932126207617892894099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12127909501610157190525465 9095932126207617892894099)
            ·
              refine ⟨13643898189311426839341149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9095932126207617892894099 13643898189311426839341149)
              ·
                refine ⟨5116461820991785064752931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13643898189311426839341149 5116461820991785064752931)
                ·
                  refine ⟨7674692731487677597129397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5116461820991785064752931 7674692731487677597129397)
                  ·
                    refine ⟨719502443576969774730881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7674692731487677597129397 719502443576969774730881)
                    ·
                      rfl

theorem cell23_4203678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_4203678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203678 prefixEnd_4203678 := by exact prefixLift 4203678
  have htrace : WordTrace (prefixWord ++ tailWord_4203678) baseStart_4203678 baseEnd_4203678 := by
    simpa [prefixWord, tailWord_4203678, baseEnd_4203678] using wordTrace_append hprefix tailTrace_4203678
  have hstable : (prefixWord ++ tailWord_4203678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203678).length < 2 ^ (prefixWord ++ tailWord_4203678).sum := by decide
  have hdescent : baseEnd_4203678 < baseStart_4203678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203681 : List Nat := [1, 2, 3, 3, 1, 1, 3, 3, 1, 1, 4]
def baseStart_4203681 : Nat := 118140960795 + 4203681 * 2 ^ 59
def prefixEnd_4203681 : Nat := 4983230072969 + 3 ^ 40 * 4203681 * 2
def baseEnd_4203681 : Nat := 2158508871172872812455129

theorem tailTrace_4203681 : CollatzResearch.WordTrace tailWord_4203681 prefixEnd_4203681 2158508871172872812455129 := by
  unfold tailWord_4203681
  simp only [CollatzResearch.WordTrace]
  refine ⟨153320841883789143402458897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102213894589192762268305931 153320841883789143402458897)
  ·
    refine ⟨114990631412841857551844173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153320841883789143402458897 114990631412841857551844173)
    ·
      refine ⟨43121486779815696581941565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114990631412841857551844173 43121486779815696581941565)
      ·
        refine ⟨16170557542430886218228087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43121486779815696581941565 16170557542430886218228087)
        ·
          refine ⟨24255836313646329327342131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16170557542430886218228087 24255836313646329327342131)
          ·
            refine ⟨36383754470469493991013197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24255836313646329327342131 36383754470469493991013197)
            ·
              refine ⟨13643907926426060246629949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36383754470469493991013197 13643907926426060246629949)
              ·
                refine ⟨5116465472409772592486231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13643907926426060246629949 5116465472409772592486231)
                ·
                  refine ⟨7674698208614658888729347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5116465472409772592486231 7674698208614658888729347)
                  ·
                    refine ⟨11512047312921988333094021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7674698208614658888729347 11512047312921988333094021)
                    ·
                      refine ⟨2158508871172872812455129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11512047312921988333094021 2158508871172872812455129)
                      ·
                        rfl

theorem cell23_4203681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_4203681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203681 prefixEnd_4203681 := by exact prefixLift 4203681
  have htrace : WordTrace (prefixWord ++ tailWord_4203681) baseStart_4203681 baseEnd_4203681 := by
    simpa [prefixWord, tailWord_4203681, baseEnd_4203681] using wordTrace_append hprefix tailTrace_4203681
  have hstable : (prefixWord ++ tailWord_4203681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203681).length < 2 ^ (prefixWord ++ tailWord_4203681).sum := by decide
  have hdescent : baseEnd_4203681 < baseStart_4203681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203698 : List Nat := [3, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2]
def baseStart_4203698 : Nat := 118140960795 + 4203698 * 2 ^ 59
def prefixEnd_4203698 : Nat := 4983230072969 + 3 ^ 40 * 4203698 * 2
def baseEnd_4203698 : Nat := 2158517600343999245942551

theorem tailTrace_4203698 : CollatzResearch.WordTrace tailWord_4203698 prefixEnd_4203698 2158517600343999245942551 := by
  unfold tailWord_4203698
  simp only [CollatzResearch.WordTrace]
  refine ⟨38330365481181888826456937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102214307949818370203885165 38330365481181888826456937)
  ·
    refine ⟨28747774110886416619842703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38330365481181888826456937 28747774110886416619842703)
    ·
      refine ⟨43121661166329624929764055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28747774110886416619842703 43121661166329624929764055)
      ·
        refine ⟨64682491749494437394646083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43121661166329624929764055 64682491749494437394646083)
        ·
          refine ⟨97023737624241656091969125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64682491749494437394646083 97023737624241656091969125)
          ·
            refine ⟨18191950804545310517244211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97023737624241656091969125 18191950804545310517244211)
            ·
              refine ⟨27287926206817965775866317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18191950804545310517244211 27287926206817965775866317)
              ·
                refine ⟨10232972327556737165949869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27287926206817965775866317 10232972327556737165949869)
                ·
                  refine ⟨3837364622833776437231201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10232972327556737165949869 3837364622833776437231201)
                  ·
                    refine ⟨2878023467125332327923401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3837364622833776437231201 2878023467125332327923401)
                    ·
                      refine ⟨2158517600343999245942551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2878023467125332327923401 2158517600343999245942551)
                      ·
                        rfl

theorem cell23_4203698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_4203698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203698 prefixEnd_4203698 := by exact prefixLift 4203698
  have htrace : WordTrace (prefixWord ++ tailWord_4203698) baseStart_4203698 baseEnd_4203698 := by
    simpa [prefixWord, tailWord_4203698, baseEnd_4203698] using wordTrace_append hprefix tailTrace_4203698
  have hstable : (prefixWord ++ tailWord_4203698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203698).length < 2 ^ (prefixWord ++ tailWord_4203698).sum := by decide
  have hdescent : baseEnd_4203698 < baseStart_4203698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203707 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 6]
def baseStart_4203707 : Nat := 118140960795 + 4203707 * 2 ^ 59
def prefixEnd_4203707 : Nat := 4983230072969 + 3 ^ 40 * 4203707 * 2
def baseEnd_4203707 : Nat := 2158522221669889710730009

theorem tailTrace_4203707 : CollatzResearch.WordTrace tailWord_4203707 prefixEnd_4203707 2158522221669889710730009 := by
  unfold tailWord_4203707
  simp only [CollatzResearch.WordTrace]
  refine ⟨153321790181694949842905375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102214526787796633228603583 153321790181694949842905375)
  ·
    refine ⟨229982685272542424764358063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153321790181694949842905375 229982685272542424764358063)
    ·
      refine ⟨344974027908813637146537095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229982685272542424764358063 344974027908813637146537095)
      ·
        refine ⟨517461041863220455719805643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344974027908813637146537095 517461041863220455719805643)
        ·
          refine ⟨776191562794830683579708465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517461041863220455719805643 776191562794830683579708465)
          ·
            refine ⟨582143672096123012684781349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 776191562794830683579708465 582143672096123012684781349)
            ·
              refine ⟨109151938518023064878396503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 582143672096123012684781349 109151938518023064878396503)
              ·
                refine ⟨163727907777034597317594755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109151938518023064878396503 163727907777034597317594755)
                ·
                  refine ⟨245591861665551895976392133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163727907777034597317594755 245591861665551895976392133)
                  ·
                    refine ⟨46048474062290980495573525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 245591861665551895976392133 46048474062290980495573525)
                    ·
                      refine ⟨2158522221669889710730009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46048474062290980495573525 2158522221669889710730009)
                      ·
                        rfl

theorem cell23_4203707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 6].length) (baseStart_4203707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203707 prefixEnd_4203707 := by exact prefixLift 4203707
  have htrace : WordTrace (prefixWord ++ tailWord_4203707) baseStart_4203707 baseEnd_4203707 := by
    simpa [prefixWord, tailWord_4203707, baseEnd_4203707] using wordTrace_append hprefix tailTrace_4203707
  have hstable : (prefixWord ++ tailWord_4203707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203707).length < 2 ^ (prefixWord ++ tailWord_4203707).sum := by decide
  have hdescent : baseEnd_4203707 < baseStart_4203707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203749 : List Nat := [1, 3, 1, 4, 3, 1, 3, 2, 1, 2, 2]
def baseStart_4203749 : Nat := 118140960795 + 4203749 * 2 ^ 59
def prefixEnd_4203749 : Nat := 4983230072969 + 3 ^ 40 * 4203749 * 2
def baseEnd_4203749 : Nat := 2158543787857378546404817

theorem tailTrace_4203749 : CollatzResearch.WordTrace tailWord_4203749 prefixEnd_4203749 2158543787857378546404817 := by
  unfold tailWord_4203749
  simp only [CollatzResearch.WordTrace]
  refine ⟨153323322047542791015934301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102215548031695194010622867 153323322047542791015934301)
  ·
    refine ⟨57496245767828546630975363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153323322047542791015934301 57496245767828546630975363)
    ·
      refine ⟨86244368651742819946463045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57496245767828546630975363 86244368651742819946463045)
      ·
        refine ⟨16170819122201778739961821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86244368651742819946463045 16170819122201778739961821)
        ·
          refine ⟨6064057170825667027485683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16170819122201778739961821 6064057170825667027485683)
          ·
            refine ⟨9096085756238500541228525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6064057170825667027485683 9096085756238500541228525)
            ·
              refine ⟨3411032158589437702960697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9096085756238500541228525 3411032158589437702960697)
              ·
                refine ⟨2558274118942078277220523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3411032158589437702960697 2558274118942078277220523)
                ·
                  refine ⟨3837411178413117415830785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2558274118942078277220523 3837411178413117415830785)
                  ·
                    refine ⟨2878058383809838061873089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3837411178413117415830785 2878058383809838061873089)
                    ·
                      refine ⟨2158543787857378546404817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2878058383809838061873089 2158543787857378546404817)
                      ·
                        rfl

theorem cell23_4203749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_4203749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203749 prefixEnd_4203749 := by exact prefixLift 4203749
  have htrace : WordTrace (prefixWord ++ tailWord_4203749) baseStart_4203749 baseEnd_4203749 := by
    simpa [prefixWord, tailWord_4203749, baseEnd_4203749] using wordTrace_append hprefix tailTrace_4203749
  have hstable : (prefixWord ++ tailWord_4203749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203749).length < 2 ^ (prefixWord ++ tailWord_4203749).sum := by decide
  have hdescent : baseEnd_4203749 < baseStart_4203749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203775 : List Nat := [1, 1, 2, 2, 1, 7, 1, 2, 1, 3, 2]
def baseStart_4203775 : Nat := 118140960795 + 4203775 * 2 ^ 59
def prefixEnd_4203775 : Nat := 4983230072969 + 3 ^ 40 * 4203775 * 2
def baseEnd_4203775 : Nat := 2158557138354395444679697

theorem tailTrace_4203775 : CollatzResearch.WordTrace tailWord_4203775 prefixEnd_4203775 2158557138354395444679697 := by
  unfold tailWord_4203775
  simp only [CollatzResearch.WordTrace]
  refine ⟨153324270345448597456380779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102216180230299064970920519 153324270345448597456380779)
  ·
    refine ⟨229986405518172896184571169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153324270345448597456380779 229986405518172896184571169)
    ·
      refine ⟨172489804138629672138428377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229986405518172896184571169 172489804138629672138428377)
      ·
        refine ⟨129367353103972254103821283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172489804138629672138428377 129367353103972254103821283)
        ·
          refine ⟨194051029655958381155731925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129367353103972254103821283 194051029655958381155731925)
          ·
            refine ⟨4548071007561524558337467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 194051029655958381155731925 4548071007561524558337467)
            ·
              refine ⟨6822106511342286837506201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4548071007561524558337467 6822106511342286837506201)
              ·
                refine ⟨5116579883506715128129651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6822106511342286837506201 5116579883506715128129651)
                ·
                  refine ⟨7674869825260072692194477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5116579883506715128129651 7674869825260072692194477)
                  ·
                    refine ⟨2878076184472527259572929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7674869825260072692194477 2878076184472527259572929)
                    ·
                      refine ⟨2158557138354395444679697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2878076184472527259572929 2158557138354395444679697)
                      ·
                        rfl

theorem cell23_4203775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 3, 2].length) (baseStart_4203775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203775 prefixEnd_4203775 := by exact prefixLift 4203775
  have htrace : WordTrace (prefixWord ++ tailWord_4203775) baseStart_4203775 baseEnd_4203775 := by
    simpa [prefixWord, tailWord_4203775, baseEnd_4203775] using wordTrace_append hprefix tailTrace_4203775
  have hstable : (prefixWord ++ tailWord_4203775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203775).length < 2 ^ (prefixWord ++ tailWord_4203775).sum := by decide
  have hdescent : baseEnd_4203775 < baseStart_4203775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203788 : List Nat := [2, 2, 1, 2, 2, 4, 1, 2, 1, 4, 2]
def baseStart_4203788 : Nat := 118140960795 + 4203788 * 2 ^ 59
def prefixEnd_4203788 : Nat := 4983230072969 + 3 ^ 40 * 4203788 * 2
def baseEnd_4203788 : Nat := 2158563813602903893817137

theorem tailTrace_4203788 : CollatzResearch.WordTrace tailWord_4203788 prefixEnd_4203788 2158563813602903893817137 := by
  unfold tailWord_4203788
  simp only [CollatzResearch.WordTrace]
  refine ⟨76662372247200750338302009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102216496329601000451069345 76662372247200750338302009)
  ·
    refine ⟨57496779185400562753726507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76662372247200750338302009 57496779185400562753726507)
    ·
      refine ⟨86245168778100844130589761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57496779185400562753726507 86245168778100844130589761)
      ·
        refine ⟨64683876583575633097942321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86245168778100844130589761 64683876583575633097942321)
        ·
          refine ⟨48512907437681724823456741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64683876583575633097942321 48512907437681724823456741)
          ·
            refine ⟨9096170144565323404398139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48512907437681724823456741 9096170144565323404398139)
            ·
              refine ⟨13644255216847985106597209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9096170144565323404398139 13644255216847985106597209)
              ·
                refine ⟨10233191412635988829947907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13644255216847985106597209 10233191412635988829947907)
                ·
                  refine ⟨15349787118953983244921861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10233191412635988829947907 15349787118953983244921861)
                  ·
                    refine ⟨2878085084803871858422849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15349787118953983244921861 2878085084803871858422849)
                    ·
                      refine ⟨2158563813602903893817137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2878085084803871858422849 2158563813602903893817137)
                      ·
                        rfl

theorem cell23_4203788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_4203788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203788 prefixEnd_4203788 := by exact prefixLift 4203788
  have htrace : WordTrace (prefixWord ++ tailWord_4203788) baseStart_4203788 baseEnd_4203788 := by
    simpa [prefixWord, tailWord_4203788, baseEnd_4203788] using wordTrace_append hprefix tailTrace_4203788
  have hstable : (prefixWord ++ tailWord_4203788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203788).length < 2 ^ (prefixWord ++ tailWord_4203788).sum := by decide
  have hdescent : baseEnd_4203788 < baseStart_4203788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203804 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_4203804 : Nat := 118140960795 + 4203804 * 2 ^ 59
def prefixEnd_4203804 : Nat := 4983230072969 + 3 ^ 40 * 4203804 * 2
def baseEnd_4203804 : Nat := 2158572029293375831217063

theorem tailTrace_4203804 : CollatzResearch.WordTrace tailWord_4203804 prefixEnd_4203804 2158572029293375831217063 := by
  unfold tailWord_4203804
  simp only [CollatzResearch.WordTrace]
  refine ⟨76662664031171767704593233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102216885374895690272790977 76662664031171767704593233)
  ·
    refine ⟨57496998023378825778444925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76662664031171767704593233 57496998023378825778444925)
    ·
      refine ⟨21561374258767059666916847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57496998023378825778444925 21561374258767059666916847)
      ·
        refine ⟨32342061388150589500375271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21561374258767059666916847 32342061388150589500375271)
        ·
          refine ⟨48513092082225884250562907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32342061388150589500375271 48513092082225884250562907)
          ·
            refine ⟨72769638123338826375844361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48513092082225884250562907 72769638123338826375844361)
            ·
              refine ⟨54577228592504119781883271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72769638123338826375844361 54577228592504119781883271)
              ·
                refine ⟨81865842888756179672824907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54577228592504119781883271 81865842888756179672824907)
                ·
                  refine ⟨122798764333134269509237361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81865842888756179672824907 122798764333134269509237361)
                  ·
                    refine ⟨92099073249850702131928021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122798764333134269509237361 92099073249850702131928021)
                    ·
                      refine ⟨2158572029293375831217063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92099073249850702131928021 2158572029293375831217063)
                      ·
                        rfl

theorem cell23_4203804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_4203804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203804 prefixEnd_4203804 := by exact prefixLift 4203804
  have htrace : WordTrace (prefixWord ++ tailWord_4203804) baseStart_4203804 baseEnd_4203804 := by
    simpa [prefixWord, tailWord_4203804, baseEnd_4203804] using wordTrace_append hprefix tailTrace_4203804
  have hstable : (prefixWord ++ tailWord_4203804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203804).length < 2 ^ (prefixWord ++ tailWord_4203804).sum := by decide
  have hdescent : baseEnd_4203804 < baseStart_4203804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203818 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_4203818 : Nat := 118140960795 + 4203818 * 2 ^ 59
def prefixEnd_4203818 : Nat := 4983230072969 + 3 ^ 40 * 4203818 * 2
def baseEnd_4203818 : Nat := 2158579218022538776441999

theorem tailTrace_4203818 : CollatzResearch.WordTrace tailWord_4203818 prefixEnd_4203818 2158579218022538776441999 := by
  unfold tailWord_4203818
  simp only [CollatzResearch.WordTrace]
  refine ⟨38331459671073203950049027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102217225789528543866797405 38331459671073203950049027)
  ·
    refine ⟨57497189506609805925073541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38331459671073203950049027 57497189506609805925073541)
    ·
      refine ⟨10780723032489338610951289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57497189506609805925073541 10780723032489338610951289)
      ·
        refine ⟨8085542274367003958213467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10780723032489338610951289 8085542274367003958213467)
        ·
          refine ⟨12128313411550505937320201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8085542274367003958213467 12128313411550505937320201)
          ·
            refine ⟨9096235058662879452990151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12128313411550505937320201 9096235058662879452990151)
            ·
              refine ⟨13644352587994319179485227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9096235058662879452990151 13644352587994319179485227)
              ·
                refine ⟨20466528881991478769227841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13644352587994319179485227 20466528881991478769227841)
                ·
                  refine ⟨15349896661493609076920881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20466528881991478769227841 15349896661493609076920881)
                  ·
                    refine ⟨11512422496120206807690661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15349896661493609076920881 11512422496120206807690661)
                    ·
                      refine ⟨2158579218022538776441999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11512422496120206807690661 2158579218022538776441999)
                      ·
                        rfl

theorem cell23_4203818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_4203818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203818 prefixEnd_4203818 := by exact prefixLift 4203818
  have htrace : WordTrace (prefixWord ++ tailWord_4203818) baseStart_4203818 baseEnd_4203818 := by
    simpa [prefixWord, tailWord_4203818, baseEnd_4203818] using wordTrace_append hprefix tailTrace_4203818
  have hstable : (prefixWord ++ tailWord_4203818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203818).length < 2 ^ (prefixWord ++ tailWord_4203818).sum := by decide
  have hdescent : baseEnd_4203818 < baseStart_4203818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203824 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 1, 7]
def baseStart_4203824 : Nat := 118140960795 + 4203824 * 2 ^ 59
def prefixEnd_4203824 : Nat := 4983230072969 + 3 ^ 40 * 4203824 * 2
def baseEnd_4203824 : Nat := 719527432968821917655657

theorem tailTrace_4203824 : CollatzResearch.WordTrace tailWord_4203824 prefixEnd_4203824 719527432968821917655657 := by
  unfold tailWord_4203824
  simp only [CollatzResearch.WordTrace]
  refine ⟨76663028761135539412457263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102217371681514052549943017 76663028761135539412457263)
  ·
    refine ⟨114994543141703309118685895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76663028761135539412457263 114994543141703309118685895)
    ·
      refine ⟨172491814712554963678028843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114994543141703309118685895 172491814712554963678028843)
      ·
        refine ⟨258737722068832445517043265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172491814712554963678028843 258737722068832445517043265)
        ·
          refine ⟨194053291551624334137782449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258737722068832445517043265 194053291551624334137782449)
          ·
            refine ⟨145539968663718250603336837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194053291551624334137782449 145539968663718250603336837)
            ·
              refine ⟨27288744124447171988125657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145539968663718250603336837 27288744124447171988125657)
              ·
                refine ⟨20466558093335378991094243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27288744124447171988125657 20466558093335378991094243)
                ·
                  refine ⟨30699837140003068486641365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20466558093335378991094243 30699837140003068486641365)
                  ·
                    refine ⟨719527432968821917655657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30699837140003068486641365 719527432968821917655657)
                    ·
                      rfl

theorem cell23_4203824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 1, 7].length) (baseStart_4203824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203824 prefixEnd_4203824 := by exact prefixLift 4203824
  have htrace : WordTrace (prefixWord ++ tailWord_4203824) baseStart_4203824 baseEnd_4203824 := by
    simpa [prefixWord, tailWord_4203824, baseEnd_4203824] using wordTrace_append hprefix tailTrace_4203824
  have hstable : (prefixWord ++ tailWord_4203824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203824).length < 2 ^ (prefixWord ++ tailWord_4203824).sum := by decide
  have hdescent : baseEnd_4203824 < baseStart_4203824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203881 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 6, 2, 3]
def baseStart_4203881 : Nat := 118140960795 + 4203881 * 2 ^ 59
def prefixEnd_4203881 : Nat := 4983230072969 + 3 ^ 40 * 4203881 * 2
def baseEnd_4203881 : Nat := 2158611567303772029954209

theorem tailTrace_4203881 : CollatzResearch.WordTrace tailWord_4203881 prefixEnd_4203881 2158611567303772029954209 := by
  unfold tailWord_4203881
  simp only [CollatzResearch.WordTrace]
  refine ⟨153328136483064577559739497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102218757655376385039826331 153328136483064577559739497)
  ·
    refine ⟨114996102362298433169804623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153328136483064577559739497 114996102362298433169804623)
    ·
      refine ⟨172494153543447649754706935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114996102362298433169804623 172494153543447649754706935)
      ·
        refine ⟨258741230315171474632060403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172494153543447649754706935 258741230315171474632060403)
        ·
          refine ⟨388111845472757211948090605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258741230315171474632060403 388111845472757211948090605)
          ·
            refine ⟨145541942052283954480533977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 388111845472757211948090605 145541942052283954480533977)
            ·
              refine ⟨109156456539212965860400483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145541942052283954480533977 109156456539212965860400483)
              ·
                refine ⟨163734684808819448790600725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109156456539212965860400483 163734684808819448790600725)
                ·
                  refine ⟨7675063350413411662059409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 163734684808819448790600725 7675063350413411662059409)
                  ·
                    refine ⟨5756297512810058746544557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7675063350413411662059409 5756297512810058746544557)
                    ·
                      refine ⟨2158611567303772029954209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5756297512810058746544557 2158611567303772029954209)
                      ·
                        rfl

theorem cell23_4203881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 2, 3].length) (baseStart_4203881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203881 prefixEnd_4203881 := by exact prefixLift 4203881
  have htrace : WordTrace (prefixWord ++ tailWord_4203881) baseStart_4203881 baseEnd_4203881 := by
    simpa [prefixWord, tailWord_4203881, baseEnd_4203881] using wordTrace_append hprefix tailTrace_4203881
  have hstable : (prefixWord ++ tailWord_4203881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203881).length < 2 ^ (prefixWord ++ tailWord_4203881).sum := by decide
  have hdescent : baseEnd_4203881 < baseStart_4203881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203935 : List Nat := [1, 1, 2, 5, 1, 4, 2, 1, 6]
def baseStart_4203935 : Nat := 118140960795 + 4203935 * 2 ^ 59
def prefixEnd_4203935 : Nat := 4983230072969 + 3 ^ 40 * 4203935 * 2
def baseEnd_4203935 : Nat := 239848810584346090964329

theorem tailTrace_4203935 : CollatzResearch.WordTrace tailWord_4203935 prefixEnd_4203935 239848810584346090964329 := by
  unfold tailWord_4203935
  simp only [CollatzResearch.WordTrace]
  refine ⟨153330106024868944782205259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102220070683245963188136839 153330106024868944782205259)
  ·
    refine ⟨229995159037303417173307889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153330106024868944782205259 229995159037303417173307889)
    ·
      refine ⟨172496369277977562879980917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229995159037303417173307889 172496369277977562879980917)
      ·
        refine ⟨16171534619810396519998211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 172496369277977562879980917 16171534619810396519998211)
        ·
          refine ⟨24257301929715594779997317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16171534619810396519998211 24257301929715594779997317)
          ·
            refine ⟨4548244111821674021249497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24257301929715594779997317 4548244111821674021249497)
            ·
              refine ⟨3411183083866255515937123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4548244111821674021249497 3411183083866255515937123)
              ·
                refine ⟨5116774625799383273905685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3411183083866255515937123 5116774625799383273905685)
                ·
                  refine ⟨239848810584346090964329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5116774625799383273905685 239848810584346090964329)
                  ·
                    rfl

theorem cell23_4203935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 6].length) (baseStart_4203935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203935 prefixEnd_4203935 := by exact prefixLift 4203935
  have htrace : WordTrace (prefixWord ++ tailWord_4203935) baseStart_4203935 baseEnd_4203935 := by
    simpa [prefixWord, tailWord_4203935, baseEnd_4203935] using wordTrace_append hprefix tailTrace_4203935
  have hstable : (prefixWord ++ tailWord_4203935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203935).length < 2 ^ (prefixWord ++ tailWord_4203935).sum := by decide
  have hdescent : baseEnd_4203935 < baseStart_4203935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203948 : List Nat := [2, 2, 1, 1, 1, 1, 7, 2, 1, 5]
def baseStart_4203948 : Nat := 118140960795 + 4203948 * 2 ^ 59
def prefixEnd_4203948 : Nat := 4983230072969 + 3 ^ 40 * 4203948 * 2
def baseEnd_4203948 : Nat := 719548656835874422605467

theorem tailTrace_4203948 : CollatzResearch.WordTrace tailWord_4203948 prefixEnd_4203948 719548656835874422605467 := by
  unfold tailWord_4203948
  simp only [CollatzResearch.WordTrace]
  refine ⟨76665290086910924001214249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102220386782547898668285665 76665290086910924001214249)
  ·
    refine ⟨57498967565183193000910687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76665290086910924001214249 57498967565183193000910687)
    ·
      refine ⟨86248451347774789501366031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57498967565183193000910687 86248451347774789501366031)
      ·
        refine ⟨129372677021662184252049047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86248451347774789501366031 129372677021662184252049047)
        ·
          refine ⟨194059015532493276378073571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129372677021662184252049047 194059015532493276378073571)
          ·
            refine ⟨291088523298739914567110357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194059015532493276378073571 291088523298739914567110357)
            ·
              refine ⟨6822387264814216747666649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 291088523298739914567110357 6822387264814216747666649)
              ·
                refine ⟨5116790448610662560749987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6822387264814216747666649 5116790448610662560749987)
                ·
                  refine ⟨7675185672915993841124981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5116790448610662560749987 7675185672915993841124981)
                  ·
                    refine ⟨719548656835874422605467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7675185672915993841124981 719548656835874422605467)
                    ·
                      rfl

theorem cell23_4203948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 5].length) (baseStart_4203948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203948 prefixEnd_4203948 := by exact prefixLift 4203948
  have htrace : WordTrace (prefixWord ++ tailWord_4203948) baseStart_4203948 baseEnd_4203948 := by
    simpa [prefixWord, tailWord_4203948, baseEnd_4203948] using wordTrace_append hprefix tailTrace_4203948
  have hstable : (prefixWord ++ tailWord_4203948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203948).length < 2 ^ (prefixWord ++ tailWord_4203948).sum := by decide
  have hdescent : baseEnd_4203948 < baseStart_4203948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203965 : List Nat := [1, 4, 1, 2, 2, 1, 5, 1, 1, 5]
def baseStart_4203965 : Nat := 118140960795 + 4203965 * 2 ^ 59
def prefixEnd_4203965 : Nat := 4983230072969 + 3 ^ 40 * 4203965 * 2
def baseEnd_4203965 : Nat := 719551566559583233767941

theorem tailTrace_4203965 : CollatzResearch.WordTrace tailWord_4203965 prefixEnd_4203965 719551566559583233767941 := by
  unfold tailWord_4203965
  simp only [CollatzResearch.WordTrace]
  refine ⟨153331200214760259905797349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102220800143173506603864899 153331200214760259905797349)
  ·
    refine ⟨28749600040267548732337003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153331200214760259905797349 28749600040267548732337003)
    ·
      refine ⟨43124400060401323098505505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28749600040267548732337003 43124400060401323098505505)
      ·
        refine ⟨32343300045300992323879129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43124400060401323098505505 32343300045300992323879129)
        ·
          refine ⟨24257475033975744242909347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32343300045300992323879129 24257475033975744242909347)
          ·
            refine ⟨36386212550963616364364021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24257475033975744242909347 36386212550963616364364021)
            ·
              refine ⟨3411207426652839034159127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36386212550963616364364021 3411207426652839034159127)
              ·
                refine ⟨5116811139979258551238691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3411207426652839034159127 5116811139979258551238691)
                ·
                  refine ⟨7675216709968887826858037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5116811139979258551238691 7675216709968887826858037)
                  ·
                    refine ⟨719551566559583233767941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7675216709968887826858037 719551566559583233767941)
                    ·
                      rfl

theorem cell23_4203965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_4203965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203965 prefixEnd_4203965 := by exact prefixLift 4203965
  have htrace : WordTrace (prefixWord ++ tailWord_4203965) baseStart_4203965 baseEnd_4203965 := by
    simpa [prefixWord, tailWord_4203965, baseEnd_4203965] using wordTrace_append hprefix tailTrace_4203965
  have hstable : (prefixWord ++ tailWord_4203965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203965).length < 2 ^ (prefixWord ++ tailWord_4203965).sum := by decide
  have hdescent : baseEnd_4203965 < baseStart_4203965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203968 : List Nat := [2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 4]
def baseStart_4203968 : Nat := 118140960795 + 4203968 * 2 ^ 59
def prefixEnd_4203968 : Nat := 4983230072969 + 3 ^ 40 * 4203968 * 2
def baseEnd_4203968 : Nat := 2158656240120713189566309

theorem tailTrace_4203968 : CollatzResearch.WordTrace tailWord_4203968 prefixEnd_4203968 2158656240120713189566309 := by
  unfold tailWord_4203968
  simp only [CollatzResearch.WordTrace]
  refine ⟨76665654816874695709078279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102220873089166260945437705 76665654816874695709078279)
  ·
    refine ⟨114998482225312043563617419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76665654816874695709078279 114998482225312043563617419)
    ·
      refine ⟨172497723337968065345426129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114998482225312043563617419 172497723337968065345426129)
      ·
        refine ⟨129373292503476049009069597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172497723337968065345426129 129373292503476049009069597)
        ·
          refine ⟨48514984688803518378401099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129373292503476049009069597 48514984688803518378401099)
          ·
            refine ⟨72772477033205277567601649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48514984688803518378401099 72772477033205277567601649)
            ·
              refine ⟨54579357774903958175701237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72772477033205277567601649 54579357774903958175701237)
              ·
                refine ⟨5116814791397246078971991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54579357774903958175701237 5116814791397246078971991)
                ·
                  refine ⟨7675222187095869118457987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5116814791397246078971991 7675222187095869118457987)
                  ·
                    refine ⟨11512833280643803677686981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7675222187095869118457987 11512833280643803677686981)
                    ·
                      refine ⟨2158656240120713189566309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11512833280643803677686981 2158656240120713189566309)
                      ·
                        rfl

theorem cell23_4203968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 4].length) (baseStart_4203968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203968 prefixEnd_4203968 := by exact prefixLift 4203968
  have htrace : WordTrace (prefixWord ++ tailWord_4203968) baseStart_4203968 baseEnd_4203968 := by
    simpa [prefixWord, tailWord_4203968, baseEnd_4203968] using wordTrace_append hprefix tailTrace_4203968
  have hstable : (prefixWord ++ tailWord_4203968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203968).length < 2 ^ (prefixWord ++ tailWord_4203968).sum := by decide
  have hdescent : baseEnd_4203968 < baseStart_4203968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4203972 : List Nat := [2, 3, 3, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_4203972 : Nat := 118140960795 + 4203972 * 2 ^ 59
def prefixEnd_4203972 : Nat := 4983230072969 + 3 ^ 40 * 4203972 * 2
def baseEnd_4203972 : Nat := 2158658294043331173916291

theorem tailTrace_4203972 : CollatzResearch.WordTrace tailWord_4203972 prefixEnd_4203972 2158658294043331173916291 := by
  unfold tailWord_4203972
  simp only [CollatzResearch.WordTrace]
  refine ⟨76665727762867450050651085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102220970350489933400868113 76665727762867450050651085)
  ·
    refine ⟨28749647911075293768994157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76665727762867450050651085 28749647911075293768994157)
    ·
      refine ⟨10781117966653235163372809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28749647911075293768994157 10781117966653235163372809)
      ·
        refine ⟨8085838474989926372529607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10781117966653235163372809 8085838474989926372529607)
        ·
          refine ⟨12128757712484889558794411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8085838474989926372529607 12128757712484889558794411)
          ·
            refine ⟨18193136568727334338191617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12128757712484889558794411 18193136568727334338191617)
            ·
              refine ⟨13644852426545500753643713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18193136568727334338191617 13644852426545500753643713)
              ·
                refine ⟨10233639319909125565232785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13644852426545500753643713 10233639319909125565232785)
                ·
                  refine ⟨7675229489931844173924589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10233639319909125565232785 7675229489931844173924589)
                  ·
                    refine ⟨2878211058724441565221721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7675229489931844173924589 2878211058724441565221721)
                    ·
                      refine ⟨2158658294043331173916291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2878211058724441565221721 2158658294043331173916291)
                      ·
                        rfl

theorem cell23_4203972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_4203972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4203972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4203972 prefixEnd_4203972 := by exact prefixLift 4203972
  have htrace : WordTrace (prefixWord ++ tailWord_4203972) baseStart_4203972 baseEnd_4203972 := by
    simpa [prefixWord, tailWord_4203972, baseEnd_4203972] using wordTrace_append hprefix tailTrace_4203972
  have hstable : (prefixWord ++ tailWord_4203972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4203972).length < 2 ^ (prefixWord ++ tailWord_4203972).sum := by decide
  have hdescent : baseEnd_4203972 < baseStart_4203972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4203972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204005 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 3, 2, 3]
def baseStart_4204005 : Nat := 118140960795 + 4204005 * 2 ^ 59
def prefixEnd_4204005 : Nat := 4983230072969 + 3 ^ 40 * 4204005 * 2
def baseEnd_4204005 : Nat := 2158675238904929544803639

theorem tailTrace_4204005 : CollatzResearch.WordTrace tailWord_4204005 prefixEnd_4204005 2158675238904929544803639 := by
  unfold tailWord_4204005
  simp only [CollatzResearch.WordTrace]
  refine ⟨153332659134615346737253469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102221772756410231158168979 153332659134615346737253469)
  ·
    refine ⟨57499747175480755026470051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153332659134615346737253469 57499747175480755026470051)
    ·
      refine ⟨86249620763221132539705077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57499747175480755026470051 86249620763221132539705077)
      ·
        refine ⟨8085901946551981175597351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86249620763221132539705077 8085901946551981175597351)
        ·
          refine ⟨12128852919827971763396027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8085901946551981175597351 12128852919827971763396027)
          ·
            refine ⟨18193279379741957645094041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12128852919827971763396027 18193279379741957645094041)
            ·
              refine ⟨13644959534806468233820531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18193279379741957645094041 13644959534806468233820531)
              ·
                refine ⟨20467439302209702350730797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13644959534806468233820531 20467439302209702350730797)
                ·
                  refine ⟨7675289738328638381524049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20467439302209702350730797 7675289738328638381524049)
                  ·
                    refine ⟨5756467303746478786143037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7675289738328638381524049 5756467303746478786143037)
                    ·
                      refine ⟨2158675238904929544803639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5756467303746478786143037 2158675238904929544803639)
                      ·
                        rfl

theorem cell23_4204005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_4204005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204005 prefixEnd_4204005 := by exact prefixLift 4204005
  have htrace : WordTrace (prefixWord ++ tailWord_4204005) baseStart_4204005 baseEnd_4204005 := by
    simpa [prefixWord, tailWord_4204005, baseEnd_4204005] using wordTrace_append hprefix tailTrace_4204005
  have hstable : (prefixWord ++ tailWord_4204005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204005).length < 2 ^ (prefixWord ++ tailWord_4204005).sum := by decide
  have hdescent : baseEnd_4204005 < baseStart_4204005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204008 : List Nat := [2, 1, 4, 1, 1, 2, 5, 7]
def baseStart_4204008 : Nat := 118140960795 + 4204008 * 2 ^ 59
def prefixEnd_4204008 : Nat := 4983230072969 + 3 ^ 40 * 4204008 * 2
def baseEnd_4204008 : Nat := 79950991827662704928375

theorem tailTrace_4204008 : CollatzResearch.WordTrace tailWord_4204008 prefixEnd_4204008 79950991827662704928375 := by
  unfold tailWord_4204008
  simp only [CollatzResearch.WordTrace]
  refine ⟨76666384276802239124806339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102221845702402985499741785 76666384276802239124806339)
  ·
    refine ⟨114999576415203358687209509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76666384276802239124806339 114999576415203358687209509)
    ·
      refine ⟨21562420577850629753851783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114999576415203358687209509 21562420577850629753851783)
      ·
        refine ⟨32343630866775944630777675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21562420577850629753851783 32343630866775944630777675)
        ·
          refine ⟨48515446300163916946166513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32343630866775944630777675 48515446300163916946166513)
          ·
            refine ⟨36386584725122937709624885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48515446300163916946166513 36386584725122937709624885)
            ·
              refine ⟨3411242317980275410277333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36386584725122937709624885 3411242317980275410277333)
              ·
                refine ⟨79950991827662704928375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3411242317980275410277333 79950991827662704928375)
                ·
                  rfl

theorem cell23_4204008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 7].length) (baseStart_4204008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204008 prefixEnd_4204008 := by exact prefixLift 4204008
  have htrace : WordTrace (prefixWord ++ tailWord_4204008) baseStart_4204008 baseEnd_4204008 := by
    simpa [prefixWord, tailWord_4204008, baseEnd_4204008] using wordTrace_append hprefix tailTrace_4204008
  have hstable : (prefixWord ++ tailWord_4204008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204008).length < 2 ^ (prefixWord ++ tailWord_4204008).sum := by decide
  have hdescent : baseEnd_4204008 < baseStart_4204008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204022 : List Nat := [5, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3]
def baseStart_4204022 : Nat := 118140960795 + 4204022 * 2 ^ 59
def prefixEnd_4204022 : Nat := 4983230072969 + 3 ^ 40 * 4204022 * 2
def baseEnd_4204022 : Nat := 2158683968076055978291061

theorem tailTrace_4204022 : CollatzResearch.WordTrace tailWord_4204022 prefixEnd_4204022 2158683968076055978291061 := by
  unfold tailWord_4204022
  simp only [CollatzResearch.WordTrace]
  refine ⟨9583329948472109915038895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102222186117035839093748213 9583329948472109915038895)
  ·
    refine ⟨14374994922708164872558343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9583329948472109915038895 14374994922708164872558343)
    ·
      refine ⟨21562492384062247308837515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14374994922708164872558343 21562492384062247308837515)
      ·
        refine ⟨32343738576093370963256273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21562492384062247308837515 32343738576093370963256273)
        ·
          refine ⟨24257803932070028222442205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32343738576093370963256273 24257803932070028222442205)
          ·
            refine ⟨9096676474526260583415827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24257803932070028222442205 9096676474526260583415827)
            ·
              refine ⟨13645014711789390875123741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9096676474526260583415827 13645014711789390875123741)
              ·
                refine ⟨5116880516921021578171403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13645014711789390875123741 5116880516921021578171403)
                ·
                  refine ⟨7675320775381532367257105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5116880516921021578171403 7675320775381532367257105)
                  ·
                    refine ⟨5756490581536149275442829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7675320775381532367257105 5756490581536149275442829)
                    ·
                      refine ⟨2158683968076055978291061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5756490581536149275442829 2158683968076055978291061)
                      ·
                        rfl

theorem cell23_4204022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_4204022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204022 prefixEnd_4204022 := by exact prefixLift 4204022
  have htrace : WordTrace (prefixWord ++ tailWord_4204022) baseStart_4204022 baseEnd_4204022 := by
    simpa [prefixWord, tailWord_4204022, baseEnd_4204022] using wordTrace_append hprefix tailTrace_4204022
  have hstable : (prefixWord ++ tailWord_4204022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204022).length < 2 ^ (prefixWord ++ tailWord_4204022).sum := by decide
  have hdescent : baseEnd_4204022 < baseStart_4204022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204031 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 5]
def baseStart_4204031 : Nat := 118140960795 + 4204031 * 2 ^ 59
def prefixEnd_4204031 : Nat := 4983230072969 + 3 ^ 40 * 4204031 * 2
def baseEnd_4204031 : Nat := 2158688589401946443078519

theorem tailTrace_4204031 : CollatzResearch.WordTrace tailWord_4204031 prefixEnd_4204031 2158688589401946443078519 := by
  unfold tailWord_4204031
  simp only [CollatzResearch.WordTrace]
  refine ⟨153333607432521153177699947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102222404955014102118466631 153333607432521153177699947)
  ·
    refine ⟨230000411148781729766549921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153333607432521153177699947 230000411148781729766549921)
    ·
      refine ⟨172500308361586297324912441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230000411148781729766549921 172500308361586297324912441)
      ·
        refine ⟨129375231271189722993684331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172500308361586297324912441 129375231271189722993684331)
        ·
          refine ⟨194062846906784584490526497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129375231271189722993684331 194062846906784584490526497)
          ·
            refine ⟨145547135180088438367894873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194062846906784584490526497 145547135180088438367894873)
            ·
              refine ⟨109160351385066328775921155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145547135180088438367894873 109160351385066328775921155)
              ·
                refine ⟨163740527077599493163881733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109160351385066328775921155 163740527077599493163881733)
                ·
                  refine ⟨30701348827049904968227825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163740527077599493163881733 30701348827049904968227825)
                  ·
                    refine ⟨23026011620287428726170869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30701348827049904968227825 23026011620287428726170869)
                    ·
                      refine ⟨2158688589401946443078519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23026011620287428726170869 2158688589401946443078519)
                      ·
                        rfl

theorem cell23_4204031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_4204031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204031 prefixEnd_4204031 := by exact prefixLift 4204031
  have htrace : WordTrace (prefixWord ++ tailWord_4204031) baseStart_4204031 baseEnd_4204031 := by
    simpa [prefixWord, tailWord_4204031, baseEnd_4204031] using wordTrace_append hprefix tailTrace_4204031
  have hstable : (prefixWord ++ tailWord_4204031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204031).length < 2 ^ (prefixWord ++ tailWord_4204031).sum := by decide
  have hdescent : baseEnd_4204031 < baseStart_4204031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204035 : List Nat := [1, 1, 1, 3, 2, 1, 2, 6, 2, 1, 3]
def baseStart_4204035 : Nat := 118140960795 + 4204035 * 2 ^ 59
def prefixEnd_4204035 : Nat := 4983230072969 + 3 ^ 40 * 4204035 * 2
def baseEnd_4204035 : Nat := 2158690643324564427428501

theorem tailTrace_4204035 : CollatzResearch.WordTrace tailWord_4204035 prefixEnd_4204035 2158690643324564427428501 := by
  unfold tailWord_4204035
  simp only [CollatzResearch.WordTrace]
  refine ⟨153333753324506661860845559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102222502216337774573897039 153333753324506661860845559)
  ·
    refine ⟨230000629986759992791268339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153333753324506661860845559 230000629986759992791268339)
    ·
      refine ⟨345000944980139989186902509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230000629986759992791268339 345000944980139989186902509)
      ·
        refine ⟨129375354367552495945088441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 345000944980139989186902509 129375354367552495945088441)
        ·
          refine ⟨97031515775664371958816331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129375354367552495945088441 97031515775664371958816331)
          ·
            refine ⟨145547273663496557938224497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97031515775664371958816331 145547273663496557938224497)
            ·
              refine ⟨109160455247622418453668373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145547273663496557938224497 109160455247622418453668373)
              ·
                refine ⟨5116896339732300865015705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 109160455247622418453668373 5116896339732300865015705)
                ·
                  refine ⟨3837672254799225648761779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5116896339732300865015705 3837672254799225648761779)
                  ·
                    refine ⟨5756508382198838473142669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3837672254799225648761779 5756508382198838473142669)
                    ·
                      refine ⟨2158690643324564427428501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5756508382198838473142669 2158690643324564427428501)
                      ·
                        rfl

theorem cell23_4204035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 1, 3].length) (baseStart_4204035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204035 prefixEnd_4204035 := by exact prefixLift 4204035
  have htrace : WordTrace (prefixWord ++ tailWord_4204035) baseStart_4204035 baseEnd_4204035 := by
    simpa [prefixWord, tailWord_4204035, baseEnd_4204035] using wordTrace_append hprefix tailTrace_4204035
  have hstable : (prefixWord ++ tailWord_4204035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204035).length < 2 ^ (prefixWord ++ tailWord_4204035).sum := by decide
  have hdescent : baseEnd_4204035 < baseStart_4204035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204149 : List Nat := [1, 3, 4, 2, 1, 1, 4, 2, 5]
def baseStart_4204149 : Nat := 118140960795 + 4204149 * 2 ^ 59
def prefixEnd_4204149 : Nat := 4983230072969 + 3 ^ 40 * 4204149 * 2
def baseEnd_4204149 : Nat := 239861020013241886822553

theorem tailTrace_4204149 : CollatzResearch.WordTrace tailWord_4204149 prefixEnd_4204149 239861020013241886822553 := by
  unfold tailWord_4204149
  simp only [CollatzResearch.WordTrace]
  refine ⟨153337911246093659330495501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102225274164062439553663667 153337911246093659330495501)
  ·
    refine ⟨57501716717285122248935813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153337911246093659330495501 57501716717285122248935813)
    ·
      refine ⟨10781571884490960421675465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57501716717285122248935813 10781571884490960421675465)
      ·
        refine ⟨8086178913368220316256599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10781571884490960421675465 8086178913368220316256599)
        ·
          refine ⟨12129268370052330474384899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8086178913368220316256599 12129268370052330474384899)
          ·
            refine ⟨18193902555078495711577349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12129268370052330474384899 18193902555078495711577349)
            ·
              refine ⟨3411356729077217945920753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18193902555078495711577349 3411356729077217945920753)
              ·
                refine ⟨2558517546807913459440565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3411356729077217945920753 2558517546807913459440565)
                ·
                  refine ⟨239861020013241886822553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2558517546807913459440565 239861020013241886822553)
                  ·
                    rfl

theorem cell23_4204149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 5].length) (baseStart_4204149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204149 prefixEnd_4204149 := by exact prefixLift 4204149
  have htrace : WordTrace (prefixWord ++ tailWord_4204149) baseStart_4204149 baseEnd_4204149 := by
    simpa [prefixWord, tailWord_4204149, baseEnd_4204149] using wordTrace_append hprefix tailTrace_4204149
  have hstable : (prefixWord ++ tailWord_4204149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204149).length < 2 ^ (prefixWord ++ tailWord_4204149).sum := by decide
  have hdescent : baseEnd_4204149 < baseStart_4204149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204185 : List Nat := [1, 2, 1, 2, 1, 2, 2, 5, 2, 2, 3]
def baseStart_4204185 : Nat := 118140960795 + 4204185 * 2 ^ 59
def prefixEnd_4204185 : Nat := 4983230072969 + 3 ^ 40 * 4204185 * 2
def baseEnd_4204185 : Nat := 2158767665422738840552811

theorem tailTrace_4204185 : CollatzResearch.WordTrace tailWord_4204185 prefixEnd_4204185 2158767665422738840552811 := by
  unfold tailWord_4204185
  simp only [CollatzResearch.WordTrace]
  refine ⟨153339224273963237478806009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102226149515975491652537339 153339224273963237478806009)
  ·
    refine ⟨115004418205472428109104507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153339224273963237478806009 115004418205472428109104507)
    ·
      refine ⟨172506627308208642163656761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115004418205472428109104507 172506627308208642163656761)
      ·
        refine ⟨129379970481156481622742571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172506627308208642163656761 129379970481156481622742571)
        ·
          refine ⟨194069955721734722434113857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129379970481156481622742571 194069955721734722434113857)
          ·
            refine ⟨145552466791301041825585393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194069955721734722434113857 145552466791301041825585393)
            ·
              refine ⟨109164350093475781369189045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145552466791301041825585393 109164350093475781369189045)
              ·
                refine ⟨10234157821263354503361473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109164350093475781369189045 10234157821263354503361473)
                ·
                  refine ⟨7675618365947515877521105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10234157821263354503361473 7675618365947515877521105)
                  ·
                    refine ⟨5756713774460636908140829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7675618365947515877521105 5756713774460636908140829)
                    ·
                      refine ⟨2158767665422738840552811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5756713774460636908140829 2158767665422738840552811)
                      ·
                        rfl

theorem cell23_4204185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_4204185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204185 prefixEnd_4204185 := by exact prefixLift 4204185
  have htrace : WordTrace (prefixWord ++ tailWord_4204185) baseStart_4204185 baseEnd_4204185 := by
    simpa [prefixWord, tailWord_4204185, baseEnd_4204185] using wordTrace_append hprefix tailTrace_4204185
  have hstable : (prefixWord ++ tailWord_4204185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204185).length < 2 ^ (prefixWord ++ tailWord_4204185).sum := by decide
  have hdescent : baseEnd_4204185 < baseStart_4204185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204205 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 8]
def baseStart_4204205 : Nat := 118140960795 + 4204205 * 2 ^ 59
def prefixEnd_4204205 : Nat := 4983230072969 + 3 ^ 40 * 4204205 * 2
def baseEnd_4204205 : Nat := 239864215003980973589191

theorem tailTrace_4204205 : CollatzResearch.WordTrace tailWord_4204205 prefixEnd_4204205 239864215003980973589191 := by
  unfold tailWord_4204205
  simp only [CollatzResearch.WordTrace]
  refine ⟨153339953733890780894534069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102226635822593853929689379 153339953733890780894534069)
  ·
    refine ⟨14375620662552260708862569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153339953733890780894534069 14375620662552260708862569)
    ·
      refine ⟨10781715496914195531646927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14375620662552260708862569 10781715496914195531646927)
      ·
        refine ⟨16172573245371293297470391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10781715496914195531646927 16172573245371293297470391)
        ·
          refine ⟨24258859868056939946205587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16172573245371293297470391 24258859868056939946205587)
          ·
            refine ⟨36388289802085409919308381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24258859868056939946205587 36388289802085409919308381)
            ·
              refine ⟨13645608675782028719740643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36388289802085409919308381 13645608675782028719740643)
              ·
                refine ⟨20468413013673043079610965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13645608675782028719740643 20468413013673043079610965)
                ·
                  refine ⟨239864215003980973589191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20468413013673043079610965 239864215003980973589191)
                  ·
                    rfl

theorem cell23_4204205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_4204205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204205 prefixEnd_4204205 := by exact prefixLift 4204205
  have htrace : WordTrace (prefixWord ++ tailWord_4204205) baseStart_4204205 baseEnd_4204205 := by
    simpa [prefixWord, tailWord_4204205, baseEnd_4204205] using wordTrace_append hprefix tailTrace_4204205
  have hstable : (prefixWord ++ tailWord_4204205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204205).length < 2 ^ (prefixWord ++ tailWord_4204205).sum := by decide
  have hdescent : baseEnd_4204205 < baseStart_4204205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204208 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 6]
def baseStart_4204208 : Nat := 118140960795 + 4204208 * 2 ^ 59
def prefixEnd_4204208 : Nat := 4983230072969 + 3 ^ 40 * 4204208 * 2
def baseEnd_4204208 : Nat := 2158779475477792250565205

theorem tailTrace_4204208 : CollatzResearch.WordTrace tailWord_4204208 prefixEnd_4204208 2158779475477792250565205 := by
  unfold tailWord_4204208
  simp only [CollatzResearch.WordTrace]
  refine ⟨76670031576439956203446639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102226708768586608271262185 76670031576439956203446639)
  ·
    refine ⟨115005047364659934305169959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76670031576439956203446639 115005047364659934305169959)
    ·
      refine ⟨172507571046989901457754939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115005047364659934305169959 172507571046989901457754939)
      ·
        refine ⟨258761356570484852186632409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172507571046989901457754939 258761356570484852186632409)
        ·
          refine ⟨194071017427863639139974307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258761356570484852186632409 194071017427863639139974307)
          ·
            refine ⟨291106526141795458709961461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194071017427863639139974307 291106526141795458709961461)
            ·
              refine ⟨27291236825793324254058887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 291106526141795458709961461 27291236825793324254058887)
              ·
                refine ⟨40936855238689986381088331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27291236825793324254058887 40936855238689986381088331)
                ·
                  refine ⟨61405282858034979571632497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40936855238689986381088331 61405282858034979571632497)
                  ·
                    refine ⟨46053962143526234678724373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61405282858034979571632497 46053962143526234678724373)
                    ·
                      refine ⟨2158779475477792250565205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46053962143526234678724373 2158779475477792250565205)
                      ·
                        rfl

theorem cell23_4204208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_4204208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204208 prefixEnd_4204208 := by exact prefixLift 4204208
  have htrace : WordTrace (prefixWord ++ tailWord_4204208) baseStart_4204208 baseEnd_4204208 := by
    simpa [prefixWord, tailWord_4204208, baseEnd_4204208] using wordTrace_append hprefix tailTrace_4204208
  have hstable : (prefixWord ++ tailWord_4204208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204208).length < 2 ^ (prefixWord ++ tailWord_4204208).sum := by decide
  have hdescent : baseEnd_4204208 < baseStart_4204208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204232 : List Nat := [2, 1, 3, 1, 2, 2, 1, 4, 3, 1, 3]
def baseStart_4204232 : Nat := 118140960795 + 4204232 * 2 ^ 59
def prefixEnd_4204232 : Nat := 4983230072969 + 3 ^ 40 * 4204232 * 2
def baseEnd_4204232 : Nat := 2158791799013500156665095

theorem tailTrace_4204232 : CollatzResearch.WordTrace tailWord_4204232 prefixEnd_4204232 2158791799013500156665095 := by
  unfold tailWord_4204232
  simp only [CollatzResearch.WordTrace]
  refine ⟨76670469252396482252883475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102227292336528643003844633 76670469252396482252883475)
  ·
    refine ⟨115005703878594723379325213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76670469252396482252883475 115005703878594723379325213)
    ·
      refine ⟨43127138954473021267246955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115005703878594723379325213 43127138954473021267246955)
      ·
        refine ⟨64690708431709531900870433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43127138954473021267246955 64690708431709531900870433)
        ·
          refine ⟨48518031323782148925652825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64690708431709531900870433 48518031323782148925652825)
          ·
            refine ⟨36388523492836611694239619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48518031323782148925652825 36388523492836611694239619)
            ·
              refine ⟨54582785239254917541359429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36388523492836611694239619 54582785239254917541359429)
              ·
                refine ⟨10234272232360297039004893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54582785239254917541359429 10234272232360297039004893)
                ·
                  refine ⟨3837852087135111389626835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10234272232360297039004893 3837852087135111389626835)
                  ·
                    refine ⟨5756778130702667084440253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3837852087135111389626835 5756778130702667084440253)
                    ·
                      refine ⟨2158791799013500156665095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5756778130702667084440253 2158791799013500156665095)
                      ·
                        rfl

theorem cell23_4204232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_4204232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204232 prefixEnd_4204232 := by exact prefixLift 4204232
  have htrace : WordTrace (prefixWord ++ tailWord_4204232) baseStart_4204232 baseEnd_4204232 := by
    simpa [prefixWord, tailWord_4204232, baseEnd_4204232] using wordTrace_append hprefix tailTrace_4204232
  have hstable : (prefixWord ++ tailWord_4204232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204232).length < 2 ^ (prefixWord ++ tailWord_4204232).sum := by decide
  have hdescent : baseEnd_4204232 < baseStart_4204232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204275 : List Nat := [1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 5]
def baseStart_4204275 : Nat := 118140960795 + 4204275 * 2 ^ 59
def prefixEnd_4204275 : Nat := 4983230072969 + 3 ^ 40 * 4204275 * 2
def baseEnd_4204275 : Nat := 2158813878681643488427397

theorem tailTrace_4204275 : CollatzResearch.WordTrace tailWord_4204275 prefixEnd_4204275 2158813878681643488427397 := by
  unfold tailWord_4204275
  simp only [CollatzResearch.WordTrace]
  refine ⟨153342506843637182849582279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102228337895758121899721519 153342506843637182849582279)
  ·
    refine ⟨230013760265455774274373419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153342506843637182849582279 230013760265455774274373419)
    ·
      refine ⟨345020640398183661411560129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230013760265455774274373419 345020640398183661411560129)
      ·
        refine ⟨258765480298637746058670097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345020640398183661411560129 258765480298637746058670097)
        ·
          refine ⟨194074110223978309544002573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258765480298637746058670097 194074110223978309544002573)
          ·
            refine ⟨72777791333991866079000965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 194074110223978309544002573 72777791333991866079000965)
            ·
              refine ⟨13645835875123474889812681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72777791333991866079000965 13645835875123474889812681)
              ·
                refine ⟨10234376906342606167359511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13645835875123474889812681 10234376906342606167359511)
                ·
                  refine ⟨15351565359513909251039267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10234376906342606167359511 15351565359513909251039267)
                  ·
                    refine ⟨23027348039270863876558901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15351565359513909251039267 23027348039270863876558901)
                    ·
                      refine ⟨2158813878681643488427397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23027348039270863876558901 2158813878681643488427397)
                      ·
                        rfl

theorem cell23_4204275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 5].length) (baseStart_4204275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204275 prefixEnd_4204275 := by exact prefixLift 4204275
  have htrace : WordTrace (prefixWord ++ tailWord_4204275) baseStart_4204275 baseEnd_4204275 := by
    simpa [prefixWord, tailWord_4204275, baseEnd_4204275] using wordTrace_append hprefix tailTrace_4204275
  have hstable : (prefixWord ++ tailWord_4204275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204275).length < 2 ^ (prefixWord ++ tailWord_4204275).sum := by decide
  have hdescent : baseEnd_4204275 < baseStart_4204275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204286 : List Nat := [4, 2, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_4204286 : Nat := 118140960795 + 4204286 * 2 ^ 59
def prefixEnd_4204286 : Nat := 4983230072969 + 3 ^ 40 * 4204286 * 2
def baseEnd_4204286 : Nat := 719606508989614315129949

theorem tailTrace_4204286 : CollatzResearch.WordTrace tailWord_4204286 prefixEnd_4204286 719606508989614315129949 := by
  unfold tailWord_4204286
  simp only [CollatzResearch.WordTrace]
  refine ⟨19167863505824666466029089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102228605364398221152155141 19167863505824666466029089)
  ·
    refine ⟨14375897629368499849521817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19167863505824666466029089 14375897629368499849521817)
    ·
      refine ⟨10781923222026374887141363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14375897629368499849521817 10781923222026374887141363)
      ·
        refine ⟨16172884833039562330712045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10781923222026374887141363 16172884833039562330712045)
        ·
          refine ⟨6064831812389835874017017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16172884833039562330712045 6064831812389835874017017)
          ·
            refine ⟨4548623859292376905512763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6064831812389835874017017 4548623859292376905512763)
            ·
              refine ⟨6822935788938565358269145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4548623859292376905512763 6822935788938565358269145)
              ·
                refine ⟨5117201841703924018701859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6822935788938565358269145 5117201841703924018701859)
                ·
                  refine ⟨7675802762555886028052789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5117201841703924018701859 7675802762555886028052789)
                  ·
                    refine ⟨719606508989614315129949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7675802762555886028052789 719606508989614315129949)
                    ·
                      rfl

theorem cell23_4204286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_4204286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204286 prefixEnd_4204286 := by exact prefixLift 4204286
  have htrace : WordTrace (prefixWord ++ tailWord_4204286) baseStart_4204286 baseEnd_4204286 := by
    simpa [prefixWord, tailWord_4204286, baseEnd_4204286] using wordTrace_append hprefix tailTrace_4204286
  have hstable : (prefixWord ++ tailWord_4204286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204286).length < 2 ^ (prefixWord ++ tailWord_4204286).sum := by decide
  have hdescent : baseEnd_4204286 < baseStart_4204286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204289 : List Nat := [1, 2, 4, 1, 1, 1, 2, 4, 3, 2, 2]
def baseStart_4204289 : Nat := 118140960795 + 4204289 * 2 ^ 59
def prefixEnd_4204289 : Nat := 4983230072969 + 3 ^ 40 * 4204289 * 2
def baseEnd_4204289 : Nat := 2158821067410806433652333

theorem tailTrace_4204289 : CollatzResearch.WordTrace tailWord_4204289 prefixEnd_4204289 2158821067410806433652333 := by
  unfold tailWord_4204289
  simp only [CollatzResearch.WordTrace]
  refine ⟨153343017465586463240591921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102228678310390975493727947 153343017465586463240591921)
  ·
    refine ⟨115007263099189847430443941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153343017465586463240591921 115007263099189847430443941)
    ·
      refine ⟨21563861831098096393208239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115007263099189847430443941 21563861831098096393208239)
      ·
        refine ⟨32345792746647144589812359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21563861831098096393208239 32345792746647144589812359)
        ·
          refine ⟨48518689119970716884718539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32345792746647144589812359 48518689119970716884718539)
          ·
            refine ⟨72778033679956075327077809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48518689119970716884718539 72778033679956075327077809)
            ·
              refine ⟨54583525259967056495308357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72778033679956075327077809 54583525259967056495308357)
              ·
                refine ⟨10234410986243823092870317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54583525259967056495308357 10234410986243823092870317)
                ·
                  refine ⟨3837904119841433659826369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10234410986243823092870317 3837904119841433659826369)
                  ·
                    refine ⟨2878428089881075244869777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3837904119841433659826369 2878428089881075244869777)
                    ·
                      refine ⟨2158821067410806433652333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2878428089881075244869777 2158821067410806433652333)
                      ·
                        rfl

theorem cell23_4204289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_4204289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204289 prefixEnd_4204289 := by exact prefixLift 4204289
  have htrace : WordTrace (prefixWord ++ tailWord_4204289) baseStart_4204289 baseEnd_4204289 := by
    simpa [prefixWord, tailWord_4204289, baseEnd_4204289] using wordTrace_append hprefix tailTrace_4204289
  have hstable : (prefixWord ++ tailWord_4204289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204289).length < 2 ^ (prefixWord ++ tailWord_4204289).sum := by decide
  have hdescent : baseEnd_4204289 < baseStart_4204289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204322 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_4204322 : Nat := 118140960795 + 4204322 * 2 ^ 59
def prefixEnd_4204322 : Nat := 4983230072969 + 3 ^ 40 * 4204322 * 2
def baseEnd_4204322 : Nat := 2158838012272404804539681

theorem tailTrace_4204322 : CollatzResearch.WordTrace tailWord_4204322 prefixEnd_4204322 2158838012272404804539681 := by
  unfold tailWord_4204322
  simp only [CollatzResearch.WordTrace]
  refine ⟨38336055268616727469135805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102229480716311273251028813 38336055268616727469135805)
  ·
    refine ⟨14376020725731272800925927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38336055268616727469135805 14376020725731272800925927)
    ·
      refine ⟨21564031088596909201388891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14376020725731272800925927 21564031088596909201388891)
      ·
        refine ⟨32346046632895363802083337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21564031088596909201388891 32346046632895363802083337)
        ·
          refine ⟨24259534974671522851562503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32346046632895363802083337 24259534974671522851562503)
          ·
            refine ⟨36389302462007284277343755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24259534974671522851562503 36389302462007284277343755)
            ·
              refine ⟨54583953693010926416015633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36389302462007284277343755 54583953693010926416015633)
              ·
                refine ⟨40937965269758194812011725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54583953693010926416015633 40937965269758194812011725)
                ·
                  refine ⟨15351736976159323054504397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40937965269758194812011725 15351736976159323054504397)
                  ·
                    refine ⟨5756901366059746145439149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15351736976159323054504397 5756901366059746145439149)
                    ·
                      refine ⟨2158838012272404804539681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5756901366059746145439149 2158838012272404804539681)
                      ·
                        rfl

theorem cell23_4204322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_4204322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204322 prefixEnd_4204322 := by exact prefixLift 4204322
  have htrace : WordTrace (prefixWord ++ tailWord_4204322) baseStart_4204322 baseEnd_4204322 := by
    simpa [prefixWord, tailWord_4204322, baseEnd_4204322] using wordTrace_append hprefix tailTrace_4204322
  have hstable : (prefixWord ++ tailWord_4204322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204322).length < 2 ^ (prefixWord ++ tailWord_4204322).sum := by decide
  have hdescent : baseEnd_4204322 < baseStart_4204322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204323 : List Nat := [1, 1, 1, 4, 2, 1, 6, 2, 1, 2, 2]
def baseStart_4204323 : Nat := 118140960795 + 4204323 * 2 ^ 59
def prefixEnd_4204323 : Nat := 4983230072969 + 3 ^ 40 * 4204323 * 2
def baseEnd_4204323 : Nat := 2158838525753059300627177

theorem tailTrace_4204323 : CollatzResearch.WordTrace tailWord_4204323 prefixEnd_4204323 2158838525753059300627177 := by
  unfold tailWord_4204323
  simp only [CollatzResearch.WordTrace]
  refine ⟨153344257547463287047329623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102229505031642191364886415 153344257547463287047329623)
  ·
    refine ⟨230016386321194930570994435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153344257547463287047329623 230016386321194930570994435)
    ·
      refine ⟨345024579481792395856491653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230016386321194930570994435 345024579481792395856491653)
      ·
        refine ⟨64692108652836074223092185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 345024579481792395856491653 64692108652836074223092185)
        ·
          refine ⟨48519081489627055667319139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64692108652836074223092185 48519081489627055667319139)
          ·
            refine ⟨72778622234440583500978709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48519081489627055667319139 72778622234440583500978709)
            ·
              refine ⟨3411497917239402351608377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72778622234440583500978709 3411497917239402351608377)
              ·
                refine ⟨2558623437929551763706283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3411497917239402351608377 2558623437929551763706283)
                ·
                  refine ⟨3837935156894327645559425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2558623437929551763706283 3837935156894327645559425)
                  ·
                    refine ⟨2878451367670745734169569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3837935156894327645559425 2878451367670745734169569)
                    ·
                      refine ⟨2158838525753059300627177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2878451367670745734169569 2158838525753059300627177)
                      ·
                        rfl

theorem cell23_4204323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 1, 2, 2].length) (baseStart_4204323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204323 prefixEnd_4204323 := by exact prefixLift 4204323
  have htrace : WordTrace (prefixWord ++ tailWord_4204323) baseStart_4204323 baseEnd_4204323 := by
    simpa [prefixWord, tailWord_4204323, baseEnd_4204323] using wordTrace_append hprefix tailTrace_4204323
  have hstable : (prefixWord ++ tailWord_4204323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204323).length < 2 ^ (prefixWord ++ tailWord_4204323).sum := by decide
  have hdescent : baseEnd_4204323 < baseStart_4204323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204325 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 2, 7]
def baseStart_4204325 : Nat := 118140960795 + 4204325 * 2 ^ 59
def prefixEnd_4204325 : Nat := 4983230072969 + 3 ^ 40 * 4204325 * 2
def baseEnd_4204325 : Nat := 719613184238122764267389

theorem tailTrace_4204325 : CollatzResearch.WordTrace tailWord_4204325 prefixEnd_4204325 719613184238122764267389 := by
  unfold tailWord_4204325
  simp only [CollatzResearch.WordTrace]
  refine ⟨153344330493456041388902429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102229553662304027592601619 153344330493456041388902429)
  ·
    refine ⟨57504123935046015520838411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153344330493456041388902429 57504123935046015520838411)
    ·
      refine ⟨86256185902569023281257617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57504123935046015520838411 86256185902569023281257617)
      ·
        refine ⟨64692139426926767460943213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86256185902569023281257617 64692139426926767460943213)
        ·
          refine ⟨24259552285097537797853705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64692139426926767460943213 24259552285097537797853705)
          ·
            refine ⟨18194664213823153348390279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24259552285097537797853705 18194664213823153348390279)
            ·
              refine ⟨27291996320734730022585419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18194664213823153348390279 27291996320734730022585419)
              ·
                refine ⟨40937994481102095033878129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27291996320734730022585419 40937994481102095033878129)
                ·
                  refine ⟨30703495860826571275408597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40937994481102095033878129 30703495860826571275408597)
                  ·
                    refine ⟨719613184238122764267389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30703495860826571275408597 719613184238122764267389)
                    ·
                      rfl

theorem cell23_4204325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_4204325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204325 prefixEnd_4204325 := by exact prefixLift 4204325
  have htrace : WordTrace (prefixWord ++ tailWord_4204325) baseStart_4204325 baseEnd_4204325 := by
    simpa [prefixWord, tailWord_4204325, baseEnd_4204325] using wordTrace_append hprefix tailTrace_4204325
  have hstable : (prefixWord ++ tailWord_4204325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204325).length < 2 ^ (prefixWord ++ tailWord_4204325).sum := by decide
  have hdescent : baseEnd_4204325 < baseStart_4204325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204339 : List Nat := [1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 3]
def baseStart_4204339 : Nat := 118140960795 + 4204339 * 2 ^ 59
def prefixEnd_4204339 : Nat := 4983230072969 + 3 ^ 40 * 4204339 * 2
def baseEnd_4204339 : Nat := 2158846741443531238027103

theorem tailTrace_4204339 : CollatzResearch.WordTrace tailWord_4204339 prefixEnd_4204339 2158846741443531238027103 := by
  unfold tailWord_4204339
  simp only [CollatzResearch.WordTrace]
  refine ⟨153344841115405321779912071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102229894076936881186608047 153344841115405321779912071)
  ·
    refine ⟨230017261673107982669868107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153344841115405321779912071 230017261673107982669868107)
    ·
      refine ⟨345025892509661974004802161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230017261673107982669868107 345025892509661974004802161)
      ·
        refine ⟨258769419382246480503601621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345025892509661974004802161 258769419382246480503601621)
        ·
          refine ⟨6064908266771401886803163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 258769419382246480503601621 6064908266771401886803163)
          ·
            refine ⟨9097362400157102830204745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6064908266771401886803163 9097362400157102830204745)
            ·
              refine ⟨6823021800117827122653559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9097362400157102830204745 6823021800117827122653559)
              ·
                refine ⟨10234532700176740683980339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6823021800117827122653559 10234532700176740683980339)
                ·
                  refine ⟨15351799050265111025970509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10234532700176740683980339 15351799050265111025970509)
                  ·
                    refine ⟨5756924643849416634738941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15351799050265111025970509 5756924643849416634738941)
                    ·
                      refine ⟨2158846741443531238027103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5756924643849416634738941 2158846741443531238027103)
                      ·
                        rfl

theorem cell23_4204339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 3].length) (baseStart_4204339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204339 prefixEnd_4204339 := by exact prefixLift 4204339
  have htrace : WordTrace (prefixWord ++ tailWord_4204339) baseStart_4204339 baseEnd_4204339 := by
    simpa [prefixWord, tailWord_4204339, baseEnd_4204339] using wordTrace_append hprefix tailTrace_4204339
  have hstable : (prefixWord ++ tailWord_4204339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204339).length < 2 ^ (prefixWord ++ tailWord_4204339).sum := by decide
  have hdescent : baseEnd_4204339 < baseStart_4204339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204372 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_4204372 : Nat := 118140960795 + 4204372 * 2 ^ 59
def prefixEnd_4204372 : Nat := 4983230072969 + 3 ^ 40 * 4204372 * 2
def baseEnd_4204372 : Nat := 719621228768376536304817

theorem tailTrace_4204372 : CollatzResearch.WordTrace tailWord_4204372 prefixEnd_4204372 719621228768376536304817 := by
  unfold tailWord_4204372
  simp only [CollatzResearch.WordTrace]
  refine ⟨76673022362142884207931685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102230696482857178943908913 76673022362142884207931685)
  ·
    refine ⟨14376191692901790788987191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76673022362142884207931685 14376191692901790788987191)
    ·
      refine ⟨21564287539352686183480787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14376191692901790788987191 21564287539352686183480787)
      ·
        refine ⟨32346431309029029275221181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21564287539352686183480787 32346431309029029275221181)
        ·
          refine ⟨12129911740885885978207943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32346431309029029275221181 12129911740885885978207943)
          ·
            refine ⟨18194867611328828967311915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12129911740885885978207943 18194867611328828967311915)
            ·
              refine ⟨27292301416993243450967873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18194867611328828967311915 27292301416993243450967873)
              ·
                refine ⟨20469226062744932588225905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27292301416993243450967873 20469226062744932588225905)
                ·
                  refine ⟨15351919547058699441169429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20469226062744932588225905 15351919547058699441169429)
                  ·
                    refine ⟨719621228768376536304817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15351919547058699441169429 719621228768376536304817)
                    ·
                      rfl

theorem cell23_4204372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_4204372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204372 prefixEnd_4204372 := by exact prefixLift 4204372
  have htrace : WordTrace (prefixWord ++ tailWord_4204372) baseStart_4204372 baseEnd_4204372 := by
    simpa [prefixWord, tailWord_4204372, baseEnd_4204372] using wordTrace_append hprefix tailTrace_4204372
  have hstable : (prefixWord ++ tailWord_4204372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204372).length < 2 ^ (prefixWord ++ tailWord_4204372).sum := by decide
  have hdescent : baseEnd_4204372 < baseStart_4204372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204392 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_4204392 : Nat := 118140960795 + 4204392 * 2 ^ 59
def prefixEnd_4204392 : Nat := 4983230072969 + 3 ^ 40 * 4204392 * 2
def baseEnd_4204392 : Nat := 2158873955918219530664359

theorem tailTrace_4204392 : CollatzResearch.WordTrace tailWord_4204392 prefixEnd_4204392 2158873955918219530664359 := by
  unfold tailWord_4204392
  simp only [CollatzResearch.WordTrace]
  refine ⟨76673387092106655915795715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102231182789475541221060953 76673387092106655915795715)
  ·
    refine ⟨115010080638159983873693573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76673387092106655915795715 115010080638159983873693573)
    ·
      refine ⟨21564390119654996976317545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115010080638159983873693573 21564390119654996976317545)
      ·
        refine ⟨16173292589741247732238159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21564390119654996976317545 16173292589741247732238159)
        ·
          refine ⟨24259938884611871598357239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16173292589741247732238159 24259938884611871598357239)
          ·
            refine ⟨36389908326917807397535859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24259938884611871598357239 36389908326917807397535859)
            ·
              refine ⟨54584862490376711096303789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36389908326917807397535859 54584862490376711096303789)
              ·
                refine ⟨20469323433891266661113921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54584862490376711096303789 20469323433891266661113921)
                ·
                  refine ⟨15351992575418449995835441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20469323433891266661113921 15351992575418449995835441)
                  ·
                    refine ⟨11513994431563837496876581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15351992575418449995835441 11513994431563837496876581)
                    ·
                      refine ⟨2158873955918219530664359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11513994431563837496876581 2158873955918219530664359)
                      ·
                        rfl

theorem cell23_4204392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_4204392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204392 prefixEnd_4204392 := by exact prefixLift 4204392
  have htrace : WordTrace (prefixWord ++ tailWord_4204392) baseStart_4204392 baseEnd_4204392 := by
    simpa [prefixWord, tailWord_4204392, baseEnd_4204392] using wordTrace_append hprefix tailTrace_4204392
  have hstable : (prefixWord ++ tailWord_4204392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204392).length < 2 ^ (prefixWord ++ tailWord_4204392).sum := by decide
  have hdescent : baseEnd_4204392 < baseStart_4204392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204396 : List Nat := [2, 2, 1, 1, 4, 4, 1, 1, 1, 4, 2]
def baseStart_4204396 : Nat := 118140960795 + 4204396 * 2 ^ 59
def prefixEnd_4204396 : Nat := 4983230072969 + 3 ^ 40 * 4204396 * 2
def baseEnd_4204396 : Nat := 2158876009840837515014341

theorem tailTrace_4204396 : CollatzResearch.WordTrace tailWord_4204396 prefixEnd_4204396 2158876009840837515014341 := by
  unfold tailWord_4204396
  simp only [CollatzResearch.WordTrace]
  refine ⟨76673460038099410257368521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102231280050799213676491361 76673460038099410257368521)
  ·
    refine ⟨57505095028574557693026391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76673460038099410257368521 57505095028574557693026391)
    ·
      refine ⟨86257642542861836539539587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57505095028574557693026391 86257642542861836539539587)
      ·
        refine ⟨129386463814292754809309381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86257642542861836539539587 129386463814292754809309381)
        ·
          refine ⟨24259961965179891526745509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129386463814292754809309381 24259961965179891526745509)
          ·
            refine ⟨4548742868471229661264783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24259961965179891526745509 4548742868471229661264783)
            ·
              refine ⟨6823114302706844491897175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4548742868471229661264783 6823114302706844491897175)
              ·
                refine ⟨10234671454060266737845763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6823114302706844491897175 10234671454060266737845763)
                ·
                  refine ⟨15352007181090400106768645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10234671454060266737845763 15352007181090400106768645)
                  ·
                    refine ⟨2878501346454450020019121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15352007181090400106768645 2878501346454450020019121)
                    ·
                      refine ⟨2158876009840837515014341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2878501346454450020019121 2158876009840837515014341)
                      ·
                        rfl

theorem cell23_4204396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 4, 2].length) (baseStart_4204396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204396 prefixEnd_4204396 := by exact prefixLift 4204396
  have htrace : WordTrace (prefixWord ++ tailWord_4204396) baseStart_4204396 baseEnd_4204396 := by
    simpa [prefixWord, tailWord_4204396, baseEnd_4204396] using wordTrace_append hprefix tailTrace_4204396
  have hstable : (prefixWord ++ tailWord_4204396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204396).length < 2 ^ (prefixWord ++ tailWord_4204396).sum := by decide
  have hdescent : baseEnd_4204396 < baseStart_4204396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204419 : List Nat := [1, 1, 1, 3, 4, 2, 3, 3, 5]
def baseStart_4204419 : Nat := 118140960795 + 4204419 * 2 ^ 59
def prefixEnd_4204419 : Nat := 4983230072969 + 3 ^ 40 * 4204419 * 2
def baseEnd_4204419 : Nat := 239876424432876769447415

theorem tailTrace_4204419 : CollatzResearch.WordTrace tailWord_4204419 prefixEnd_4204419 239876424432876769447415 := by
  unfold tailWord_4204419
  simp only [CollatzResearch.WordTrace]
  refine ⟨153347758955115495442824311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102231839303410330295216207 153347758955115495442824311)
  ·
    refine ⟨230021638432673243164236467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153347758955115495442824311 230021638432673243164236467)
    ·
      refine ⟨345032457649009864746354701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230021638432673243164236467 345032457649009864746354701)
      ·
        refine ⟨129387171618378699279883013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 345032457649009864746354701 129387171618378699279883013)
        ·
          refine ⟨24260094678446006114978065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129387171618378699279883013 24260094678446006114978065)
          ·
            refine ⟨18195071008834504586233549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24260094678446006114978065 18195071008834504586233549)
            ·
              refine ⟨6823151628312939219837581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18195071008834504586233549 6823151628312939219837581)
              ·
                refine ⟨2558681860617352207439093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6823151628312939219837581 2558681860617352207439093)
                ·
                  refine ⟨239876424432876769447415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2558681860617352207439093 239876424432876769447415)
                  ·
                    rfl

theorem cell23_4204419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 5].length) (baseStart_4204419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204419 prefixEnd_4204419 := by exact prefixLift 4204419
  have htrace : WordTrace (prefixWord ++ tailWord_4204419) baseStart_4204419 baseEnd_4204419 := by
    simpa [prefixWord, tailWord_4204419, baseEnd_4204419] using wordTrace_append hprefix tailTrace_4204419
  have hstable : (prefixWord ++ tailWord_4204419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204419).length < 2 ^ (prefixWord ++ tailWord_4204419).sum := by decide
  have hdescent : baseEnd_4204419 < baseStart_4204419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204442 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7]
def baseStart_4204442 : Nat := 118140960795 + 4204442 * 2 ^ 59
def prefixEnd_4204442 : Nat := 4983230072969 + 3 ^ 40 * 4204442 * 2
def baseEnd_4204442 : Nat := 2158899629950944335039129

theorem tailTrace_4204442 : CollatzResearch.WordTrace tailWord_4204442 prefixEnd_4204442 2158899629950944335039129 := by
  unfold tailWord_4204442
  simp only [CollatzResearch.WordTrace]
  refine ⟨38337149458508042592727895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102232398556021446913941053 38337149458508042592727895)
  ·
    refine ⟨57505724187762063889091843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38337149458508042592727895 57505724187762063889091843)
    ·
      refine ⟨86258586281643095833637765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57505724187762063889091843 86258586281643095833637765)
      ·
        refine ⟨16173484927808080468807081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86258586281643095833637765 16173484927808080468807081)
        ·
          refine ⟨12130113695856060351605311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16173484927808080468807081 12130113695856060351605311)
          ·
            refine ⟨18195170543784090527407967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12130113695856060351605311 18195170543784090527407967)
            ·
              refine ⟨27292755815676135791111951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18195170543784090527407967 27292755815676135791111951)
              ·
                refine ⟨40939133723514203686667927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27292755815676135791111951 40939133723514203686667927)
                ·
                  refine ⟨61408700585271305530001891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40939133723514203686667927 61408700585271305530001891)
                  ·
                    refine ⟨92113050877906958295002837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61408700585271305530001891 92113050877906958295002837)
                    ·
                      refine ⟨2158899629950944335039129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92113050877906958295002837 2158899629950944335039129)
                      ·
                        rfl

theorem cell23_4204442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_4204442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204442 prefixEnd_4204442 := by exact prefixLift 4204442
  have htrace : WordTrace (prefixWord ++ tailWord_4204442) baseStart_4204442 baseEnd_4204442 := by
    simpa [prefixWord, tailWord_4204442, baseEnd_4204442] using wordTrace_append hprefix tailTrace_4204442
  have hstable : (prefixWord ++ tailWord_4204442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204442).length < 2 ^ (prefixWord ++ tailWord_4204442).sum := by decide
  have hdescent : baseEnd_4204442 < baseStart_4204442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204447 : List Nat := [1, 1, 2, 5, 4, 1, 2, 1, 2, 2, 2]
def baseStart_4204447 : Nat := 118140960795 + 4204447 * 2 ^ 59
def prefixEnd_4204447 : Nat := 4983230072969 + 3 ^ 40 * 4204447 * 2
def baseEnd_4204447 : Nat := 2158902197354216815476607

theorem tailTrace_4204447 : CollatzResearch.WordTrace tailWord_4204447 prefixEnd_4204447 2158902197354216815476607 := by
  unfold tailWord_4204447
  simp only [CollatzResearch.WordTrace]
  refine ⟨153348780199014056224843595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102232520132676037483229063 153348780199014056224843595)
  ·
    refine ⟨230023170298521084337265393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153348780199014056224843595 230023170298521084337265393)
    ·
      refine ⟨172517377723890813252949045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230023170298521084337265393 172517377723890813252949045)
      ·
        refine ⟨16173504161614763742463973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 172517377723890813252949045 16173504161614763742463973)
        ·
          refine ⟨3032532030302768201711995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16173504161614763742463973 3032532030302768201711995)
          ·
            refine ⟨4548798045454152302567993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3032532030302768201711995 4548798045454152302567993)
            ·
              refine ⟨3411598534090614226925995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4548798045454152302567993 3411598534090614226925995)
              ·
                refine ⟨5117397801135921340388993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3411598534090614226925995 5117397801135921340388993)
                ·
                  refine ⟨3838048350851941005291745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5117397801135921340388993 3838048350851941005291745)
                  ·
                    refine ⟨2878536263138955753968809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3838048350851941005291745 2878536263138955753968809)
                    ·
                      refine ⟨2158902197354216815476607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2878536263138955753968809 2158902197354216815476607)
                      ·
                        rfl

theorem cell23_4204447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_4204447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204447 prefixEnd_4204447 := by exact prefixLift 4204447
  have htrace : WordTrace (prefixWord ++ tailWord_4204447) baseStart_4204447 baseEnd_4204447 := by
    simpa [prefixWord, tailWord_4204447, baseEnd_4204447] using wordTrace_append hprefix tailTrace_4204447
  have hstable : (prefixWord ++ tailWord_4204447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204447).length < 2 ^ (prefixWord ++ tailWord_4204447).sum := by decide
  have hdescent : baseEnd_4204447 < baseStart_4204447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204469 : List Nat := [1, 3, 3, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_4204469 : Nat := 118140960795 + 4204469 * 2 ^ 59
def prefixEnd_4204469 : Nat := 4983230072969 + 3 ^ 40 * 4204469 * 2
def baseEnd_4204469 : Nat := 2158913493928615729401505

theorem tailTrace_4204469 : CollatzResearch.WordTrace tailWord_4204469 prefixEnd_4204469 2158913493928615729401505 := by
  unfold tailWord_4204469
  simp only [CollatzResearch.WordTrace]
  refine ⟨153349582604934353982144461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102233055069956235988096307 153349582604934353982144461)
  ·
    refine ⟨57506093476850382743304173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153349582604934353982144461 57506093476850382743304173)
    ·
      refine ⟨21564785053818893528739065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57506093476850382743304173 21564785053818893528739065)
      ·
        refine ⟨16173588790364170146554299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21564785053818893528739065 16173588790364170146554299)
        ·
          refine ⟨24260383185546255219831449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16173588790364170146554299 24260383185546255219831449)
          ·
            refine ⟨18195287389159691414873587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24260383185546255219831449 18195287389159691414873587)
            ·
              refine ⟨27292931083739537122310381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18195287389159691414873587 27292931083739537122310381)
              ·
                refine ⟨10234849156402326420866393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27292931083739537122310381 10234849156402326420866393)
                ·
                  refine ⟨7676136867301744815649795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10234849156402326420866393 7676136867301744815649795)
                  ·
                    refine ⟨11514205300952617223474693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7676136867301744815649795 11514205300952617223474693)
                    ·
                      refine ⟨2158913493928615729401505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11514205300952617223474693 2158913493928615729401505)
                      ·
                        rfl

theorem cell23_4204469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_4204469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204469 prefixEnd_4204469 := by exact prefixLift 4204469
  have htrace : WordTrace (prefixWord ++ tailWord_4204469) baseStart_4204469 baseEnd_4204469 := by
    simpa [prefixWord, tailWord_4204469, baseEnd_4204469] using wordTrace_append hprefix tailTrace_4204469
  have hstable : (prefixWord ++ tailWord_4204469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204469).length < 2 ^ (prefixWord ++ tailWord_4204469).sum := by decide
  have hdescent : baseEnd_4204469 < baseStart_4204469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204586 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 4, 4]
def baseStart_4204586 : Nat := 118140960795 + 4204586 * 2 ^ 59
def prefixEnd_4204586 : Nat := 4983230072969 + 3 ^ 40 * 4204586 * 2
def baseEnd_4204586 : Nat := 719657857055063923879489

theorem tailTrace_4204586 : CollatzResearch.WordTrace tailWord_4204586 prefixEnd_4204586 719657857055063923879489 := by
  unfold tailWord_4204586
  simp only [CollatzResearch.WordTrace]
  refine ⟨38338462486377620741038403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102235899963673655309435741 38338462486377620741038403)
  ·
    refine ⟨57507693729566431111557605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38338462486377620741038403 57507693729566431111557605)
    ·
      refine ⟨10782692574293705833417051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57507693729566431111557605 10782692574293705833417051)
      ·
        refine ⟨16174038861440558750125577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10782692574293705833417051 16174038861440558750125577)
        ·
          refine ⟨12130529146080419062594183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16174038861440558750125577 12130529146080419062594183)
          ·
            refine ⟨18195793719120628593891275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12130529146080419062594183 18195793719120628593891275)
            ·
              refine ⟨27293690578680942890836913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18195793719120628593891275 27293690578680942890836913)
              ·
                refine ⟨20470267934010707168127685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27293690578680942890836913 20470267934010707168127685)
                ·
                  refine ⟨3838175237627007594023941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20470267934010707168127685 3838175237627007594023941)
                  ·
                    refine ⟨719657857055063923879489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3838175237627007594023941 719657857055063923879489)
                    ·
                      rfl

theorem cell23_4204586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_4204586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204586 prefixEnd_4204586 := by exact prefixLift 4204586
  have htrace : WordTrace (prefixWord ++ tailWord_4204586) baseStart_4204586 baseEnd_4204586 := by
    simpa [prefixWord, tailWord_4204586, baseEnd_4204586] using wordTrace_append hprefix tailTrace_4204586
  have hstable : (prefixWord ++ tailWord_4204586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204586).length < 2 ^ (prefixWord ++ tailWord_4204586).sum := by decide
  have hdescent : baseEnd_4204586 < baseStart_4204586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204630 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_4204630 : Nat := 118140960795 + 4204630 * 2 ^ 59
def prefixEnd_4204630 : Nat := 4983230072969 + 3 ^ 40 * 4204630 * 2
def baseEnd_4204630 : Nat := 2158996164313989599488265

theorem tailTrace_4204630 : CollatzResearch.WordTrace tailWord_4204630 prefixEnd_4204630 2158996164313989599488265 := by
  unfold tailWord_4204630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9584715922334442404922209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102236969838234052319170229 9584715922334442404922209)
  ·
    refine ⟨7188536941750831803691657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9584715922334442404922209 7188536941750831803691657)
    ·
      refine ⟨5391402706313123852768743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7188536941750831803691657 5391402706313123852768743)
      ·
        refine ⟨8087104059469685779153115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5391402706313123852768743 8087104059469685779153115)
        ·
          refine ⟨12130656089204528668729673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8087104059469685779153115 12130656089204528668729673)
          ·
            refine ⟨9097992066903396501547255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12130656089204528668729673 9097992066903396501547255)
            ·
              refine ⟨13646988100355094752320883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9097992066903396501547255 13646988100355094752320883)
              ·
                refine ⟨20470482150532642128481325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13646988100355094752320883 20470482150532642128481325)
                ·
                  refine ⟨7676430806449740798180497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20470482150532642128481325 7676430806449740798180497)
                  ·
                    refine ⟨5757323104837305598635373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7676430806449740798180497 5757323104837305598635373)
                    ·
                      refine ⟨2158996164313989599488265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5757323104837305598635373 2158996164313989599488265)
                      ·
                        rfl

theorem cell23_4204630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_4204630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204630 prefixEnd_4204630 := by exact prefixLift 4204630
  have htrace : WordTrace (prefixWord ++ tailWord_4204630) baseStart_4204630 baseEnd_4204630 := by
    simpa [prefixWord, tailWord_4204630, baseEnd_4204630] using wordTrace_append hprefix tailTrace_4204630
  have hstable : (prefixWord ++ tailWord_4204630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204630).length < 2 ^ (prefixWord ++ tailWord_4204630).sum := by decide
  have hdescent : baseEnd_4204630 < baseStart_4204630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204679 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_4204679 : Nat := 118140960795 + 4204679 * 2 ^ 59
def prefixEnd_4204679 : Nat := 4983230072969 + 3 ^ 40 * 4204679 * 2
def baseEnd_4204679 : Nat := 2159021324866059907775539

theorem tailTrace_4204679 : CollatzResearch.WordTrace tailWord_4204679 prefixEnd_4204679 2159021324866059907775539 := by
  unfold tailWord_4204679
  simp only [CollatzResearch.WordTrace]
  refine ⟨153357241934173559847289091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102238161289449039898192727 153357241934173559847289091)
  ·
    refine ⟨230035862901260339770933637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153357241934173559847289091 230035862901260339770933637)
    ·
      refine ⟨43131724293986313707050057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230035862901260339770933637 43131724293986313707050057)
      ·
        refine ⟨32348793220489735280287543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43131724293986313707050057 32348793220489735280287543)
        ·
          refine ⟨48523189830734602920431315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32348793220489735280287543 48523189830734602920431315)
          ·
            refine ⟨72784784746101904380646973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48523189830734602920431315 72784784746101904380646973)
            ·
              refine ⟨27294294279788214142742615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72784784746101904380646973 27294294279788214142742615)
              ·
                refine ⟨40941441419682321214113923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27294294279788214142742615 40941441419682321214113923)
                ·
                  refine ⟨61412162129523481821170885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40941441419682321214113923 61412162129523481821170885)
                  ·
                    refine ⟨11514780399285652841469541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61412162129523481821170885 11514780399285652841469541)
                    ·
                      refine ⟨2159021324866059907775539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11514780399285652841469541 2159021324866059907775539)
                      ·
                        rfl

theorem cell23_4204679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_4204679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204679 prefixEnd_4204679 := by exact prefixLift 4204679
  have htrace : WordTrace (prefixWord ++ tailWord_4204679) baseStart_4204679 baseEnd_4204679 := by
    simpa [prefixWord, tailWord_4204679, baseEnd_4204679] using wordTrace_append hprefix tailTrace_4204679
  have hstable : (prefixWord ++ tailWord_4204679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204679).length < 2 ^ (prefixWord ++ tailWord_4204679).sum := by decide
  have hdescent : baseEnd_4204679 < baseStart_4204679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204699 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 3]
def baseStart_4204699 : Nat := 118140960795 + 4204699 * 2 ^ 59
def prefixEnd_4204699 : Nat := 4983230072969 + 3 ^ 40 * 4204699 * 2
def baseEnd_4204699 : Nat := 2159031594479149829525447

theorem tailTrace_4204699 : CollatzResearch.WordTrace tailWord_4204699 prefixEnd_4204699 2159031594479149829525447 := by
  unfold tailWord_4204699
  simp only [CollatzResearch.WordTrace]
  refine ⟨153357971394101103263017151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102238647596067402175344767 153357971394101103263017151)
  ·
    refine ⟨230036957091151654894525727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153357971394101103263017151 230036957091151654894525727)
    ·
      refine ⟨345055435636727482341788591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230036957091151654894525727 345055435636727482341788591)
      ·
        refine ⟨517583153455091223512682887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345055435636727482341788591 517583153455091223512682887)
        ·
          refine ⟨776374730182636835269024331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517583153455091223512682887 776374730182636835269024331)
          ·
            refine ⟨1164562095273955252903536497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 776374730182636835269024331 1164562095273955252903536497)
            ·
              refine ⟨873421571455466439677652373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1164562095273955252903536497 873421571455466439677652373)
              ·
                refine ⟨40941636161974989359889955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 873421571455466439677652373 40941636161974989359889955)
                ·
                  refine ⟨61412454242962484039834933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40941636161974989359889955 61412454242962484039834933)
                  ·
                    refine ⟨5757417585277732878734525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61412454242962484039834933 5757417585277732878734525)
                    ·
                      refine ⟨2159031594479149829525447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5757417585277732878734525 2159031594479149829525447)
                      ·
                        rfl

theorem cell23_4204699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 3].length) (baseStart_4204699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204699 prefixEnd_4204699 := by exact prefixLift 4204699
  have htrace : WordTrace (prefixWord ++ tailWord_4204699) baseStart_4204699 baseEnd_4204699 := by
    simpa [prefixWord, tailWord_4204699, baseEnd_4204699] using wordTrace_append hprefix tailTrace_4204699
  have hstable : (prefixWord ++ tailWord_4204699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204699).length < 2 ^ (prefixWord ++ tailWord_4204699).sum := by decide
  have hdescent : baseEnd_4204699 < baseStart_4204699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204717 : List Nat := [1, 5, 2, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_4204717 : Nat := 118140960795 + 4204717 * 2 ^ 59
def prefixEnd_4204717 : Nat := 4983230072969 + 3 ^ 40 * 4204717 * 2
def baseEnd_4204717 : Nat := 2159040837130930759100365

theorem tailTrace_4204717 : CollatzResearch.WordTrace tailWord_4204717 prefixEnd_4204717 2159040837130930759100365 := by
  unfold tailWord_4204717
  simp only [CollatzResearch.WordTrace]
  refine ⟨153358627908035892337172405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102239085272023928224781603 153358627908035892337172405)
  ·
    refine ⟨14377371366378364906609913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153358627908035892337172405 14377371366378364906609913)
    ·
      refine ⟨10783028524783773679957435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14377371366378364906609913 10783028524783773679957435)
      ·
        refine ⟨16174542787175660519936153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10783028524783773679957435 16174542787175660519936153)
        ·
          refine ⟨12130907090381745389952115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16174542787175660519936153 12130907090381745389952115)
          ·
            refine ⟨18196360635572618084928173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12130907090381745389952115 18196360635572618084928173)
            ·
              refine ⟨6823635238339731781848065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18196360635572618084928173 6823635238339731781848065)
              ·
                refine ⟨5117726428754798836386049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6823635238339731781848065 5117726428754798836386049)
                ·
                  refine ⟨3838294821566099127289537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5117726428754798836386049 3838294821566099127289537)
                  ·
                    refine ⟨2878721116174574345467153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3838294821566099127289537 2878721116174574345467153)
                    ·
                      refine ⟨2159040837130930759100365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2878721116174574345467153 2159040837130930759100365)
                      ·
                        rfl

theorem cell23_4204717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_4204717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204717 prefixEnd_4204717 := by exact prefixLift 4204717
  have htrace : WordTrace (prefixWord ++ tailWord_4204717) baseStart_4204717 baseEnd_4204717 := by
    simpa [prefixWord, tailWord_4204717, baseEnd_4204717] using wordTrace_append hprefix tailTrace_4204717
  have hstable : (prefixWord ++ tailWord_4204717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204717).length < 2 ^ (prefixWord ++ tailWord_4204717).sum := by decide
  have hdescent : baseEnd_4204717 < baseStart_4204717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204719 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 4, 5]
def baseStart_4204719 : Nat := 118140960795 + 4204719 * 2 ^ 59
def prefixEnd_4204719 : Nat := 4983230072969 + 3 ^ 40 * 4204719 * 2
def baseEnd_4204719 : Nat := 719680621364079917091785

theorem tailTrace_4204719 : CollatzResearch.WordTrace tailWord_4204719 prefixEnd_4204719 719680621364079917091785 := by
  unfold tailWord_4204719
  simp only [CollatzResearch.WordTrace]
  refine ⟨153358700854028646678745211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102239133902685764452496807 153358700854028646678745211)
  ·
    refine ⟨230038051281042970018117817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153358700854028646678745211 230038051281042970018117817)
    ·
      refine ⟨172528538460782227513588363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230038051281042970018117817 172528538460782227513588363)
      ·
        refine ⟨258792807691173341270382545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172528538460782227513588363 258792807691173341270382545)
        ·
          refine ⟨194094605768380005952786909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258792807691173341270382545 194094605768380005952786909)
          ·
            refine ⟨72785477163142502232295091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 194094605768380005952786909 72785477163142502232295091)
            ·
              refine ⟨109178215744713753348442637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72785477163142502232295091 109178215744713753348442637)
              ·
                refine ⟨40941830904267657505665989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109178215744713753348442637 40941830904267657505665989)
                ·
                  refine ⟨7676593294550185782312373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40941830904267657505665989 7676593294550185782312373)
                  ·
                    refine ⟨719680621364079917091785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7676593294550185782312373 719680621364079917091785)
                    ·
                      rfl

theorem cell23_4204719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 5].length) (baseStart_4204719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204719 prefixEnd_4204719 := by exact prefixLift 4204719
  have htrace : WordTrace (prefixWord ++ tailWord_4204719) baseStart_4204719 baseEnd_4204719 := by
    simpa [prefixWord, tailWord_4204719, baseEnd_4204719] using wordTrace_append hprefix tailTrace_4204719
  have hstable : (prefixWord ++ tailWord_4204719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204719).length < 2 ^ (prefixWord ++ tailWord_4204719).sum := by decide
  have hdescent : baseEnd_4204719 < baseStart_4204719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204729 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 1, 1, 7]
def baseStart_4204729 : Nat := 118140960795 + 4204729 * 2 ^ 59
def prefixEnd_4204729 : Nat := 4983230072969 + 3 ^ 40 * 4204729 * 2
def baseEnd_4204729 : Nat := 2159046998898784712150309

theorem tailTrace_4204729 : CollatzResearch.WordTrace tailWord_4204729 prefixEnd_4204729 2159046998898784712150309 := by
  unfold tailWord_4204729
  simp only [CollatzResearch.WordTrace]
  refine ⟨153359065583992418386609241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102239377055994945591072827 153359065583992418386609241)
  ·
    refine ⟨115019299187994313789956931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153359065583992418386609241 115019299187994313789956931)
    ·
      refine ⟨172528948781991470684935397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115019299187994313789956931 172528948781991470684935397)
      ·
        refine ⟨32349177896623400753425387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172528948781991470684935397 32349177896623400753425387)
        ·
          refine ⟨48523766844935101130138081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32349177896623400753425387 48523766844935101130138081)
          ·
            refine ⟨36392825133701325847603561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48523766844935101130138081 36392825133701325847603561)
            ·
              refine ⟨27294618850275994385702671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36392825133701325847603561 27294618850275994385702671)
              ·
                refine ⟨40941928275413991578554007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27294618850275994385702671 40941928275413991578554007)
                ·
                  refine ⟨61412892413120987367831011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40941928275413991578554007 61412892413120987367831011)
                  ·
                    refine ⟨92119338619681481051746517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61412892413120987367831011 92119338619681481051746517)
                    ·
                      refine ⟨2159046998898784712150309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92119338619681481051746517 2159046998898784712150309)
                      ·
                        rfl

theorem cell23_4204729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_4204729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204729 prefixEnd_4204729 := by exact prefixLift 4204729
  have htrace : WordTrace (prefixWord ++ tailWord_4204729) baseStart_4204729 baseEnd_4204729 := by
    simpa [prefixWord, tailWord_4204729, baseEnd_4204729] using wordTrace_append hprefix tailTrace_4204729
  have hstable : (prefixWord ++ tailWord_4204729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204729).length < 2 ^ (prefixWord ++ tailWord_4204729).sum := by decide
  have hdescent : baseEnd_4204729 < baseStart_4204729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204734 : List Nat := [4, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2]
def baseStart_4204734 : Nat := 118140960795 + 4204734 * 2 ^ 59
def prefixEnd_4204734 : Nat := 4983230072969 + 3 ^ 40 * 4204734 * 2
def baseEnd_4204734 : Nat := 2159049566302057192587787

theorem tailTrace_4204734 : CollatzResearch.WordTrace tailWord_4204734 prefixEnd_4204734 2159049566302057192587787 := by
  unfold tailWord_4204734
  simp only [CollatzResearch.WordTrace]
  refine ⟨19169905993621788030067657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102239498632649536160360837 19169905993621788030067657)
  ·
    refine ⟨14377429495216341022550743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19169905993621788030067657 14377429495216341022550743)
    ·
      refine ⟨21566144242824511533826115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14377429495216341022550743 21566144242824511533826115)
      ·
        refine ⟨32349216364236767300739173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21566144242824511533826115 32349216364236767300739173)
        ·
          refine ⟨6065478068294393868888595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32349216364236767300739173 6065478068294393868888595)
          ·
            refine ⟨9098217102441590803332893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6065478068294393868888595 9098217102441590803332893)
            ·
              refine ⟨3411831413415596551249835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9098217102441590803332893 3411831413415596551249835)
              ·
                refine ⟨5117747120123394826874753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3411831413415596551249835 5117747120123394826874753)
                ·
                  refine ⟨3838310340092546120156065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5117747120123394826874753 3838310340092546120156065)
                  ·
                    refine ⟨2878732755069409590117049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3838310340092546120156065 2878732755069409590117049)
                    ·
                      refine ⟨2159049566302057192587787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2878732755069409590117049 2159049566302057192587787)
                      ·
                        rfl

theorem cell23_4204734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_4204734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204734 prefixEnd_4204734 := by exact prefixLift 4204734
  have htrace : WordTrace (prefixWord ++ tailWord_4204734) baseStart_4204734 baseEnd_4204734 := by
    simpa [prefixWord, tailWord_4204734, baseEnd_4204734] using wordTrace_append hprefix tailTrace_4204734
  have hstable : (prefixWord ++ tailWord_4204734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204734).length < 2 ^ (prefixWord ++ tailWord_4204734).sum := by decide
  have hdescent : baseEnd_4204734 < baseStart_4204734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204757 : List Nat := [1, 3, 2, 4, 3, 1, 1, 3, 5]
def baseStart_4204757 : Nat := 118140960795 + 4204757 * 2 ^ 59
def prefixEnd_4204757 : Nat := 4983230072969 + 3 ^ 40 * 4204757 * 2
def baseEnd_4204757 : Nat := 239895708484123400288909

theorem tailTrace_4204757 : CollatzResearch.WordTrace tailWord_4204757 prefixEnd_4204757 239895708484123400288909 := by
  unfold tailWord_4204757
  simp only [CollatzResearch.WordTrace]
  refine ⟨153360086827890979168628525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102240057885260652779085683 153360086827890979168628525)
  ·
    refine ⟨57510032560459117188235697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153360086827890979168628525 57510032560459117188235697)
    ·
      refine ⟨43132524420344337891176773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57510032560459117188235697 43132524420344337891176773)
      ·
        refine ⟨8087348328814563354595645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43132524420344337891176773 8087348328814563354595645)
        ·
          refine ⟨3032755623305461257973367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8087348328814563354595645 3032755623305461257973367)
          ·
            refine ⟨4549133434958191886960051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3032755623305461257973367 4549133434958191886960051)
            ·
              refine ⟨6823700152437287830440077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4549133434958191886960051 6823700152437287830440077)
              ·
                refine ⟨2558887557163982936415029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6823700152437287830440077 2558887557163982936415029)
                ·
                  refine ⟨239895708484123400288909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2558887557163982936415029 239895708484123400288909)
                  ·
                    rfl

theorem cell23_4204757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 5].length) (baseStart_4204757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204757 prefixEnd_4204757 := by exact prefixLift 4204757
  have htrace : WordTrace (prefixWord ++ tailWord_4204757) baseStart_4204757 baseEnd_4204757 := by
    simpa [prefixWord, tailWord_4204757, baseEnd_4204757] using wordTrace_append hprefix tailTrace_4204757
  have hstable : (prefixWord ++ tailWord_4204757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204757).length < 2 ^ (prefixWord ++ tailWord_4204757).sum := by decide
  have hdescent : baseEnd_4204757 < baseStart_4204757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204759 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 5]
def baseStart_4204759 : Nat := 118140960795 + 4204759 * 2 ^ 59
def prefixEnd_4204759 : Nat := 4983230072969 + 3 ^ 40 * 4204759 * 2
def baseEnd_4204759 : Nat := 2159062403318419594775171

theorem tailTrace_4204759 : CollatzResearch.WordTrace tailWord_4204759 prefixEnd_4204759 2159062403318419594775171 := by
  unfold tailWord_4204759
  simp only [CollatzResearch.WordTrace]
  refine ⟨153360159773883733510201331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102240106515922489006800887 153360159773883733510201331)
  ·
    refine ⟨230040239660825600265301997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153360159773883733510201331 230040239660825600265301997)
    ·
      refine ⟨86265089872809600099488249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230040239660825600265301997 86265089872809600099488249)
      ·
        refine ⟨64698817404607200074616187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86265089872809600099488249 64698817404607200074616187)
        ·
          refine ⟨97048226106910800111924281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64698817404607200074616187 97048226106910800111924281)
          ·
            refine ⟨72786169580183100083943211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97048226106910800111924281 72786169580183100083943211)
            ·
              refine ⟨109179254370274650125914817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72786169580183100083943211 109179254370274650125914817)
              ·
                refine ⟨81884440777705987594436113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109179254370274650125914817 81884440777705987594436113)
                ·
                  refine ⟨61413330583279490695827085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81884440777705987594436113 61413330583279490695827085)
                  ·
                    refine ⟨23029998968729809010935157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61413330583279490695827085 23029998968729809010935157)
                    ·
                      refine ⟨2159062403318419594775171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23029998968729809010935157 2159062403318419594775171)
                      ·
                        rfl

theorem cell23_4204759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_4204759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204759 prefixEnd_4204759 := by exact prefixLift 4204759
  have htrace : WordTrace (prefixWord ++ tailWord_4204759) baseStart_4204759 baseEnd_4204759 := by
    simpa [prefixWord, tailWord_4204759, baseEnd_4204759] using wordTrace_append hprefix tailTrace_4204759
  have hstable : (prefixWord ++ tailWord_4204759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204759).length < 2 ^ (prefixWord ++ tailWord_4204759).sum := by decide
  have hdescent : baseEnd_4204759 < baseStart_4204759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204773 : List Nat := [1, 3, 1, 4, 2, 2, 1, 2, 2, 1, 4]
def baseStart_4204773 : Nat := 118140960795 + 4204773 * 2 ^ 59
def prefixEnd_4204773 : Nat := 4983230072969 + 3 ^ 40 * 4204773 * 2
def baseEnd_4204773 : Nat := 2159069592047582540000107

theorem tailTrace_4204773 : CollatzResearch.WordTrace tailWord_4204773 prefixEnd_4204773 2159069592047582540000107 := by
  unfold tailWord_4204773
  simp only [CollatzResearch.WordTrace]
  refine ⟨153360670395833013901210973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102240446930555342600807315 153360670395833013901210973)
  ·
    refine ⟨57510251398437380212954115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153360670395833013901210973 57510251398437380212954115)
    ·
      refine ⟨86265377097656070319431173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57510251398437380212954115 86265377097656070319431173)
      ·
        refine ⟨16174758205810513184893345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86265377097656070319431173 16174758205810513184893345)
        ·
          refine ⟨12131068654357884888670009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16174758205810513184893345 12131068654357884888670009)
          ·
            refine ⟨9098301490768413666502507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12131068654357884888670009 9098301490768413666502507)
            ·
              refine ⟨13647452236152620499753761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9098301490768413666502507 13647452236152620499753761)
              ·
                refine ⟨10235589177114465374815321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13647452236152620499753761 10235589177114465374815321)
                ·
                  refine ⟨7676691882835849031111491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10235589177114465374815321 7676691882835849031111491)
                  ·
                    refine ⟨11515037824253773546667237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7676691882835849031111491 11515037824253773546667237)
                    ·
                      refine ⟨2159069592047582540000107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11515037824253773546667237 2159069592047582540000107)
                      ·
                        rfl

theorem cell23_4204773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_4204773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204773 prefixEnd_4204773 := by exact prefixLift 4204773
  have htrace : WordTrace (prefixWord ++ tailWord_4204773) baseStart_4204773 baseEnd_4204773 := by
    simpa [prefixWord, tailWord_4204773, baseEnd_4204773] using wordTrace_append hprefix tailTrace_4204773
  have hstable : (prefixWord ++ tailWord_4204773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204773).length < 2 ^ (prefixWord ++ tailWord_4204773).sum := by decide
  have hdescent : baseEnd_4204773 < baseStart_4204773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204779 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 8]
def baseStart_4204779 : Nat := 118140960795 + 4204779 * 2 ^ 59
def prefixEnd_4204779 : Nat := 4983230072969 + 3 ^ 40 * 4204779 * 2
def baseEnd_4204779 : Nat := 239896963659056612947231

theorem tailTrace_4204779 : CollatzResearch.WordTrace tailWord_4204779 prefixEnd_4204779 239896963659056612947231 := by
  unfold tailWord_4204779
  simp only [CollatzResearch.WordTrace]
  refine ⟨153360889233811276925929391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102240592822540851283952927 153360889233811276925929391)
  ·
    refine ⟨230041333850716915388894087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153360889233811276925929391 230041333850716915388894087)
    ·
      refine ⟨345062000776075373083341131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230041333850716915388894087 345062000776075373083341131)
      ·
        refine ⟨517593001164113059625011697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345062000776075373083341131 517593001164113059625011697)
        ·
          refine ⟨388194750873084794718758773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 517593001164113059625011697 388194750873084794718758773)
          ·
            refine ⟨36393257894351699504883635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 388194750873084794718758773 36393257894351699504883635)
            ·
              refine ⟨54589886841527549257325453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36393257894351699504883635 54589886841527549257325453)
              ·
                refine ⟨20471207565572830971497045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54589886841527549257325453 20471207565572830971497045)
                ·
                  refine ⟨239896963659056612947231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20471207565572830971497045 239896963659056612947231)
                  ·
                    rfl

theorem cell23_4204779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 8].length) (baseStart_4204779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204779 prefixEnd_4204779 := by exact prefixLift 4204779
  have htrace : WordTrace (prefixWord ++ tailWord_4204779) baseStart_4204779 baseEnd_4204779 := by
    simpa [prefixWord, tailWord_4204779, baseEnd_4204779] using wordTrace_append hprefix tailTrace_4204779
  have hstable : (prefixWord ++ tailWord_4204779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204779).length < 2 ^ (prefixWord ++ tailWord_4204779).sum := by decide
  have hdescent : baseEnd_4204779 < baseStart_4204779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204783 : List Nat := [1, 1, 2, 1, 6, 1, 3, 1, 3, 4]
def baseStart_4204783 : Nat := 118140960795 + 4204783 * 2 ^ 59
def prefixEnd_4204783 : Nat := 4983230072969 + 3 ^ 40 * 4204783 * 2
def baseEnd_4204783 : Nat := 719691575618042500291687

theorem tailTrace_4204783 : CollatzResearch.WordTrace tailWord_4204783 prefixEnd_4204783 719691575618042500291687 := by
  unfold tailWord_4204783
  simp only [CollatzResearch.WordTrace]
  refine ⟨153361035125796785609075003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102240690083864523739383335 153361035125796785609075003)
  ·
    refine ⟨230041552688695178413612505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153361035125796785609075003 230041552688695178413612505)
    ·
      refine ⟨172531164516521383810209379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230041552688695178413612505 172531164516521383810209379)
      ·
        refine ⟨258796746774782075715314069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172531164516521383810209379 258796746774782075715314069)
        ·
          refine ⟨12131097505067909799155347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 258796746774782075715314069 12131097505067909799155347)
          ·
            refine ⟨18196646257601864698733021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12131097505067909799155347 18196646257601864698733021)
            ·
              refine ⟨6823742346600699262024883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18196646257601864698733021 6823742346600699262024883)
              ·
                refine ⟨10235613519901048893037325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6823742346600699262024883 10235613519901048893037325)
                ·
                  refine ⟨3838355069962893334888997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10235613519901048893037325 3838355069962893334888997)
                  ·
                    refine ⟨719691575618042500291687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3838355069962893334888997 719691575618042500291687)
                    ·
                      rfl

theorem cell23_4204783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 4].length) (baseStart_4204783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204783 prefixEnd_4204783 := by exact prefixLift 4204783
  have htrace : WordTrace (prefixWord ++ tailWord_4204783) baseStart_4204783 baseEnd_4204783 := by
    simpa [prefixWord, tailWord_4204783, baseEnd_4204783] using wordTrace_append hprefix tailTrace_4204783
  have hstable : (prefixWord ++ tailWord_4204783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204783).length < 2 ^ (prefixWord ++ tailWord_4204783).sum := by decide
  have hdescent : baseEnd_4204783 < baseStart_4204783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204819 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 7]
def baseStart_4204819 : Nat := 118140960795 + 4204819 * 2 ^ 59
def prefixEnd_4204819 : Nat := 4983230072969 + 3 ^ 40 * 4204819 * 2
def baseEnd_4204819 : Nat := 2159093212157689360024895

theorem tailTrace_4204819 : CollatzResearch.WordTrace tailWord_4204819 prefixEnd_4204819 2159093212157689360024895 := by
  unfold tailWord_4204819
  simp only [CollatzResearch.WordTrace]
  refine ⟨153362348153666363757385511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102241565435777575838257007 153362348153666363757385511)
  ·
    refine ⟨230043522230499545636078267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153362348153666363757385511 230043522230499545636078267)
    ·
      refine ⟨345065283345749318454117401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230043522230499545636078267 345065283345749318454117401)
      ·
        refine ⟨258798962509311988840588051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345065283345749318454117401 258798962509311988840588051)
        ·
          refine ⟨388198443763967983260882077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258798962509311988840588051 388198443763967983260882077)
          ·
            refine ⟨145574416411487993722830779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 388198443763967983260882077 145574416411487993722830779)
            ·
              refine ⟨218361624617231990584246169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145574416411487993722830779 218361624617231990584246169)
              ·
                refine ⟨163771218462923992938184627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218361624617231990584246169 163771218462923992938184627)
                ·
                  refine ⟨245656827694385989407276941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163771218462923992938184627 245656827694385989407276941)
                  ·
                    refine ⟨92121310385394746027728853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 245656827694385989407276941 92121310385394746027728853)
                    ·
                      refine ⟨2159093212157689360024895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92121310385394746027728853 2159093212157689360024895)
                      ·
                        rfl

theorem cell23_4204819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_4204819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204819 prefixEnd_4204819 := by exact prefixLift 4204819
  have htrace : WordTrace (prefixWord ++ tailWord_4204819) baseStart_4204819 baseEnd_4204819 := by
    simpa [prefixWord, tailWord_4204819, baseEnd_4204819] using wordTrace_append hprefix tailTrace_4204819
  have hstable : (prefixWord ++ tailWord_4204819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204819).length < 2 ^ (prefixWord ++ tailWord_4204819).sum := by decide
  have hdescent : baseEnd_4204819 < baseStart_4204819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204830 : List Nat := [4, 3, 2, 1, 1, 1, 1, 4, 6]
def baseStart_4204830 : Nat := 118140960795 + 4204830 * 2 ^ 59
def prefixEnd_4204830 : Nat := 4983230072969 + 3 ^ 40 * 4204830 * 2
def baseEnd_4204830 : Nat := 239899873382765424109705

theorem tailTrace_4204830 : CollatzResearch.WordTrace tailWord_4204830 prefixEnd_4204830 239899873382765424109705 := by
  unfold tailWord_4204830
  simp only [CollatzResearch.WordTrace]
  refine ⟨19170343669578314079504493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102241832904417675090690629 19170343669578314079504493)
  ·
    refine ⟨7188878876091867779814185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19170343669578314079504493 7188878876091867779814185)
    ·
      refine ⟨5391659157068900834860639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7188878876091867779814185 5391659157068900834860639)
      ·
        refine ⟨8087488735603351252290959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5391659157068900834860639 8087488735603351252290959)
        ·
          refine ⟨12131233103405026878436439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8087488735603351252290959 12131233103405026878436439)
          ·
            refine ⟨18196849655107540317654659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12131233103405026878436439 18196849655107540317654659)
            ·
              refine ⟨27295274482661310476481989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18196849655107540317654659 27295274482661310476481989)
              ·
                refine ⟨5117863965498995714340373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27295274482661310476481989 5117863965498995714340373)
                ·
                  refine ⟨239899873382765424109705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5117863965498995714340373 239899873382765424109705)
                  ·
                    rfl

theorem cell23_4204830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_4204830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204830 prefixEnd_4204830 := by exact prefixLift 4204830
  have htrace : WordTrace (prefixWord ++ tailWord_4204830) baseStart_4204830 baseEnd_4204830 := by
    simpa [prefixWord, tailWord_4204830, baseEnd_4204830] using wordTrace_append hprefix tailTrace_4204830
  have hstable : (prefixWord ++ tailWord_4204830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204830).length < 2 ^ (prefixWord ++ tailWord_4204830).sum := by decide
  have hdescent : baseEnd_4204830 < baseStart_4204830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204834 : List Nat := [3, 3, 1, 1, 3, 3, 2, 2, 1, 4]
def baseStart_4204834 : Nat := 118140960795 + 4204834 * 2 ^ 59
def prefixEnd_4204834 : Nat := 4983230072969 + 3 ^ 40 * 4204834 * 2
def baseEnd_4204834 : Nat := 719700304789168933779109

theorem tailTrace_4204834 : CollatzResearch.WordTrace tailWord_4204834 prefixEnd_4204834 719700304789168933779109 := by
  unfold tailWord_4204834
  simp only [CollatzResearch.WordTrace]
  refine ⟨38340723812153005329795389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102241930165741347546121037 38340723812153005329795389)
  ·
    refine ⟨14377771429557376998673271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38340723812153005329795389 14377771429557376998673271)
    ·
      refine ⟨21566657144336065498009907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14377771429557376998673271 21566657144336065498009907)
      ·
        refine ⟨32349985716504098247014861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21566657144336065498009907 32349985716504098247014861)
        ·
          refine ⟨12131244643689036842630573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32349985716504098247014861 12131244643689036842630573)
          ·
            refine ⟨4549216741383388815986465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12131244643689036842630573 4549216741383388815986465)
            ·
              refine ⟨3411912556037541611989849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4549216741383388815986465 3411912556037541611989849)
              ·
                refine ⟨2558934417028156208992387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3411912556037541611989849 2558934417028156208992387)
                ·
                  refine ⟨3838401625542234313488581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2558934417028156208992387 3838401625542234313488581)
                  ·
                    refine ⟨719700304789168933779109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3838401625542234313488581 719700304789168933779109)
                    ·
                      rfl

theorem cell23_4204834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_4204834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204834 prefixEnd_4204834 := by exact prefixLift 4204834
  have htrace : WordTrace (prefixWord ++ tailWord_4204834) baseStart_4204834 baseEnd_4204834 := by
    simpa [prefixWord, tailWord_4204834, baseEnd_4204834] using wordTrace_append hprefix tailTrace_4204834
  have hstable : (prefixWord ++ tailWord_4204834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204834).length < 2 ^ (prefixWord ++ tailWord_4204834).sum := by decide
  have hdescent : baseEnd_4204834 < baseStart_4204834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204856 : List Nat := [2, 1, 2, 1, 3, 1, 3, 3, 1, 6]
def baseStart_4204856 : Nat := 118140960795 + 4204856 * 2 ^ 59
def prefixEnd_4204856 : Nat := 4983230072969 + 3 ^ 40 * 4204856 * 2
def baseEnd_4204856 : Nat := 719704070313968571754075

theorem tailTrace_4204856 : CollatzResearch.WordTrace tailWord_4204856 prefixEnd_4204856 719704070313968571754075 := by
  unfold tailWord_4204856
  simp only [CollatzResearch.WordTrace]
  refine ⟨76681848827266159538241211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102242465103021546050988281 76681848827266159538241211)
  ·
    refine ⟨115022773240899239307361817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76681848827266159538241211 115022773240899239307361817)
    ·
      refine ⟨86267079930674429480521363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115022773240899239307361817 86267079930674429480521363)
      ·
        refine ⟨129400619896011644220782045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86267079930674429480521363 129400619896011644220782045)
        ·
          refine ⟨48525232461004366582793267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129400619896011644220782045 48525232461004366582793267)
          ·
            refine ⟨72787848691506549874189901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48525232461004366582793267 72787848691506549874189901)
            ·
              refine ⟨27295443259314956202821213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72787848691506549874189901 27295443259314956202821213)
              ·
                refine ⟨10235791222243108576057955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27295443259314956202821213 10235791222243108576057955)
                ·
                  refine ⟨15353686833364662864086933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10235791222243108576057955 15353686833364662864086933)
                  ·
                    refine ⟨719704070313968571754075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15353686833364662864086933 719704070313968571754075)
                    ·
                      rfl

theorem cell23_4204856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_4204856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204856 prefixEnd_4204856 := by exact prefixLift 4204856
  have htrace : WordTrace (prefixWord ++ tailWord_4204856) baseStart_4204856 baseEnd_4204856 := by
    simpa [prefixWord, tailWord_4204856, baseEnd_4204856] using wordTrace_append hprefix tailTrace_4204856
  have hstable : (prefixWord ++ tailWord_4204856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204856).length < 2 ^ (prefixWord ++ tailWord_4204856).sum := by decide
  have hdescent : baseEnd_4204856 < baseStart_4204856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204863 : List Nat := [1, 1, 2, 2, 4, 1, 2, 4, 1, 1, 4]
def baseStart_4204863 : Nat := 118140960795 + 4204863 * 2 ^ 59
def prefixEnd_4204863 : Nat := 4983230072969 + 3 ^ 40 * 4204863 * 2
def baseEnd_4204863 : Nat := 2159115805306487187874693

theorem tailTrace_4204863 : CollatzResearch.WordTrace tailWord_4204863 prefixEnd_4204863 2159115805306487187874693 := by
  unfold tailWord_4204863
  simp only [CollatzResearch.WordTrace]
  refine ⟨153363952965506959271987243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102242635310337972847991495 153363952965506959271987243)
  ·
    refine ⟨230045929448260438907980865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153363952965506959271987243 230045929448260438907980865)
    ·
      refine ⟨172534447086195329180985649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230045929448260438907980865 172534447086195329180985649)
      ·
        refine ⟨129400835314646496885739237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172534447086195329180985649 129400835314646496885739237)
        ·
          refine ⟨24262656621496218166076107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129400835314646496885739237 24262656621496218166076107)
          ·
            refine ⟨36393984932244327249114161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24262656621496218166076107 36393984932244327249114161)
            ·
              refine ⟨27295488699183245436835621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36393984932244327249114161 27295488699183245436835621)
              ·
                refine ⟨5117904131096858519406679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27295488699183245436835621 5117904131096858519406679)
                ·
                  refine ⟨7676856196645287779110019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5117904131096858519406679 7676856196645287779110019)
                  ·
                    refine ⟨11515284294967931668665029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7676856196645287779110019 11515284294967931668665029)
                    ·
                      refine ⟨2159115805306487187874693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11515284294967931668665029 2159115805306487187874693)
                      ·
                        rfl

theorem cell23_4204863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 1, 4].length) (baseStart_4204863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204863 prefixEnd_4204863 := by exact prefixLift 4204863
  have htrace : WordTrace (prefixWord ++ tailWord_4204863) baseStart_4204863 baseEnd_4204863 := by
    simpa [prefixWord, tailWord_4204863, baseEnd_4204863] using wordTrace_append hprefix tailTrace_4204863
  have hstable : (prefixWord ++ tailWord_4204863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204863).length < 2 ^ (prefixWord ++ tailWord_4204863).sum := by decide
  have hdescent : baseEnd_4204863 < baseStart_4204863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204880 : List Nat := [2, 1, 1, 1, 1, 6, 4, 1, 1, 1, 4]
def baseStart_4204880 : Nat := 118140960795 + 4204880 * 2 ^ 59
def prefixEnd_4204880 : Nat := 4983230072969 + 3 ^ 40 * 4204880 * 2
def baseEnd_4204880 : Nat := 2159124534477613621362115

theorem tailTrace_4204880 : CollatzResearch.WordTrace tailWord_4204880 prefixEnd_4204880 2159124534477613621362115 := by
  unfold tailWord_4204880
  simp only [CollatzResearch.WordTrace]
  refine ⟨76682286503222685587678047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102243048670963580783570729 76682286503222685587678047)
  ·
    refine ⟨115023429754834028381517071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76682286503222685587678047 115023429754834028381517071)
    ·
      refine ⟨172535144632251042572275607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115023429754834028381517071 172535144632251042572275607)
      ·
        refine ⟨258802716948376563858413411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172535144632251042572275607 258802716948376563858413411)
        ·
          refine ⟨388204075422564845787620117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258802716948376563858413411 388204075422564845787620117)
          ·
            refine ⟨18197066035432727146294693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 388204075422564845787620117 18197066035432727146294693)
            ·
              refine ⟨3411949881643636339930255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18197066035432727146294693 3411949881643636339930255)
              ·
                refine ⟨5117924822465454509895383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3411949881643636339930255 5117924822465454509895383)
                ·
                  refine ⟨7676887233698181764843075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5117924822465454509895383 7676887233698181764843075)
                  ·
                    refine ⟨11515330850547272647264613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7676887233698181764843075 11515330850547272647264613)
                    ·
                      refine ⟨2159124534477613621362115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11515330850547272647264613 2159124534477613621362115)
                      ·
                        rfl

theorem cell23_4204880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 1, 1, 4].length) (baseStart_4204880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204880 prefixEnd_4204880 := by exact prefixLift 4204880
  have htrace : WordTrace (prefixWord ++ tailWord_4204880) baseStart_4204880 baseEnd_4204880 := by
    simpa [prefixWord, tailWord_4204880, baseEnd_4204880] using wordTrace_append hprefix tailTrace_4204880
  have hstable : (prefixWord ++ tailWord_4204880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204880).length < 2 ^ (prefixWord ++ tailWord_4204880).sum := by decide
  have hdescent : baseEnd_4204880 < baseStart_4204880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204917 : List Nat := [1, 3, 4, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_4204917 : Nat := 118140960795 + 4204917 * 2 ^ 59
def prefixEnd_4204917 : Nat := 4983230072969 + 3 ^ 40 * 4204917 * 2
def baseEnd_4204917 : Nat := 2159143533261829976599445

theorem tailTrace_4204917 : CollatzResearch.WordTrace tailWord_4204917 prefixEnd_4204917 2159143533261829976599445 := by
  unfold tailWord_4204917
  simp only [CollatzResearch.WordTrace]
  refine ⟨153365922507311326494453005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102243948338207550996302003 153365922507311326494453005)
  ·
    refine ⟨57512220940241747435419877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153365922507311326494453005 57512220940241747435419877)
    ·
      refine ⟨10783541426295327644141227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57512220940241747435419877 10783541426295327644141227)
      ·
        refine ⟨16175312139442991466211841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10783541426295327644141227 16175312139442991466211841)
        ·
          refine ⟨12131484104582243599658881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16175312139442991466211841 12131484104582243599658881)
          ·
            refine ⟨9098613078436682699744161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12131484104582243599658881 9098613078436682699744161)
            ·
              refine ⟨6823959808827512024808121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9098613078436682699744161 6823959808827512024808121)
              ·
                refine ⟨5117969856620634018606091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6823959808827512024808121 5117969856620634018606091)
                ·
                  refine ⟨7676954784930951027909137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5117969856620634018606091 7676954784930951027909137)
                  ·
                    refine ⟨5757716088698213270931853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7676954784930951027909137 5757716088698213270931853)
                    ·
                      refine ⟨2159143533261829976599445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5757716088698213270931853 2159143533261829976599445)
                      ·
                        rfl

theorem cell23_4204917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_4204917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204917 prefixEnd_4204917 := by exact prefixLift 4204917
  have htrace : WordTrace (prefixWord ++ tailWord_4204917) baseStart_4204917 baseEnd_4204917 := by
    simpa [prefixWord, tailWord_4204917, baseEnd_4204917] using wordTrace_append hprefix tailTrace_4204917
  have hstable : (prefixWord ++ tailWord_4204917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204917).length < 2 ^ (prefixWord ++ tailWord_4204917).sum := by decide
  have hdescent : baseEnd_4204917 < baseStart_4204917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204931 : List Nat := [1, 1, 1, 3, 6, 2, 1, 3, 1, 2, 2]
def baseStart_4204931 : Nat := 118140960795 + 4204931 * 2 ^ 59
def prefixEnd_4204931 : Nat := 4983230072969 + 3 ^ 40 * 4204931 * 2
def baseEnd_4204931 : Nat := 2159150721990992921824381

theorem tailTrace_4204931 : CollatzResearch.WordTrace tailWord_4204931 prefixEnd_4204931 2159150721990992921824381 := by
  unfold tailWord_4204931
  simp only [CollatzResearch.WordTrace]
  refine ⟨153366433129260606885462647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102244288752840404590308431 153366433129260606885462647)
  ·
    refine ⟨230049649693890910328193971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153366433129260606885462647 230049649693890910328193971)
    ·
      refine ⟨345074474540836365492290957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230049649693890910328193971 345074474540836365492290957)
      ·
        refine ⟨129402927952813637059609109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 345074474540836365492290957 129402927952813637059609109)
        ·
          refine ⟨6065762247788139237169177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 129402927952813637059609109 6065762247788139237169177)
          ·
            refine ⟨4549321685841104427876883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6065762247788139237169177 4549321685841104427876883)
            ·
              refine ⟨6823982528761656641815325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4549321685841104427876883 6823982528761656641815325)
              ·
                refine ⟨2558993448285621240680747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6823982528761656641815325 2558993448285621240680747)
                ·
                  refine ⟨3838490172428431861021121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2558993448285621240680747 3838490172428431861021121)
                  ·
                    refine ⟨2878867629321323895765841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3838490172428431861021121 2878867629321323895765841)
                    ·
                      refine ⟨2159150721990992921824381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2878867629321323895765841 2159150721990992921824381)
                      ·
                        rfl

theorem cell23_4204931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 1, 2, 2].length) (baseStart_4204931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204931 prefixEnd_4204931 := by exact prefixLift 4204931
  have htrace : WordTrace (prefixWord ++ tailWord_4204931) baseStart_4204931 baseEnd_4204931 := by
    simpa [prefixWord, tailWord_4204931, baseEnd_4204931] using wordTrace_append hprefix tailTrace_4204931
  have hstable : (prefixWord ++ tailWord_4204931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204931).length < 2 ^ (prefixWord ++ tailWord_4204931).sum := by decide
  have hdescent : baseEnd_4204931 < baseStart_4204931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4204948 : List Nat := [2, 4, 2, 1, 3, 1, 3, 2, 1, 2, 2]
def baseStart_4204948 : Nat := 118140960795 + 4204948 * 2 ^ 59
def prefixEnd_4204948 : Nat := 4983230072969 + 3 ^ 40 * 4204948 * 2
def baseEnd_4204948 : Nat := 2159159451162119355311803

theorem tailTrace_4204948 : CollatzResearch.WordTrace tailWord_4204948 prefixEnd_4204948 2159159451162119355311803 := by
  unfold tailWord_4204948
  simp only [CollatzResearch.WordTrace]
  refine ⟨76683526585099509394415749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102244702113466012525887665 76683526585099509394415749)
  ·
    refine ⟨14378161234706158011452953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76683526585099509394415749 14378161234706158011452953)
    ·
      refine ⟨10783620926029618508589715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14378161234706158011452953 10783620926029618508589715)
      ·
        refine ⟨16175431389044427762884573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10783620926029618508589715 16175431389044427762884573)
        ·
          refine ⟨6065786770891660411081715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16175431389044427762884573 6065786770891660411081715)
          ·
            refine ⟨9098680156337490616622573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6065786770891660411081715 9098680156337490616622573)
            ·
              refine ⟨3412005058626558981233465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9098680156337490616622573 3412005058626558981233465)
              ·
                refine ⟨2559003793969919235925099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3412005058626558981233465 2559003793969919235925099)
                ·
                  refine ⟨3838505690954878853887649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2559003793969919235925099 3838505690954878853887649)
                  ·
                    refine ⟨2878879268216159140415737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3838505690954878853887649 2878879268216159140415737)
                    ·
                      refine ⟨2159159451162119355311803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2878879268216159140415737 2159159451162119355311803)
                      ·
                        rfl

theorem cell23_4204948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_4204948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4204948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4204948 prefixEnd_4204948 := by exact prefixLift 4204948
  have htrace : WordTrace (prefixWord ++ tailWord_4204948) baseStart_4204948 baseEnd_4204948 := by
    simpa [prefixWord, tailWord_4204948, baseEnd_4204948] using wordTrace_append hprefix tailTrace_4204948
  have hstable : (prefixWord ++ tailWord_4204948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4204948).length < 2 ^ (prefixWord ++ tailWord_4204948).sum := by decide
  have hdescent : baseEnd_4204948 < baseStart_4204948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4204948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205003 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 3]
def baseStart_4205003 : Nat := 118140960795 + 4205003 * 2 ^ 59
def prefixEnd_4205003 : Nat := 4983230072969 + 3 ^ 40 * 4205003 * 2
def baseEnd_4205003 : Nat := 2159187692598116640124049

theorem tailTrace_4205003 : CollatzResearch.WordTrace tailWord_4205003 prefixEnd_4205003 2159187692598116640124049 := by
  unfold tailWord_4205003
  simp only [CollatzResearch.WordTrace]
  refine ⟨153369059184999763182083663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102246039456666508788055775 153369059184999763182083663)
  ·
    refine ⟨230053588777499644773125495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153369059184999763182083663 230053588777499644773125495)
    ·
      refine ⟨345080383166249467159688243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230053588777499644773125495 345080383166249467159688243)
      ·
        refine ⟨517620574749374200739532365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345080383166249467159688243 517620574749374200739532365)
        ·
          refine ⟨194107715531015325277324637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 517620574749374200739532365 194107715531015325277324637)
          ·
            refine ⟨72790393324130746978996739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 194107715531015325277324637 72790393324130746978996739)
            ·
              refine ⟨109185589986196120468495109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72790393324130746978996739 109185589986196120468495109)
              ·
                refine ⟨20472298122411772587842833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109185589986196120468495109 20472298122411772587842833)
                ·
                  refine ⟨15354223591808829440882125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20472298122411772587842833 15354223591808829440882125)
                  ·
                    refine ⟨5757833846928311040330797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15354223591808829440882125 5757833846928311040330797)
                    ·
                      refine ⟨2159187692598116640124049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5757833846928311040330797 2159187692598116640124049)
                      ·
                        rfl

theorem cell23_4205003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 3].length) (baseStart_4205003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205003 prefixEnd_4205003 := by exact prefixLift 4205003
  have htrace : WordTrace (prefixWord ++ tailWord_4205003) baseStart_4205003 baseEnd_4205003 := by
    simpa [prefixWord, tailWord_4205003, baseEnd_4205003] using wordTrace_append hprefix tailTrace_4205003
  have hstable : (prefixWord ++ tailWord_4205003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205003).length < 2 ^ (prefixWord ++ tailWord_4205003).sum := by decide
  have hdescent : baseEnd_4205003 < baseStart_4205003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205043 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 4]
def baseStart_4205043 : Nat := 118140960795 + 4205043 * 2 ^ 59
def prefixEnd_4205043 : Nat := 4983230072969 + 3 ^ 40 * 4205043 * 2
def baseEnd_4205043 : Nat := 2159208231824296483623865

theorem tailTrace_4205043 : CollatzResearch.WordTrace tailWord_4205043 prefixEnd_4205043 2159208231824296483623865 := by
  unfold tailWord_4205043
  simp only [CollatzResearch.WordTrace]
  refine ⟨153370518104854850013539783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102247012069903233342359855 153370518104854850013539783)
  ·
    refine ⟨230055777157282275020309675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153370518104854850013539783 230055777157282275020309675)
    ·
      refine ⟨345083665735923412530464513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230055777157282275020309675 345083665735923412530464513)
      ·
        refine ⟨258812749301942559397848385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345083665735923412530464513 258812749301942559397848385)
        ·
          refine ⟨194109561976456919548386289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258812749301942559397848385 194109561976456919548386289)
          ·
            refine ⟨145582171482342689661289717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194109561976456919548386289 145582171482342689661289717)
            ·
              refine ⟨13648328576469627155745911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 145582171482342689661289717 13648328576469627155745911)
              ·
                refine ⟨20472492864704440733618867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13648328576469627155745911 20472492864704440733618867)
                ·
                  refine ⟨30708739297056661100428301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20472492864704440733618867 30708739297056661100428301)
                  ·
                    refine ⟨11515777236396247912660613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30708739297056661100428301 11515777236396247912660613)
                    ·
                      refine ⟨2159208231824296483623865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11515777236396247912660613 2159208231824296483623865)
                      ·
                        rfl

theorem cell23_4205043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 4].length) (baseStart_4205043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205043 prefixEnd_4205043 := by exact prefixLift 4205043
  have htrace : WordTrace (prefixWord ++ tailWord_4205043) baseStart_4205043 baseEnd_4205043 := by
    simpa [prefixWord, tailWord_4205043, baseEnd_4205043] using wordTrace_append hprefix tailTrace_4205043
  have hstable : (prefixWord ++ tailWord_4205043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205043).length < 2 ^ (prefixWord ++ tailWord_4205043).sum := by decide
  have hdescent : baseEnd_4205043 < baseStart_4205043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205080 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 1, 4, 3]
def baseStart_4205080 : Nat := 118140960795 + 4205080 * 2 ^ 59
def prefixEnd_4205080 : Nat := 4983230072969 + 3 ^ 40 * 4205080 * 2
def baseEnd_4205080 : Nat := 2159227230608512838861195

theorem tailTrace_4205080 : CollatzResearch.WordTrace tailWord_4205080 prefixEnd_4205080 2159227230608512838861195 := by
  unfold tailWord_4205080
  simp only [CollatzResearch.WordTrace]
  refine ⟨76685933802860402666318347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102247911737147203555091129 76685933802860402666318347)
  ·
    refine ⟨115028900704290603999477521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76685933802860402666318347 115028900704290603999477521)
    ·
      refine ⟨86271675528217952999608141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115028900704290603999477521 86271675528217952999608141)
      ·
        refine ⟨32351878323081732374853053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86271675528217952999608141 32351878323081732374853053)
        ·
          refine ⟨12131954371155649640569895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32351878323081732374853053 12131954371155649640569895)
          ·
            refine ⟨18197931556733474460854843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12131954371155649640569895 18197931556733474460854843)
            ·
              refine ⟨27296897335100211691282265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18197931556733474460854843 27296897335100211691282265)
              ·
                refine ⟨20472673001325158768461699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27296897335100211691282265 20472673001325158768461699)
                ·
                  refine ⟨30709009501987738152692549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20472673001325158768461699 30709009501987738152692549)
                  ·
                    refine ⟨5757939281622700903629853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30709009501987738152692549 5757939281622700903629853)
                    ·
                      refine ⟨2159227230608512838861195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5757939281622700903629853 2159227230608512838861195)
                      ·
                        rfl

theorem cell23_4205080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_4205080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205080 prefixEnd_4205080 := by exact prefixLift 4205080
  have htrace : WordTrace (prefixWord ++ tailWord_4205080) baseStart_4205080 baseEnd_4205080 := by
    simpa [prefixWord, tailWord_4205080, baseEnd_4205080] using wordTrace_append hprefix tailTrace_4205080
  have hstable : (prefixWord ++ tailWord_4205080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205080).length < 2 ^ (prefixWord ++ tailWord_4205080).sum := by decide
  have hdescent : baseEnd_4205080 < baseStart_4205080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205121 : List Nat := [1, 2, 5, 1, 1, 3, 3, 2, 1, 4]
def baseStart_4205121 : Nat := 118140960795 + 4205121 * 2 ^ 59
def prefixEnd_4205121 : Nat := 4983230072969 + 3 ^ 40 * 4205121 * 2
def baseEnd_4205121 : Nat := 719749427771782392816169

theorem tailTrace_4205121 : CollatzResearch.WordTrace tailWord_4205121 prefixEnd_4205121 719749427771782392816169 := by
  unfold tailWord_4205121
  simp only [CollatzResearch.WordTrace]
  refine ⟨153373362998572269334879217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102248908665714846223252811 153373362998572269334879217)
  ·
    refine ⟨115030022248929202001159413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153373362998572269334879217 115030022248929202001159413)
    ·
      refine ⟨10784064585837112687608695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115030022248929202001159413 10784064585837112687608695)
      ·
        refine ⟨16176096878755669031413043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10784064585837112687608695 16176096878755669031413043)
        ·
          refine ⟨24264145318133503547119565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16176096878755669031413043 24264145318133503547119565)
          ·
            refine ⟨9099054494300063830169837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24264145318133503547119565 9099054494300063830169837)
            ·
              refine ⟨3412145435362523936313689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9099054494300063830169837 3412145435362523936313689)
              ·
                refine ⟨2559109076521892952235267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3412145435362523936313689 2559109076521892952235267)
                ·
                  refine ⟨3838663614782839428352901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2559109076521892952235267 3838663614782839428352901)
                  ·
                    refine ⟨719749427771782392816169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3838663614782839428352901 719749427771782392816169)
                    ·
                      rfl

theorem cell23_4205121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_4205121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205121 prefixEnd_4205121 := by exact prefixLift 4205121
  have htrace : WordTrace (prefixWord ++ tailWord_4205121) baseStart_4205121 baseEnd_4205121 := by
    simpa [prefixWord, tailWord_4205121, baseEnd_4205121] using wordTrace_append hprefix tailTrace_4205121
  have hstable : (prefixWord ++ tailWord_4205121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205121).length < 2 ^ (prefixWord ++ tailWord_4205121).sum := by decide
  have hdescent : baseEnd_4205121 < baseStart_4205121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205163 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 6]
def baseStart_4205163 : Nat := 118140960795 + 4205163 * 2 ^ 59
def prefixEnd_4205163 : Nat := 4983230072969 + 3 ^ 40 * 4205163 * 2
def baseEnd_4205163 : Nat := 2159269849502836014123313

theorem tailTrace_4205163 : CollatzResearch.WordTrace tailWord_4205163 prefixEnd_4205163 2159269849502836014123313 := by
  unfold tailWord_4205163
  simp only [CollatzResearch.WordTrace]
  refine ⟨153374894864420110507908143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102249929909613407005272095 153374894864420110507908143)
  ·
    refine ⟨230062342296630165761862215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153374894864420110507908143 230062342296630165761862215)
    ·
      refine ⟨345093513444945248642793323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230062342296630165761862215 345093513444945248642793323)
      ·
        refine ⟨517640270167417872964189985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345093513444945248642793323 517640270167417872964189985)
        ·
          refine ⟨388230202625563404723142489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 517640270167417872964189985 388230202625563404723142489)
          ·
            refine ⟨291172651969172553542356867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 388230202625563404723142489 291172651969172553542356867)
            ·
              refine ⟨436758977953758830313535301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291172651969172553542356867 436758977953758830313535301)
              ·
                refine ⟨81892308366329780683787869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 436758977953758830313535301 81892308366329780683787869)
                ·
                  refine ⟨30709615637373667756420451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81892308366329780683787869 30709615637373667756420451)
                  ·
                    refine ⟨46064423456060501634630677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30709615637373667756420451 46064423456060501634630677)
                    ·
                      refine ⟨2159269849502836014123313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46064423456060501634630677 2159269849502836014123313)
                      ·
                        rfl

theorem cell23_4205163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 6].length) (baseStart_4205163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205163 prefixEnd_4205163 := by exact prefixLift 4205163
  have htrace : WordTrace (prefixWord ++ tailWord_4205163) baseStart_4205163 baseEnd_4205163 := by
    simpa [prefixWord, tailWord_4205163, baseEnd_4205163] using wordTrace_append hprefix tailTrace_4205163
  have hstable : (prefixWord ++ tailWord_4205163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205163).length < 2 ^ (prefixWord ++ tailWord_4205163).sum := by decide
  have hdescent : baseEnd_4205163 < baseStart_4205163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205177 : List Nat := [1, 2, 1, 3, 3, 2, 1, 4, 2, 4]
def baseStart_4205177 : Nat := 118140960795 + 4205177 * 2 ^ 59
def prefixEnd_4205177 : Nat := 4983230072969 + 3 ^ 40 * 4205177 * 2
def baseEnd_4205177 : Nat := 719759012743999653116083

theorem tailTrace_4205177 : CollatzResearch.WordTrace tailWord_4205177 prefixEnd_4205177 719759012743999653116083 := by
  unfold tailWord_4205177
  simp only [CollatzResearch.WordTrace]
  refine ⟨153375405486369390898917785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102250270324246260599278523 153375405486369390898917785)
  ·
    refine ⟨115031554114777043174188339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153375405486369390898917785 115031554114777043174188339)
    ·
      refine ⟨172547331172165564761282509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115031554114777043174188339 172547331172165564761282509)
      ·
        refine ⟨64705249189562086785480941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172547331172165564761282509 64705249189562086785480941)
        ·
          refine ⟨24264468446085782544555353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64705249189562086785480941 24264468446085782544555353)
          ·
            refine ⟨18198351334564336908416515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24264468446085782544555353 18198351334564336908416515)
            ·
              refine ⟨27297527001846505362624773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18198351334564336908416515 27297527001846505362624773)
              ·
                refine ⟨5118286312846219755492145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27297527001846505362624773 5118286312846219755492145)
                ·
                  refine ⟨3838714734634664816619109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5118286312846219755492145 3838714734634664816619109)
                  ·
                    refine ⟨719759012743999653116083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3838714734634664816619109 719759012743999653116083)
                    ·
                      rfl

theorem cell23_4205177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 4].length) (baseStart_4205177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205177 prefixEnd_4205177 := by exact prefixLift 4205177
  have htrace : WordTrace (prefixWord ++ tailWord_4205177) baseStart_4205177 baseEnd_4205177 := by
    simpa [prefixWord, tailWord_4205177, baseEnd_4205177] using wordTrace_append hprefix tailTrace_4205177
  have hstable : (prefixWord ++ tailWord_4205177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205177).length < 2 ^ (prefixWord ++ tailWord_4205177).sum := by decide
  have hdescent : baseEnd_4205177 < baseStart_4205177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205183 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 7]
def baseStart_4205183 : Nat := 118140960795 + 4205183 * 2 ^ 59
def prefixEnd_4205183 : Nat := 4983230072969 + 3 ^ 40 * 4205183 * 2
def baseEnd_4205183 : Nat := 2159280119115925935873221

theorem tailTrace_4205183 : CollatzResearch.WordTrace tailWord_4205183 prefixEnd_4205183 2159280119115925935873221 := by
  unfold tailWord_4205183
  simp only [CollatzResearch.WordTrace]
  refine ⟨153375624324347653923636203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102250416216231769282424135 153375624324347653923636203)
  ·
    refine ⟨230063436486521480885454305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153375624324347653923636203 230063436486521480885454305)
    ·
      refine ⟨172547577364891110664090729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230063436486521480885454305 172547577364891110664090729)
      ·
        refine ⟨129410683023668332998068047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172547577364891110664090729 129410683023668332998068047)
        ·
          refine ⟨194116024535502499497102071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129410683023668332998068047 194116024535502499497102071)
          ·
            refine ⟨291174036803253749245653107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194116024535502499497102071 291174036803253749245653107)
            ·
              refine ⟨436761055204880623868479661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291174036803253749245653107 436761055204880623868479661)
              ·
                refine ⟨163785395701830233950679873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 436761055204880623868479661 163785395701830233950679873)
                ·
                  refine ⟨122839046776372675463009905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163785395701830233950679873 122839046776372675463009905)
                  ·
                    refine ⟨92129285082279506597257429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122839046776372675463009905 92129285082279506597257429)
                    ·
                      refine ⟨2159280119115925935873221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92129285082279506597257429 2159280119115925935873221)
                      ·
                        rfl

theorem cell23_4205183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_4205183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205183 prefixEnd_4205183 := by exact prefixLift 4205183
  have htrace : WordTrace (prefixWord ++ tailWord_4205183) baseStart_4205183 baseEnd_4205183 := by
    simpa [prefixWord, tailWord_4205183, baseEnd_4205183] using wordTrace_append hprefix tailTrace_4205183
  have hstable : (prefixWord ++ tailWord_4205183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205183).length < 2 ^ (prefixWord ++ tailWord_4205183).sum := by decide
  have hdescent : baseEnd_4205183 < baseStart_4205183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205204 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_4205204 : Nat := 118140960795 + 4205204 * 2 ^ 59
def prefixEnd_4205204 : Nat := 4983230072969 + 3 ^ 40 * 4205204 * 2
def baseEnd_4205204 : Nat := 2159290902209670353710625

theorem tailTrace_4205204 : CollatzResearch.WordTrace tailWord_4205204 prefixEnd_4205204 2159290902209670353710625 := by
  unfold tailWord_4205204
  simp only [CollatzResearch.WordTrace]
  refine ⟨76688195128635787255075333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102250926838181049673433777 76688195128635787255075333)
  ·
    refine ⟨14379036586619210110326625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76688195128635787255075333 14379036586619210110326625)
    ·
      refine ⟨10784277439964407582744969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14379036586619210110326625 10784277439964407582744969)
      ·
        refine ⟨8088208079973305687058727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10784277439964407582744969 8088208079973305687058727)
        ·
          refine ⟨12132312119959958530588091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8088208079973305687058727 12132312119959958530588091)
          ·
            refine ⟨18198468179939937795882137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12132312119959958530588091 18198468179939937795882137)
            ·
              refine ⟨13648851134954953346911603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18198468179939937795882137 13648851134954953346911603)
              ·
                refine ⟨20473276702432430020367405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13648851134954953346911603 20473276702432430020367405)
                ·
                  refine ⟨7677478763412161257637777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20473276702432430020367405 7677478763412161257637777)
                  ·
                    refine ⟨5758109072559120943228333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7677478763412161257637777 5758109072559120943228333)
                    ·
                      refine ⟨2159290902209670353710625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5758109072559120943228333 2159290902209670353710625)
                      ·
                        rfl

theorem cell23_4205204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_4205204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205204 prefixEnd_4205204 := by exact prefixLift 4205204
  have htrace : WordTrace (prefixWord ++ tailWord_4205204) baseStart_4205204 baseEnd_4205204 := by
    simpa [prefixWord, tailWord_4205204, baseEnd_4205204] using wordTrace_append hprefix tailTrace_4205204
  have hstable : (prefixWord ++ tailWord_4205204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205204).length < 2 ^ (prefixWord ++ tailWord_4205204).sum := by decide
  have hdescent : baseEnd_4205204 < baseStart_4205204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205274 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2]
def baseStart_4205274 : Nat := 118140960795 + 4205274 * 2 ^ 59
def prefixEnd_4205274 : Nat := 4983230072969 + 3 ^ 40 * 4205274 * 2
def baseEnd_4205274 : Nat := 2159326845855485079835303

theorem tailTrace_4205274 : CollatzResearch.WordTrace tailWord_4205274 prefixEnd_4205274 2159326845855485079835303 := by
  unfold tailWord_4205274
  simp only [CollatzResearch.WordTrace]
  refine ⟨38344735841754494116299719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102252628911345317643465917 38344735841754494116299719)
  ·
    refine ⟨57517103762631741174449579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38344735841754494116299719 57517103762631741174449579)
    ·
      refine ⟨86275655643947611761674369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57517103762631741174449579 86275655643947611761674369)
      ·
        refine ⟨64706741732960708821255777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86275655643947611761674369 64706741732960708821255777)
        ·
          refine ⟨48530056299720531615941833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64706741732960708821255777 48530056299720531615941833)
          ·
            refine ⟨36397542224790398711956375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48530056299720531615941833 36397542224790398711956375)
            ·
              refine ⟨54596313337185598067934563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36397542224790398711956375 54596313337185598067934563)
              ·
                refine ⟨81894470005778397101901845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54596313337185598067934563 81894470005778397101901845)
                ·
                  refine ⟨3838803281520862364151649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81894470005778397101901845 3838803281520862364151649)
                  ·
                    refine ⟨2879102461140646773113737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3838803281520862364151649 2879102461140646773113737)
                    ·
                      refine ⟨2159326845855485079835303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2879102461140646773113737 2159326845855485079835303)
                      ·
                        rfl

theorem cell23_4205274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_4205274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205274 prefixEnd_4205274 := by exact prefixLift 4205274
  have htrace : WordTrace (prefixWord ++ tailWord_4205274) baseStart_4205274 baseEnd_4205274 := by
    simpa [prefixWord, tailWord_4205274, baseEnd_4205274] using wordTrace_append hprefix tailTrace_4205274
  have hstable : (prefixWord ++ tailWord_4205274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205274).length < 2 ^ (prefixWord ++ tailWord_4205274).sum := by decide
  have hdescent : baseEnd_4205274 < baseStart_4205274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205290 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_4205290 : Nat := 118140960795 + 4205290 * 2 ^ 59
def prefixEnd_4205290 : Nat := 4983230072969 + 3 ^ 40 * 4205290 * 2
def baseEnd_4205290 : Nat := 2159335061545957017235229

theorem tailTrace_4205290 : CollatzResearch.WordTrace tailWord_4205290 prefixEnd_4205290 2159335061545957017235229 := by
  unfold tailWord_4205290
  simp only [CollatzResearch.WordTrace]
  refine ⟨38344881733740002799445331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102253017956640007465187549 38344881733740002799445331)
  ·
    refine ⟨57517322600610004199167997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38344881733740002799445331 57517322600610004199167997)
    ·
      refine ⟨21568995975228751574687999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57517322600610004199167997 21568995975228751574687999)
      ·
        refine ⟨32353493962843127362031999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21568995975228751574687999 32353493962843127362031999)
        ·
          refine ⟨48530240944264691043047999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32353493962843127362031999 48530240944264691043047999)
          ·
            refine ⟨72795361416397036564571999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48530240944264691043047999 72795361416397036564571999)
            ·
              refine ⟨109193042124595554846857999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72795361416397036564571999 109193042124595554846857999)
              ·
                refine ⟨163789563186893332270286999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109193042124595554846857999 163789563186893332270286999)
                ·
                  refine ⟨245684344780339998405430499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163789563186893332270286999 245684344780339998405430499)
                  ·
                    refine ⟨368526517170509997608145749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 245684344780339998405430499 368526517170509997608145749)
                    ·
                      refine ⟨2159335061545957017235229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 368526517170509997608145749 2159335061545957017235229)
                      ·
                        rfl

theorem cell23_4205290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_4205290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205290 prefixEnd_4205290 := by exact prefixLift 4205290
  have htrace : WordTrace (prefixWord ++ tailWord_4205290) baseStart_4205290 baseEnd_4205290 := by
    simpa [prefixWord, tailWord_4205290, baseEnd_4205290] using wordTrace_append hprefix tailTrace_4205290
  have hstable : (prefixWord ++ tailWord_4205290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205290).length < 2 ^ (prefixWord ++ tailWord_4205290).sum := by decide
  have hdescent : baseEnd_4205290 < baseStart_4205290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205308 : List Nat := [2, 2, 2, 1, 3, 2, 4, 1, 2, 2, 2]
def baseStart_4205308 : Nat := 118140960795 + 4205308 * 2 ^ 59
def prefixEnd_4205308 : Nat := 4983230072969 + 3 ^ 40 * 4205308 * 2
def baseEnd_4205308 : Nat := 2159344304197737946810147

theorem tailTrace_4205308 : CollatzResearch.WordTrace tailWord_4205308 prefixEnd_4205308 2159344304197737946810147 := by
  unfold tailWord_4205308
  simp only [CollatzResearch.WordTrace]
  refine ⟨76690091724447400135968289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102253455632596533514624385 76690091724447400135968289)
  ·
    refine ⟨57517568793335550101976217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76690091724447400135968289 57517568793335550101976217)
    ·
      refine ⟨43138176595001662576482163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57517568793335550101976217 43138176595001662576482163)
      ·
        refine ⟨64707264892502493864723245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43138176595001662576482163 64707264892502493864723245)
        ·
          refine ⟨24265224334688435199271217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64707264892502493864723245 24265224334688435199271217)
          ·
            refine ⟨18198918251016326399453413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24265224334688435199271217 18198918251016326399453413)
            ·
              refine ⟨3412297172065561199897515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18198918251016326399453413 3412297172065561199897515)
              ·
                refine ⟨5118445758098341799846273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3412297172065561199897515 5118445758098341799846273)
                ·
                  refine ⟨3838834318573756349884705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5118445758098341799846273 3838834318573756349884705)
                  ·
                    refine ⟨2879125738930317262413529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3838834318573756349884705 2879125738930317262413529)
                    ·
                      refine ⟨2159344304197737946810147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2879125738930317262413529 2159344304197737946810147)
                      ·
                        rfl

theorem cell23_4205308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_4205308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205308 prefixEnd_4205308 := by exact prefixLift 4205308
  have htrace : WordTrace (prefixWord ++ tailWord_4205308) baseStart_4205308 baseEnd_4205308 := by
    simpa [prefixWord, tailWord_4205308, baseEnd_4205308] using wordTrace_append hprefix tailTrace_4205308
  have hstable : (prefixWord ++ tailWord_4205308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205308).length < 2 ^ (prefixWord ++ tailWord_4205308).sum := by decide
  have hdescent : baseEnd_4205308 < baseStart_4205308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205327 : List Nat := [1, 1, 2, 1, 1, 1, 8, 1, 2, 5]
def baseStart_4205327 : Nat := 118140960795 + 4205327 * 2 ^ 59
def prefixEnd_4205327 : Nat := 4983230072969 + 3 ^ 40 * 4205327 * 2
def baseEnd_4205327 : Nat := 719784686776724457490853

theorem tailTrace_4205327 : CollatzResearch.WordTrace tailWord_4205327 prefixEnd_4205327 719784686776724457490853 := by
  unfold tailWord_4205327
  simp only [CollatzResearch.WordTrace]
  refine ⟨153380876435825966516878235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102253917623883977677918823 153380876435825966516878235)
  ·
    refine ⟨230071314653738949775317353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153380876435825966516878235 230071314653738949775317353)
    ·
      refine ⟨172553485990304212331488015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230071314653738949775317353 172553485990304212331488015)
      ·
        refine ⟨258830228985456318497232023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172553485990304212331488015 258830228985456318497232023)
        ·
          refine ⟨388245343478184477745848035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258830228985456318497232023 388245343478184477745848035)
          ·
            refine ⟨582368015217276716618772053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388245343478184477745848035 582368015217276716618772053)
            ·
              refine ⟨6824625178327461522876235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 582368015217276716618772053 6824625178327461522876235)
              ·
                refine ⟨10236937767491192284314353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6824625178327461522876235 10236937767491192284314353)
                ·
                  refine ⟨7677703325618394213235765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10236937767491192284314353 7677703325618394213235765)
                  ·
                    refine ⟨719784686776724457490853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7677703325618394213235765 719784686776724457490853)
                    ·
                      rfl

theorem cell23_4205327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 5].length) (baseStart_4205327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205327 prefixEnd_4205327 := by exact prefixLift 4205327
  have htrace : WordTrace (prefixWord ++ tailWord_4205327) baseStart_4205327 baseEnd_4205327 := by
    simpa [prefixWord, tailWord_4205327, baseEnd_4205327] using wordTrace_append hprefix tailTrace_4205327
  have hstable : (prefixWord ++ tailWord_4205327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205327).length < 2 ^ (prefixWord ++ tailWord_4205327).sum := by decide
  have hdescent : baseEnd_4205327 < baseStart_4205327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205348 : List Nat := [2, 3, 1, 3, 3, 2, 2, 2, 5]
def baseStart_4205348 : Nat := 118140960795 + 4205348 * 2 ^ 59
def prefixEnd_4205348 : Nat := 4983230072969 + 3 ^ 40 * 4205348 * 2
def baseEnd_4205348 : Nat := 239929427047101976701107

theorem tailTrace_4205348 : CollatzResearch.WordTrace tailWord_4205348 prefixEnd_4205348 239929427047101976701107 := by
  unfold tailWord_4205348
  simp only [CollatzResearch.WordTrace]
  refine ⟨76690821184374943551696349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102254428245833258068928465 76690821184374943551696349)
  ·
    refine ⟨28759057944140603831886131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76690821184374943551696349 28759057944140603831886131)
    ·
      refine ⟨43138586916210905747829197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28759057944140603831886131 43138586916210905747829197)
      ·
        refine ⟨16176970093579089655435949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43138586916210905747829197 16176970093579089655435949)
        ·
          refine ⟨6066363785092158620788481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16176970093579089655435949 6066363785092158620788481)
          ·
            refine ⟨4549772838819118965591361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6066363785092158620788481 4549772838819118965591361)
            ·
              refine ⟨3412329629114339224193521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4549772838819118965591361 3412329629114339224193521)
              ·
                refine ⟨2559247221835754418145141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3412329629114339224193521 2559247221835754418145141)
                ·
                  refine ⟨239929427047101976701107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2559247221835754418145141 239929427047101976701107)
                  ·
                    rfl

theorem cell23_4205348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_4205348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205348 prefixEnd_4205348 := by exact prefixLift 4205348
  have htrace : WordTrace (prefixWord ++ tailWord_4205348) baseStart_4205348 baseEnd_4205348 := by
    simpa [prefixWord, tailWord_4205348, baseEnd_4205348] using wordTrace_append hprefix tailTrace_4205348
  have hstable : (prefixWord ++ tailWord_4205348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205348).length < 2 ^ (prefixWord ++ tailWord_4205348).sum := by decide
  have hdescent : baseEnd_4205348 < baseStart_4205348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205367 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 3]
def baseStart_4205367 : Nat := 118140960795 + 4205367 * 2 ^ 59
def prefixEnd_4205367 : Nat := 4983230072969 + 3 ^ 40 * 4205367 * 2
def baseEnd_4205367 : Nat := 2159374599556353215972375

theorem tailTrace_4205367 : CollatzResearch.WordTrace tailWord_4205367 prefixEnd_4205367 2159374599556353215972375 := by
  unfold tailWord_4205367
  simp only [CollatzResearch.WordTrace]
  refine ⟨153382335355681053348334355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102254890237120702232222903 153382335355681053348334355)
  ·
    refine ⟨230073503033521580022501533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153382335355681053348334355 230073503033521580022501533)
    ·
      refine ⟨86277563637570592508438075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230073503033521580022501533 86277563637570592508438075)
      ·
        refine ⟨129416345456355888762657113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86277563637570592508438075 129416345456355888762657113)
        ·
          refine ⟨97062259092266916571992835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129416345456355888762657113 97062259092266916571992835)
          ·
            refine ⟨145593388638400374857989253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97062259092266916571992835 145593388638400374857989253)
            ·
              refine ⟨27298760369700070285872985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145593388638400374857989253 27298760369700070285872985)
              ·
                refine ⟨20474070277275052714404739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27298760369700070285872985 20474070277275052714404739)
                ·
                  refine ⟨30711105415912579071607109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20474070277275052714404739 30711105415912579071607109)
                  ·
                    refine ⟨5758332265483608575926333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30711105415912579071607109 5758332265483608575926333)
                    ·
                      refine ⟨2159374599556353215972375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5758332265483608575926333 2159374599556353215972375)
                      ·
                        rfl

theorem cell23_4205367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_4205367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205367 prefixEnd_4205367 := by exact prefixLift 4205367
  have htrace : WordTrace (prefixWord ++ tailWord_4205367) baseStart_4205367 baseEnd_4205367 := by
    simpa [prefixWord, tailWord_4205367, baseEnd_4205367] using wordTrace_append hprefix tailTrace_4205367
  have hstable : (prefixWord ++ tailWord_4205367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205367).length < 2 ^ (prefixWord ++ tailWord_4205367).sum := by decide
  have hdescent : baseEnd_4205367 < baseStart_4205367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205404 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 8]
def baseStart_4205404 : Nat := 118140960795 + 4205404 * 2 ^ 59
def prefixEnd_4205404 : Nat := 4983230072969 + 3 ^ 40 * 4205404 * 2
def baseEnd_4205404 : Nat := 239932622037841063467745

theorem tailTrace_4205404 : CollatzResearch.WordTrace tailWord_4205404 prefixEnd_4205404 239932622037841063467745 := by
  unfold tailWord_4205404
  simp only [CollatzResearch.WordTrace]
  refine ⟨76691842428273504333715633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102255789904364672444954177 76691842428273504333715633)
  ·
    refine ⟨57518881821205128250286725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76691842428273504333715633 57518881821205128250286725)
    ·
      refine ⟨10784790341475961546928761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57518881821205128250286725 10784790341475961546928761)
      ·
        refine ⟨8088592756106971160196571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10784790341475961546928761 8088592756106971160196571)
        ·
          refine ⟨12132889134160456740294857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8088592756106971160196571 12132889134160456740294857)
          ·
            refine ⟨9099666850620342555221143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12132889134160456740294857 9099666850620342555221143)
            ·
              refine ⟨13649500275930513832831715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9099666850620342555221143 13649500275930513832831715)
              ·
                refine ⟨20474250413895770749247573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13649500275930513832831715 20474250413895770749247573)
                ·
                  refine ⟨239932622037841063467745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20474250413895770749247573 239932622037841063467745)
                  ·
                    rfl

theorem cell23_4205404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 8].length) (baseStart_4205404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205404 prefixEnd_4205404 := by exact prefixLift 4205404
  have htrace : WordTrace (prefixWord ++ tailWord_4205404) baseStart_4205404 baseEnd_4205404 := by
    simpa [prefixWord, tailWord_4205404, baseEnd_4205404] using wordTrace_append hprefix tailTrace_4205404
  have hstable : (prefixWord ++ tailWord_4205404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205404).length < 2 ^ (prefixWord ++ tailWord_4205404).sum := by decide
  have hdescent : baseEnd_4205404 < baseStart_4205404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205424 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 1, 5, 2]
def baseStart_4205424 : Nat := 118140960795 + 4205424 * 2 ^ 59
def prefixEnd_4205424 : Nat := 4983230072969 + 3 ^ 40 * 4205424 * 2
def baseEnd_4205424 : Nat := 2159403867953659492959613

theorem tailTrace_4205424 : CollatzResearch.WordTrace tailWord_4205424 prefixEnd_4205424 2159403867953659492959613 := by
  unfold tailWord_4205424
  simp only [CollatzResearch.WordTrace]
  refine ⟨76692207158237276041579663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102256276210983034722106217 76692207158237276041579663)
  ·
    refine ⟨115038310737355914062369495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76692207158237276041579663 115038310737355914062369495)
    ·
      refine ⟨172557466106033871093554243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115038310737355914062369495 172557466106033871093554243)
      ·
        refine ⟨258836199159050806640331365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172557466106033871093554243 258836199159050806640331365)
        ·
          refine ⟨48531787342322026245062131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 258836199159050806640331365 48531787342322026245062131)
          ·
            refine ⟨72797681013483039367593197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48531787342322026245062131 72797681013483039367593197)
            ·
              refine ⟨27299130380056139762847449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72797681013483039367593197 27299130380056139762847449)
              ·
                refine ⟨20474347785042104822135587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27299130380056139762847449 20474347785042104822135587)
                ·
                  refine ⟨30711521677563157233203381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20474347785042104822135587 30711521677563157233203381)
                  ·
                    refine ⟨2879205157271545990612817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30711521677563157233203381 2879205157271545990612817)
                    ·
                      refine ⟨2159403867953659492959613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2879205157271545990612817 2159403867953659492959613)
                      ·
                        rfl

theorem cell23_4205424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 1, 5, 2].length) (baseStart_4205424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205424 prefixEnd_4205424 := by exact prefixLift 4205424
  have htrace : WordTrace (prefixWord ++ tailWord_4205424) baseStart_4205424 baseEnd_4205424 := by
    simpa [prefixWord, tailWord_4205424, baseEnd_4205424] using wordTrace_append hprefix tailTrace_4205424
  have hstable : (prefixWord ++ tailWord_4205424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205424).length < 2 ^ (prefixWord ++ tailWord_4205424).sum := by decide
  have hdescent : baseEnd_4205424 < baseStart_4205424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205485 : List Nat := [1, 5, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_4205485 : Nat := 118140960795 + 4205485 * 2 ^ 59
def prefixEnd_4205485 : Nat := 4983230072969 + 3 ^ 40 * 4205485 * 2
def baseEnd_4205485 : Nat := 719811730091194584765611

theorem tailTrace_4205485 : CollatzResearch.WordTrace tailWord_4205485 prefixEnd_4205485 719811730091194584765611 := by
  unfold tailWord_4205485
  simp only [CollatzResearch.WordTrace]
  refine ⟨153386639169253559501129909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102257759446169039667419939 153386639169253559501129909)
  ·
    refine ⟨14379997422117521203230929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153386639169253559501129909 14379997422117521203230929)
    ·
      refine ⟨10784998066588140902423197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14379997422117521203230929 10784998066588140902423197)
      ·
        refine ⟨4044374274970552838408699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10784998066588140902423197 4044374274970552838408699)
        ·
          refine ⟨6066561412455829257613049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4044374274970552838408699 6066561412455829257613049)
          ·
            refine ⟨4549921059341871943209787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6066561412455829257613049 4549921059341871943209787)
            ·
              refine ⟨6824881589012807914814681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4549921059341871943209787 6824881589012807914814681)
              ·
                refine ⟨5118661191759605936111011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6824881589012807914814681 5118661191759605936111011)
                ·
                  refine ⟨7677991787639408904166517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5118661191759605936111011 7677991787639408904166517)
                  ·
                    refine ⟨719811730091194584765611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7677991787639408904166517 719811730091194584765611)
                    ·
                      rfl

theorem cell23_4205485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_4205485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205485 prefixEnd_4205485 := by exact prefixLift 4205485
  have htrace : WordTrace (prefixWord ++ tailWord_4205485) baseStart_4205485 baseEnd_4205485 := by
    simpa [prefixWord, tailWord_4205485, baseEnd_4205485] using wordTrace_append hprefix tailTrace_4205485
  have hstable : (prefixWord ++ tailWord_4205485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205485).length < 2 ^ (prefixWord ++ tailWord_4205485).sum := by decide
  have hdescent : baseEnd_4205485 < baseStart_4205485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205501 : List Nat := [1, 4, 1, 2, 4, 1, 1, 2, 1, 2, 4]
def baseStart_4205501 : Nat := 118140960795 + 4205501 * 2 ^ 59
def prefixEnd_4205501 : Nat := 4983230072969 + 3 ^ 40 * 4205501 * 2
def baseEnd_4205501 : Nat := 2159443405964055691696759

theorem tailTrace_4205501 : CollatzResearch.WordTrace tailWord_4205501 prefixEnd_4205501 2159443405964055691696759 := by
  unfold tailWord_4205501
  simp only [CollatzResearch.WordTrace]
  refine ⟨153387222737195594233712357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102258148491463729489141571 153387222737195594233712357)
  ·
    refine ⟨28760104263224173918821067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153387222737195594233712357 28760104263224173918821067)
    ·
      refine ⟨43140156394836260878231601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28760104263224173918821067 43140156394836260878231601)
      ·
        refine ⟨32355117296127195658673701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43140156394836260878231601 32355117296127195658673701)
        ·
          refine ⟨6066584493023849186001319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32355117296127195658673701 6066584493023849186001319)
          ·
            refine ⟨9099876739535773779001979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6066584493023849186001319 9099876739535773779001979)
            ·
              refine ⟨13649815109303660668502969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9099876739535773779001979 13649815109303660668502969)
              ·
                refine ⟨10237361331977745501377227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13649815109303660668502969 10237361331977745501377227)
                ·
                  refine ⟨15356041997966618252065841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10237361331977745501377227 15356041997966618252065841)
                  ·
                    refine ⟨11517031498474963689049381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15356041997966618252065841 11517031498474963689049381)
                    ·
                      refine ⟨2159443405964055691696759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11517031498474963689049381 2159443405964055691696759)
                      ·
                        rfl

theorem cell23_4205501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_4205501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205501 prefixEnd_4205501 := by exact prefixLift 4205501
  have htrace : WordTrace (prefixWord ++ tailWord_4205501) baseStart_4205501 baseEnd_4205501 := by
    simpa [prefixWord, tailWord_4205501, baseEnd_4205501] using wordTrace_append hprefix tailTrace_4205501
  have hstable : (prefixWord ++ tailWord_4205501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205501).length < 2 ^ (prefixWord ++ tailWord_4205501).sum := by decide
  have hdescent : baseEnd_4205501 < baseStart_4205501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205504 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 3]
def baseStart_4205504 : Nat := 118140960795 + 4205504 * 2 ^ 59
def prefixEnd_4205504 : Nat := 4983230072969 + 3 ^ 40 * 4205504 * 2
def baseEnd_4205504 : Nat := 2159444946406019179959245

theorem tailTrace_4205504 : CollatzResearch.WordTrace tailWord_4205504 prefixEnd_4205504 2159444946406019179959245 := by
  unfold tailWord_4205504
  simp only [CollatzResearch.WordTrace]
  refine ⟨76693666078092362873035783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102258221437456483830714377 76693666078092362873035783)
  ·
    refine ⟨115040499117138544309553675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76693666078092362873035783 115040499117138544309553675)
    ·
      refine ⟨172560748675707816464330513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115040499117138544309553675 172560748675707816464330513)
      ·
        refine ⟨129420561506780862348247885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172560748675707816464330513 129420561506780862348247885)
        ·
          refine ⟨48532710565042823380592957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129420561506780862348247885 48532710565042823380592957)
          ·
            refine ⟨18199766461891058767722359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48532710565042823380592957 18199766461891058767722359)
            ·
              refine ⟨27299649692836588151583539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18199766461891058767722359 27299649692836588151583539)
              ·
                refine ⟨40949474539254882227375309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27299649692836588151583539 40949474539254882227375309)
                ·
                  refine ⟨15356052952220580835265741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40949474539254882227375309 15356052952220580835265741)
                  ·
                    refine ⟨5758519857082717813224653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15356052952220580835265741 5758519857082717813224653)
                    ·
                      refine ⟨2159444946406019179959245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5758519857082717813224653 2159444946406019179959245)
                      ·
                        rfl

theorem cell23_4205504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_4205504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205504 prefixEnd_4205504 := by exact prefixLift 4205504
  have htrace : WordTrace (prefixWord ++ tailWord_4205504) baseStart_4205504 baseEnd_4205504 := by
    simpa [prefixWord, tailWord_4205504, baseEnd_4205504] using wordTrace_append hprefix tailTrace_4205504
  have hstable : (prefixWord ++ tailWord_4205504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205504).length < 2 ^ (prefixWord ++ tailWord_4205504).sum := by decide
  have hdescent : baseEnd_4205504 < baseStart_4205504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205522 : List Nat := [3, 2, 2, 3, 1, 2, 1, 4, 1, 2, 2]
def baseStart_4205522 : Nat := 118140960795 + 4205522 * 2 ^ 59
def prefixEnd_4205522 : Nat := 4983230072969 + 3 ^ 40 * 4205522 * 2
def baseEnd_4205522 : Nat := 2159454189057800109534163

theorem tailTrace_4205522 : CollatzResearch.WordTrace tailWord_4205522 prefixEnd_4205522 2159454189057800109534163 := by
  unfold tailWord_4205522
  simp only [CollatzResearch.WordTrace]
  refine ⟨38346997167529878705056705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102258659113413009880151213 38346997167529878705056705)
  ·
    refine ⟨28760247875647409028792529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38346997167529878705056705 28760247875647409028792529)
    ·
      refine ⟨21570185906735556771594397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28760247875647409028792529 21570185906735556771594397)
      ·
        refine ⟨8088819715025833789347899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21570185906735556771594397 8088819715025833789347899)
        ·
          refine ⟨12133229572538750684021849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8088819715025833789347899 12133229572538750684021849)
          ·
            refine ⟨9099922179404063013016387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12133229572538750684021849 9099922179404063013016387)
            ·
              refine ⟨13649883269106094519524581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9099922179404063013016387 13649883269106094519524581)
              ·
                refine ⟨2559353112957392722410859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13649883269106094519524581 2559353112957392722410859)
                ·
                  refine ⟨3839029669436089083616289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2559353112957392722410859 3839029669436089083616289)
                  ·
                    refine ⟨2879272252077066812712217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3839029669436089083616289 2879272252077066812712217)
                    ·
                      refine ⟨2159454189057800109534163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2879272252077066812712217 2159454189057800109534163)
                      ·
                        rfl

theorem cell23_4205522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_4205522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205522 prefixEnd_4205522 := by exact prefixLift 4205522
  have htrace : WordTrace (prefixWord ++ tailWord_4205522) baseStart_4205522 baseEnd_4205522 := by
    simpa [prefixWord, tailWord_4205522, baseEnd_4205522] using wordTrace_append hprefix tailTrace_4205522
  have hstable : (prefixWord ++ tailWord_4205522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205522).length < 2 ^ (prefixWord ++ tailWord_4205522).sum := by decide
  have hdescent : baseEnd_4205522 < baseStart_4205522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205524 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_4205524 : Nat := 118140960795 + 4205524 * 2 ^ 59
def prefixEnd_4205524 : Nat := 4983230072969 + 3 ^ 40 * 4205524 * 2
def baseEnd_4205524 : Nat := 719818405339703033903051

theorem tailTrace_4205524 : CollatzResearch.WordTrace tailWord_4205524 prefixEnd_4205524 719818405339703033903051 := by
  unfold tailWord_4205524
  simp only [CollatzResearch.WordTrace]
  refine ⟨76694030808056134580899813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102258707744074846107866417 76694030808056134580899813)
  ·
    refine ⟨14380130776510525233918715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76694030808056134580899813 14380130776510525233918715)
    ·
      refine ⟨21570196164765787850878073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14380130776510525233918715 21570196164765787850878073)
      ·
        refine ⟨16177647123574340888158555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21570196164765787850878073 16177647123574340888158555)
        ·
          refine ⟨24266470685361511332237833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16177647123574340888158555 24266470685361511332237833)
          ·
            refine ⟨18199853014021133499178375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24266470685361511332237833 18199853014021133499178375)
            ·
              refine ⟨27299779521031700248767563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18199853014021133499178375 27299779521031700248767563)
              ·
                refine ⟨40949669281547550373151345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27299779521031700248767563 40949669281547550373151345)
                ·
                  refine ⟨30712251961160662779863509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40949669281547550373151345 30712251961160662779863509)
                  ·
                    refine ⟨719818405339703033903051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30712251961160662779863509 719818405339703033903051)
                    ·
                      rfl

theorem cell23_4205524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_4205524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205524 prefixEnd_4205524 := by exact prefixLift 4205524
  have htrace : WordTrace (prefixWord ++ tailWord_4205524) baseStart_4205524 baseEnd_4205524 := by
    simpa [prefixWord, tailWord_4205524, baseEnd_4205524] using wordTrace_append hprefix tailTrace_4205524
  have hstable : (prefixWord ++ tailWord_4205524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205524).length < 2 ^ (prefixWord ++ tailWord_4205524).sum := by decide
  have hdescent : baseEnd_4205524 < baseStart_4205524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205538 : List Nat := [3, 3, 3, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_4205538 : Nat := 118140960795 + 4205538 * 2 ^ 59
def prefixEnd_4205538 : Nat := 4983230072969 + 3 ^ 40 * 4205538 * 2
def baseEnd_4205538 : Nat := 2159462404748272046934089

theorem tailTrace_4205538 : CollatzResearch.WordTrace tailWord_4205538 prefixEnd_4205538 2159462404748272046934089 := by
  unfold tailWord_4205538
  simp only [CollatzResearch.WordTrace]
  refine ⟨38347143059515387388202317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102259048158707699701872845 38347143059515387388202317)
  ·
    refine ⟨14380178647318270270575869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38347143059515387388202317 14380178647318270270575869)
    ·
      refine ⟨5392566992744351351465951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14380178647318270270575869 5392566992744351351465951)
      ·
        refine ⟨8088850489116527027198927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5392566992744351351465951 8088850489116527027198927)
        ·
          refine ⟨12133275733674790540798391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8088850489116527027198927 12133275733674790540798391)
          ·
            refine ⟨18199913600512185811197587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12133275733674790540798391 18199913600512185811197587)
            ·
              refine ⟨27299870400768278716796381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18199913600512185811197587 27299870400768278716796381)
              ·
                refine ⟨10237451400288104518798643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27299870400768278716796381 10237451400288104518798643)
                ·
                  refine ⟨15356177100432156778197965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10237451400288104518798643 15356177100432156778197965)
                  ·
                    refine ⟨5758566412662058791824237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15356177100432156778197965 5758566412662058791824237)
                    ·
                      refine ⟨2159462404748272046934089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5758566412662058791824237 2159462404748272046934089)
                      ·
                        rfl

theorem cell23_4205538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_4205538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205538 prefixEnd_4205538 := by exact prefixLift 4205538
  have htrace : WordTrace (prefixWord ++ tailWord_4205538) baseStart_4205538 baseEnd_4205538 := by
    simpa [prefixWord, tailWord_4205538, baseEnd_4205538] using wordTrace_append hprefix tailTrace_4205538
  have hstable : (prefixWord ++ tailWord_4205538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205538).length < 2 ^ (prefixWord ++ tailWord_4205538).sum := by decide
  have hdescent : baseEnd_4205538 < baseStart_4205538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205556 : List Nat := [2, 6, 2, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_4205556 : Nat := 118140960795 + 4205556 * 2 ^ 59
def prefixEnd_4205556 : Nat := 4983230072969 + 3 ^ 40 * 4205556 * 2
def baseEnd_4205556 : Nat := 2159471647400052976509007

theorem tailTrace_4205556 : CollatzResearch.WordTrace tailWord_4205556 prefixEnd_4205556 2159471647400052976509007 := by
  unfold tailWord_4205556
  simp only [CollatzResearch.WordTrace]
  refine ⟨76694614375998169313482261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102259485834664225751309681 76694614375998169313482261)
  ·
    refine ⟨3595060048874914186569481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76694614375998169313482261 3595060048874914186569481)
    ·
      refine ⟨2696295036656185639927111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3595060048874914186569481 2696295036656185639927111)
      ·
        refine ⟨4044442554984278459890667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2696295036656185639927111 4044442554984278459890667)
        ·
          refine ⟨6066663832476417689836001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4044442554984278459890667 6066663832476417689836001)
          ·
            refine ⟨4549997874357313267377001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6066663832476417689836001 4549997874357313267377001)
            ·
              refine ⟨3412498405767984950532751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4549997874357313267377001 3412498405767984950532751)
              ·
                refine ⟨5118747608651977425799127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3412498405767984950532751 5118747608651977425799127)
                ·
                  refine ⟨7678121412977966138698691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5118747608651977425799127 7678121412977966138698691)
                  ·
                    refine ⟨11517182119466949208048037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7678121412977966138698691 11517182119466949208048037)
                    ·
                      refine ⟨2159471647400052976509007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11517182119466949208048037 2159471647400052976509007)
                      ·
                        rfl

theorem cell23_4205556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_4205556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205556 prefixEnd_4205556 := by exact prefixLift 4205556
  have htrace : WordTrace (prefixWord ++ tailWord_4205556) baseStart_4205556 baseEnd_4205556 := by
    simpa [prefixWord, tailWord_4205556, baseEnd_4205556] using wordTrace_append hprefix tailTrace_4205556
  have hstable : (prefixWord ++ tailWord_4205556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205556).length < 2 ^ (prefixWord ++ tailWord_4205556).sum := by decide
  have hdescent : baseEnd_4205556 < baseStart_4205556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205561 : List Nat := [1, 2, 1, 3, 1, 3, 1, 4, 1, 4, 2]
def baseStart_4205561 : Nat := 118140960795 + 4205561 * 2 ^ 59
def prefixEnd_4205561 : Nat := 4983230072969 + 3 ^ 40 * 4205561 * 2
def baseEnd_4205561 : Nat := 2159474214803325456946483

theorem tailTrace_4205561 : CollatzResearch.WordTrace tailWord_4205561 prefixEnd_4205561 2159474214803325456946483 := by
  unfold tailWord_4205561
  simp only [CollatzResearch.WordTrace]
  refine ⟨153389411116978224480896537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102259607411318816320597691 153389411116978224480896537)
  ·
    refine ⟨115042058337733668360672403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153389411116978224480896537 115042058337733668360672403)
    ·
      refine ⟨172563087506600502541008605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115042058337733668360672403 172563087506600502541008605)
      ·
        refine ⟨64711157814975188452878227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172563087506600502541008605 64711157814975188452878227)
        ·
          refine ⟨97066736722462782679317341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64711157814975188452878227 97066736722462782679317341)
          ·
            refine ⟨36400026270923543504744003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97066736722462782679317341 36400026270923543504744003)
            ·
              refine ⟨54600039406385315257116005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36400026270923543504744003 54600039406385315257116005)
              ·
                refine ⟨10237507388697246610709251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54600039406385315257116005 10237507388697246610709251)
                ·
                  refine ⟨15356261083045869916063877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10237507388697246610709251 15356261083045869916063877)
                  ·
                    refine ⟨2879298953071100609261977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15356261083045869916063877 2879298953071100609261977)
                    ·
                      refine ⟨2159474214803325456946483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2879298953071100609261977 2159474214803325456946483)
                      ·
                        rfl

theorem cell23_4205561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_4205561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205561 prefixEnd_4205561 := by exact prefixLift 4205561
  have htrace : WordTrace (prefixWord ++ tailWord_4205561) baseStart_4205561 baseEnd_4205561 := by
    simpa [prefixWord, tailWord_4205561, baseEnd_4205561] using wordTrace_append hprefix tailTrace_4205561
  have hstable : (prefixWord ++ tailWord_4205561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205561).length < 2 ^ (prefixWord ++ tailWord_4205561).sum := by decide
  have hdescent : baseEnd_4205561 < baseStart_4205561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205591 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 4]
def baseStart_4205591 : Nat := 118140960795 + 4205591 * 2 ^ 59
def prefixEnd_4205591 : Nat := 4983230072969 + 3 ^ 40 * 4205591 * 2
def baseEnd_4205591 : Nat := 2159489619222960339571345

theorem tailTrace_4205591 : CollatzResearch.WordTrace tailWord_4205591 prefixEnd_4205591 2159489619222960339571345 := by
  unfold tailWord_4205591
  simp only [CollatzResearch.WordTrace]
  refine ⟨153390505306869539604488627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102260336871246359736325751 153390505306869539604488627)
  ·
    refine ⟨230085757960304309406732941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153390505306869539604488627 230085757960304309406732941)
    ·
      refine ⟨86282159235114116027524853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230085757960304309406732941 86282159235114116027524853)
      ·
        refine ⟨8088952428291948377580455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86282159235114116027524853 8088952428291948377580455)
        ·
          refine ⟨12133428642437922566370683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8088952428291948377580455 12133428642437922566370683)
          ·
            refine ⟨18200142963656883849556025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12133428642437922566370683 18200142963656883849556025)
            ·
              refine ⟨13650107222742662887167019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18200142963656883849556025 13650107222742662887167019)
              ·
                refine ⟨20475160834113994330750529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13650107222742662887167019 20475160834113994330750529)
                ·
                  refine ⟨15356370625585495748062897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20475160834113994330750529 15356370625585495748062897)
                  ·
                    refine ⟨11517277969189121811047173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15356370625585495748062897 11517277969189121811047173)
                    ·
                      refine ⟨2159489619222960339571345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11517277969189121811047173 2159489619222960339571345)
                      ·
                        rfl

theorem cell23_4205591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_4205591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205591 prefixEnd_4205591 := by exact prefixLift 4205591
  have htrace : WordTrace (prefixWord ++ tailWord_4205591) baseStart_4205591 baseEnd_4205591 := by
    simpa [prefixWord, tailWord_4205591, baseEnd_4205591] using wordTrace_append hprefix tailTrace_4205591
  have hstable : (prefixWord ++ tailWord_4205591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205591).length < 2 ^ (prefixWord ++ tailWord_4205591).sum := by decide
  have hdescent : baseEnd_4205591 < baseStart_4205591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205621 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 1, 7, 2]
def baseStart_4205621 : Nat := 118140960795 + 4205621 * 2 ^ 59
def prefixEnd_4205621 : Nat := 4983230072969 + 3 ^ 40 * 4205621 * 2
def baseEnd_4205621 : Nat := 2159505023642595222196207

theorem tailTrace_4205621 : CollatzResearch.WordTrace tailWord_4205621 prefixEnd_4205621 2159505023642595222196207 := by
  unfold tailWord_4205621
  simp only [CollatzResearch.WordTrace]
  refine ⟨153391599496760854728080717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102261066331173903152053811 153391599496760854728080717)
  ·
    refine ⟨57521849811285320523030269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153391599496760854728080717 57521849811285320523030269)
    ·
      refine ⟨21570693679231995196136351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57521849811285320523030269 21570693679231995196136351)
      ·
        refine ⟨32356040518847992794204527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21570693679231995196136351 32356040518847992794204527)
        ·
          refine ⟨48534060778271989191306791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32356040518847992794204527 48534060778271989191306791)
          ·
            refine ⟨72801091167407983786960187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48534060778271989191306791 72801091167407983786960187)
            ·
              refine ⟨109201636751111975680440281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72801091167407983786960187 109201636751111975680440281)
              ·
                refine ⟨81901227563333981760330211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109201636751111975680440281 81901227563333981760330211)
                ·
                  refine ⟨122851841345000972640495317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81901227563333981760330211 122851841345000972640495317)
                  ·
                    refine ⟨2879340031523460296261609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 122851841345000972640495317 2879340031523460296261609)
                    ·
                      refine ⟨2159505023642595222196207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2879340031523460296261609 2159505023642595222196207)
                      ·
                        rfl

theorem cell23_4205621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_4205621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205621 prefixEnd_4205621 := by exact prefixLift 4205621
  have htrace : WordTrace (prefixWord ++ tailWord_4205621) baseStart_4205621 baseEnd_4205621 := by
    simpa [prefixWord, tailWord_4205621, baseEnd_4205621] using wordTrace_append hprefix tailTrace_4205621
  have hstable : (prefixWord ++ tailWord_4205621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205621).length < 2 ^ (prefixWord ++ tailWord_4205621).sum := by decide
  have hdescent : baseEnd_4205621 < baseStart_4205621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205711 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 2, 9, 2]
def baseStart_4205711 : Nat := 118140960795 + 4205711 * 2 ^ 59
def prefixEnd_4205711 : Nat := 4983230072969 + 3 ^ 40 * 4205711 * 2
def baseEnd_4205711 : Nat := 2159551236901499870070793

theorem tailTrace_4205711 : CollatzResearch.WordTrace tailWord_4205711 prefixEnd_4205711 2159551236901499870070793 := by
  unfold tailWord_4205711
  simp only [CollatzResearch.WordTrace]
  refine ⟨153394882066434800098856987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102263254710956533399237991 153394882066434800098856987)
  ·
    refine ⟨230092323099652200148285481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153394882066434800098856987 230092323099652200148285481)
    ·
      refine ⟨172569242324739150111214111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230092323099652200148285481 172569242324739150111214111)
      ·
        refine ⟨258853863487108725166821167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172569242324739150111214111 258853863487108725166821167)
        ·
          refine ⟨388280795230663087750231751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258853863487108725166821167 388280795230663087750231751)
          ·
            refine ⟨582421192845994631625347627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388280795230663087750231751 582421192845994631625347627)
            ·
              refine ⟨873631789268991947438021441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 582421192845994631625347627 873631789268991947438021441)
              ·
                refine ⟨655223841951743960578516081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 873631789268991947438021441 655223841951743960578516081)
                ·
                  refine ⟨491417881463807970433887061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 655223841951743960578516081 491417881463807970433887061)
                  ·
                    refine ⟨2879401649201999826761057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 491417881463807970433887061 2879401649201999826761057)
                    ·
                      refine ⟨2159551236901499870070793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2879401649201999826761057 2159551236901499870070793)
                      ·
                        rfl

theorem cell23_4205711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 9, 2].length) (baseStart_4205711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205711 prefixEnd_4205711 := by exact prefixLift 4205711
  have htrace : WordTrace (prefixWord ++ tailWord_4205711) baseStart_4205711 baseEnd_4205711 := by
    simpa [prefixWord, tailWord_4205711, baseEnd_4205711] using wordTrace_append hprefix tailTrace_4205711
  have hstable : (prefixWord ++ tailWord_4205711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205711).length < 2 ^ (prefixWord ++ tailWord_4205711).sum := by decide
  have hdescent : baseEnd_4205711 < baseStart_4205711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205728 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 1, 5, 2]
def baseStart_4205728 : Nat := 118140960795 + 4205728 * 2 ^ 59
def prefixEnd_4205728 : Nat := 4983230072969 + 3 ^ 40 * 4205728 * 2
def baseEnd_4205728 : Nat := 2159559966072626303558215

theorem tailTrace_4205728 : CollatzResearch.WordTrace tailWord_4205728 prefixEnd_4205728 2159559966072626303558215 := by
  unfold tailWord_4205728
  simp only [CollatzResearch.WordTrace]
  refine ⟨76697751053686606001112919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102263668071582141334817225 76697751053686606001112919)
  ·
    refine ⟨115046626580529909001669379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76697751053686606001112919 115046626580529909001669379)
    ·
      refine ⟨172569939870794863502504069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115046626580529909001669379 172569939870794863502504069)
      ·
        refine ⟨32356863725774036906719513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172569939870794863502504069 32356863725774036906719513)
        ·
          refine ⟨24267647794330527680039635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32356863725774036906719513 24267647794330527680039635)
          ·
            refine ⟨36401471691495791520059453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24267647794330527680039635 36401471691495791520059453)
            ·
              refine ⟨13650551884310921820022295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36401471691495791520059453 13650551884310921820022295)
              ·
                refine ⟨20475827826466382730033443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13650551884310921820022295 20475827826466382730033443)
                ·
                  refine ⟨30713741739699574095050165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20475827826466382730033443 30713741739699574095050165)
                  ·
                    refine ⟨2879413288096835071410953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30713741739699574095050165 2879413288096835071410953)
                    ·
                      refine ⟨2159559966072626303558215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2879413288096835071410953 2159559966072626303558215)
                      ·
                        rfl

theorem cell23_4205728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_4205728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205728 prefixEnd_4205728 := by exact prefixLift 4205728
  have htrace : WordTrace (prefixWord ++ tailWord_4205728) baseStart_4205728 baseEnd_4205728 := by
    simpa [prefixWord, tailWord_4205728, baseEnd_4205728] using wordTrace_append hprefix tailTrace_4205728
  have hstable : (prefixWord ++ tailWord_4205728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205728).length < 2 ^ (prefixWord ++ tailWord_4205728).sum := by decide
  have hdescent : baseEnd_4205728 < baseStart_4205728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205768 : List Nat := [2, 1, 3, 1, 2, 1, 2, 5, 2, 4]
def baseStart_4205768 : Nat := 118140960795 + 4205768 * 2 ^ 59
def prefixEnd_4205768 : Nat := 4983230072969 + 3 ^ 40 * 4205768 * 2
def baseEnd_4205768 : Nat := 719860168432935382352677

theorem tailTrace_4205768 : CollatzResearch.WordTrace tailWord_4205768 prefixEnd_4205768 719860168432935382352677 := by
  unfold tailWord_4205768
  simp only [CollatzResearch.WordTrace]
  refine ⟨76698480513614149416840979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102264640684818865889121305 76698480513614149416840979)
  ·
    refine ⟨115047720770421224125261469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76698480513614149416840979 115047720770421224125261469)
    ·
      refine ⟨43142895288907959046973051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115047720770421224125261469 43142895288907959046973051)
      ·
        refine ⟨64714342933361938570459577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43142895288907959046973051 64714342933361938570459577)
        ·
          refine ⟨48535757200021453927844683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64714342933361938570459577 48535757200021453927844683)
          ·
            refine ⟨72803635800032180891767025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48535757200021453927844683 72803635800032180891767025)
            ·
              refine ⟨54602726850024135668825269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72803635800032180891767025 54602726850024135668825269)
              ·
                refine ⟨5119005642189762718952369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54602726850024135668825269 5119005642189762718952369)
                ·
                  refine ⟨3839254231642322039214277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5119005642189762718952369 3839254231642322039214277)
                  ·
                    refine ⟨719860168432935382352677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3839254231642322039214277 719860168432935382352677)
                    ·
                      rfl

theorem cell23_4205768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_4205768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205768 prefixEnd_4205768 := by exact prefixLift 4205768
  have htrace : WordTrace (prefixWord ++ tailWord_4205768) baseStart_4205768 baseEnd_4205768 := by
    simpa [prefixWord, tailWord_4205768, baseEnd_4205768] using wordTrace_append hprefix tailTrace_4205768
  have hstable : (prefixWord ++ tailWord_4205768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205768).length < 2 ^ (prefixWord ++ tailWord_4205768).sum := by decide
  have hdescent : baseEnd_4205768 < baseStart_4205768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205771 : List Nat := [1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 4]
def baseStart_4205771 : Nat := 118140960795 + 4205771 * 2 ^ 59
def prefixEnd_4205771 : Nat := 4983230072969 + 3 ^ 40 * 4205771 * 2
def baseEnd_4205771 : Nat := 2159582045740769635320517

theorem tailTrace_4205771 : CollatzResearch.WordTrace tailWord_4205771 prefixEnd_4205771 2159582045740769635320517 := by
  unfold tailWord_4205771
  simp only [CollatzResearch.WordTrace]
  refine ⟨153397070446217430346041167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102264713630811620230694111 153397070446217430346041167)
  ·
    refine ⟨230095605669326145519061751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153397070446217430346041167 230095605669326145519061751)
    ·
      refine ⟨345143408503989218278592627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230095605669326145519061751 345143408503989218278592627)
      ·
        refine ⟨517715112755983827417888941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345143408503989218278592627 517715112755983827417888941)
        ·
          refine ⟨194143167283493935281708353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 517715112755983827417888941 194143167283493935281708353)
          ·
            refine ⟨145607375462620451461281265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194143167283493935281708353 145607375462620451461281265)
            ·
              refine ⟨109205531596965338595960949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145607375462620451461281265 109205531596965338595960949)
              ·
                refine ⟨10238018587215500493371339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109205531596965338595960949 10238018587215500493371339)
                ·
                  refine ⟨15357027880823250740057009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10238018587215500493371339 15357027880823250740057009)
                  ·
                    refine ⟨11517770910617438055042757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15357027880823250740057009 11517770910617438055042757)
                    ·
                      refine ⟨2159582045740769635320517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11517770910617438055042757 2159582045740769635320517)
                      ·
                        rfl

theorem cell23_4205771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 4].length) (baseStart_4205771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205771 prefixEnd_4205771 := by exact prefixLift 4205771
  have htrace : WordTrace (prefixWord ++ tailWord_4205771) baseStart_4205771 baseEnd_4205771 := by
    simpa [prefixWord, tailWord_4205771, baseEnd_4205771] using wordTrace_append hprefix tailTrace_4205771
  have hstable : (prefixWord ++ tailWord_4205771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205771).length < 2 ^ (prefixWord ++ tailWord_4205771).sum := by decide
  have hdescent : baseEnd_4205771 < baseStart_4205771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205835 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 3, 3, 2]
def baseStart_4205835 : Nat := 118140960795 + 4205835 * 2 ^ 59
def prefixEnd_4205835 : Nat := 4983230072969 + 3 ^ 40 * 4205835 * 2
def baseEnd_4205835 : Nat := 2159614908502657384920223

theorem tailTrace_4205835 : CollatzResearch.WordTrace tailWord_4205835 prefixEnd_4205835 2159614908502657384920223 := by
  unfold tailWord_4205835
  simp only [CollatzResearch.WordTrace]
  refine ⟨153399404717985569276370959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102266269811990379517580639 153399404717985569276370959)
  ·
    refine ⟨230099107076978353914556439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153399404717985569276370959 230099107076978353914556439)
    ·
      refine ⟨345148660615467530871834659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230099107076978353914556439 345148660615467530871834659)
      ·
        refine ⟨517722990923201296307751989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345148660615467530871834659 517722990923201296307751989)
        ·
          refine ⟨48536530399050121528851749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 517722990923201296307751989 48536530399050121528851749)
          ·
            refine ⟨9100599449821897786659703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48536530399050121528851749 9100599449821897786659703)
            ·
              refine ⟨13650899174732846679989555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9100599449821897786659703 13650899174732846679989555)
              ·
                refine ⟨20476348762099270019984333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13650899174732846679989555 20476348762099270019984333)
                ·
                  refine ⟨7678630785787226257494125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20476348762099270019984333 7678630785787226257494125)
                  ·
                    refine ⟨2879486544670209846560297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7678630785787226257494125 2879486544670209846560297)
                    ·
                      refine ⟨2159614908502657384920223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2879486544670209846560297 2159614908502657384920223)
                      ·
                        rfl

theorem cell23_4205835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 3, 2].length) (baseStart_4205835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205835 prefixEnd_4205835 := by exact prefixLift 4205835
  have htrace : WordTrace (prefixWord ++ tailWord_4205835) baseStart_4205835 baseEnd_4205835 := by
    simpa [prefixWord, tailWord_4205835, baseEnd_4205835] using wordTrace_append hprefix tailTrace_4205835
  have hstable : (prefixWord ++ tailWord_4205835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205835).length < 2 ^ (prefixWord ++ tailWord_4205835).sum := by decide
  have hdescent : baseEnd_4205835 < baseStart_4205835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205871 : List Nat := [1, 1, 2, 1, 2, 1, 3, 5, 7]
def baseStart_4205871 : Nat := 118140960795 + 4205871 * 2 ^ 59
def prefixEnd_4205871 : Nat := 4983230072969 + 3 ^ 40 * 4205871 * 2
def baseEnd_4205871 : Nat := 239959265978468804896673

theorem tailTrace_4205871 : CollatzResearch.WordTrace tailWord_4205871 prefixEnd_4205871 239959265978468804896673 := by
  unfold tailWord_4205871
  simp only [CollatzResearch.WordTrace]
  refine ⟨153400717745855147424681467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102267145163903431616454311 153400717745855147424681467)
  ·
    refine ⟨230101076618782721137022201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153400717745855147424681467 230101076618782721137022201)
    ·
      refine ⟨172575807464087040852766651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230101076618782721137022201 172575807464087040852766651)
      ·
        refine ⟨258863711196130561279149977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172575807464087040852766651 258863711196130561279149977)
        ·
          refine ⟨194147783397097920959362483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258863711196130561279149977 194147783397097920959362483)
          ·
            refine ⟨291221675095646881439043725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194147783397097920959362483 291221675095646881439043725)
            ·
              refine ⟨109208128160867580539641397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 291221675095646881439043725 109208128160867580539641397)
              ·
                refine ⟨10238262015081335675591381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109208128160867580539641397 10238262015081335675591381)
                ·
                  refine ⟨239959265978468804896673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10238262015081335675591381 239959265978468804896673)
                  ·
                    rfl

theorem cell23_4205871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 7].length) (baseStart_4205871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205871 prefixEnd_4205871 := by exact prefixLift 4205871
  have htrace : WordTrace (prefixWord ++ tailWord_4205871) baseStart_4205871 baseEnd_4205871 := by
    simpa [prefixWord, tailWord_4205871, baseEnd_4205871] using wordTrace_append hprefix tailTrace_4205871
  have hstable : (prefixWord ++ tailWord_4205871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205871).length < 2 ^ (prefixWord ++ tailWord_4205871).sum := by decide
  have hdescent : baseEnd_4205871 < baseStart_4205871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205882 : List Nat := [3, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2]
def baseStart_4205882 : Nat := 118140960795 + 4205882 * 2 ^ 59
def prefixEnd_4205882 : Nat := 4983230072969 + 3 ^ 40 * 4205882 * 2
def baseEnd_4205882 : Nat := 2159639042093418701032507

theorem tailTrace_4205882 : CollatzResearch.WordTrace tailWord_4205882 prefixEnd_4205882 2159639042093418701032507 := by
  unfold tailWord_4205882
  simp only [CollatzResearch.WordTrace]
  refine ⟨38350279737203824075832975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102267412632543530868887933 38350279737203824075832975)
  ·
    refine ⟨57525419605805736113749463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38350279737203824075832975 57525419605805736113749463)
    ·
      refine ⟨86288129408708604170624195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57525419605805736113749463 86288129408708604170624195)
      ·
        refine ⟨129432194113062906255936293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86288129408708604170624195 129432194113062906255936293)
        ·
          refine ⟨24268536396199294922988055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129432194113062906255936293 24268536396199294922988055)
          ·
            refine ⟨36402804594298942384482083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24268536396199294922988055 36402804594298942384482083)
            ·
              refine ⟨54604206891448413576723125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36402804594298942384482083 54604206891448413576723125)
              ·
                refine ⟨5119144396073288772817793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54604206891448413576723125 5119144396073288772817793)
                ·
                  refine ⟨3839358297054966579613345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5119144396073288772817793 3839358297054966579613345)
                  ·
                    refine ⟨2879518722791224934710009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3839358297054966579613345 2879518722791224934710009)
                    ·
                      refine ⟨2159639042093418701032507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2879518722791224934710009 2159639042093418701032507)
                      ·
                        rfl

theorem cell23_4205882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2].length) (baseStart_4205882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205882 prefixEnd_4205882 := by exact prefixLift 4205882
  have htrace : WordTrace (prefixWord ++ tailWord_4205882) baseStart_4205882 baseEnd_4205882 := by
    simpa [prefixWord, tailWord_4205882, baseEnd_4205882] using wordTrace_append hprefix tailTrace_4205882
  have hstable : (prefixWord ++ tailWord_4205882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205882).length < 2 ^ (prefixWord ++ tailWord_4205882).sum := by decide
  have hdescent : baseEnd_4205882 < baseStart_4205882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205905 : List Nat := [1, 2, 2, 1, 4, 1, 4, 3, 5]
def baseStart_4205905 : Nat := 118140960795 + 4205905 * 2 ^ 59
def prefixEnd_4205905 : Nat := 4983230072969 + 3 ^ 40 * 4205905 * 2
def baseEnd_4205905 : Nat := 239961205794274679004989

theorem tailTrace_4205905 : CollatzResearch.WordTrace tailWord_4205905 prefixEnd_4205905 239961205794274679004989 := by
  unfold tailWord_4205905
  simp only [CollatzResearch.WordTrace]
  refine ⟨153401957827731971231419169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102267971885154647487612779 153401957827731971231419169)
  ·
    refine ⟨115051468370798978423564377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153401957827731971231419169 115051468370798978423564377)
    ·
      refine ⟨86288601278099233817673283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115051468370798978423564377 86288601278099233817673283)
      ·
        refine ⟨129432901917148850726509925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86288601278099233817673283 129432901917148850726509925)
        ·
          refine ⟨24268669109465409511220611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129432901917148850726509925 24268669109465409511220611)
          ·
            refine ⟨36403003664198114266830917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24268669109465409511220611 36403003664198114266830917)
            ·
              refine ⟨6825563187037146425030797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36403003664198114266830917 6825563187037146425030797)
              ·
                refine ⟨2559586195138929909386549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6825563187037146425030797 2559586195138929909386549)
                ·
                  refine ⟨239961205794274679004989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2559586195138929909386549 239961205794274679004989)
                  ·
                    rfl

theorem cell23_4205905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 5].length) (baseStart_4205905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205905 prefixEnd_4205905 := by exact prefixLift 4205905
  have htrace : WordTrace (prefixWord ++ tailWord_4205905) baseStart_4205905 baseEnd_4205905 := by
    simpa [prefixWord, tailWord_4205905, baseEnd_4205905] using wordTrace_append hprefix tailTrace_4205905
  have hstable : (prefixWord ++ tailWord_4205905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205905).length < 2 ^ (prefixWord ++ tailWord_4205905).sum := by decide
  have hdescent : baseEnd_4205905 < baseStart_4205905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205910 : List Nat := [5, 2, 3, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_4205910 : Nat := 118140960795 + 4205910 * 2 ^ 59
def prefixEnd_4205910 : Nat := 4983230072969 + 3 ^ 40 * 4205910 * 2
def baseEnd_4205910 : Nat := 2159653419551744591482379

theorem tailTrace_4205910 : CollatzResearch.WordTrace tailWord_4205910 prefixEnd_4205910 2159653419551744591482379 := by
  unfold tailWord_4205910
  simp only [CollatzResearch.WordTrace]
  refine ⟨9587633762044616067834449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102268093461809238056900789 9587633762044616067834449)
  ·
    refine ⟨7190725321533462050875837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9587633762044616067834449 7190725321533462050875837)
    ·
      refine ⟨2696521995575048269078439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7190725321533462050875837 2696521995575048269078439)
      ·
        refine ⟨4044782993362572403617659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2696521995575048269078439 4044782993362572403617659)
        ·
          refine ⟨6067174490043858605426489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4044782993362572403617659 6067174490043858605426489)
          ·
            refine ⟨4550380867532893954069867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6067174490043858605426489 4550380867532893954069867)
            ·
              refine ⟨6825571301299340931104801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4550380867532893954069867 6825571301299340931104801)
              ·
                refine ⟨5119178475974505698328601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6825571301299340931104801 5119178475974505698328601)
                ·
                  refine ⟨3839383856980879273746451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5119178475974505698328601 3839383856980879273746451)
                  ·
                    refine ⟨5759075785471318910619677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3839383856980879273746451 5759075785471318910619677)
                    ·
                      refine ⟨2159653419551744591482379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5759075785471318910619677 2159653419551744591482379)
                      ·
                        rfl

theorem cell23_4205910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_4205910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205910 prefixEnd_4205910 := by exact prefixLift 4205910
  have htrace : WordTrace (prefixWord ++ tailWord_4205910) baseStart_4205910 baseEnd_4205910 := by
    simpa [prefixWord, tailWord_4205910, baseEnd_4205910] using wordTrace_append hprefix tailTrace_4205910
  have hstable : (prefixWord ++ tailWord_4205910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205910).length < 2 ^ (prefixWord ++ tailWord_4205910).sum := by decide
  have hdescent : baseEnd_4205910 < baseStart_4205910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205931 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 4, 8]
def baseStart_4205931 : Nat := 118140960795 + 4205931 * 2 ^ 59
def prefixEnd_4205931 : Nat := 4983230072969 + 3 ^ 40 * 4205931 * 2
def baseEnd_4205931 : Nat := 719888067548496336439927

theorem tailTrace_4205931 : CollatzResearch.WordTrace tailWord_4205931 prefixEnd_4205931 719888067548496336439927 := by
  unfold tailWord_4205931
  simp only [CollatzResearch.WordTrace]
  refine ⟨153402906125637777671865647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102268604083758518447910431 153402906125637777671865647)
  ·
    refine ⟨230104359188456666507798471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153402906125637777671865647 230104359188456666507798471)
    ·
      refine ⟨345156538782684999761697707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230104359188456666507798471 345156538782684999761697707)
      ·
        refine ⟨517734808174027499642546561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345156538782684999761697707 517734808174027499642546561)
        ·
          refine ⟨388301106130520624731909921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 517734808174027499642546561 388301106130520624731909921)
          ·
            refine ⟨291225829597890468548932441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 388301106130520624731909921 291225829597890468548932441)
            ·
              refine ⟨218419372198417851411699331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291225829597890468548932441 218419372198417851411699331)
              ·
                refine ⟨327629058297626777117548997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218419372198417851411699331 327629058297626777117548997)
                ·
                  refine ⟨61430448430805020709540437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 327629058297626777117548997 61430448430805020709540437)
                  ·
                    refine ⟨719888067548496336439927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61430448430805020709540437 719888067548496336439927)
                    ·
                      rfl

theorem cell23_4205931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 8].length) (baseStart_4205931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205931 prefixEnd_4205931 := by exact prefixLift 4205931
  have htrace : WordTrace (prefixWord ++ tailWord_4205931) baseStart_4205931 baseEnd_4205931 := by
    simpa [prefixWord, tailWord_4205931, baseEnd_4205931] using wordTrace_append hprefix tailTrace_4205931
  have hstable : (prefixWord ++ tailWord_4205931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205931).length < 2 ^ (prefixWord ++ tailWord_4205931).sum := by decide
  have hdescent : baseEnd_4205931 < baseStart_4205931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205938 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_4205938 : Nat := 118140960795 + 4205938 * 2 ^ 59
def prefixEnd_4205938 : Nat := 4983230072969 + 3 ^ 40 * 4205938 * 2
def baseEnd_4205938 : Nat := 2159667797010070481932249

theorem tailTrace_4205938 : CollatzResearch.WordTrace tailWord_4205938 prefixEnd_4205938 2159667797010070481932249 := by
  unfold tailWord_4205938
  simp only [CollatzResearch.WordTrace]
  refine ⟨38350790359153104466842617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102268774291074945244913645 38350790359153104466842617)
  ·
    refine ⟨28763092769364828350131963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38350790359153104466842617 28763092769364828350131963)
    ·
      refine ⟨43144639154047242525197945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28763092769364828350131963 43144639154047242525197945)
      ·
        refine ⟨32358479365535431893898459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43144639154047242525197945 32358479365535431893898459)
        ·
          refine ⟨48537719048303147840847689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32358479365535431893898459 48537719048303147840847689)
          ·
            refine ⟨36403289286227360880635767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48537719048303147840847689 36403289286227360880635767)
            ·
              refine ⟨54604933929341041320953651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36403289286227360880635767 54604933929341041320953651)
              ·
                refine ⟨81907400894011561981430477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54604933929341041320953651 81907400894011561981430477)
                ·
                  refine ⟨30715275335254335743036429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81907400894011561981430477 30715275335254335743036429)
                  ·
                    refine ⟨11518228250720375903638661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30715275335254335743036429 11518228250720375903638661)
                    ·
                      refine ⟨2159667797010070481932249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11518228250720375903638661 2159667797010070481932249)
                      ·
                        rfl

theorem cell23_4205938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_4205938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205938 prefixEnd_4205938 := by exact prefixLift 4205938
  have htrace : WordTrace (prefixWord ++ tailWord_4205938) baseStart_4205938 baseEnd_4205938 := by
    simpa [prefixWord, tailWord_4205938, baseEnd_4205938] using wordTrace_append hprefix tailTrace_4205938
  have hstable : (prefixWord ++ tailWord_4205938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205938).length < 2 ^ (prefixWord ++ tailWord_4205938).sum := by decide
  have hdescent : baseEnd_4205938 < baseStart_4205938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205972 : List Nat := [2, 4, 2, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_4205972 : Nat := 118140960795 + 4205972 * 2 ^ 59
def prefixEnd_4205972 : Nat := 4983230072969 + 3 ^ 40 * 4205972 * 2
def baseEnd_4205972 : Nat := 2159685255352323348907093

theorem tailTrace_4205972 : CollatzResearch.WordTrace tailWord_4205972 prefixEnd_4205972 2159685255352323348907093 := by
  unfold tailWord_4205972
  simp only [CollatzResearch.WordTrace]
  refine ⟨76702200759244620837054085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102269601012326161116072113 76702200759244620837054085)
  ·
    refine ⟨14381662642358366406947641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76702200759244620837054085 14381662642358366406947641)
    ·
      refine ⟨10786246981768774805210731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14381662642358366406947641 10786246981768774805210731)
      ·
        refine ⟨16179370472653162207816097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10786246981768774805210731 16179370472653162207816097)
        ·
          refine ⟨12134527854489871655862073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16179370472653162207816097 12134527854489871655862073)
          ·
            refine ⟨9100895890867403741896555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12134527854489871655862073 9100895890867403741896555)
            ·
              refine ⟨13651343836301105612844833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9100895890867403741896555 13651343836301105612844833)
              ·
                refine ⟨10238507877225829209633625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13651343836301105612844833 10238507877225829209633625)
                ·
                  refine ⟨7678880907919371907225219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10238507877225829209633625 7678880907919371907225219)
                  ·
                    refine ⟨11518321361879057860837829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7678880907919371907225219 11518321361879057860837829)
                    ·
                      refine ⟨2159685255352323348907093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11518321361879057860837829 2159685255352323348907093)
                      ·
                        rfl

theorem cell23_4205972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_4205972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205972 prefixEnd_4205972 := by exact prefixLift 4205972
  have htrace : WordTrace (prefixWord ++ tailWord_4205972) baseStart_4205972 baseEnd_4205972 := by
    simpa [prefixWord, tailWord_4205972, baseEnd_4205972] using wordTrace_append hprefix tailTrace_4205972
  have hstable : (prefixWord ++ tailWord_4205972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205972).length < 2 ^ (prefixWord ++ tailWord_4205972).sum := by decide
  have hdescent : baseEnd_4205972 < baseStart_4205972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4205978 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 8]
def baseStart_4205978 : Nat := 118140960795 + 4205978 * 2 ^ 59
def prefixEnd_4205978 : Nat := 4983230072969 + 3 ^ 40 * 4205978 * 2
def baseEnd_4205978 : Nat := 239965370692916702825785

theorem tailTrace_4205978 : CollatzResearch.WordTrace tailWord_4205978 prefixEnd_4205978 239965370692916702825785 := by
  unfold tailWord_4205978
  simp only [CollatzResearch.WordTrace]
  refine ⟨38351155089116876174706647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102269746904311669799217725 38351155089116876174706647)
  ·
    refine ⟨57526732633675314262059971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38351155089116876174706647 57526732633675314262059971)
    ·
      refine ⟨86290098950512971393089957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57526732633675314262059971 86290098950512971393089957)
      ·
        refine ⟨16179393553221182136204367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86290098950512971393089957 16179393553221182136204367)
        ·
          refine ⟨24269090329831773204306551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16179393553221182136204367 24269090329831773204306551)
          ·
            refine ⟨36403635494747659806459827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24269090329831773204306551 36403635494747659806459827)
            ·
              refine ⟨54605453242121489709689741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36403635494747659806459827 54605453242121489709689741)
              ·
                refine ⟨20477044965795558641133653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54605453242121489709689741 20477044965795558641133653)
                ·
                  refine ⟨239965370692916702825785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20477044965795558641133653 239965370692916702825785)
                  ·
                    rfl

theorem cell23_4205978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 8].length) (baseStart_4205978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4205978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4205978 prefixEnd_4205978 := by exact prefixLift 4205978
  have htrace : WordTrace (prefixWord ++ tailWord_4205978) baseStart_4205978 baseEnd_4205978 := by
    simpa [prefixWord, tailWord_4205978, baseEnd_4205978] using wordTrace_append hprefix tailTrace_4205978
  have hstable : (prefixWord ++ tailWord_4205978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4205978).length < 2 ^ (prefixWord ++ tailWord_4205978).sum := by decide
  have hdescent : baseEnd_4205978 < baseStart_4205978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4205978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206015 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 1, 5, 2]
def baseStart_4206015 : Nat := 118140960795 + 4206015 * 2 ^ 59
def prefixEnd_4206015 : Nat := 4983230072969 + 3 ^ 40 * 4206015 * 2
def baseEnd_4206015 : Nat := 2159707335020466680669395

theorem tailTrace_4206015 : CollatzResearch.WordTrace tailWord_4206015 prefixEnd_4206015 2159707335020466680669395 := by
  unfold tailWord_4206015
  simp only [CollatzResearch.WordTrace]
  refine ⟨153405969857333460017923499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102270646571555640011948999 153405969857333460017923499)
  ·
    refine ⟨230108954786000190026885249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153405969857333460017923499 230108954786000190026885249)
    ·
      refine ⟨172581716089500142520163937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230108954786000190026885249 172581716089500142520163937)
      ·
        refine ⟨129436287067125106890122953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172581716089500142520163937 129436287067125106890122953)
        ·
          refine ⟨97077215300343830167592215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129436287067125106890122953 97077215300343830167592215)
          ·
            refine ⟨145615822950515745251388323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97077215300343830167592215 145615822950515745251388323)
            ·
              refine ⟨218423734425773617877082485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145615822950515745251388323 218423734425773617877082485)
              ·
                refine ⟨20477225102416276675976483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 218423734425773617877082485 20477225102416276675976483)
                ·
                  refine ⟨30715837653624415013964725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20477225102416276675976483 30715837653624415013964725)
                  ·
                    refine ⟨2879609780027288907559193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30715837653624415013964725 2879609780027288907559193)
                    ·
                      refine ⟨2159707335020466680669395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2879609780027288907559193 2159707335020466680669395)
                      ·
                        rfl

theorem cell23_4206015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 5, 2].length) (baseStart_4206015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206015 prefixEnd_4206015 := by exact prefixLift 4206015
  have htrace : WordTrace (prefixWord ++ tailWord_4206015) baseStart_4206015 baseEnd_4206015 := by
    simpa [prefixWord, tailWord_4206015, baseEnd_4206015] using wordTrace_append hprefix tailTrace_4206015
  have hstable : (prefixWord ++ tailWord_4206015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206015).length < 2 ^ (prefixWord ++ tailWord_4206015).sum := by decide
  have hdescent : baseEnd_4206015 < baseStart_4206015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206055 : List Nat := [1, 1, 5, 2, 1, 2, 1, 3, 1, 6]
def baseStart_4206055 : Nat := 118140960795 + 4206055 * 2 ^ 59
def prefixEnd_4206055 : Nat := 4983230072969 + 3 ^ 40 * 4206055 * 2
def baseEnd_4206055 : Nat := 719909291415548841389737

theorem tailTrace_4206055 : CollatzResearch.WordTrace tailWord_4206055 prefixEnd_4206055 719909291415548841389737 := by
  unfold tailWord_4206055
  simp only [CollatzResearch.WordTrace]
  refine ⟨153407428777188546849379619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102271619184792364566253079 153407428777188546849379619)
  ·
    refine ⟨230111143165782820274069429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153407428777188546849379619 230111143165782820274069429)
    ·
      refine ⟨21572919671792139400694009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 230111143165782820274069429 21572919671792139400694009)
      ·
        refine ⟨16179689753844104550520507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21572919671792139400694009 16179689753844104550520507)
        ·
          refine ⟨24269534630766156825780761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16179689753844104550520507 24269534630766156825780761)
          ·
            refine ⟨18202150973074617619335571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24269534630766156825780761 18202150973074617619335571)
            ·
              refine ⟨27303226459611926429003357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18202150973074617619335571 27303226459611926429003357)
              ·
                refine ⟨10238709922354472410876259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27303226459611926429003357 10238709922354472410876259)
                ·
                  refine ⟨15358064883531708616314389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10238709922354472410876259 15358064883531708616314389)
                  ·
                    refine ⟨719909291415548841389737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15358064883531708616314389 719909291415548841389737)
                    ·
                      rfl

theorem cell23_4206055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_4206055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206055 prefixEnd_4206055 := by exact prefixLift 4206055
  have htrace : WordTrace (prefixWord ++ tailWord_4206055) baseStart_4206055 baseEnd_4206055 := by
    simpa [prefixWord, tailWord_4206055, baseEnd_4206055] using wordTrace_append hprefix tailTrace_4206055
  have hstable : (prefixWord ++ tailWord_4206055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206055).length < 2 ^ (prefixWord ++ tailWord_4206055).sum := by decide
  have hdescent : baseEnd_4206055 < baseStart_4206055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206062 : List Nat := [4, 1, 2, 1, 2, 1, 2, 4, 1, 1, 4]
def baseStart_4206062 : Nat := 118140960795 + 4206062 * 2 ^ 59
def prefixEnd_4206062 : Nat := 4983230072969 + 3 ^ 40 * 4206062 * 2
def baseEnd_4206062 : Nat := 2159731468611227996781679

theorem tailTrace_4206062 : CollatzResearch.WordTrace tailWord_4206062 prefixEnd_4206062 2159731468611227996781679 := by
  unfold tailWord_4206062
  simp only [CollatzResearch.WordTrace]
  refine ⟨19175960511020398380610555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102271789392108791363256293 19175960511020398380610555)
  ·
    refine ⟨28763940766530597570915833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19175960511020398380610555 28763940766530597570915833)
    ·
      refine ⟨21572955574897948178186875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28763940766530597570915833 21572955574897948178186875)
      ·
        refine ⟨32359433362346922267280313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21572955574897948178186875 32359433362346922267280313)
        ·
          refine ⟨24269575021760191700460235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32359433362346922267280313 24269575021760191700460235)
          ·
            refine ⟨36404362532640287550690353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24269575021760191700460235 36404362532640287550690353)
            ·
              refine ⟨27303271899480215663017765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36404362532640287550690353 27303271899480215663017765)
              ·
                refine ⟨5119363481152540436815831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27303271899480215663017765 5119363481152540436815831)
                ·
                  refine ⟨7679045221728810655223747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5119363481152540436815831 7679045221728810655223747)
                  ·
                    refine ⟨11518567832593215982835621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7679045221728810655223747 11518567832593215982835621)
                    ·
                      refine ⟨2159731468611227996781679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11518567832593215982835621 2159731468611227996781679)
                      ·
                        rfl

theorem cell23_4206062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_4206062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206062 prefixEnd_4206062 := by exact prefixLift 4206062
  have htrace : WordTrace (prefixWord ++ tailWord_4206062) baseStart_4206062 baseEnd_4206062 := by
    simpa [prefixWord, tailWord_4206062, baseEnd_4206062] using wordTrace_append hprefix tailTrace_4206062
  have hstable : (prefixWord ++ tailWord_4206062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206062).length < 2 ^ (prefixWord ++ tailWord_4206062).sum := by decide
  have hdescent : baseEnd_4206062 < baseStart_4206062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206066 : List Nat := [3, 2, 1, 4, 1, 3, 1, 1, 2, 3, 2]
def baseStart_4206066 : Nat := 118140960795 + 4206066 * 2 ^ 59
def prefixEnd_4206066 : Nat := 4983230072969 + 3 ^ 40 * 4206066 * 2
def baseEnd_4206066 : Nat := 2159733522533845981131661

theorem tailTrace_4206066 : CollatzResearch.WordTrace tailWord_4206066 prefixEnd_4206066 2159733522533845981131661 := by
  unfold tailWord_4206066
  simp only [CollatzResearch.WordTrace]
  refine ⟨38351957495037173932007513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102271886653432463818686701 38351957495037173932007513)
  ·
    refine ⟨28763968121277880449005635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38351957495037173932007513 28763968121277880449005635)
    ·
      refine ⟨43145952181916820673508453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28763968121277880449005635 43145952181916820673508453)
      ·
        refine ⟨8089866034109403876282835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43145952181916820673508453 8089866034109403876282835)
        ·
          refine ⟨12134799051164105814424253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8089866034109403876282835 12134799051164105814424253)
          ·
            refine ⟨4550549644186539680409095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12134799051164105814424253 4550549644186539680409095)
            ·
              refine ⟨6825824466279809520613643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4550549644186539680409095 6825824466279809520613643)
              ·
                refine ⟨10238736699419714280920465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6825824466279809520613643 10238736699419714280920465)
                ·
                  refine ⟨7679052524564785710690349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10238736699419714280920465 7679052524564785710690349)
                  ·
                    refine ⟨2879644696711794641508881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7679052524564785710690349 2879644696711794641508881)
                    ·
                      refine ⟨2159733522533845981131661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2879644696711794641508881 2159733522533845981131661)
                      ·
                        rfl

theorem cell23_4206066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_4206066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206066 prefixEnd_4206066 := by exact prefixLift 4206066
  have htrace : WordTrace (prefixWord ++ tailWord_4206066) baseStart_4206066 baseEnd_4206066 := by
    simpa [prefixWord, tailWord_4206066, baseEnd_4206066] using wordTrace_append hprefix tailTrace_4206066
  have hstable : (prefixWord ++ tailWord_4206066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206066).length < 2 ^ (prefixWord ++ tailWord_4206066).sum := by decide
  have hdescent : baseEnd_4206066 < baseStart_4206066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206155 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 3]
def baseStart_4206155 : Nat := 118140960795 + 4206155 * 2 ^ 59
def prefixEnd_4206155 : Nat := 4983230072969 + 3 ^ 40 * 4206155 * 2
def baseEnd_4206155 : Nat := 2159779222312096132918751

theorem tailTrace_4206155 : CollatzResearch.WordTrace tailWord_4206155 prefixEnd_4206155 2159779222312096132918751 := by
  unfold tailWord_4206155
  simp only [CollatzResearch.WordTrace]
  refine ⟨153411076076826263928019919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102274050717884175952013279 153411076076826263928019919)
  ·
    refine ⟨230116614115239395892029879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153411076076826263928019919 230116614115239395892029879)
    ·
      refine ⟨345174921172859093838044819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230116614115239395892029879 345174921172859093838044819)
      ·
        refine ⟨517762381759288640757067229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345174921172859093838044819 517762381759288640757067229)
        ·
          refine ⟨194160893159733240283900211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 517762381759288640757067229 194160893159733240283900211)
          ·
            refine ⟨291241339739599860425850317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194160893159733240283900211 291241339739599860425850317)
            ·
              refine ⟨109215502402349947659693869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 291241339739599860425850317 109215502402349947659693869)
              ·
                refine ⟨40955813400881230372385201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109215502402349947659693869 40955813400881230372385201)
                ·
                  refine ⟨30716860050660922779288901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40955813400881230372385201 30716860050660922779288901)
                  ·
                    refine ⟨5759411259498923021116669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30716860050660922779288901 5759411259498923021116669)
                    ·
                      refine ⟨2159779222312096132918751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5759411259498923021116669 2159779222312096132918751)
                      ·
                        rfl

theorem cell23_4206155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 3].length) (baseStart_4206155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206155 prefixEnd_4206155 := by exact prefixLift 4206155
  have htrace : WordTrace (prefixWord ++ tailWord_4206155) baseStart_4206155 baseEnd_4206155 := by
    simpa [prefixWord, tailWord_4206155, baseEnd_4206155] using wordTrace_append hprefix tailTrace_4206155
  have hstable : (prefixWord ++ tailWord_4206155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206155).length < 2 ^ (prefixWord ++ tailWord_4206155).sum := by decide
  have hdescent : baseEnd_4206155 < baseStart_4206155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206165 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_4206165 : Nat := 118140960795 + 4206165 * 2 ^ 59
def prefixEnd_4206165 : Nat := 4983230072969 + 3 ^ 40 * 4206165 * 2
def baseEnd_4206165 : Nat := 2159784357118641093793705

theorem tailTrace_4206165 : CollatzResearch.WordTrace tailWord_4206165 prefixEnd_4206165 2159784357118641093793705 := by
  unfold tailWord_4206165
  simp only [CollatzResearch.WordTrace]
  refine ⟨153411440806790035635883949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102274293871193357090589299 153411440806790035635883949)
  ·
    refine ⟨57529290302546263363456481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153411440806790035635883949 57529290302546263363456481)
    ·
      refine ⟨43146967726909697522592361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57529290302546263363456481 43146967726909697522592361)
      ·
        refine ⟨32360225795182273141944271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43146967726909697522592361 32360225795182273141944271)
        ·
          refine ⟨48540338692773409712916407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32360225795182273141944271 48540338692773409712916407)
          ·
            refine ⟨72810508039160114569374611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48540338692773409712916407 72810508039160114569374611)
            ·
              refine ⟨109215762058740171854061917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72810508039160114569374611 109215762058740171854061917)
              ·
                refine ⟨40955910772027564445273219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109215762058740171854061917 40955910772027564445273219)
                ·
                  refine ⟨61433866158041346667909829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40955910772027564445273219 61433866158041346667909829)
                  ·
                    refine ⟨11518849904632752500233093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61433866158041346667909829 11518849904632752500233093)
                    ·
                      refine ⟨2159784357118641093793705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11518849904632752500233093 2159784357118641093793705)
                      ·
                        rfl

theorem cell23_4206165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_4206165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206165 prefixEnd_4206165 := by exact prefixLift 4206165
  have htrace : WordTrace (prefixWord ++ tailWord_4206165) baseStart_4206165 baseEnd_4206165 := by
    simpa [prefixWord, tailWord_4206165, baseEnd_4206165] using wordTrace_append hprefix tailTrace_4206165
  have hstable : (prefixWord ++ tailWord_4206165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206165).length < 2 ^ (prefixWord ++ tailWord_4206165).sum := by decide
  have hdescent : baseEnd_4206165 < baseStart_4206165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206172 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_4206172 : Nat := 118140960795 + 4206172 * 2 ^ 59
def prefixEnd_4206172 : Nat := 4983230072969 + 3 ^ 40 * 4206172 * 2
def baseEnd_4206172 : Nat := 2159787951483222566406173

theorem tailTrace_4206172 : CollatzResearch.WordTrace tailWord_4206172 prefixEnd_4206172 2159787951483222566406173 := by
  unfold tailWord_4206172
  simp only [CollatzResearch.WordTrace]
  refine ⟨76705848058882337915694385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102274464078509783887592513 76705848058882337915694385)
  ·
    refine ⟨57529386044161753436770789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76705848058882337915694385 57529386044161753436770789)
    ·
      refine ⟨10786759883280328769394523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57529386044161753436770789 10786759883280328769394523)
      ·
        refine ⟨16180139824920493154091785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10786759883280328769394523 16180139824920493154091785)
        ·
          refine ⟨12135104868690369865568839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16180139824920493154091785 12135104868690369865568839)
          ·
            refine ⟨18202657303035554798353259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12135104868690369865568839 18202657303035554798353259)
            ·
              refine ⟨27303985954553332197529889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18202657303035554798353259 27303985954553332197529889)
              ·
                refine ⟨20477989465914999148147417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27303985954553332197529889 20477989465914999148147417)
                ·
                  refine ⟨15358492099436249361110563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20477989465914999148147417 15358492099436249361110563)
                  ·
                    refine ⟨23037738149154374041665845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15358492099436249361110563 23037738149154374041665845)
                    ·
                      refine ⟨2159787951483222566406173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23037738149154374041665845 2159787951483222566406173)
                      ·
                        rfl

theorem cell23_4206172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_4206172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206172 prefixEnd_4206172 := by exact prefixLift 4206172
  have htrace : WordTrace (prefixWord ++ tailWord_4206172) baseStart_4206172 baseEnd_4206172 := by
    simpa [prefixWord, tailWord_4206172, baseEnd_4206172] using wordTrace_append hprefix tailTrace_4206172
  have hstable : (prefixWord ++ tailWord_4206172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206172).length < 2 ^ (prefixWord ++ tailWord_4206172).sum := by decide
  have hdescent : baseEnd_4206172 < baseStart_4206172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206173 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_4206173 : Nat := 118140960795 + 4206173 * 2 ^ 59
def prefixEnd_4206173 : Nat := 4983230072969 + 3 ^ 40 * 4206173 * 2
def baseEnd_4206173 : Nat := 2159788464963877062493669

theorem tailTrace_4206173 : CollatzResearch.WordTrace tailWord_4206173 prefixEnd_4206173 2159788464963877062493669 := by
  unfold tailWord_4206173
  simp only [CollatzResearch.WordTrace]
  refine ⟨153411732590761053002175173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102274488393840702001450115 153411732590761053002175173)
  ·
    refine ⟨28764699860767697437907845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153411732590761053002175173 28764699860767697437907845)
    ·
      refine ⟨5393381223893943269607721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28764699860767697437907845 5393381223893943269607721)
      ·
        refine ⟨4045035917920457452205791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5393381223893943269607721 4045035917920457452205791)
        ·
          refine ⟨6067553876880686178308687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4045035917920457452205791 6067553876880686178308687)
          ·
            refine ⟨9101330815321029267463031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6067553876880686178308687 9101330815321029267463031)
            ·
              refine ⟨13651996222981543901194547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9101330815321029267463031 13651996222981543901194547)
              ·
                refine ⟨20477994334472315851791821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13651996222981543901194547 20477994334472315851791821)
                ·
                  refine ⟨7679247875427118444421933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20477994334472315851791821 7679247875427118444421933)
                  ·
                    refine ⟨2879717953285169416658225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7679247875427118444421933 2879717953285169416658225)
                    ·
                      refine ⟨2159788464963877062493669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2879717953285169416658225 2159788464963877062493669)
                      ·
                        rfl

theorem cell23_4206173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_4206173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206173 prefixEnd_4206173 := by exact prefixLift 4206173
  have htrace : WordTrace (prefixWord ++ tailWord_4206173) baseStart_4206173 baseEnd_4206173 := by
    simpa [prefixWord, tailWord_4206173, baseEnd_4206173] using wordTrace_append hprefix tailTrace_4206173
  have hstable : (prefixWord ++ tailWord_4206173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206173).length < 2 ^ (prefixWord ++ tailWord_4206173).sum := by decide
  have hdescent : baseEnd_4206173 < baseStart_4206173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206209 : List Nat := [1, 2, 4, 2, 1, 3, 1, 4, 5]
def baseStart_4206209 : Nat := 118140960795 + 4206209 * 2 ^ 59
def prefixEnd_4206209 : Nat := 4983230072969 + 3 ^ 40 * 4206209 * 2
def baseEnd_4206209 : Nat := 239978550029715435738167

theorem tailTrace_4206209 : CollatzResearch.WordTrace tailWord_4206209 prefixEnd_4206209 239978550029715435738167 := by
  unfold tailWord_4206209
  simp only [CollatzResearch.WordTrace]
  refine ⟨153413045618630631150485681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102275363745753754100323787 153413045618630631150485681)
  ·
    refine ⟨115059784213972973362864261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153413045618630631150485681 115059784213972973362864261)
    ·
      refine ⟨21573709540119932505537049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115059784213972973362864261 21573709540119932505537049)
      ·
        refine ⟨16180282155089949379152787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21573709540119932505537049 16180282155089949379152787)
        ·
          refine ⟨24270423232634924068729181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16180282155089949379152787 24270423232634924068729181)
          ·
            refine ⟨9101408712238096525773443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24270423232634924068729181 9101408712238096525773443)
            ·
              refine ⟨13652113068357144788660165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9101408712238096525773443 13652113068357144788660165)
              ·
                refine ⟨2559771200316964647873781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13652113068357144788660165 2559771200316964647873781)
                ·
                  refine ⟨239978550029715435738167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2559771200316964647873781 239978550029715435738167)
                  ·
                    rfl

theorem cell23_4206209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 5].length) (baseStart_4206209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206209 prefixEnd_4206209 := by exact prefixLift 4206209
  have htrace : WordTrace (prefixWord ++ tailWord_4206209) baseStart_4206209 baseEnd_4206209 := by
    simpa [prefixWord, tailWord_4206209, baseEnd_4206209] using wordTrace_append hprefix tailTrace_4206209
  have hstable : (prefixWord ++ tailWord_4206209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206209).length < 2 ^ (prefixWord ++ tailWord_4206209).sum := by decide
  have hdescent : baseEnd_4206209 < baseStart_4206209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206239 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 1, 7]
def baseStart_4206239 : Nat := 118140960795 + 4206239 * 2 ^ 59
def prefixEnd_4206239 : Nat := 4983230072969 + 3 ^ 40 * 4206239 * 2
def baseEnd_4206239 : Nat := 719940784895691268089455

theorem tailTrace_4206239 : CollatzResearch.WordTrace tailWord_4206239 prefixEnd_4206239 719940784895691268089455 := by
  unfold tailWord_4206239
  simp only [CollatzResearch.WordTrace]
  refine ⟨153414139808521946274077771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102276093205681297516051847 153414139808521946274077771)
  ·
    refine ⟨230121209712782919411116657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153414139808521946274077771 230121209712782919411116657)
    ·
      refine ⟨172590907284587189558337493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230121209712782919411116657 172590907284587189558337493)
      ·
        refine ⟨4045099389482512255273535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 172590907284587189558337493 4045099389482512255273535)
        ·
          refine ⟨6067649084223768382910303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4045099389482512255273535 6067649084223768382910303)
          ·
            refine ⟨9101473626335652574365455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6067649084223768382910303 9101473626335652574365455)
            ·
              refine ⟨13652210439503478861548183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9101473626335652574365455 13652210439503478861548183)
              ·
                refine ⟨20478315659255218292322275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13652210439503478861548183 20478315659255218292322275)
                ·
                  refine ⟨30717473488882827438483413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20478315659255218292322275 30717473488882827438483413)
                  ·
                    refine ⟨719940784895691268089455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30717473488882827438483413 719940784895691268089455)
                    ·
                      rfl

theorem cell23_4206239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 7].length) (baseStart_4206239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206239 prefixEnd_4206239 := by exact prefixLift 4206239
  have htrace : WordTrace (prefixWord ++ tailWord_4206239) baseStart_4206239 baseEnd_4206239 := by
    simpa [prefixWord, tailWord_4206239, baseEnd_4206239] using wordTrace_append hprefix tailTrace_4206239
  have hstable : (prefixWord ++ tailWord_4206239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206239).length < 2 ^ (prefixWord ++ tailWord_4206239).sum := by decide
  have hdescent : baseEnd_4206239 < baseStart_4206239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206255 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 6]
def baseStart_4206255 : Nat := 118140960795 + 4206255 * 2 ^ 59
def prefixEnd_4206255 : Nat := 4983230072969 + 3 ^ 40 * 4206255 * 2
def baseEnd_4206255 : Nat := 2159830570377545741668291

theorem tailTrace_4206255 : CollatzResearch.WordTrace tailWord_4206255 prefixEnd_4206255 2159830570377545741668291 := by
  unfold tailWord_4206255
  simp only [CollatzResearch.WordTrace]
  refine ⟨153414723376463981006660219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102276482250975987337773479 153414723376463981006660219)
  ·
    refine ⟨230122085064695971509990329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153414723376463981006660219 230122085064695971509990329)
    ·
      refine ⟨172591563798521978632492747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230122085064695971509990329 172591563798521978632492747)
      ·
        refine ⟨258887345697782967948739121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172591563798521978632492747 258887345697782967948739121)
        ·
          refine ⟨194165509273337225961554341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258887345697782967948739121 194165509273337225961554341)
          ·
            refine ⟨36406032988750729867791439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 194165509273337225961554341 36406032988750729867791439)
            ·
              refine ⟨54609049483126094801687159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36406032988750729867791439 54609049483126094801687159)
              ·
                refine ⟨81913574224689142202530739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54609049483126094801687159 81913574224689142202530739)
                ·
                  refine ⟨122870361337033713303796109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81913574224689142202530739 122870361337033713303796109)
                  ·
                    refine ⟨46076385501387642488923541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122870361337033713303796109 46076385501387642488923541)
                    ·
                      refine ⟨2159830570377545741668291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46076385501387642488923541 2159830570377545741668291)
                      ·
                        rfl

theorem cell23_4206255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_4206255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206255 prefixEnd_4206255 := by exact prefixLift 4206255
  have htrace : WordTrace (prefixWord ++ tailWord_4206255) baseStart_4206255 baseEnd_4206255 := by
    simpa [prefixWord, tailWord_4206255, baseEnd_4206255] using wordTrace_append hprefix tailTrace_4206255
  have hstable : (prefixWord ++ tailWord_4206255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206255).length < 2 ^ (prefixWord ++ tailWord_4206255).sum := by decide
  have hdescent : baseEnd_4206255 < baseStart_4206255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206269 : List Nat := [1, 4, 1, 2, 1, 2, 4, 1, 3, 4]
def baseStart_4206269 : Nat := 118140960795 + 4206269 * 2 ^ 59
def prefixEnd_4206269 : Nat := 4983230072969 + 3 ^ 40 * 4206269 * 2
def baseEnd_4206269 : Nat := 719945919702236228964409

theorem tailTrace_4206269 : CollatzResearch.WordTrace tailWord_4206269 prefixEnd_4206269 719945919702236228964409 := by
  unfold tailWord_4206269
  simp only [CollatzResearch.WordTrace]
  refine ⟨153415233998413261397669861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102276822665608840931779907 153415233998413261397669861)
  ·
    refine ⟨28765356374702486512063099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153415233998413261397669861 28765356374702486512063099)
    ·
      refine ⟨43148034562053729768094649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28765356374702486512063099 43148034562053729768094649)
      ·
        refine ⟨32361025921540297326070987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43148034562053729768094649 32361025921540297326070987)
        ·
          refine ⟨48541538882310445989106481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32361025921540297326070987 48541538882310445989106481)
          ·
            refine ⟨36406154161732834491829861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48541538882310445989106481 36406154161732834491829861)
            ·
              refine ⟨6826153905324906467218099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36406154161732834491829861 6826153905324906467218099)
              ·
                refine ⟨10239230857987359700827149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6826153905324906467218099 10239230857987359700827149)
                ·
                  refine ⟨3839711571745259887810181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10239230857987359700827149 3839711571745259887810181)
                  ·
                    refine ⟨719945919702236228964409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3839711571745259887810181 719945919702236228964409)
                    ·
                      rfl

theorem cell23_4206269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_4206269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206269 prefixEnd_4206269 := by exact prefixLift 4206269
  have htrace : WordTrace (prefixWord ++ tailWord_4206269) baseStart_4206269 baseEnd_4206269 := by
    simpa [prefixWord, tailWord_4206269, baseEnd_4206269] using wordTrace_append hprefix tailTrace_4206269
  have hstable : (prefixWord ++ tailWord_4206269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206269).length < 2 ^ (prefixWord ++ tailWord_4206269).sum := by decide
  have hdescent : baseEnd_4206269 < baseStart_4206269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206346 : List Nat := [3, 1, 2, 2, 1, 5, 1, 2, 1, 5]
def baseStart_4206346 : Nat := 118140960795 + 4206346 * 2 ^ 59
def prefixEnd_4206346 : Nat := 4983230072969 + 3 ^ 40 * 4206346 * 2
def baseEnd_4206346 : Nat := 719959099039034961876791

theorem tailTrace_4206346 : CollatzResearch.WordTrace tailWord_4206346 prefixEnd_4206346 719959099039034961876791 := by
  unfold tailWord_4206346
  simp only [CollatzResearch.WordTrace]
  refine ⟨38354510604783575887055723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102278694946089535698815261 38354510604783575887055723)
  ·
    refine ⟨57531765907175363830583585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38354510604783575887055723 57531765907175363830583585)
    ·
      refine ⟨43148824430381522872937689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57531765907175363830583585 43148824430381522872937689)
      ·
        refine ⟨32361618322786142154703267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43148824430381522872937689 32361618322786142154703267)
        ·
          refine ⟨48542427484179213232054901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32361618322786142154703267 48542427484179213232054901)
          ·
            refine ⟨4550852576641801240505147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48542427484179213232054901 4550852576641801240505147)
            ·
              refine ⟨6826278864962701860757721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4550852576641801240505147 6826278864962701860757721)
              ·
                refine ⟨5119709148722026395568291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6826278864962701860757721 5119709148722026395568291)
                ·
                  refine ⟨7679563723083039593352437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5119709148722026395568291 7679563723083039593352437)
                  ·
                    refine ⟨719959099039034961876791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7679563723083039593352437 719959099039034961876791)
                    ·
                      rfl

theorem cell23_4206346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_4206346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206346 prefixEnd_4206346 := by exact prefixLift 4206346
  have htrace : WordTrace (prefixWord ++ tailWord_4206346) baseStart_4206346 baseEnd_4206346 := by
    simpa [prefixWord, tailWord_4206346, baseEnd_4206346] using wordTrace_append hprefix tailTrace_4206346
  have hstable : (prefixWord ++ tailWord_4206346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206346).length < 2 ^ (prefixWord ++ tailWord_4206346).sum := by decide
  have hdescent : baseEnd_4206346 < baseStart_4206346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206359 : List Nat := [1, 1, 3, 4, 2, 2, 1, 2, 1, 6]
def baseStart_4206359 : Nat := 118140960795 + 4206359 * 2 ^ 59
def prefixEnd_4206359 : Nat := 4983230072969 + 3 ^ 40 * 4206359 * 2
def baseEnd_4206359 : Nat := 719961324121871111589271

theorem tailTrace_4206359 : CollatzResearch.WordTrace tailWord_4206359 prefixEnd_4206359 719961324121871111589271 := by
  unfold tailWord_4206359
  simp only [CollatzResearch.WordTrace]
  refine ⟨153418516568087206768446131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102279011045391471178964087 153418516568087206768446131)
  ·
    refine ⟨230127774852130810152669197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153418516568087206768446131 230127774852130810152669197)
    ·
      refine ⟨86297915569549053807250949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230127774852130810152669197 86297915569549053807250949)
      ·
        refine ⟨16180859169290447588859553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86297915569549053807250949 16180859169290447588859553)
        ·
          refine ⟨12135644376967835691644665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16180859169290447588859553 12135644376967835691644665)
          ·
            refine ⟨9101733282725876768733499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12135644376967835691644665 9101733282725876768733499)
            ·
              refine ⟨13652599924088815153100249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9101733282725876768733499 13652599924088815153100249)
              ·
                refine ⟨10239449943066611364825187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13652599924088815153100249 10239449943066611364825187)
                ·
                  refine ⟨15359174914599917047237781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10239449943066611364825187 15359174914599917047237781)
                  ·
                    refine ⟨719961324121871111589271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15359174914599917047237781 719961324121871111589271)
                    ·
                      rfl

theorem cell23_4206359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_4206359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206359 prefixEnd_4206359 := by exact prefixLift 4206359
  have htrace : WordTrace (prefixWord ++ tailWord_4206359) baseStart_4206359 baseEnd_4206359 := by
    simpa [prefixWord, tailWord_4206359, baseEnd_4206359] using wordTrace_append hprefix tailTrace_4206359
  have hstable : (prefixWord ++ tailWord_4206359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206359).length < 2 ^ (prefixWord ++ tailWord_4206359).sum := by decide
  have hdescent : baseEnd_4206359 < baseStart_4206359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206369 : List Nat := [1, 2, 3, 2, 1, 3, 3, 1, 1, 1, 5]
def baseStart_4206369 : Nat := 118140960795 + 4206369 * 2 ^ 59
def prefixEnd_4206369 : Nat := 4983230072969 + 3 ^ 40 * 4206369 * 2
def baseEnd_4206369 : Nat := 2159889107172158295642767

theorem tailTrace_4206369 : CollatzResearch.WordTrace tailWord_4206369 prefixEnd_4206369 2159889107172158295642767 := by
  unfold tailWord_4206369
  simp only [CollatzResearch.WordTrace]
  refine ⟨153418881298050978476310161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102279254198700652317540107 153418881298050978476310161)
  ·
    refine ⟨115064160973538233857232621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153418881298050978476310161 115064160973538233857232621)
    ·
      refine ⟨43149060365076837696462233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115064160973538233857232621 43149060365076837696462233)
      ·
        refine ⟨32361795273807628272346675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43149060365076837696462233 32361795273807628272346675)
        ·
          refine ⟨48542692910711442408520013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32361795273807628272346675 48542692910711442408520013)
          ·
            refine ⟨18203509841516790903195005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48542692910711442408520013 18203509841516790903195005)
            ·
              refine ⟨6826316190568796588698127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18203509841516790903195005 6826316190568796588698127)
              ·
                refine ⟨10239474285853194883047191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6826316190568796588698127 10239474285853194883047191)
                ·
                  refine ⟨15359211428779792324570787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10239474285853194883047191 15359211428779792324570787)
                  ·
                    refine ⟨23038817143169688486856181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15359211428779792324570787 23038817143169688486856181)
                    ·
                      refine ⟨2159889107172158295642767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23038817143169688486856181 2159889107172158295642767)
                      ·
                        rfl

theorem cell23_4206369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_4206369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206369 prefixEnd_4206369 := by exact prefixLift 4206369
  have htrace : WordTrace (prefixWord ++ tailWord_4206369) baseStart_4206369 baseEnd_4206369 := by
    simpa [prefixWord, tailWord_4206369, baseEnd_4206369] using wordTrace_append hprefix tailTrace_4206369
  have hstable : (prefixWord ++ tailWord_4206369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206369).length < 2 ^ (prefixWord ++ tailWord_4206369).sum := by decide
  have hdescent : baseEnd_4206369 < baseStart_4206369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206372 : List Nat := [2, 3, 1, 3, 2, 12]
def baseStart_4206372 : Nat := 118140960795 + 4206372 * 2 ^ 59
def prefixEnd_4206372 : Nat := 4983230072969 + 3 ^ 40 * 4206372 * 2
def baseEnd_4206372 : Nat := 8888438879070460016071

theorem tailTrace_4206372 : CollatzResearch.WordTrace tailWord_4206372 prefixEnd_4206372 8888438879070460016071 := by
  unfold tailWord_4206372
  simp only [CollatzResearch.WordTrace]
  refine ⟨76709495358520054994334685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102279327144693406659112913 76709495358520054994334685)
  ·
    refine ⟨28766060759445020622875507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76709495358520054994334685 28766060759445020622875507)
    ·
      refine ⟨43149091139167530934313261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28766060759445020622875507 43149091139167530934313261)
      ·
        refine ⟨16180909177187824100367473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43149091139167530934313261 16180909177187824100367473)
        ·
          refine ⟨12135681882890868075275605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16180909177187824100367473 12135681882890868075275605)
          ·
            refine ⟨8888438879070460016071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 12135681882890868075275605 8888438879070460016071)
            ·
              rfl

theorem cell23_4206372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 12].length) (baseStart_4206372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206372 prefixEnd_4206372 := by exact prefixLift 4206372
  have htrace : WordTrace (prefixWord ++ tailWord_4206372) baseStart_4206372 baseEnd_4206372 := by
    simpa [prefixWord, tailWord_4206372, baseEnd_4206372] using wordTrace_append hprefix tailTrace_4206372
  have hstable : (prefixWord ++ tailWord_4206372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206372).length < 2 ^ (prefixWord ++ tailWord_4206372).sum := by decide
  have hdescent : baseEnd_4206372 < baseStart_4206372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206376 : List Nat := [2, 1, 5, 1, 1, 2, 1, 4, 2, 4]
def baseStart_4206376 : Nat := 118140960795 + 4206376 * 2 ^ 59
def prefixEnd_4206376 : Nat := 4983230072969 + 3 ^ 40 * 4206376 * 2
def baseEnd_4206376 : Nat := 719964233845579922751745

theorem tailTrace_4206376 : CollatzResearch.WordTrace tailWord_4206376 prefixEnd_4206376 719964233845579922751745 := by
  unfold tailWord_4206376
  simp only [CollatzResearch.WordTrace]
  refine ⟨76709568304512809335907491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102279424406017079114543321 76709568304512809335907491)
  ·
    refine ⟨115064352456769214003861237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76709568304512809335907491 115064352456769214003861237)
    ·
      refine ⟨10787283042822113812861991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115064352456769214003861237 10787283042822113812861991)
      ·
        refine ⟨16180924564233170719292987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10787283042822113812861991 16180924564233170719292987)
        ·
          refine ⟨24271386846349756078939481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16180924564233170719292987 24271386846349756078939481)
          ·
            refine ⟨18203540134762317059204611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24271386846349756078939481 18203540134762317059204611)
            ·
              refine ⟨27305310202143475588806917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18203540134762317059204611 27305310202143475588806917)
              ·
                refine ⟨5119745662901901672901297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27305310202143475588806917 5119745662901901672901297)
                ·
                  refine ⟨3839809247176426254675973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5119745662901901672901297 3839809247176426254675973)
                  ·
                    refine ⟨719964233845579922751745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3839809247176426254675973 719964233845579922751745)
                    ·
                      rfl

theorem cell23_4206376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_4206376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206376 prefixEnd_4206376 := by exact prefixLift 4206376
  have htrace : WordTrace (prefixWord ++ tailWord_4206376) baseStart_4206376 baseEnd_4206376 := by
    simpa [prefixWord, tailWord_4206376, baseEnd_4206376] using wordTrace_append hprefix tailTrace_4206376
  have hstable : (prefixWord ++ tailWord_4206376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206376).length < 2 ^ (prefixWord ++ tailWord_4206376).sum := by decide
  have hdescent : baseEnd_4206376 < baseStart_4206376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206383 : List Nat := [1, 1, 2, 1, 2, 1, 2, 8, 1, 2, 2]
def baseStart_4206383 : Nat := 118140960795 + 4206383 * 2 ^ 59
def prefixEnd_4206383 : Nat := 4983230072969 + 3 ^ 40 * 4206383 * 2
def baseEnd_4206383 : Nat := 2159896295901321240867703

theorem tailTrace_4206383 : CollatzResearch.WordTrace tailWord_4206383 prefixEnd_4206383 2159896295901321240867703 := by
  unfold tailWord_4206383
  simp only [CollatzResearch.WordTrace]
  refine ⟨153419391920000258867319803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102279594613333505911546535 153419391920000258867319803)
  ·
    refine ⟨230129087880000388300979705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153419391920000258867319803 230129087880000388300979705)
    ·
      refine ⟨172596815910000291225734779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230129087880000388300979705 172596815910000291225734779)
      ·
        refine ⟨258895223865000436838602169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172596815910000291225734779 258895223865000436838602169)
        ·
          refine ⟨194171417898750327628951627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258895223865000436838602169 194171417898750327628951627)
          ·
            refine ⟨291257126848125491443427441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194171417898750327628951627 291257126848125491443427441)
            ·
              refine ⟨218442845136094118582570581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291257126848125491443427441 218442845136094118582570581)
              ·
                refine ⟨2559877091438602952139499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 218442845136094118582570581 2559877091438602952139499)
                ·
                  refine ⟨3839815637157904428209249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2559877091438602952139499 3839815637157904428209249)
                  ·
                    refine ⟨2879861727868428321156937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3839815637157904428209249 2879861727868428321156937)
                    ·
                      refine ⟨2159896295901321240867703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2879861727868428321156937 2159896295901321240867703)
                      ·
                        rfl

theorem cell23_4206383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 1, 2, 2].length) (baseStart_4206383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206383 prefixEnd_4206383 := by exact prefixLift 4206383
  have htrace : WordTrace (prefixWord ++ tailWord_4206383) baseStart_4206383 baseEnd_4206383 := by
    simpa [prefixWord, tailWord_4206383, baseEnd_4206383] using wordTrace_append hprefix tailTrace_4206383
  have hstable : (prefixWord ++ tailWord_4206383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206383).length < 2 ^ (prefixWord ++ tailWord_4206383).sum := by decide
  have hdescent : baseEnd_4206383 < baseStart_4206383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206420 : List Nat := [2, 4, 1, 1, 3, 3, 2, 1, 1, 2, 3]
def baseStart_4206420 : Nat := 118140960795 + 4206420 * 2 ^ 59
def prefixEnd_4206420 : Nat := 4983230072969 + 3 ^ 40 * 4206420 * 2
def baseEnd_4206420 : Nat := 2159915294685537596105033

theorem tailTrace_4206420 : CollatzResearch.WordTrace tailWord_4206420 prefixEnd_4206420 2159915294685537596105033 := by
  unfold tailWord_4206420
  simp only [CollatzResearch.WordTrace]
  refine ⟨76710370710433107093208357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102280494280577476124277809 76710370710433107093208357)
  ·
    refine ⟨14383194508206207579976567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76710370710433107093208357 14383194508206207579976567)
    ·
      refine ⟨21574791762309311369964851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14383194508206207579976567 21574791762309311369964851)
      ·
        refine ⟨32362187643463967054947277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21574791762309311369964851 32362187643463967054947277)
        ·
          refine ⟨12135820366298987645605229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32362187643463967054947277 12135820366298987645605229)
          ·
            refine ⟨4550932637362120367101961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12135820366298987645605229 4550932637362120367101961)
            ·
              refine ⟨3413199478021590275326471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4550932637362120367101961 3413199478021590275326471)
              ·
                refine ⟨5119799217032385412989707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3413199478021590275326471 5119799217032385412989707)
                ·
                  refine ⟨7679698825548578119484561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5119799217032385412989707 7679698825548578119484561)
                  ·
                    refine ⟨5759774119161433589613421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7679698825548578119484561 5759774119161433589613421)
                    ·
                      refine ⟨2159915294685537596105033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5759774119161433589613421 2159915294685537596105033)
                      ·
                        rfl

theorem cell23_4206420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_4206420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206420 prefixEnd_4206420 := by exact prefixLift 4206420
  have htrace : WordTrace (prefixWord ++ tailWord_4206420) baseStart_4206420 baseEnd_4206420 := by
    simpa [prefixWord, tailWord_4206420, baseEnd_4206420] using wordTrace_append hprefix tailTrace_4206420
  have hstable : (prefixWord ++ tailWord_4206420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206420).length < 2 ^ (prefixWord ++ tailWord_4206420).sum := by decide
  have hdescent : baseEnd_4206420 < baseStart_4206420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206489 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 4, 3, 3]
def baseStart_4206489 : Nat := 118140960795 + 4206489 * 2 ^ 59
def prefixEnd_4206489 : Nat := 4983230072969 + 3 ^ 40 * 4206489 * 2
def baseEnd_4206489 : Nat := 2159950724850697826142215

theorem tailTrace_4206489 : CollatzResearch.WordTrace tailWord_4206489 prefixEnd_4206489 2159950724850697826142215 := by
  unfold tailWord_4206489
  simp only [CollatzResearch.WordTrace]
  refine ⟨153423258057616238970678521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102282172038410825980452347 153423258057616238970678521)
  ·
    refine ⟨115067443543212179228008891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153423258057616238970678521 115067443543212179228008891)
    ·
      refine ⟨172601165314818268842013337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115067443543212179228008891 172601165314818268842013337)
      ·
        refine ⟨129450873986113701631510003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172601165314818268842013337 129450873986113701631510003)
        ·
          refine ⟨194176310979170552447265005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129450873986113701631510003 194176310979170552447265005)
          ·
            refine ⟨72816116617188957167724377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 194176310979170552447265005 72816116617188957167724377)
            ·
              refine ⟨54612087462891717875793283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72816116617188957167724377 54612087462891717875793283)
              ·
                refine ⟨81918131194337576813689925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54612087462891717875793283 81918131194337576813689925)
                ·
                  refine ⟨15359649598938295652566861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81918131194337576813689925 15359649598938295652566861)
                  ·
                    refine ⟨5759868599601860869712573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15359649598938295652566861 5759868599601860869712573)
                    ·
                      refine ⟨2159950724850697826142215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5759868599601860869712573 2159950724850697826142215)
                      ·
                        rfl

theorem cell23_4206489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_4206489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206489 prefixEnd_4206489 := by exact prefixLift 4206489
  have htrace : WordTrace (prefixWord ++ tailWord_4206489) baseStart_4206489 baseEnd_4206489 := by
    simpa [prefixWord, tailWord_4206489, baseEnd_4206489] using wordTrace_append hprefix tailTrace_4206489
  have hstable : (prefixWord ++ tailWord_4206489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206489).length < 2 ^ (prefixWord ++ tailWord_4206489).sum := by decide
  have hdescent : baseEnd_4206489 < baseStart_4206489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206526 : List Nat := [4, 2, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_4206526 : Nat := 118140960795 + 4206526 * 2 ^ 59
def prefixEnd_4206526 : Nat := 4983230072969 + 3 ^ 40 * 4206526 * 2
def baseEnd_4206526 : Nat := 719989907878304727126515

theorem tailTrace_4206526 : CollatzResearch.WordTrace tailWord_4206526 prefixEnd_4206526 719989907878304727126515 := by
  unfold tailWord_4206526
  simp only [CollatzResearch.WordTrace]
  refine ⟨19178075944810274286221929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102283071705654796193183621 19178075944810274286221929)
  ·
    refine ⟨14383556958607705714666447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19178075944810274286221929 14383556958607705714666447)
    ·
      refine ⟨21575335437911558571999671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14383556958607705714666447 21575335437911558571999671)
      ·
        refine ⟨32363003156867337857999507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21575335437911558571999671 32363003156867337857999507)
        ·
          refine ⟨48544504735301006786999261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32363003156867337857999507 48544504735301006786999261)
          ·
            refine ⟨18204189275737877545124723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48544504735301006786999261 18204189275737877545124723)
            ·
              refine ⟨27306283913606816317687085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18204189275737877545124723 27306283913606816317687085)
              ·
                refine ⟨10239856467602556119132657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27306283913606816317687085 10239856467602556119132657)
                ·
                  refine ⟨7679892350701917089349493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10239856467602556119132657 7679892350701917089349493)
                  ·
                    refine ⟨719989907878304727126515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7679892350701917089349493 719989907878304727126515)
                    ·
                      rfl

theorem cell23_4206526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_4206526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206526 prefixEnd_4206526 := by exact prefixLift 4206526
  have htrace : WordTrace (prefixWord ++ tailWord_4206526) baseStart_4206526 baseEnd_4206526 := by
    simpa [prefixWord, tailWord_4206526, baseEnd_4206526] using wordTrace_append hprefix tailTrace_4206526
  have hstable : (prefixWord ++ tailWord_4206526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206526).length < 2 ^ (prefixWord ++ tailWord_4206526).sum := by decide
  have hdescent : baseEnd_4206526 < baseStart_4206526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206563 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 2, 4, 2]
def baseStart_4206563 : Nat := 118140960795 + 4206563 * 2 ^ 59
def prefixEnd_4206563 : Nat := 4983230072969 + 3 ^ 40 * 4206563 * 2
def baseEnd_4206563 : Nat := 2159988722419130536616875

theorem tailTrace_4206563 : CollatzResearch.WordTrace tailWord_4206563 prefixEnd_4206563 2159988722419130536616875 := by
  unfold tailWord_4206563
  simp only [CollatzResearch.WordTrace]
  refine ⟨153425957059348149608872343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102283971372898766405914895 153425957059348149608872343)
  ·
    refine ⟨230138935589022224413308515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153425957059348149608872343 230138935589022224413308515)
    ·
      refine ⟨345208403383533336619962773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230138935589022224413308515 345208403383533336619962773)
      ·
        refine ⟨16181643908603125154060755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 345208403383533336619962773 16181643908603125154060755)
        ·
          refine ⟨24272465862904687731091133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16181643908603125154060755 24272465862904687731091133)
          ·
            refine ⟨9102174698589257899159175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24272465862904687731091133 9102174698589257899159175)
            ·
              refine ⟨13653262047883886848738763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9102174698589257899159175 13653262047883886848738763)
              ·
                refine ⟨20479893071825830273108145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13653262047883886848738763 20479893071825830273108145)
                ·
                  refine ⟨15359919803869372704831109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20479893071825830273108145 15359919803869372704831109)
                  ·
                    refine ⟨2879984963225507382155833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15359919803869372704831109 2879984963225507382155833)
                    ·
                      refine ⟨2159988722419130536616875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2879984963225507382155833 2159988722419130536616875)
                      ·
                        rfl

theorem cell23_4206563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_4206563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206563 prefixEnd_4206563 := by exact prefixLift 4206563
  have htrace : WordTrace (prefixWord ++ tailWord_4206563) baseStart_4206563 baseEnd_4206563 := by
    simpa [prefixWord, tailWord_4206563, baseEnd_4206563] using wordTrace_append hprefix tailTrace_4206563
  have hstable : (prefixWord ++ tailWord_4206563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206563).length < 2 ^ (prefixWord ++ tailWord_4206563).sum := by decide
  have hdescent : baseEnd_4206563 < baseStart_4206563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206619 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 4]
def baseStart_4206619 : Nat := 118140960795 + 4206619 * 2 ^ 59
def prefixEnd_4206619 : Nat := 4983230072969 + 3 ^ 40 * 4206619 * 2
def baseEnd_4206619 : Nat := 2160017477335782317516617

theorem tailTrace_4206619 : CollatzResearch.WordTrace tailWord_4206619 prefixEnd_4206619 2160017477335782317516617 := by
  unfold tailWord_4206619
  simp only [CollatzResearch.WordTrace]
  refine ⟨153427999547145271172910911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102285333031430180781940607 153427999547145271172910911)
  ·
    refine ⟨230141999320717906759366367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153427999547145271172910911 230141999320717906759366367)
    ·
      refine ⟨345212998981076860139049551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230141999320717906759366367 345212998981076860139049551)
      ·
        refine ⟨517819498471615290208574327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345212998981076860139049551 517819498471615290208574327)
        ·
          refine ⟨776729247707422935312861491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517819498471615290208574327 776729247707422935312861491)
          ·
            refine ⟨1165093871561134402969292237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 776729247707422935312861491 1165093871561134402969292237)
            ·
              refine ⟨436910201835425401113484589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1165093871561134402969292237 436910201835425401113484589)
              ·
                refine ⟨163841325688284525417556721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 436910201835425401113484589 163841325688284525417556721)
                ·
                  refine ⟨122880994266213394063167541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163841325688284525417556721 122880994266213394063167541)
                  ·
                    refine ⟨11520093212457505693421957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 122880994266213394063167541 11520093212457505693421957)
                    ·
                      refine ⟨2160017477335782317516617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11520093212457505693421957 2160017477335782317516617)
                      ·
                        rfl

theorem cell23_4206619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 4].length) (baseStart_4206619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206619 prefixEnd_4206619 := by exact prefixLift 4206619
  have htrace : WordTrace (prefixWord ++ tailWord_4206619) baseStart_4206619 baseEnd_4206619 := by
    simpa [prefixWord, tailWord_4206619, baseEnd_4206619] using wordTrace_append hprefix tailTrace_4206619
  have hstable : (prefixWord ++ tailWord_4206619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206619).length < 2 ^ (prefixWord ++ tailWord_4206619).sum := by decide
  have hdescent : baseEnd_4206619 < baseStart_4206619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206653 : List Nat := [1, 4, 1, 3, 1, 1, 1, 5, 1, 1, 4]
def baseStart_4206653 : Nat := 118140960795 + 4206653 * 2 ^ 59
def prefixEnd_4206653 : Nat := 4983230072969 + 3 ^ 40 * 4206653 * 2
def baseEnd_4206653 : Nat := 2160034935678035184491461

theorem tailTrace_4206653 : CollatzResearch.WordTrace tailWord_4206653 prefixEnd_4206653 2160034935678035184491461 := by
  unfold tailWord_4206653
  simp only [CollatzResearch.WordTrace]
  refine ⟨153429239629022094979648613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102286159752681396653099075 153429239629022094979648613)
  ·
    refine ⟨28767982430441642808684115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153429239629022094979648613 28767982430441642808684115)
    ·
      refine ⟨43151973645662464213026173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28767982430441642808684115 43151973645662464213026173)
      ·
        refine ⟨16181990117123424079884815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43151973645662464213026173 16181990117123424079884815)
        ·
          refine ⟨24272985175685136119827223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16181990117123424079884815 24272985175685136119827223)
          ·
            refine ⟨36409477763527704179740835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24272985175685136119827223 36409477763527704179740835)
            ·
              refine ⟨54614216645291556269611253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36409477763527704179740835 54614216645291556269611253)
              ·
                refine ⟨5120082810496083400276055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54614216645291556269611253 5120082810496083400276055)
                ·
                  refine ⟨7680124215744125100414083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5120082810496083400276055 7680124215744125100414083)
                  ·
                    refine ⟨11520186323616187650621125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7680124215744125100414083 11520186323616187650621125)
                    ·
                      refine ⟨2160034935678035184491461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11520186323616187650621125 2160034935678035184491461)
                      ·
                        rfl

theorem cell23_4206653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_4206653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206653 prefixEnd_4206653 := by exact prefixLift 4206653
  have htrace : WordTrace (prefixWord ++ tailWord_4206653) baseStart_4206653 baseEnd_4206653 := by
    simpa [prefixWord, tailWord_4206653, baseEnd_4206653] using wordTrace_append hprefix tailTrace_4206653
  have hstable : (prefixWord ++ tailWord_4206653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206653).length < 2 ^ (prefixWord ++ tailWord_4206653).sum := by decide
  have hdescent : baseEnd_4206653 < baseStart_4206653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206656 : List Nat := [2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 5]
def baseStart_4206656 : Nat := 118140960795 + 4206656 * 2 ^ 59
def prefixEnd_4206656 : Nat := 4983230072969 + 3 ^ 40 * 4206656 * 2
def baseEnd_4206656 : Nat := 2160036476119998672753947

theorem tailTrace_4206656 : CollatzResearch.WordTrace tailWord_4206656 prefixEnd_4206656 2160036476119998672753947 := by
  unfold tailWord_4206656
  simp only [CollatzResearch.WordTrace]
  refine ⟨76714674524005613246003911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102286232698674150994671881 76714674524005613246003911)
  ·
    refine ⟨115072011786008419869005867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76714674524005613246003911 115072011786008419869005867)
    ·
      refine ⟨172608017679012629803508801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115072011786008419869005867 172608017679012629803508801)
      ·
        refine ⟨129456013259259472352631601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172608017679012629803508801 129456013259259472352631601)
        ·
          refine ⟨97092009944444604264473701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129456013259259472352631601 97092009944444604264473701)
          ·
            refine ⟨18204751864583363299588819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97092009944444604264473701 18204751864583363299588819)
            ·
              refine ⟨27307127796875044949383229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18204751864583363299588819 27307127796875044949383229)
              ·
                refine ⟨10240172923828141856018711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27307127796875044949383229 10240172923828141856018711)
                ·
                  refine ⟨15360259385742212784028067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10240172923828141856018711 15360259385742212784028067)
                  ·
                    refine ⟨23040389078613319176042101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15360259385742212784028067 23040389078613319176042101)
                    ·
                      refine ⟨2160036476119998672753947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23040389078613319176042101 2160036476119998672753947)
                      ·
                        rfl

theorem cell23_4206656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_4206656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206656 prefixEnd_4206656 := by exact prefixLift 4206656
  have htrace : WordTrace (prefixWord ++ tailWord_4206656) baseStart_4206656 baseEnd_4206656 := by
    simpa [prefixWord, tailWord_4206656, baseEnd_4206656] using wordTrace_append hprefix tailTrace_4206656
  have hstable : (prefixWord ++ tailWord_4206656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206656).length < 2 ^ (prefixWord ++ tailWord_4206656).sum := by decide
  have hdescent : baseEnd_4206656 < baseStart_4206656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206663 : List Nat := [1, 1, 4, 1, 3, 1, 2, 4, 2, 4]
def baseStart_4206663 : Nat := 118140960795 + 4206663 * 2 ^ 59
def prefixEnd_4206663 : Nat := 4983230072969 + 3 ^ 40 * 4206663 * 2
def baseEnd_4206663 : Nat := 720013356828193381788805

theorem tailTrace_4206663 : CollatzResearch.WordTrace tailWord_4206663 prefixEnd_4206663 720013356828193381788805 := by
  unfold tailWord_4206663
  simp only [CollatzResearch.WordTrace]
  refine ⟨153429604358985866687512643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102286402905990577791675095 153429604358985866687512643)
  ·
    refine ⟨230144406538478800031268965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153429604358985866687512643 230144406538478800031268965)
    ·
      refine ⟨43152076225964775005862931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230144406538478800031268965 43152076225964775005862931)
      ·
        refine ⟨64728114338947162508794397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43152076225964775005862931 64728114338947162508794397)
        ·
          refine ⟨24273042877105185940797899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64728114338947162508794397 24273042877105185940797899)
          ·
            refine ⟨36409564315657778911196849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24273042877105185940797899 36409564315657778911196849)
            ·
              refine ⟨27307173236743334183397637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36409564315657778911196849 27307173236743334183397637)
              ·
                refine ⟨5120094981889375159387057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27307173236743334183397637 5120094981889375159387057)
                ·
                  refine ⟨3840071236417031369540293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5120094981889375159387057 3840071236417031369540293)
                  ·
                    refine ⟨720013356828193381788805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3840071236417031369540293 720013356828193381788805)
                    ·
                      rfl

theorem cell23_4206663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_4206663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206663 prefixEnd_4206663 := by exact prefixLift 4206663
  have htrace : WordTrace (prefixWord ++ tailWord_4206663) baseStart_4206663 baseEnd_4206663 := by
    simpa [prefixWord, tailWord_4206663, baseEnd_4206663] using wordTrace_append hprefix tailTrace_4206663
  have hstable : (prefixWord ++ tailWord_4206663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206663).length < 2 ^ (prefixWord ++ tailWord_4206663).sum := by decide
  have hdescent : baseEnd_4206663 < baseStart_4206663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206680 : List Nat := [2, 1, 2, 2, 1, 4, 4, 1, 2, 4]
def baseStart_4206680 : Nat := 118140960795 + 4206680 * 2 ^ 59
def prefixEnd_4206680 : Nat := 4983230072969 + 3 ^ 40 * 4206680 * 2
def baseEnd_4206680 : Nat := 720016266551902192951279

theorem tailTrace_4206680 : CollatzResearch.WordTrace tailWord_4206680 prefixEnd_4206680 720016266551902192951279 := by
  unfold tailWord_4206680
  simp only [CollatzResearch.WordTrace]
  refine ⟨76715112199962139295440747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102286816266616185727254329 76715112199962139295440747)
  ·
    refine ⟨115072668299943208943161121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76715112199962139295440747 115072668299943208943161121)
    ·
      refine ⟨86304501224957406707370841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115072668299943208943161121 86304501224957406707370841)
      ·
        refine ⟨64728375918718055030528131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86304501224957406707370841 64728375918718055030528131)
        ·
          refine ⟨97092563878077082545792197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64728375918718055030528131 97092563878077082545792197)
          ·
            refine ⟨18204855727139452977336037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97092563878077082545792197 18204855727139452977336037)
            ·
              refine ⟨3413410448838647433250507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18204855727139452977336037 3413410448838647433250507)
              ·
                refine ⟨5120115673257971149875761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3413410448838647433250507 5120115673257971149875761)
                ·
                  refine ⟨3840086754943478362406821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5120115673257971149875761 3840086754943478362406821)
                  ·
                    refine ⟨720016266551902192951279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3840086754943478362406821 720016266551902192951279)
                    ·
                      rfl

theorem cell23_4206680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 2, 4].length) (baseStart_4206680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206680 prefixEnd_4206680 := by exact prefixLift 4206680
  have htrace : WordTrace (prefixWord ++ tailWord_4206680) baseStart_4206680 baseEnd_4206680 := by
    simpa [prefixWord, tailWord_4206680, baseEnd_4206680] using wordTrace_append hprefix tailTrace_4206680
  have hstable : (prefixWord ++ tailWord_4206680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206680).length < 2 ^ (prefixWord ++ tailWord_4206680).sum := by decide
  have hdescent : baseEnd_4206680 < baseStart_4206680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206703 : List Nat := [1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 3]
def baseStart_4206703 : Nat := 118140960795 + 4206703 * 2 ^ 59
def prefixEnd_4206703 : Nat := 4983230072969 + 3 ^ 40 * 4206703 * 2
def baseEnd_4206703 : Nat := 2160060609710759988866231

theorem tailTrace_4206703 : CollatzResearch.WordTrace tailWord_4206703 prefixEnd_4206703 2160060609710759988866231 := by
  unfold tailWord_4206703
  simp only [CollatzResearch.WordTrace]
  refine ⟨153431063278840953518968763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102287375519227302345979175 153431063278840953518968763)
  ·
    refine ⟨230146594918261430278453145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153431063278840953518968763 230146594918261430278453145)
    ·
      refine ⟨172609946188696072708839859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230146594918261430278453145 172609946188696072708839859)
      ·
        refine ⟨258914919283044109063259789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172609946188696072708839859 258914919283044109063259789)
        ·
          refine ⟨97093094731141540898722421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258914919283044109063259789 97093094731141540898722421)
          ·
            refine ⟨9102477631044519459255227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97093094731141540898722421 9102477631044519459255227)
            ·
              refine ⟨13653716446566779188882841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9102477631044519459255227 13653716446566779188882841)
              ·
                refine ⟨10240287334925084391662131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13653716446566779188882841 10240287334925084391662131)
                ·
                  refine ⟨15360431002387626587493197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10240287334925084391662131 15360431002387626587493197)
                  ·
                    refine ⟨5760161625895359970309949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15360431002387626587493197 5760161625895359970309949)
                    ·
                      refine ⟨2160060609710759988866231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5760161625895359970309949 2160060609710759988866231)
                      ·
                        rfl

theorem cell23_4206703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 3].length) (baseStart_4206703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206703 prefixEnd_4206703 := by exact prefixLift 4206703
  have htrace : WordTrace (prefixWord ++ tailWord_4206703) baseStart_4206703 baseEnd_4206703 := by
    simpa [prefixWord, tailWord_4206703, baseEnd_4206703] using wordTrace_append hprefix tailTrace_4206703
  have hstable : (prefixWord ++ tailWord_4206703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206703).length < 2 ^ (prefixWord ++ tailWord_4206703).sum := by decide
  have hdescent : baseEnd_4206703 < baseStart_4206703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206730 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 3, 3, 2]
def baseStart_4206730 : Nat := 118140960795 + 4206730 * 2 ^ 59
def prefixEnd_4206730 : Nat := 4983230072969 + 3 ^ 40 * 4206730 * 2
def baseEnd_4206730 : Nat := 2160074473688431383228607

theorem tailTrace_4206730 : CollatzResearch.WordTrace tailWord_4206730 prefixEnd_4206730 2160074473688431383228607 := by
  unfold tailWord_4206730
  simp only [CollatzResearch.WordTrace]
  refine ⟨38358012012435784282550411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102288032033162091420134429 38358012012435784282550411)
  ·
    refine ⟨57537018018653676423825617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38358012012435784282550411 57537018018653676423825617)
    ·
      refine ⟨43152763513990257317869213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57537018018653676423825617 43152763513990257317869213)
      ·
        refine ⟨16182286317746346494200955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43152763513990257317869213 16182286317746346494200955)
        ·
          refine ⟨24273429476619519741301433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16182286317746346494200955 24273429476619519741301433)
          ·
            refine ⟨18205072107464639805976075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24273429476619519741301433 18205072107464639805976075)
            ·
              refine ⟨27307608161196959708964113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18205072107464639805976075 27307608161196959708964113)
              ·
                refine ⟨20480706120897719781723085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27307608161196959708964113 20480706120897719781723085)
                ·
                  refine ⟨7680264795336644918146157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20480706120897719781723085 7680264795336644918146157)
                  ·
                    refine ⟨2880099298251241844304809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7680264795336644918146157 2880099298251241844304809)
                    ·
                      refine ⟨2160074473688431383228607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2880099298251241844304809 2160074473688431383228607)
                      ·
                        rfl

theorem cell23_4206730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_4206730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206730 prefixEnd_4206730 := by exact prefixLift 4206730
  have htrace : WordTrace (prefixWord ++ tailWord_4206730) baseStart_4206730 baseEnd_4206730 := by
    simpa [prefixWord, tailWord_4206730, baseEnd_4206730] using wordTrace_append hprefix tailTrace_4206730
  have hstable : (prefixWord ++ tailWord_4206730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206730).length < 2 ^ (prefixWord ++ tailWord_4206730).sum := by decide
  have hdescent : baseEnd_4206730 < baseStart_4206730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206736 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 2, 6]
def baseStart_4206736 : Nat := 118140960795 + 4206736 * 2 ^ 59
def prefixEnd_4206736 : Nat := 4983230072969 + 3 ^ 40 * 4206736 * 2
def baseEnd_4206736 : Nat := 720025851524119453251193

theorem tailTrace_4206736 : CollatzResearch.WordTrace tailWord_4206736 prefixEnd_4206736 720025851524119453251193 := by
  unfold tailWord_4206736
  simp only [CollatzResearch.WordTrace]
  refine ⟨76716133443860700077460031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102288177925147600103280041 76716133443860700077460031)
  ·
    refine ⟨115074200165791050116190047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76716133443860700077460031 115074200165791050116190047)
    ·
      refine ⟨172611300248686575174285071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115074200165791050116190047 172611300248686575174285071)
      ·
        refine ⟨258916950373029862761427607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172611300248686575174285071 258916950373029862761427607)
        ·
          refine ⟨388375425559544794142141411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258916950373029862761427607 388375425559544794142141411)
          ·
            refine ⟨582563138339317191213212117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388375425559544794142141411 582563138339317191213212117)
            ·
              refine ⟨13653823554827746669059659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 582563138339317191213212117 13653823554827746669059659)
              ·
                refine ⟨20480735332241620003589489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13653823554827746669059659 20480735332241620003589489)
                ·
                  refine ⟨15360551499181215002692117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20480735332241620003589489 15360551499181215002692117)
                  ·
                    refine ⟨720025851524119453251193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15360551499181215002692117 720025851524119453251193)
                    ·
                      rfl

theorem cell23_4206736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 2, 6].length) (baseStart_4206736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206736 prefixEnd_4206736 := by exact prefixLift 4206736
  have htrace : WordTrace (prefixWord ++ tailWord_4206736) baseStart_4206736 baseEnd_4206736 := by
    simpa [prefixWord, tailWord_4206736, baseEnd_4206736] using wordTrace_append hprefix tailTrace_4206736
  have hstable : (prefixWord ++ tailWord_4206736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206736).length < 2 ^ (prefixWord ++ tailWord_4206736).sum := by decide
  have hdescent : baseEnd_4206736 < baseStart_4206736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206794 : List Nat := [3, 1, 2, 1, 3, 1, 5, 1, 2, 2, 2]
def baseStart_4206794 : Nat := 118140960795 + 4206794 * 2 ^ 59
def prefixEnd_4206794 : Nat := 4983230072969 + 3 ^ 40 * 4206794 * 2
def baseEnd_4206794 : Nat := 2160107336450319132828313

theorem tailTrace_4206794 : CollatzResearch.WordTrace tailWord_4206794 prefixEnd_4206794 2160107336450319132828313 := by
  unfold tailWord_4206794
  simp only [CollatzResearch.WordTrace]
  refine ⟨38358595580377819015132859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102289588214340850707020957 38358595580377819015132859)
  ·
    refine ⟨57537893370566728522699289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38358595580377819015132859 57537893370566728522699289)
    ·
      refine ⟨43153420027925046392024467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57537893370566728522699289 43153420027925046392024467)
      ·
        refine ⟨64730130041887569588036701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43153420027925046392024467 64730130041887569588036701)
        ·
          refine ⟨24273798765707838595513763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64730130041887569588036701 24273798765707838595513763)
          ·
            refine ⟨36410698148561757893270645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24273798765707838595513763 36410698148561757893270645)
            ·
              refine ⟨3413502951427664802494123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36410698148561757893270645 3413502951427664802494123)
              ·
                refine ⟨5120254427141497203741185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3413502951427664802494123 5120254427141497203741185)
                ·
                  refine ⟨3840190820356122902805889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5120254427141497203741185 3840190820356122902805889)
                  ·
                    refine ⟨2880143115267092177104417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3840190820356122902805889 2880143115267092177104417)
                    ·
                      refine ⟨2160107336450319132828313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2880143115267092177104417 2160107336450319132828313)
                      ·
                        rfl

theorem cell23_4206794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_4206794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206794 prefixEnd_4206794 := by exact prefixLift 4206794
  have htrace : WordTrace (prefixWord ++ tailWord_4206794) baseStart_4206794 baseEnd_4206794 := by
    simpa [prefixWord, tailWord_4206794, baseEnd_4206794] using wordTrace_append hprefix tailTrace_4206794
  have hstable : (prefixWord ++ tailWord_4206794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206794).length < 2 ^ (prefixWord ++ tailWord_4206794).sum := by decide
  have hdescent : baseEnd_4206794 < baseStart_4206794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206833 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 4, 1, 4]
def baseStart_4206833 : Nat := 118140960795 + 4206833 * 2 ^ 59
def prefixEnd_4206833 : Nat := 4983230072969 + 3 ^ 40 * 4206833 * 2
def baseEnd_4206833 : Nat := 2160127362195844480240633

theorem tailTrace_4206833 : CollatzResearch.WordTrace tailWord_4206833 prefixEnd_4206833 2160127362195844480240633 := by
  unfold tailWord_4206833
  simp only [CollatzResearch.WordTrace]
  refine ⟨153435804768369985721201153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102290536512246657147467435 153435804768369985721201153)
  ·
    refine ⟨115076853576277489290900865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153435804768369985721201153 115076853576277489290900865)
    ·
      refine ⟨86307640182208116968175649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115076853576277489290900865 86307640182208116968175649)
      ·
        refine ⟨64730730136656087726131737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86307640182208116968175649 64730730136656087726131737)
        ·
          refine ⟨48548047602492065794598803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64730730136656087726131737 48548047602492065794598803)
          ·
            refine ⟨72822071403738098691898205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48548047602492065794598803 72822071403738098691898205)
            ·
              refine ⟨27308276776401787009461827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72822071403738098691898205 27308276776401787009461827)
              ·
                refine ⟨40962415164602680514192741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27308276776401787009461827 40962415164602680514192741)
                ·
                  refine ⟨7680452843363002596411139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40962415164602680514192741 7680452843363002596411139)
                  ·
                    refine ⟨11520679265044503894616709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7680452843363002596411139 11520679265044503894616709)
                    ·
                      refine ⟨2160127362195844480240633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11520679265044503894616709 2160127362195844480240633)
                      ·
                        rfl

theorem cell23_4206833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_4206833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206833 prefixEnd_4206833 := by exact prefixLift 4206833
  have htrace : WordTrace (prefixWord ++ tailWord_4206833) baseStart_4206833 baseEnd_4206833 := by
    simpa [prefixWord, tailWord_4206833, baseEnd_4206833] using wordTrace_append hprefix tailTrace_4206833
  have hstable : (prefixWord ++ tailWord_4206833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206833).length < 2 ^ (prefixWord ++ tailWord_4206833).sum := by decide
  have hdescent : baseEnd_4206833 < baseStart_4206833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206853 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 1, 4, 3]
def baseStart_4206853 : Nat := 118140960795 + 4206853 * 2 ^ 59
def prefixEnd_4206853 : Nat := 4983230072969 + 3 ^ 40 * 4206853 * 2
def baseEnd_4206853 : Nat := 2160137631808934401990541

theorem tailTrace_4206853 : CollatzResearch.WordTrace tailWord_4206853 prefixEnd_4206853 2160137631808934401990541 := by
  unfold tailWord_4206853
  simp only [CollatzResearch.WordTrace]
  refine ⟨153436534228297529136929213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102291022818865019424619475 153436534228297529136929213)
  ·
    refine ⟨57538700335611573426348455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153436534228297529136929213 57538700335611573426348455)
    ·
      refine ⟨86308050503417360139522683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57538700335611573426348455 86308050503417360139522683)
      ·
        refine ⟨129462075755126040209284025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86308050503417360139522683 129462075755126040209284025)
        ·
          refine ⟨97096556816344530156963019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129462075755126040209284025 97096556816344530156963019)
          ·
            refine ⟨145644835224516795235444529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97096556816344530156963019 145644835224516795235444529)
            ·
              refine ⟨109233626418387596426583397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145644835224516795235444529 109233626418387596426583397)
              ·
                refine ⟨20481304953447674329984387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109233626418387596426583397 20481304953447674329984387)
                ·
                  refine ⟨30721957430171511494976581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20481304953447674329984387 30721957430171511494976581)
                  ·
                    refine ⟨5760367018157158405308109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30721957430171511494976581 5760367018157158405308109)
                    ·
                      refine ⟨2160137631808934401990541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5760367018157158405308109 2160137631808934401990541)
                      ·
                        rfl

theorem cell23_4206853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_4206853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206853 prefixEnd_4206853 := by exact prefixLift 4206853
  have htrace : WordTrace (prefixWord ++ tailWord_4206853) baseStart_4206853 baseEnd_4206853 := by
    simpa [prefixWord, tailWord_4206853, baseEnd_4206853] using wordTrace_append hprefix tailTrace_4206853
  have hstable : (prefixWord ++ tailWord_4206853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206853).length < 2 ^ (prefixWord ++ tailWord_4206853).sum := by decide
  have hdescent : baseEnd_4206853 < baseStart_4206853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206953 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 1, 1, 6]
def baseStart_4206953 : Nat := 118140960795 + 4206953 * 2 ^ 59
def prefixEnd_4206953 : Nat := 4983230072969 + 3 ^ 40 * 4206953 * 2
def baseEnd_4206953 : Nat := 2160188979874384010740081

theorem tailTrace_4206953 : CollatzResearch.WordTrace tailWord_4206953 prefixEnd_4206953 2160188979874384010740081 := by
  unfold tailWord_4206953
  simp only [CollatzResearch.WordTrace]
  refine ⟨153440181527935246215569513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102293454351956830810379675 153440181527935246215569513)
  ·
    refine ⟨115080136145951434661677135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153440181527935246215569513 115080136145951434661677135)
    ·
      refine ⟨172620204218927151992515703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115080136145951434661677135 172620204218927151992515703)
      ·
        refine ⟨258930306328390727988773555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172620204218927151992515703 258930306328390727988773555)
        ·
          refine ⟨388395459492586091983160333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258930306328390727988773555 388395459492586091983160333)
          ·
            refine ⟨145648297309719784493685125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 388395459492586091983160333 145648297309719784493685125)
            ·
              refine ⟨27309055745572459592565961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145648297309719784493685125 27309055745572459592565961)
              ·
                refine ⟨20481791809179344694424471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27309055745572459592565961 20481791809179344694424471)
                ·
                  refine ⟨30722687713769017041636707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20481791809179344694424471 30722687713769017041636707)
                  ·
                    refine ⟨46084031570653525562455061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30722687713769017041636707 46084031570653525562455061)
                    ·
                      refine ⟨2160188979874384010740081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46084031570653525562455061 2160188979874384010740081)
                      ·
                        rfl

theorem cell23_4206953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_4206953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206953 prefixEnd_4206953 := by exact prefixLift 4206953
  have htrace : WordTrace (prefixWord ++ tailWord_4206953) baseStart_4206953 baseEnd_4206953 := by
    simpa [prefixWord, tailWord_4206953, baseEnd_4206953] using wordTrace_append hprefix tailTrace_4206953
  have hstable : (prefixWord ++ tailWord_4206953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206953).length < 2 ^ (prefixWord ++ tailWord_4206953).sum := by decide
  have hdescent : baseEnd_4206953 < baseStart_4206953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4206960 : List Nat := [2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 5]
def baseStart_4206960 : Nat := 118140960795 + 4206960 * 2 ^ 59
def prefixEnd_4206960 : Nat := 4983230072969 + 3 ^ 40 * 4206960 * 2
def baseEnd_4206960 : Nat := 2160192574238965483352549

theorem tailTrace_4206960 : CollatzResearch.WordTrace tailWord_4206960 prefixEnd_4206960 2160192574238965483352549 := by
  unfold tailWord_4206960
  simp only [CollatzResearch.WordTrace]
  refine ⟨76720218419454943205537167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102293624559273257607382889 76720218419454943205537167)
  ·
    refine ⟨115080327629182414808305751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76720218419454943205537167 115080327629182414808305751)
    ·
      refine ⟨172620491443773622212458627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115080327629182414808305751 172620491443773622212458627)
      ·
        refine ⟨258930737165660433318687941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172620491443773622212458627 258930737165660433318687941)
        ·
          refine ⟨48549513218561331247253989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 258930737165660433318687941 48549513218561331247253989)
          ·
            refine ⟨9103033728480249608860123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48549513218561331247253989 9103033728480249608860123)
            ·
              refine ⟨13654550592720374413290185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9103033728480249608860123 13654550592720374413290185)
              ·
                refine ⟨10240912944540280809967639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13654550592720374413290185 10240912944540280809967639)
                ·
                  refine ⟨15361369416810421214951459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10240912944540280809967639 15361369416810421214951459)
                  ·
                    refine ⟨23042054125215631822427189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15361369416810421214951459 23042054125215631822427189)
                    ·
                      refine ⟨2160192574238965483352549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23042054125215631822427189 2160192574238965483352549)
                      ·
                        rfl

theorem cell23_4206960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 5].length) (baseStart_4206960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4206960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4206960 prefixEnd_4206960 := by exact prefixLift 4206960
  have htrace : WordTrace (prefixWord ++ tailWord_4206960) baseStart_4206960 baseEnd_4206960 := by
    simpa [prefixWord, tailWord_4206960, baseEnd_4206960] using wordTrace_append hprefix tailTrace_4206960
  have hstable : (prefixWord ++ tailWord_4206960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4206960).length < 2 ^ (prefixWord ++ tailWord_4206960).sum := by decide
  have hdescent : baseEnd_4206960 < baseStart_4206960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4206960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207007 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 4, 1, 3]
def baseStart_4207007 : Nat := 118140960795 + 4207007 * 2 ^ 59
def prefixEnd_4207007 : Nat := 4983230072969 + 3 ^ 40 * 4207007 * 2
def baseEnd_4207007 : Nat := 2160216707829726799464833

theorem tailTrace_4207007 : CollatzResearch.WordTrace tailWord_4207007 prefixEnd_4207007 2160216707829726799464833 := by
  unfold tailWord_4207007
  simp only [CollatzResearch.WordTrace]
  refine ⟨153442151069739613438035275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102294767379826408958690183 153442151069739613438035275)
  ·
    refine ⟨230163226604609420157052913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153442151069739613438035275 230163226604609420157052913)
    ·
      refine ⟨172622419953457065117789685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230163226604609420157052913 172622419953457065117789685)
      ·
        refine ⟨16183351870636599854792783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 172622419953457065117789685 16183351870636599854792783)
        ·
          refine ⟨24275027805954899782189175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16183351870636599854792783 24275027805954899782189175)
          ·
            refine ⟨36412541708932349673283763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24275027805954899782189175 36412541708932349673283763)
            ·
              refine ⟨54618812563398524509925645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36412541708932349673283763 54618812563398524509925645)
              ·
                refine ⟨20482054711274446691222117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54618812563398524509925645 20482054711274446691222117)
                ·
                  refine ⟨3840385258363958754604147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20482054711274446691222117 3840385258363958754604147)
                  ·
                    refine ⟨5760577887545938131906221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3840385258363958754604147 5760577887545938131906221)
                    ·
                      refine ⟨2160216707829726799464833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5760577887545938131906221 2160216707829726799464833)
                      ·
                        rfl

theorem cell23_4207007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_4207007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207007 prefixEnd_4207007 := by exact prefixLift 4207007
  have htrace : WordTrace (prefixWord ++ tailWord_4207007) baseStart_4207007 baseEnd_4207007 := by
    simpa [prefixWord, tailWord_4207007, baseEnd_4207007] using wordTrace_append hprefix tailTrace_4207007
  have hstable : (prefixWord ++ tailWord_4207007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207007).length < 2 ^ (prefixWord ++ tailWord_4207007).sum := by decide
  have hdescent : baseEnd_4207007 < baseStart_4207007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207008 : List Nat := [2, 1, 1, 4, 1, 4, 3, 2, 1, 2, 2]
def baseStart_4207008 : Nat := 118140960795 + 4207008 * 2 ^ 59
def prefixEnd_4207008 : Nat := 4983230072969 + 3 ^ 40 * 4207008 * 2
def baseEnd_4207008 : Nat := 2160217221310381295552329

theorem tailTrace_4207008 : CollatzResearch.WordTrace tailWord_4207008 prefixEnd_4207008 2160217221310381295552329 := by
  unfold tailWord_4207008
  simp only [CollatzResearch.WordTrace]
  refine ⟨76721093771367995304410839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102294791695157327072547785 76721093771367995304410839)
  ·
    refine ⟨115081640657051992956616259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76721093771367995304410839 115081640657051992956616259)
    ·
      refine ⟨172622460985577989434924389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115081640657051992956616259 172622460985577989434924389)
      ·
        refine ⟨32366711434795873019048323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172622460985577989434924389 32366711434795873019048323)
        ·
          refine ⟨48550067152193809528572485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32366711434795873019048323 48550067152193809528572485)
          ·
            refine ⟨9103137591036339286607341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48550067152193809528572485 9103137591036339286607341)
            ·
              refine ⟨3413676596638627232477753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9103137591036339286607341 3413676596638627232477753)
              ·
                refine ⟨2560257447478970424358315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3413676596638627232477753 2560257447478970424358315)
                ·
                  refine ⟨3840386171218455636537473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2560257447478970424358315 3840386171218455636537473)
                  ·
                    refine ⟨2880289628413841727403105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3840386171218455636537473 2880289628413841727403105)
                    ·
                      refine ⟨2160217221310381295552329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2880289628413841727403105 2160217221310381295552329)
                      ·
                        rfl

theorem cell23_4207008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_4207008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207008 prefixEnd_4207008 := by exact prefixLift 4207008
  have htrace : WordTrace (prefixWord ++ tailWord_4207008) baseStart_4207008 baseEnd_4207008 := by
    simpa [prefixWord, tailWord_4207008, baseEnd_4207008] using wordTrace_append hprefix tailTrace_4207008
  have hstable : (prefixWord ++ tailWord_4207008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207008).length < 2 ^ (prefixWord ++ tailWord_4207008).sum := by decide
  have hdescent : baseEnd_4207008 < baseStart_4207008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207010 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_4207010 : Nat := 118140960795 + 4207010 * 2 ^ 59
def prefixEnd_4207010 : Nat := 4983230072969 + 3 ^ 40 * 4207010 * 2
def baseEnd_4207010 : Nat := 720072749423896762575773

theorem tailTrace_4207010 : CollatzResearch.WordTrace tailWord_4207010 prefixEnd_4207010 720072749423896762575773 := by
  unfold tailWord_4207010
  simp only [CollatzResearch.WordTrace]
  refine ⟨38360565122182186237598621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102294840325819163300262989 38360565122182186237598621)
  ·
    refine ⟨14385211920818319839099483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38360565122182186237598621 14385211920818319839099483)
    ·
      refine ⟨21577817881227479758649225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14385211920818319839099483 21577817881227479758649225)
      ·
        refine ⟨16183363410920609818986919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21577817881227479758649225 16183363410920609818986919)
        ·
          refine ⟨24275045116380914728480379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16183363410920609818986919 24275045116380914728480379)
          ·
            refine ⟨36412567674571372092720569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24275045116380914728480379 36412567674571372092720569)
            ·
              refine ⟨27309425755928529069540427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36412567674571372092720569 27309425755928529069540427)
              ·
                refine ⟨40964138633892793604310641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27309425755928529069540427 40964138633892793604310641)
                ·
                  refine ⟨30723103975419595203232981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40964138633892793604310641 30723103975419595203232981)
                  ·
                    refine ⟨720072749423896762575773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30723103975419595203232981 720072749423896762575773)
                    ·
                      rfl

theorem cell23_4207010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_4207010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207010 prefixEnd_4207010 := by exact prefixLift 4207010
  have htrace : WordTrace (prefixWord ++ tailWord_4207010) baseStart_4207010 baseEnd_4207010 := by
    simpa [prefixWord, tailWord_4207010, baseEnd_4207010] using wordTrace_append hprefix tailTrace_4207010
  have hstable : (prefixWord ++ tailWord_4207010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207010).length < 2 ^ (prefixWord ++ tailWord_4207010).sum := by decide
  have hdescent : baseEnd_4207010 < baseStart_4207010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207018 : List Nat := [3, 1, 6, 1, 1, 1, 1, 3, 2, 4]
def baseStart_4207018 : Nat := 118140960795 + 4207018 * 2 ^ 59
def prefixEnd_4207018 : Nat := 4983230072969 + 3 ^ 40 * 4207018 * 2
def baseEnd_4207018 : Nat := 720074118705642085475761

theorem tailTrace_4207018 : CollatzResearch.WordTrace tailWord_4207018 prefixEnd_4207018 720074118705642085475761 := by
  unfold tailWord_4207018
  simp only [CollatzResearch.WordTrace]
  refine ⟨38360638068174940579171427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102295034848466508211123805 38360638068174940579171427)
  ·
    refine ⟨57540957102262410868757141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38360638068174940579171427 57540957102262410868757141)
    ·
      refine ⟨2697232364168550509472991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57540957102262410868757141 2697232364168550509472991)
      ·
        refine ⟨4045848546252825764209487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2697232364168550509472991 4045848546252825764209487)
        ·
          refine ⟨6068772819379238646314231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4045848546252825764209487 6068772819379238646314231)
          ·
            refine ⟨9103159229068857969471347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6068772819379238646314231 9103159229068857969471347)
            ·
              refine ⟨13654738843603286954207021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9103159229068857969471347 13654738843603286954207021)
              ·
                refine ⟨5120527066351232607827633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13654738843603286954207021 5120527066351232607827633)
                ·
                  refine ⟨3840395299763424455870725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5120527066351232607827633 3840395299763424455870725)
                  ·
                    refine ⟨720074118705642085475761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3840395299763424455870725 720074118705642085475761)
                    ·
                      rfl

theorem cell23_4207018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_4207018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207018 prefixEnd_4207018 := by exact prefixLift 4207018
  have htrace : WordTrace (prefixWord ++ tailWord_4207018) baseStart_4207018 baseEnd_4207018 := by
    simpa [prefixWord, tailWord_4207018, baseEnd_4207018] using wordTrace_append hprefix tailTrace_4207018
  have hstable : (prefixWord ++ tailWord_4207018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207018).length < 2 ^ (prefixWord ++ tailWord_4207018).sum := by decide
  have hdescent : baseEnd_4207018 < baseStart_4207018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207047 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 3, 4, 2]
def baseStart_4207047 : Nat := 118140960795 + 4207047 * 2 ^ 59
def prefixEnd_4207047 : Nat := 4983230072969 + 3 ^ 40 * 4207047 * 2
def baseEnd_4207047 : Nat := 2160237247055906642964649

theorem tailTrace_4207047 : CollatzResearch.WordTrace tailWord_4207047 prefixEnd_4207047 2160237247055906642964649 := by
  unfold tailWord_4207047
  simp only [CollatzResearch.WordTrace]
  refine ⟨153443609989594700269491395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102295739993063133512994263 153443609989594700269491395)
  ·
    refine ⟨230165414984392050404237093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153443609989594700269491395 230165414984392050404237093)
    ·
      refine ⟨43156015309573509450794455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230165414984392050404237093 43156015309573509450794455)
      ·
        refine ⟨64734022964360264176191683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43156015309573509450794455 64734022964360264176191683)
        ·
          refine ⟨97101034446540396264287525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64734022964360264176191683 97101034446540396264287525)
          ·
            refine ⟨18206443958726324299553911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97101034446540396264287525 18206443958726324299553911)
            ·
              refine ⟨27309665938089486449330867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18206443958726324299553911 27309665938089486449330867)
              ·
                refine ⟨40964498907134229673996301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27309665938089486449330867 40964498907134229673996301)
                ·
                  refine ⟨15361687090175336127748613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40964498907134229673996301 15361687090175336127748613)
                  ·
                    refine ⟨2880316329407875523952865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15361687090175336127748613 2880316329407875523952865)
                    ·
                      refine ⟨2160237247055906642964649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2880316329407875523952865 2160237247055906642964649)
                      ·
                        rfl

theorem cell23_4207047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_4207047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207047 prefixEnd_4207047 := by exact prefixLift 4207047
  have htrace : WordTrace (prefixWord ++ tailWord_4207047) baseStart_4207047 baseEnd_4207047 := by
    simpa [prefixWord, tailWord_4207047, baseEnd_4207047] using wordTrace_append hprefix tailTrace_4207047
  have hstable : (prefixWord ++ tailWord_4207047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207047).length < 2 ^ (prefixWord ++ tailWord_4207047).sum := by decide
  have hdescent : baseEnd_4207047 < baseStart_4207047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207050 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_4207050 : Nat := 118140960795 + 4207050 * 2 ^ 59
def prefixEnd_4207050 : Nat := 4983230072969 + 3 ^ 40 * 4207050 * 2
def baseEnd_4207050 : Nat := 2160238787497870131227135

theorem tailTrace_4207050 : CollatzResearch.WordTrace tailWord_4207050 prefixEnd_4207050 2160238787497870131227135 := by
  unfold tailWord_4207050
  simp only [CollatzResearch.WordTrace]
  refine ⟨38360929852145957945462651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102295812939055887854567069 38360929852145957945462651)
  ·
    refine ⟨57541394778218936918193977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38360929852145957945462651 57541394778218936918193977)
    ·
      refine ⟨43156046083664202688645483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57541394778218936918193977 43156046083664202688645483)
      ·
        refine ⟨64734069125496304032968225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43156046083664202688645483 64734069125496304032968225)
        ·
          refine ⟨48550551844122228024726169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64734069125496304032968225 48550551844122228024726169)
          ·
            refine ⟨36412913883091671018544627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48550551844122228024726169 36412913883091671018544627)
            ·
              refine ⟨54619370824637506527816941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36412913883091671018544627 54619370824637506527816941)
              ·
                refine ⟨20482264059239064947931353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54619370824637506527816941 20482264059239064947931353)
                ·
                  refine ⟨15361698044429298710948515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20482264059239064947931353 15361698044429298710948515)
                  ·
                    refine ⟨23042547066643948066422773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15361698044429298710948515 23042547066643948066422773)
                    ·
                      refine ⟨2160238787497870131227135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23042547066643948066422773 2160238787497870131227135)
                      ·
                        rfl

theorem cell23_4207050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_4207050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207050 prefixEnd_4207050 := by exact prefixLift 4207050
  have htrace : WordTrace (prefixWord ++ tailWord_4207050) baseStart_4207050 baseEnd_4207050 := by
    simpa [prefixWord, tailWord_4207050, baseEnd_4207050] using wordTrace_append hprefix tailTrace_4207050
  have hstable : (prefixWord ++ tailWord_4207050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207050).length < 2 ^ (prefixWord ++ tailWord_4207050).sum := by decide
  have hdescent : baseEnd_4207050 < baseStart_4207050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207058 : List Nat := [3, 2, 2, 4, 1, 1, 2, 2, 2, 1, 3]
def baseStart_4207058 : Nat := 118140960795 + 4207058 * 2 ^ 59
def prefixEnd_4207058 : Nat := 4983230072969 + 3 ^ 40 * 4207058 * 2
def baseEnd_4207058 : Nat := 2160242895343106099927099

theorem tailTrace_4207058 : CollatzResearch.WordTrace tailWord_4207058 prefixEnd_4207058 2160242895343106099927099 := by
  unfold tailWord_4207058
  simp only [CollatzResearch.WordTrace]
  refine ⟨38361002798138712287035457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102296007461703232765427885 38361002798138712287035457)
  ·
    refine ⟨28770752098604034215276593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38361002798138712287035457 28770752098604034215276593)
    ·
      refine ⟨21578064073953025661457445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28770752098604034215276593 21578064073953025661457445)
      ·
        refine ⟨4045887013866192311523271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21578064073953025661457445 4045887013866192311523271)
        ·
          refine ⟨6068830520799288467284907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4045887013866192311523271 6068830520799288467284907)
          ·
            refine ⟨9103245781198932700927361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6068830520799288467284907 9103245781198932700927361)
            ·
              refine ⟨6827434335899199525695521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9103245781198932700927361 6827434335899199525695521)
              ·
                refine ⟨5120575751924399644271641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6827434335899199525695521 5120575751924399644271641)
                ·
                  refine ⟨3840431813943299733203731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5120575751924399644271641 3840431813943299733203731)
                  ·
                    refine ⟨5760647720914949599805597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3840431813943299733203731 5760647720914949599805597)
                    ·
                      refine ⟨2160242895343106099927099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5760647720914949599805597 2160242895343106099927099)
                      ·
                        rfl

theorem cell23_4207058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_4207058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207058 prefixEnd_4207058 := by exact prefixLift 4207058
  have htrace : WordTrace (prefixWord ++ tailWord_4207058) baseStart_4207058 baseEnd_4207058 := by
    simpa [prefixWord, tailWord_4207058, baseEnd_4207058] using wordTrace_append hprefix tailTrace_4207058
  have hstable : (prefixWord ++ tailWord_4207058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207058).length < 2 ^ (prefixWord ++ tailWord_4207058).sum := by decide
  have hdescent : baseEnd_4207058 < baseStart_4207058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207157 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_4207157 : Nat := 118140960795 + 4207157 * 2 ^ 59
def prefixEnd_4207157 : Nat := 4983230072969 + 3 ^ 40 * 4207157 * 2
def baseEnd_4207157 : Nat := 2160293729927901212589143

theorem tailTrace_4207157 : CollatzResearch.WordTrace tailWord_4207157 prefixEnd_4207157 2160293729927901212589143 := by
  unfold tailWord_4207157
  simp only [CollatzResearch.WordTrace]
  refine ⟨153447622019196189055995725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102298414679464126037330483 153447622019196189055995725)
  ·
    refine ⟨57542858257198570895998397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153447622019196189055995725 57542858257198570895998397)
    ·
      refine ⟨21578571846449464085999399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57542858257198570895998397 21578571846449464085999399)
      ·
        refine ⟨32367857769674196128999099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21578571846449464085999399 32367857769674196128999099)
        ·
          refine ⟨48551786654511294193498649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32367857769674196128999099 48551786654511294193498649)
          ·
            refine ⟨36413839990883470645123987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48551786654511294193498649 36413839990883470645123987)
            ·
              refine ⟨54620759986325205967685981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36413839990883470645123987 54620759986325205967685981)
              ·
                refine ⟨20482784994871952237882243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54620759986325205967685981 20482784994871952237882243)
                ·
                  refine ⟨30724177492307928356823365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20482784994871952237882243 30724177492307928356823365)
                  ·
                    refine ⟨5760783279807736566904381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30724177492307928356823365 5760783279807736566904381)
                    ·
                      refine ⟨2160293729927901212589143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5760783279807736566904381 2160293729927901212589143)
                      ·
                        rfl

theorem cell23_4207157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_4207157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207157 prefixEnd_4207157 := by exact prefixLift 4207157
  have htrace : WordTrace (prefixWord ++ tailWord_4207157) baseStart_4207157 baseEnd_4207157 := by
    simpa [prefixWord, tailWord_4207157, baseEnd_4207157] using wordTrace_append hprefix tailTrace_4207157
  have hstable : (prefixWord ++ tailWord_4207157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207157).length < 2 ^ (prefixWord ++ tailWord_4207157).sum := by decide
  have hdescent : baseEnd_4207157 < baseStart_4207157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207160 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 10]
def baseStart_4207160 : Nat := 118140960795 + 4207160 * 2 ^ 59
def prefixEnd_4207160 : Nat := 4983230072969 + 3 ^ 40 * 4207160 * 2
def baseEnd_4207160 : Nat := 240032807818873855650181

theorem tailTrace_4207160 : CollatzResearch.WordTrace tailWord_4207160 prefixEnd_4207160 240032807818873855650181 := by
  unfold tailWord_4207160
  simp only [CollatzResearch.WordTrace]
  refine ⟨76723865719092660284177467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102298487625456880378903289 76723865719092660284177467)
  ·
    refine ⟨115085798578638990426266201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76723865719092660284177467 115085798578638990426266201)
    ·
      refine ⟨86314348933979242819699651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115085798578638990426266201 86314348933979242819699651)
      ·
        refine ⟨129471523400968864229549477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86314348933979242819699651 129471523400968864229549477)
        ·
          refine ⟨24275910637681662043040527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129471523400968864229549477 24275910637681662043040527)
          ·
            refine ⟨36413865956522493064560791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24275910637681662043040527 36413865956522493064560791)
            ·
              refine ⟨54620798934783739596841187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36413865956522493064560791 54620798934783739596841187)
              ·
                refine ⟨81931198402175609395261781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54620798934783739596841187 81931198402175609395261781)
                ·
                  refine ⟨240032807818873855650181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 81931198402175609395261781 240032807818873855650181)
                  ·
                    rfl

theorem cell23_4207160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 10].length) (baseStart_4207160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207160 prefixEnd_4207160 := by exact prefixLift 4207160
  have htrace : WordTrace (prefixWord ++ tailWord_4207160) baseStart_4207160 baseEnd_4207160 := by
    simpa [prefixWord, tailWord_4207160, baseEnd_4207160] using wordTrace_append hprefix tailTrace_4207160
  have hstable : (prefixWord ++ tailWord_4207160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207160).length < 2 ^ (prefixWord ++ tailWord_4207160).sum := by decide
  have hdescent : baseEnd_4207160 < baseStart_4207160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207181 : List Nat := [1, 6, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_4207181 : Nat := 118140960795 + 4207181 * 2 ^ 59
def prefixEnd_4207181 : Nat := 4983230072969 + 3 ^ 40 * 4207181 * 2
def baseEnd_4207181 : Nat := 720102017821203039563011

theorem tailTrace_4207181 : CollatzResearch.WordTrace tailWord_4207181 prefixEnd_4207181 720102017821203039563011 := by
  unfold tailWord_4207181
  simp only [CollatzResearch.WordTrace]
  refine ⟨153448497371109241154869397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102298998247406160769912931 153448497371109241154869397)
  ·
    refine ⟨7192898314270745679134503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 153448497371109241154869397 7192898314270745679134503)
    ·
      refine ⟨10789347471406118518701755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7192898314270745679134503 10789347471406118518701755)
      ·
        refine ⟨16184021207109177778052633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10789347471406118518701755 16184021207109177778052633)
        ·
          refine ⟨12138015905331883333539475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16184021207109177778052633 12138015905331883333539475)
          ·
            refine ⟨18207023857997825000309213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12138015905331883333539475 18207023857997825000309213)
            ·
              refine ⟨6827633946749184375115955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18207023857997825000309213 6827633946749184375115955)
              ·
                refine ⟨10241450920123776562673933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6827633946749184375115955 10241450920123776562673933)
                ·
                  refine ⟨3840544095046416211002725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10241450920123776562673933 3840544095046416211002725)
                  ·
                    refine ⟨720102017821203039563011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3840544095046416211002725 720102017821203039563011)
                    ·
                      rfl

theorem cell23_4207181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_4207181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207181 prefixEnd_4207181 := by exact prefixLift 4207181
  have htrace : WordTrace (prefixWord ++ tailWord_4207181) baseStart_4207181 baseEnd_4207181 := by
    simpa [prefixWord, tailWord_4207181, baseEnd_4207181] using wordTrace_append hprefix tailTrace_4207181
  have hstable : (prefixWord ++ tailWord_4207181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207181).length < 2 ^ (prefixWord ++ tailWord_4207181).sum := by decide
  have hdescent : baseEnd_4207181 < baseStart_4207181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207204 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 5, 1, 3]
def baseStart_4207204 : Nat := 118140960795 + 4207204 * 2 ^ 59
def prefixEnd_4207204 : Nat := 4983230072969 + 3 ^ 40 * 4207204 * 2
def baseEnd_4207204 : Nat := 2160317863518662528701427

theorem tailTrace_4207204 : CollatzResearch.WordTrace tailWord_4207204 prefixEnd_4207204 2160317863518662528701427 := by
  unfold tailWord_4207204
  simp only [CollatzResearch.WordTrace]
  refine ⟨76724668125012958041478333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102299557500017277388637777 76724668125012958041478333)
  ·
    refine ⟨28771750546879859265554375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76724668125012958041478333 28771750546879859265554375)
    ·
      refine ⟨43157625820319788898331563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28771750546879859265554375 43157625820319788898331563)
      ·
        refine ⟨64736438730479683347497345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43157625820319788898331563 64736438730479683347497345)
        ·
          refine ⟨48552329047859762510623009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64736438730479683347497345 48552329047859762510623009)
          ·
            refine ⟨36414246785894821882967257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48552329047859762510623009 36414246785894821882967257)
            ·
              refine ⟨27310685089421116412225443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36414246785894821882967257 27310685089421116412225443)
              ·
                refine ⟨40966027634131674618338165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27310685089421116412225443 40966027634131674618338165)
                ·
                  refine ⟨3840565090699844495469203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40966027634131674618338165 3840565090699844495469203)
                  ·
                    refine ⟨5760847636049766743203805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3840565090699844495469203 5760847636049766743203805)
                    ·
                      refine ⟨2160317863518662528701427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5760847636049766743203805 2160317863518662528701427)
                      ·
                        rfl

theorem cell23_4207204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_4207204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207204 prefixEnd_4207204 := by exact prefixLift 4207204
  have htrace : WordTrace (prefixWord ++ tailWord_4207204) baseStart_4207204 baseEnd_4207204 := by
    simpa [prefixWord, tailWord_4207204, baseEnd_4207204] using wordTrace_append hprefix tailTrace_4207204
  have hstable : (prefixWord ++ tailWord_4207204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207204).length < 2 ^ (prefixWord ++ tailWord_4207204).sum := by decide
  have hdescent : baseEnd_4207204 < baseStart_4207204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207261 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 5, 2, 2]
def baseStart_4207261 : Nat := 118140960795 + 4207261 * 2 ^ 59
def prefixEnd_4207261 : Nat := 4983230072969 + 3 ^ 40 * 4207261 * 2
def baseEnd_4207261 : Nat := 2160347131915968805688665

theorem tailTrace_4207261 : CollatzResearch.WordTrace tailWord_4207261 prefixEnd_4207261 2160347131915968805688665 := by
  unfold tailWord_4207261
  simp only [CollatzResearch.WordTrace]
  refine ⟨153451415210819414817781637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102300943473879609878521091 153451415210819414817781637)
  ·
    refine ⟨28772140352028640278334057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153451415210819414817781637 28772140352028640278334057)
    ·
      refine ⟨21579105264021480208750543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28772140352028640278334057 21579105264021480208750543)
      ·
        refine ⟨32368657896032220313125815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21579105264021480208750543 32368657896032220313125815)
        ·
          refine ⟨48552986844048330469688723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32368657896032220313125815 48552986844048330469688723)
          ·
            refine ⟨72829480266072495704533085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48552986844048330469688723 72829480266072495704533085)
            ·
              refine ⟨27311055099777185889199907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72829480266072495704533085 27311055099777185889199907)
              ·
                refine ⟨40966582649665778833799861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27311055099777185889199907 40966582649665778833799861)
                ·
                  refine ⟨3840617123406166765668737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40966582649665778833799861 3840617123406166765668737)
                  ·
                    refine ⟨2880462842554625074251553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3840617123406166765668737 2880462842554625074251553)
                    ·
                      refine ⟨2160347131915968805688665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2880462842554625074251553 2160347131915968805688665)
                      ·
                        rfl

theorem cell23_4207261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_4207261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207261 prefixEnd_4207261 := by exact prefixLift 4207261
  have htrace : WordTrace (prefixWord ++ tailWord_4207261) baseStart_4207261 baseEnd_4207261 := by
    simpa [prefixWord, tailWord_4207261, baseEnd_4207261] using wordTrace_append hprefix tailTrace_4207261
  have hstable : (prefixWord ++ tailWord_4207261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207261).length < 2 ^ (prefixWord ++ tailWord_4207261).sum := by decide
  have hdescent : baseEnd_4207261 < baseStart_4207261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207265 : List Nat := [1, 2, 3, 3, 4, 1, 1, 1, 2, 3, 2]
def baseStart_4207265 : Nat := 118140960795 + 4207265 * 2 ^ 59
def prefixEnd_4207265 : Nat := 4983230072969 + 3 ^ 40 * 4207265 * 2
def baseEnd_4207265 : Nat := 2160349185838586790038647

theorem tailTrace_4207265 : CollatzResearch.WordTrace tailWord_4207265 prefixEnd_4207265 2160349185838586790038647 := by
  unfold tailWord_4207265
  simp only [CollatzResearch.WordTrace]
  refine ⟨153451561102804923500927249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102301040735203282333951499 153451561102804923500927249)
  ·
    refine ⟨115088670827103692625695437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153451561102804923500927249 115088670827103692625695437)
    ·
      refine ⟨43158251560163884734635789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115088670827103692625695437 43158251560163884734635789)
      ·
        refine ⟨16184344335061456775488421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43158251560163884734635789 16184344335061456775488421)
        ·
          refine ⟨3034564562824023145404079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16184344335061456775488421 3034564562824023145404079)
          ·
            refine ⟨4551846844236034718106119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3034564562824023145404079 4551846844236034718106119)
            ·
              refine ⟨6827770266354052077159179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4551846844236034718106119 6827770266354052077159179)
              ·
                refine ⟨10241655399531078115738769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6827770266354052077159179 10241655399531078115738769)
                ·
                  refine ⟨7681241549648308586804077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10241655399531078115738769 7681241549648308586804077)
                  ·
                    refine ⟨2880465581118115720051529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7681241549648308586804077 2880465581118115720051529)
                    ·
                      refine ⟨2160349185838586790038647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2880465581118115720051529 2160349185838586790038647)
                      ·
                        rfl

theorem cell23_4207265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_4207265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207265 prefixEnd_4207265 := by exact prefixLift 4207265
  have htrace : WordTrace (prefixWord ++ tailWord_4207265) baseStart_4207265 baseEnd_4207265 := by
    simpa [prefixWord, tailWord_4207265, baseEnd_4207265] using wordTrace_append hprefix tailTrace_4207265
  have hstable : (prefixWord ++ tailWord_4207265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207265).length < 2 ^ (prefixWord ++ tailWord_4207265).sum := by decide
  have hdescent : baseEnd_4207265 < baseStart_4207265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207278 : List Nat := [4, 1, 4, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_4207278 : Nat := 118140960795 + 4207278 * 2 ^ 59
def prefixEnd_4207278 : Nat := 4983230072969 + 3 ^ 40 * 4207278 * 2
def baseEnd_4207278 : Nat := 2160355861087095239176087

theorem tailTrace_4207278 : CollatzResearch.WordTrace tailWord_4207278 prefixEnd_4207278 2160355861087095239176087 := by
  unfold tailWord_4207278
  simp only [CollatzResearch.WordTrace]
  refine ⟨19181504406469728340143811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102301356834505217814100325 19181504406469728340143811)
  ·
    refine ⟨28772256609704592510215717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19181504406469728340143811 28772256609704592510215717)
    ·
      refine ⟨5394798114319611095665447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28772256609704592510215717 5394798114319611095665447)
      ·
        refine ⟨8092197171479416643498171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5394798114319611095665447 8092197171479416643498171)
        ·
          refine ⟨12138295757219124965247257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8092197171479416643498171 12138295757219124965247257)
          ·
            refine ⟨9103721817914343723935443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12138295757219124965247257 9103721817914343723935443)
            ·
              refine ⟨13655582726871515585903165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9103721817914343723935443 13655582726871515585903165)
              ·
                refine ⟨5120843522576818344713687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13655582726871515585903165 5120843522576818344713687)
                ·
                  refine ⟨7681265283865227517070531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5120843522576818344713687 7681265283865227517070531)
                  ·
                    refine ⟨11521897925797841275605797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7681265283865227517070531 11521897925797841275605797)
                    ·
                      refine ⟨2160355861087095239176087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11521897925797841275605797 2160355861087095239176087)
                      ·
                        rfl

theorem cell23_4207278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_4207278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207278 prefixEnd_4207278 := by exact prefixLift 4207278
  have htrace : WordTrace (prefixWord ++ tailWord_4207278) baseStart_4207278 baseEnd_4207278 := by
    simpa [prefixWord, tailWord_4207278, baseEnd_4207278] using wordTrace_append hprefix tailTrace_4207278
  have hstable : (prefixWord ++ tailWord_4207278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207278).length < 2 ^ (prefixWord ++ tailWord_4207278).sum := by decide
  have hdescent : baseEnd_4207278 < baseStart_4207278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207337 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 1, 3, 5]
def baseStart_4207337 : Nat := 118140960795 + 4207337 * 2 ^ 59
def prefixEnd_4207337 : Nat := 4983230072969 + 3 ^ 40 * 4207337 * 2
def baseEnd_4207337 : Nat := 2160386156445710508338315

theorem tailTrace_4207337 : CollatzResearch.WordTrace tailWord_4207337 prefixEnd_4207337 2160386156445710508338315 := by
  unfold tailWord_4207337
  simp only [CollatzResearch.WordTrace]
  refine ⟨153454187158544079797548265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102302791439029386531698843 153454187158544079797548265)
  ·
    refine ⟨115090640368908059848161199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153454187158544079797548265 115090640368908059848161199)
    ·
      refine ⟨172635960553362089772241799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115090640368908059848161199 172635960553362089772241799)
      ·
        refine ⟨258953940830043134658362699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172635960553362089772241799 258953940830043134658362699)
        ·
          refine ⟨388430911245064701987544049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258953940830043134658362699 388430911245064701987544049)
          ·
            refine ⟨291323183433798526490658037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 388430911245064701987544049 291323183433798526490658037)
            ·
              refine ⟨27311548446918611858499191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 291323183433798526490658037 27311548446918611858499191)
              ·
                refine ⟨40967322670377917787748787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27311548446918611858499191 40967322670377917787748787)
                ·
                  refine ⟨61450984005566876681623181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40967322670377917787748787 61450984005566876681623181)
                  ·
                    refine ⟨23044119002087578755608693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61450984005566876681623181 23044119002087578755608693)
                    ·
                      refine ⟨2160386156445710508338315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23044119002087578755608693 2160386156445710508338315)
                      ·
                        rfl

theorem cell23_4207337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_4207337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207337 prefixEnd_4207337 := by exact prefixLift 4207337
  have htrace : WordTrace (prefixWord ++ tailWord_4207337) baseStart_4207337 baseEnd_4207337 := by
    simpa [prefixWord, tailWord_4207337, baseEnd_4207337] using wordTrace_append hprefix tailTrace_4207337
  have hstable : (prefixWord ++ tailWord_4207337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207337).length < 2 ^ (prefixWord ++ tailWord_4207337).sum := by decide
  have hdescent : baseEnd_4207337 < baseStart_4207337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207362 : List Nat := [3, 4, 1, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_4207362 : Nat := 118140960795 + 4207362 * 2 ^ 59
def prefixEnd_4207362 : Nat := 4983230072969 + 3 ^ 40 * 4207362 * 2
def baseEnd_4207362 : Nat := 2160398993462072910525701

theorem tailTrace_4207362 : CollatzResearch.WordTrace tailWord_4207362 prefixEnd_4207362 2160398993462072910525701 := by
  unfold tailWord_4207362
  simp only [CollatzResearch.WordTrace]
  refine ⟨38363774745863377266802085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102303399322302339378138893 38363774745863377266802085)
  ·
    refine ⟨7193207764849383237525391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38363774745863377266802085 7193207764849383237525391)
    ·
      refine ⟨10789811647274074856288087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7193207764849383237525391 10789811647274074856288087)
      ·
        refine ⟨16184717470911112284432131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10789811647274074856288087 16184717470911112284432131)
        ·
          refine ⟨24277076206366668426648197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16184717470911112284432131 24277076206366668426648197)
          ·
            refine ⟨4551951788693750329996537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24277076206366668426648197 4551951788693750329996537)
            ·
              refine ⟨3413963841520312747497403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4551951788693750329996537 3413963841520312747497403)
              ·
                refine ⟨5120945762280469121246105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3413963841520312747497403 5120945762280469121246105)
                ·
                  refine ⟨3840709321710351840934579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5120945762280469121246105 3840709321710351840934579)
                  ·
                    refine ⟨5761063982565527761401869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3840709321710351840934579 5761063982565527761401869)
                    ·
                      refine ⟨2160398993462072910525701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5761063982565527761401869 2160398993462072910525701)
                      ·
                        rfl

theorem cell23_4207362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_4207362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207362 prefixEnd_4207362 := by exact prefixLift 4207362
  have htrace : WordTrace (prefixWord ++ tailWord_4207362) baseStart_4207362 baseEnd_4207362 := by
    simpa [prefixWord, tailWord_4207362, baseEnd_4207362] using wordTrace_append hprefix tailTrace_4207362
  have hstable : (prefixWord ++ tailWord_4207362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207362).length < 2 ^ (prefixWord ++ tailWord_4207362).sum := by decide
  have hdescent : baseEnd_4207362 < baseStart_4207362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207364 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_4207364 : Nat := 118140960795 + 4207364 * 2 ^ 59
def prefixEnd_4207364 : Nat := 4983230072969 + 3 ^ 40 * 4207364 * 2
def baseEnd_4207364 : Nat := 2160400020423381902700691

theorem tailTrace_4207364 : CollatzResearch.WordTrace tailWord_4207364 prefixEnd_4207364 2160400020423381902700691 := by
  unfold tailWord_4207364
  simp only [CollatzResearch.WordTrace]
  refine ⟨76727585964723131704390573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102303447952964175605854097 76727585964723131704390573)
  ·
    refine ⟨28772844736771174389146465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76727585964723131704390573 28772844736771174389146465)
    ·
      refine ⟨21579633552578380791859849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28772844736771174389146465 21579633552578380791859849)
      ·
        refine ⟨16184725164433785593894887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21579633552578380791859849 16184725164433785593894887)
        ·
          refine ⟨24277087746650678390842331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16184725164433785593894887 24277087746650678390842331)
          ·
            refine ⟨36415631619976017586263497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24277087746650678390842331 36415631619976017586263497)
            ·
              refine ⟨27311723714982013189697623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36415631619976017586263497 27311723714982013189697623)
              ·
                refine ⟨40967585572473019784546435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27311723714982013189697623 40967585572473019784546435)
                ·
                  refine ⟨61451378358709529676819653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40967585572473019784546435 61451378358709529676819653)
                  ·
                    refine ⟨11522133442258036814403685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61451378358709529676819653 11522133442258036814403685)
                    ·
                      refine ⟨2160400020423381902700691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11522133442258036814403685 2160400020423381902700691)
                      ·
                        rfl

theorem cell23_4207364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_4207364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207364 prefixEnd_4207364 := by exact prefixLift 4207364
  have htrace : WordTrace (prefixWord ++ tailWord_4207364) baseStart_4207364 baseEnd_4207364 := by
    simpa [prefixWord, tailWord_4207364, baseEnd_4207364] using wordTrace_append hprefix tailTrace_4207364
  have hstable : (prefixWord ++ tailWord_4207364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207364).length < 2 ^ (prefixWord ++ tailWord_4207364).sum := by decide
  have hdescent : baseEnd_4207364 < baseStart_4207364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207384 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 4, 3, 3]
def baseStart_4207384 : Nat := 118140960795 + 4207384 * 2 ^ 59
def prefixEnd_4207384 : Nat := 4983230072969 + 3 ^ 40 * 4207384 * 2
def baseEnd_4207384 : Nat := 2160410290036471824450599

theorem tailTrace_4207384 : CollatzResearch.WordTrace tailWord_4207384 prefixEnd_4207384 2160410290036471824450599 := by
  unfold tailWord_4207384
  simp only [CollatzResearch.WordTrace]
  refine ⟨76727950694686903412254603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102303934259582537883006137 76727950694686903412254603)
  ·
    refine ⟨115091926042030355118381905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76727950694686903412254603 115091926042030355118381905)
    ·
      refine ⟨86318944531522766338786429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115091926042030355118381905 86318944531522766338786429)
      ·
        refine ⟨32369604199321037377044911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86318944531522766338786429 32369604199321037377044911)
        ·
          refine ⟨48554406298981556065567367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32369604199321037377044911 48554406298981556065567367)
          ·
            refine ⟨72831609448472334098351051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48554406298981556065567367 72831609448472334098351051)
            ·
              refine ⟨109247414172708501147526577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72831609448472334098351051 109247414172708501147526577)
              ·
                refine ⟨81935560629531375860644933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109247414172708501147526577 81935560629531375860644933)
                ·
                  refine ⟨15362917618037132973870925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81935560629531375860644933 15362917618037132973870925)
                  ·
                    refine ⟨5761094106763924865201597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15362917618037132973870925 5761094106763924865201597)
                    ·
                      refine ⟨2160410290036471824450599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5761094106763924865201597 2160410290036471824450599)
                      ·
                        rfl

theorem cell23_4207384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_4207384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207384 prefixEnd_4207384 := by exact prefixLift 4207384
  have htrace : WordTrace (prefixWord ++ tailWord_4207384) baseStart_4207384 baseEnd_4207384 := by
    simpa [prefixWord, tailWord_4207384, baseEnd_4207384] using wordTrace_append hprefix tailTrace_4207384
  have hstable : (prefixWord ++ tailWord_4207384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207384).length < 2 ^ (prefixWord ++ tailWord_4207384).sum := by decide
  have hdescent : baseEnd_4207384 < baseStart_4207384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207404 : List Nat := [2, 2, 1, 1, 1, 4, 1, 4, 2, 5]
def baseStart_4207404 : Nat := 118140960795 + 4207404 * 2 ^ 59
def prefixEnd_4207404 : Nat := 4983230072969 + 3 ^ 40 * 4207404 * 2
def baseEnd_4207404 : Nat := 720140186549853915400169

theorem tailTrace_4207404 : CollatzResearch.WordTrace tailWord_4207404 prefixEnd_4207404 720140186549853915400169 := by
  unfold tailWord_4207404
  simp only [CollatzResearch.WordTrace]
  refine ⟨76728315424650675120118633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102304420566200900160158177 76728315424650675120118633)
  ·
    refine ⟨57546236568488006340088975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76728315424650675120118633 57546236568488006340088975)
    ·
      refine ⟨86319354852732009510133463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57546236568488006340088975 86319354852732009510133463)
      ·
        refine ⟨129479032279098014265200195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86319354852732009510133463 129479032279098014265200195)
        ·
          refine ⟨194218548418647021397800293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129479032279098014265200195 194218548418647021397800293)
          ·
            refine ⟨36415977828496316512087555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 194218548418647021397800293 36415977828496316512087555)
            ·
              refine ⟨54623966742744474768131333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36415977828496316512087555 54623966742744474768131333)
              ·
                refine ⟨10241993764264589019024625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54623966742744474768131333 10241993764264589019024625)
                ·
                  refine ⟨7681495323198441764268469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10241993764264589019024625 7681495323198441764268469)
                  ·
                    refine ⟨720140186549853915400169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7681495323198441764268469 720140186549853915400169)
                    ·
                      rfl

theorem cell23_4207404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_4207404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207404 prefixEnd_4207404 := by exact prefixLift 4207404
  have htrace : WordTrace (prefixWord ++ tailWord_4207404) baseStart_4207404 baseEnd_4207404 := by
    simpa [prefixWord, tailWord_4207404, baseEnd_4207404] using wordTrace_append hprefix tailTrace_4207404
  have hstable : (prefixWord ++ tailWord_4207404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207404).length < 2 ^ (prefixWord ++ tailWord_4207404).sum := by decide
  have hdescent : baseEnd_4207404 < baseStart_4207404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207407 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 8]
def baseStart_4207407 : Nat := 118140960795 + 4207407 * 2 ^ 59
def prefixEnd_4207407 : Nat := 4983230072969 + 3 ^ 40 * 4207407 * 2
def baseEnd_4207407 : Nat := 2160422100091525234462993

theorem tailTrace_4207407 : CollatzResearch.WordTrace tailWord_4207407 prefixEnd_4207407 2160422100091525234462993 := by
  unfold tailWord_4207407
  simp only [CollatzResearch.WordTrace]
  refine ⟨153456740268290481752596475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102304493512193654501730983 153456740268290481752596475)
  ·
    refine ⟨230185110402435722628894713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153456740268290481752596475 230185110402435722628894713)
    ·
      refine ⟨172638832801826791971671035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230185110402435722628894713 172638832801826791971671035)
      ·
        refine ⟨258958249202740187957506553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172638832801826791971671035 258958249202740187957506553)
        ·
          refine ⟨194218686902055140968129915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258958249202740187957506553 194218686902055140968129915)
          ·
            refine ⟨291328030353082711452194873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194218686902055140968129915 291328030353082711452194873)
            ·
              refine ⟨218496022764812033589146155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291328030353082711452194873 218496022764812033589146155)
              ·
                refine ⟨327744034147218050383719233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218496022764812033589146155 327744034147218050383719233)
                ·
                  refine ⟨245808025610413537787789425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 327744034147218050383719233 245808025610413537787789425)
                  ·
                    refine ⟨184356019207810153340842069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 245808025610413537787789425 184356019207810153340842069)
                    ·
                      refine ⟨2160422100091525234462993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 184356019207810153340842069 2160422100091525234462993)
                      ·
                        rfl

theorem cell23_4207407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_4207407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207407 prefixEnd_4207407 := by exact prefixLift 4207407
  have htrace : WordTrace (prefixWord ++ tailWord_4207407) baseStart_4207407 baseEnd_4207407 := by
    simpa [prefixWord, tailWord_4207407, baseEnd_4207407] using wordTrace_append hprefix tailTrace_4207407
  have hstable : (prefixWord ++ tailWord_4207407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207407).length < 2 ^ (prefixWord ++ tailWord_4207407).sum := by decide
  have hdescent : baseEnd_4207407 < baseStart_4207407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207411 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 2, 5, 2]
def baseStart_4207411 : Nat := 118140960795 + 4207411 * 2 ^ 59
def prefixEnd_4207411 : Nat := 4983230072969 + 3 ^ 40 * 4207411 * 2
def baseEnd_4207411 : Nat := 2160424154014143218812975

theorem tailTrace_4207411 : CollatzResearch.WordTrace tailWord_4207411 prefixEnd_4207411 2160424154014143218812975 := by
  unfold tailWord_4207411
  simp only [CollatzResearch.WordTrace]
  refine ⟨153456886160275990435742087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102304590773517326957161391 153456886160275990435742087)
  ·
    refine ⟨230185329240413985653613131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153456886160275990435742087 230185329240413985653613131)
    ·
      refine ⟨345277993860620978480419697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230185329240413985653613131 345277993860620978480419697)
      ·
        refine ⟨258958495395465733860314773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345277993860620978480419697 258958495395465733860314773)
        ·
          refine ⟨12138679471662456274702255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 258958495395465733860314773 12138679471662456274702255)
          ·
            refine ⟨18208019207493684412053383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12138679471662456274702255 18208019207493684412053383)
            ·
              refine ⟨27312028811240526618080075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18208019207493684412053383 27312028811240526618080075)
              ·
                refine ⟨40968043216860789927120113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27312028811240526618080075 40968043216860789927120113)
                ·
                  refine ⟨30726032412645592445340085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40968043216860789927120113 30726032412645592445340085)
                  ·
                    refine ⟨2880565538685524291750633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30726032412645592445340085 2880565538685524291750633)
                    ·
                      refine ⟨2160424154014143218812975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2880565538685524291750633 2160424154014143218812975)
                      ·
                        rfl

theorem cell23_4207411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 5, 2].length) (baseStart_4207411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207411 prefixEnd_4207411 := by exact prefixLift 4207411
  have htrace : WordTrace (prefixWord ++ tailWord_4207411) baseStart_4207411 baseEnd_4207411 := by
    simpa [prefixWord, tailWord_4207411, baseEnd_4207411] using wordTrace_append hprefix tailTrace_4207411
  have hstable : (prefixWord ++ tailWord_4207411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207411).length < 2 ^ (prefixWord ++ tailWord_4207411).sum := by decide
  have hdescent : baseEnd_4207411 < baseStart_4207411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207424 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 4]
def baseStart_4207424 : Nat := 118140960795 + 4207424 * 2 ^ 59
def prefixEnd_4207424 : Nat := 4983230072969 + 3 ^ 40 * 4207424 * 2
def baseEnd_4207424 : Nat := 2160430829262651667950415

theorem tailTrace_4207424 : CollatzResearch.WordTrace tailWord_4207424 prefixEnd_4207424 2160430829262651667950415 := by
  unfold tailWord_4207424
  simp only [CollatzResearch.WordTrace]
  refine ⟨76728680154614446827982663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102304906872819262437310217 76728680154614446827982663)
  ·
    refine ⟨115093020231921670241973995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76728680154614446827982663 115093020231921670241973995)
    ·
      refine ⟨172639530347882505362960993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115093020231921670241973995 172639530347882505362960993)
      ·
        refine ⟨129479647760911879022220745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172639530347882505362960993 129479647760911879022220745)
        ·
          refine ⟨97109735820683909266665559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129479647760911879022220745 97109735820683909266665559)
          ·
            refine ⟨145664603731025863899998339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97109735820683909266665559 145664603731025863899998339)
            ·
              refine ⟨218496905596538795849997509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145664603731025863899998339 218496905596538795849997509)
              ·
                refine ⟨40968169799351024221874533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218496905596538795849997509 40968169799351024221874533)
                ·
                  refine ⟨7681531837378317041601475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40968169799351024221874533 7681531837378317041601475)
                  ·
                    refine ⟨11522297756067475562402213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7681531837378317041601475 11522297756067475562402213)
                    ·
                      refine ⟨2160430829262651667950415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11522297756067475562402213 2160430829262651667950415)
                      ·
                        rfl

theorem cell23_4207424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_4207424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207424 prefixEnd_4207424 := by exact prefixLift 4207424
  have htrace : WordTrace (prefixWord ++ tailWord_4207424) baseStart_4207424 baseEnd_4207424 := by
    simpa [prefixWord, tailWord_4207424, baseEnd_4207424] using wordTrace_append hprefix tailTrace_4207424
  have hstable : (prefixWord ++ tailWord_4207424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207424).length < 2 ^ (prefixWord ++ tailWord_4207424).sum := by decide
  have hdescent : baseEnd_4207424 < baseStart_4207424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207441 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 1, 3, 4]
def baseStart_4207441 : Nat := 118140960795 + 4207441 * 2 ^ 59
def prefixEnd_4207441 : Nat := 4983230072969 + 3 ^ 40 * 4207441 * 2
def baseEnd_4207441 : Nat := 2160439558433778101437837

theorem tailTrace_4207441 : CollatzResearch.WordTrace tailWord_4207441 prefixEnd_4207441 2160439558433778101437837 := by
  unfold tailWord_4207441
  simp only [CollatzResearch.WordTrace]
  refine ⟨153457980350167305559334177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102305320233444870372889451 153457980350167305559334177)
  ·
    refine ⟨115093485262625479169500633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153457980350167305559334177 115093485262625479169500633)
    ·
      refine ⟨86320113946969109377125475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115093485262625479169500633 86320113946969109377125475)
      ·
        refine ⟨129480170920453664065688213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86320113946969109377125475 129480170920453664065688213)
        ·
          refine ⟨6069383011896265503079135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 129480170920453664065688213 6069383011896265503079135)
          ·
            refine ⟨9104074517844398254618703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6069383011896265503079135 9104074517844398254618703)
            ·
              refine ⟨13656111776766597381928055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9104074517844398254618703 13656111776766597381928055)
              ·
                refine ⟨20484167665149896072892083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13656111776766597381928055 20484167665149896072892083)
                ·
                  refine ⟨30726251497724844109338125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20484167665149896072892083 30726251497724844109338125)
                  ·
                    refine ⟨11522344311646816541001797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30726251497724844109338125 11522344311646816541001797)
                    ·
                      refine ⟨2160439558433778101437837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11522344311646816541001797 2160439558433778101437837)
                      ·
                        rfl

theorem cell23_4207441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_4207441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207441 prefixEnd_4207441 := by exact prefixLift 4207441
  have htrace : WordTrace (prefixWord ++ tailWord_4207441) baseStart_4207441 baseEnd_4207441 := by
    simpa [prefixWord, tailWord_4207441, baseEnd_4207441] using wordTrace_append hprefix tailTrace_4207441
  have hstable : (prefixWord ++ tailWord_4207441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207441).length < 2 ^ (prefixWord ++ tailWord_4207441).sum := by decide
  have hdescent : baseEnd_4207441 < baseStart_4207441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207461 : List Nat := [1, 3, 1, 3, 1, 1, 2, 4, 2, 2, 3]
def baseStart_4207461 : Nat := 118140960795 + 4207461 * 2 ^ 59
def prefixEnd_4207461 : Nat := 4983230072969 + 3 ^ 40 * 4207461 * 2
def baseEnd_4207461 : Nat := 2160449828046868023187745

theorem tailTrace_4207461 : CollatzResearch.WordTrace tailWord_4207461 prefixEnd_4207461 2160449828046868023187745 := by
  unfold tailWord_4207461
  simp only [CollatzResearch.WordTrace]
  refine ⟨153458709810094848975062237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102305806540063232650041491 153458709810094848975062237)
  ·
    refine ⟨57547016178785568365648339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153458709810094848975062237 57547016178785568365648339)
    ·
      refine ⟨86320524268178352548472509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57547016178785568365648339 86320524268178352548472509)
      ·
        refine ⟨32370196600566882205677191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86320524268178352548472509 32370196600566882205677191)
        ·
          refine ⟨48555294900850323308515787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32370196600566882205677191 48555294900850323308515787)
          ·
            refine ⟨72832942351275484962773681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48555294900850323308515787 72832942351275484962773681)
            ·
              refine ⟨54624706763456613722080261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72832942351275484962773681 54624706763456613722080261)
              ·
                refine ⟨10242132518148115072890049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54624706763456613722080261 10242132518148115072890049)
                ·
                  refine ⟨7681599388611086304667537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10242132518148115072890049 7681599388611086304667537)
                  ·
                    refine ⟨5761199541458314728500653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7681599388611086304667537 5761199541458314728500653)
                    ·
                      refine ⟨2160449828046868023187745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5761199541458314728500653 2160449828046868023187745)
                      ·
                        rfl

theorem cell23_4207461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_4207461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207461 prefixEnd_4207461 := by exact prefixLift 4207461
  have htrace : WordTrace (prefixWord ++ tailWord_4207461) baseStart_4207461 baseEnd_4207461 := by
    simpa [prefixWord, tailWord_4207461, baseEnd_4207461] using wordTrace_append hprefix tailTrace_4207461
  have hstable : (prefixWord ++ tailWord_4207461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207461).length < 2 ^ (prefixWord ++ tailWord_4207461).sum := by decide
  have hdescent : baseEnd_4207461 < baseStart_4207461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207468 : List Nat := [2, 2, 1, 1, 4, 1, 1, 6, 1, 4]
def baseStart_4207468 : Nat := 118140960795 + 4207468 * 2 ^ 59
def prefixEnd_4207468 : Nat := 4983230072969 + 3 ^ 40 * 4207468 * 2
def baseEnd_4207468 : Nat := 720151140803816498600071

theorem tailTrace_4207468 : CollatzResearch.WordTrace tailWord_4207468 prefixEnd_4207468 720151140803816498600071 := by
  unfold tailWord_4207468
  simp only [CollatzResearch.WordTrace]
  refine ⟨76729482560534744585283529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102305976747379659447044705 76729482560534744585283529)
  ·
    refine ⟨57547111920401058438962647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76729482560534744585283529 57547111920401058438962647)
    ·
      refine ⟨86320667880601587658443971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57547111920401058438962647 86320667880601587658443971)
      ·
        refine ⟨129481001820902381487665957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86320667880601587658443971 129481001820902381487665957)
        ·
          refine ⟨24277687841419196528937367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129481001820902381487665957 24277687841419196528937367)
          ·
            refine ⟨36416531762128794793406051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24277687841419196528937367 36416531762128794793406051)
            ·
              refine ⟨54624797643193192190109077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36416531762128794793406051 54624797643193192190109077)
              ·
                refine ⟨2560537389524680883911363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54624797643193192190109077 2560537389524680883911363)
                ·
                  refine ⟨3840806084287021325867045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2560537389524680883911363 3840806084287021325867045)
                  ·
                    refine ⟨720151140803816498600071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3840806084287021325867045 720151140803816498600071)
                    ·
                      rfl

theorem cell23_4207468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 1, 4].length) (baseStart_4207468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207468 prefixEnd_4207468 := by exact prefixLift 4207468
  have htrace : WordTrace (prefixWord ++ tailWord_4207468) baseStart_4207468 baseEnd_4207468 := by
    simpa [prefixWord, tailWord_4207468, baseEnd_4207468] using wordTrace_append hprefix tailTrace_4207468
  have hstable : (prefixWord ++ tailWord_4207468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207468).length < 2 ^ (prefixWord ++ tailWord_4207468).sum := by decide
  have hdescent : baseEnd_4207468 < baseStart_4207468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207478 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_4207478 : Nat := 118140960795 + 4207478 * 2 ^ 59
def prefixEnd_4207478 : Nat := 4983230072969 + 3 ^ 40 * 4207478 * 2
def baseEnd_4207478 : Nat := 2160458557217994456675167

theorem tailTrace_4207478 : CollatzResearch.WordTrace tailWord_4207478 prefixEnd_4207478 2160458557217994456675167 := by
  unfold tailWord_4207478
  simp only [CollatzResearch.WordTrace]
  refine ⟨9591208115689578804901943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102306219900688840585620725 9591208115689578804901943)
  ·
    refine ⟨14386812173534368207352915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9591208115689578804901943 14386812173534368207352915)
    ·
      refine ⟨21580218260301552311029373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14386812173534368207352915 21580218260301552311029373)
      ·
        refine ⟨8092581847613082116636015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21580218260301552311029373 8092581847613082116636015)
        ·
          refine ⟨12138872771419623174954023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8092581847613082116636015 12138872771419623174954023)
          ·
            refine ⟨18208309157129434762431035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12138872771419623174954023 18208309157129434762431035)
            ·
              refine ⟨27312463735694152143646553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18208309157129434762431035 27312463735694152143646553)
              ·
                refine ⟨20484347801770614107734915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27312463735694152143646553 20484347801770614107734915)
                ·
                  refine ⟨30726521702655921161602373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20484347801770614107734915 30726521702655921161602373)
                  ·
                    refine ⟨5761222819247985217800445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30726521702655921161602373 5761222819247985217800445)
                    ·
                      refine ⟨2160458557217994456675167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5761222819247985217800445 2160458557217994456675167)
                      ·
                        rfl

theorem cell23_4207478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_4207478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207478 prefixEnd_4207478 := by exact prefixLift 4207478
  have htrace : WordTrace (prefixWord ++ tailWord_4207478) baseStart_4207478 baseEnd_4207478 := by
    simpa [prefixWord, tailWord_4207478, baseEnd_4207478] using wordTrace_append hprefix tailTrace_4207478
  have hstable : (prefixWord ++ tailWord_4207478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207478).length < 2 ^ (prefixWord ++ tailWord_4207478).sum := by decide
  have hdescent : baseEnd_4207478 < baseStart_4207478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207511 : List Nat := [1, 1, 3, 3, 1, 2, 1, 5, 1, 5]
def baseStart_4207511 : Nat := 118140960795 + 4207511 * 2 ^ 59
def prefixEnd_4207511 : Nat := 4983230072969 + 3 ^ 40 * 4207511 * 2
def baseEnd_4207511 : Nat := 720158500693197609187505

theorem tailTrace_4207511 : CollatzResearch.WordTrace tailWord_4207511 prefixEnd_4207511 720158500693197609187505 := by
  unfold tailWord_4207511
  simp only [CollatzResearch.WordTrace]
  refine ⟨153460533459913707514382387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102307022306609138342921591 153460533459913707514382387)
  ·
    refine ⟨230190800189870561271573581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153460533459913707514382387 230190800189870561271573581)
    ·
      refine ⟨86321550071201460476840093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230190800189870561271573581 86321550071201460476840093)
      ·
        refine ⟨32370581276700547678815035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86321550071201460476840093 32370581276700547678815035)
        ·
          refine ⟨48555871915050821518222553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32370581276700547678815035 48555871915050821518222553)
          ·
            refine ⟨36416903936288116138666915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48555871915050821518222553 36416903936288116138666915)
            ·
              refine ⟨54625355904432174208000373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36416903936288116138666915 54625355904432174208000373)
              ·
                refine ⟨5121127116040516332000035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54625355904432174208000373 5121127116040516332000035)
                ·
                  refine ⟨7681690674060774498000053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5121127116040516332000035 7681690674060774498000053)
                  ·
                    refine ⟨720158500693197609187505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7681690674060774498000053 720158500693197609187505)
                    ·
                      rfl

theorem cell23_4207511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 5].length) (baseStart_4207511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207511 prefixEnd_4207511 := by exact prefixLift 4207511
  have htrace : WordTrace (prefixWord ++ tailWord_4207511) baseStart_4207511 baseEnd_4207511 := by
    simpa [prefixWord, tailWord_4207511, baseEnd_4207511] using wordTrace_append hprefix tailTrace_4207511
  have hstable : (prefixWord ++ tailWord_4207511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207511).length < 2 ^ (prefixWord ++ tailWord_4207511).sum := by decide
  have hdescent : baseEnd_4207511 < baseStart_4207511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207541 : List Nat := [1, 3, 3, 2, 1, 1, 2, 3, 1, 6]
def baseStart_4207541 : Nat := 118140960795 + 4207541 * 2 ^ 59
def prefixEnd_4207541 : Nat := 4983230072969 + 3 ^ 40 * 4207541 * 2
def baseEnd_4207541 : Nat := 720163635499742570062459

theorem tailTrace_4207541 : CollatzResearch.WordTrace tailWord_4207541 prefixEnd_4207541 720163635499742570062459 := by
  unfold tailWord_4207541
  simp only [CollatzResearch.WordTrace]
  refine ⟨153461627649805022637974477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102307751766536681758649651 153461627649805022637974477)
  ·
    refine ⟨57548110368676883489240429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153461627649805022637974477 57548110368676883489240429)
    ·
      refine ⟨21580541388253831308465161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57548110368676883489240429 21580541388253831308465161)
      ·
        refine ⟨16185406041190373481348871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21580541388253831308465161 16185406041190373481348871)
        ·
          refine ⟨24278109061785560222023307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16185406041190373481348871 24278109061785560222023307)
          ·
            refine ⟨36417163592678340333034961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24278109061785560222023307 36417163592678340333034961)
            ·
              refine ⟨27312872694508755249776221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36417163592678340333034961 27312872694508755249776221)
              ·
                refine ⟨10242327260440783218666083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27312872694508755249776221 10242327260440783218666083)
                ·
                  refine ⟨15363490890661174827999125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10242327260440783218666083 15363490890661174827999125)
                  ·
                    refine ⟨720163635499742570062459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15363490890661174827999125 720163635499742570062459)
                    ·
                      rfl

theorem cell23_4207541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_4207541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207541 prefixEnd_4207541 := by exact prefixLift 4207541
  have htrace : WordTrace (prefixWord ++ tailWord_4207541) baseStart_4207541 baseEnd_4207541 := by
    simpa [prefixWord, tailWord_4207541, baseEnd_4207541] using wordTrace_append hprefix tailTrace_4207541
  have hstable : (prefixWord ++ tailWord_4207541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207541).length < 2 ^ (prefixWord ++ tailWord_4207541).sum := by decide
  have hdescent : baseEnd_4207541 < baseStart_4207541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207641 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 1, 6, 3]
def baseStart_4207641 : Nat := 118140960795 + 4207641 * 2 ^ 59
def prefixEnd_4207641 : Nat := 4983230072969 + 3 ^ 40 * 4207641 * 2
def baseEnd_4207641 : Nat := 2160542254564677318936917

theorem tailTrace_4207641 : CollatzResearch.WordTrace tailWord_4207641 prefixEnd_4207641 2160542254564677318936917 := by
  unfold tailWord_4207641
  simp only [CollatzResearch.WordTrace]
  refine ⟨153465274949442739716614777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102310183299628493144409851 153465274949442739716614777)
  ·
    refine ⟨115098956212082054787461083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153465274949442739716614777 115098956212082054787461083)
    ·
      refine ⟨172648434318123082181191625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115098956212082054787461083 172648434318123082181191625)
      ·
        refine ⟨129486325738592311635893719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172648434318123082181191625 129486325738592311635893719)
        ·
          refine ⟨194229488607888467453840579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129486325738592311635893719 194229488607888467453840579)
          ·
            refine ⟨291344232911832701180760869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194229488607888467453840579 291344232911832701180760869)
            ·
              refine ⟨54627043670968631471392663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 291344232911832701180760869 54627043670968631471392663)
              ·
                refine ⟨81940565506452947207088995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54627043670968631471392663 81940565506452947207088995)
                ·
                  refine ⟨122910848259679420810633493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81940565506452947207088995 122910848259679420810633493)
                  ·
                    refine ⟨5761446012172472850498445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 122910848259679420810633493 5761446012172472850498445)
                    ·
                      refine ⟨2160542254564677318936917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5761446012172472850498445 2160542254564677318936917)
                      ·
                        rfl

theorem cell23_4207641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_4207641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207641 prefixEnd_4207641 := by exact prefixLift 4207641
  have htrace : WordTrace (prefixWord ++ tailWord_4207641) baseStart_4207641 baseEnd_4207641 := by
    simpa [prefixWord, tailWord_4207641, baseEnd_4207641] using wordTrace_append hprefix tailTrace_4207641
  have hstable : (prefixWord ++ tailWord_4207641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207641).length < 2 ^ (prefixWord ++ tailWord_4207641).sum := by decide
  have hdescent : baseEnd_4207641 < baseStart_4207641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207708 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 4, 5]
def baseStart_4207708 : Nat := 118140960795 + 4207708 * 2 ^ 59
def prefixEnd_4207708 : Nat := 4983230072969 + 3 ^ 40 * 4207708 * 2
def baseEnd_4207708 : Nat := 720192219256176185599703

theorem tailTrace_4207708 : CollatzResearch.WordTrace tailWord_4207708 prefixEnd_4207708 720192219256176185599703 := by
  unfold tailWord_4207708
  simp only [CollatzResearch.WordTrace]
  refine ⟨76733859320100005079651889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102311812426800006772869185 76733859320100005079651889)
  ·
    refine ⟨57550394490075003809738917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76733859320100005079651889 57550394490075003809738917)
    ·
      refine ⟨10790698966889063214326047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57550394490075003809738917 10790698966889063214326047)
      ·
        refine ⟨16186048450333594821489071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10790698966889063214326047 16186048450333594821489071)
        ·
          refine ⟨24279072675500392232233607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16186048450333594821489071 24279072675500392232233607)
          ·
            refine ⟨36418609013250588348350411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24279072675500392232233607 36418609013250588348350411)
            ·
              refine ⟨54627913519875882522525617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36418609013250588348350411 54627913519875882522525617)
              ·
                refine ⟨40970935139906911891894213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54627913519875882522525617 40970935139906911891894213)
                ·
                  refine ⟨7682050338732545979730165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40970935139906911891894213 7682050338732545979730165)
                  ·
                    refine ⟨720192219256176185599703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7682050338732545979730165 720192219256176185599703)
                    ·
                      rfl

theorem cell23_4207708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_4207708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207708 prefixEnd_4207708 := by exact prefixLift 4207708
  have htrace : WordTrace (prefixWord ++ tailWord_4207708) baseStart_4207708 baseEnd_4207708 := by
    simpa [prefixWord, tailWord_4207708, baseEnd_4207708] using wordTrace_append hprefix tailTrace_4207708
  have hstable : (prefixWord ++ tailWord_4207708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207708).length < 2 ^ (prefixWord ++ tailWord_4207708).sum := by decide
  have hdescent : baseEnd_4207708 < baseStart_4207708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207725 : List Nat := [1, 5, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_4207725 : Nat := 118140960795 + 4207725 * 2 ^ 59
def prefixEnd_4207725 : Nat := 4983230072969 + 3 ^ 40 * 4207725 * 2
def baseEnd_4207725 : Nat := 720195128979884996762177

theorem tailTrace_4207725 : CollatzResearch.WordTrace tailWord_4207725 prefixEnd_4207725 720195128979884996762177 := by
  unfold tailWord_4207725
  simp only [CollatzResearch.WordTrace]
  refine ⟨153468338681138422062672629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102312225787425614708448419 153468338681138422062672629)
  ·
    refine ⟨14387656751356727068375559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153468338681138422062672629 14387656751356727068375559)
    ·
      refine ⟨21581485127035090602563339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14387656751356727068375559 21581485127035090602563339)
      ·
        refine ⟨32372227690552635903845009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21581485127035090602563339 32372227690552635903845009)
        ·
          refine ⟨24279170767914476927883757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32372227690552635903845009 24279170767914476927883757)
          ·
            refine ⟨9104689037967928847956409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24279170767914476927883757 9104689037967928847956409)
            ·
              refine ⟨6828516778475946635967307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9104689037967928847956409 6828516778475946635967307)
              ·
                refine ⟨10242775167713919953950961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6828516778475946635967307 10242775167713919953950961)
                ·
                  refine ⟨7682081375785439965463221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10242775167713919953950961 7682081375785439965463221)
                  ·
                    refine ⟨720195128979884996762177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7682081375785439965463221 720195128979884996762177)
                    ·
                      rfl

theorem cell23_4207725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_4207725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207725 prefixEnd_4207725 := by exact prefixLift 4207725
  have htrace : WordTrace (prefixWord ++ tailWord_4207725) baseStart_4207725 baseEnd_4207725 := by
    simpa [prefixWord, tailWord_4207725, baseEnd_4207725] using wordTrace_append hprefix tailTrace_4207725
  have hstable : (prefixWord ++ tailWord_4207725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207725).length < 2 ^ (prefixWord ++ tailWord_4207725).sum := by decide
  have hdescent : baseEnd_4207725 < baseStart_4207725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207745 : List Nat := [1, 2, 4, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_4207745 : Nat := 118140960795 + 4207745 * 2 ^ 59
def prefixEnd_4207745 : Nat := 4983230072969 + 3 ^ 40 * 4207745 * 2
def baseEnd_4207745 : Nat := 2160595656552744912036439

theorem tailTrace_4207745 : CollatzResearch.WordTrace tailWord_4207745 prefixEnd_4207745 2160595656552744912036439 := by
  unfold tailWord_4207745
  simp only [CollatzResearch.WordTrace]
  refine ⟨153469068141065965478400689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102312712094043976985600459 153469068141065965478400689)
  ·
    refine ⟨115101801105799474108800517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153469068141065965478400689 115101801105799474108800517)
    ·
      refine ⟨21581587707337401395400097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115101801105799474108800517 21581587707337401395400097)
      ·
        refine ⟨16186190780503051046550073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21581587707337401395400097 16186190780503051046550073)
        ·
          refine ⟨12139643085377288284912555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16186190780503051046550073 12139643085377288284912555)
          ·
            refine ⟨18209464628065932427368833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12139643085377288284912555 18209464628065932427368833)
            ·
              refine ⟨13657098471049449320526625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18209464628065932427368833 13657098471049449320526625)
              ·
                refine ⟨10242823853287086990394969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13657098471049449320526625 10242823853287086990394969)
                ·
                  refine ⟨7682117889965315242796227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10242823853287086990394969 7682117889965315242796227)
                  ·
                    refine ⟨11523176834947972864194341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7682117889965315242796227 11523176834947972864194341)
                    ·
                      refine ⟨2160595656552744912036439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11523176834947972864194341 2160595656552744912036439)
                      ·
                        rfl

theorem cell23_4207745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_4207745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207745 prefixEnd_4207745 := by exact prefixLift 4207745
  have htrace : WordTrace (prefixWord ++ tailWord_4207745) baseStart_4207745 baseEnd_4207745 := by
    simpa [prefixWord, tailWord_4207745, baseEnd_4207745] using wordTrace_append hprefix tailTrace_4207745
  have hstable : (prefixWord ++ tailWord_4207745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207745).length < 2 ^ (prefixWord ++ tailWord_4207745).sum := by decide
  have hdescent : baseEnd_4207745 < baseStart_4207745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207762 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_4207762 : Nat := 118140960795 + 4207762 * 2 ^ 59
def prefixEnd_4207762 : Nat := 4983230072969 + 3 ^ 40 * 4207762 * 2
def baseEnd_4207762 : Nat := 2160604385723871345523861

theorem tailTrace_4207762 : CollatzResearch.WordTrace tailWord_4207762 prefixEnd_4207762 2160604385723871345523861 := by
  unfold tailWord_4207762
  simp only [CollatzResearch.WordTrace]
  refine ⟨38367422045501094345442385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102313125454669584921179693 38367422045501094345442385)
  ·
    refine ⟨28775566534125820759081789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38367422045501094345442385 28775566534125820759081789)
    ·
      refine ⟨10790837450297182784655671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28775566534125820759081789 10790837450297182784655671)
      ·
        refine ⟨16186256175445774176983507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10790837450297182784655671 16186256175445774176983507)
        ·
          refine ⟨24279384263168661265475261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16186256175445774176983507 24279384263168661265475261)
          ·
            refine ⟨9104769098688247974553223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24279384263168661265475261 9104769098688247974553223)
            ·
              refine ⟨13657153648032371961829835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9104769098688247974553223 13657153648032371961829835)
              ·
                refine ⟨20485730472048557942744753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13657153648032371961829835 20485730472048557942744753)
                ·
                  refine ⟨15364297854036418457058565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20485730472048557942744753 15364297854036418457058565)
                  ·
                    refine ⟨2880805847631828460698481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15364297854036418457058565 2880805847631828460698481)
                    ·
                      refine ⟨2160604385723871345523861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2880805847631828460698481 2160604385723871345523861)
                      ·
                        rfl

theorem cell23_4207762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_4207762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207762 prefixEnd_4207762 := by exact prefixLift 4207762
  have htrace : WordTrace (prefixWord ++ tailWord_4207762) baseStart_4207762 baseEnd_4207762 := by
    simpa [prefixWord, tailWord_4207762, baseEnd_4207762] using wordTrace_append hprefix tailTrace_4207762
  have hstable : (prefixWord ++ tailWord_4207762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207762).length < 2 ^ (prefixWord ++ tailWord_4207762).sum := by decide
  have hdescent : baseEnd_4207762 < baseStart_4207762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207832 : List Nat := [2, 1, 2, 2, 5, 1, 2, 2, 1, 5]
def baseStart_4207832 : Nat := 118140960795 + 4207832 * 2 ^ 59
def prefixEnd_4207832 : Nat := 4983230072969 + 3 ^ 40 * 4207832 * 2
def baseEnd_4207832 : Nat := 720213443123228690549513

theorem tailTrace_4207832 : CollatzResearch.WordTrace tailWord_4207832 prefixEnd_4207832 720213443123228690549513 := by
  unfold tailWord_4207832
  simp only [CollatzResearch.WordTrace]
  refine ⟨76736120645875389668408875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102314827527833852891211833 76736120645875389668408875)
  ·
    refine ⟨115104180968813084502613313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76736120645875389668408875 115104180968813084502613313)
    ·
      refine ⟨86328135726609813376959985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115104180968813084502613313 86328135726609813376959985)
      ·
        refine ⟨64746101794957360032719989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86328135726609813376959985 64746101794957360032719989)
        ·
          refine ⟨6069947043277252503067499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64746101794957360032719989 6069947043277252503067499)
          ·
            refine ⟨9104920564915878754601249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6069947043277252503067499 9104920564915878754601249)
            ·
              refine ⟨6828690423686909065950937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9104920564915878754601249 6828690423686909065950937)
              ·
                refine ⟨5121517817765181799463203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6828690423686909065950937 5121517817765181799463203)
                ·
                  refine ⟨7682276726647772699194805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5121517817765181799463203 7682276726647772699194805)
                  ·
                    refine ⟨720213443123228690549513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7682276726647772699194805 720213443123228690549513)
                    ·
                      rfl

theorem cell23_4207832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 1, 5].length) (baseStart_4207832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207832 prefixEnd_4207832 := by exact prefixLift 4207832
  have htrace : WordTrace (prefixWord ++ tailWord_4207832) baseStart_4207832 baseEnd_4207832 := by
    simpa [prefixWord, tailWord_4207832, baseEnd_4207832] using wordTrace_append hprefix tailTrace_4207832
  have hstable : (prefixWord ++ tailWord_4207832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207832).length < 2 ^ (prefixWord ++ tailWord_4207832).sum := by decide
  have hdescent : baseEnd_4207832 < baseStart_4207832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207862 : List Nat := [5, 1, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_4207862 : Nat := 118140960795 + 4207862 * 2 ^ 59
def prefixEnd_4207862 : Nat := 4983230072969 + 3 ^ 40 * 4207862 * 2
def baseEnd_4207862 : Nat := 720218577929773651424467

theorem tailTrace_4207862 : CollatzResearch.WordTrace tailWord_4207862 prefixEnd_4207862 720218577929773651424467 := by
  unfold tailWord_4207862
  simp only [CollatzResearch.WordTrace]
  refine ⟨9592083467602630903775615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102315556987761396306939893 9592083467602630903775615)
  ·
    refine ⟨14388125201403946355663423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9592083467602630903775615 14388125201403946355663423)
    ·
      refine ⟨21582187802105919533495135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14388125201403946355663423 21582187802105919533495135)
      ·
        refine ⟨32373281703158879300242703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21582187802105919533495135 32373281703158879300242703)
        ·
          refine ⟨48559922554738318950364055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32373281703158879300242703 48559922554738318950364055)
          ·
            refine ⟨72839883832107478425546083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48559922554738318950364055 72839883832107478425546083)
            ·
              refine ⟨109259825748161217638319125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72839883832107478425546083 109259825748161217638319125)
              ·
                refine ⟨5121554331945057076796209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 109259825748161217638319125 5121554331945057076796209)
                ·
                  refine ⟨3841165748958792807597157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5121554331945057076796209 3841165748958792807597157)
                  ·
                    refine ⟨720218577929773651424467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3841165748958792807597157 720218577929773651424467)
                    ·
                      rfl

theorem cell23_4207862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_4207862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207862 prefixEnd_4207862 := by exact prefixLift 4207862
  have htrace : WordTrace (prefixWord ++ tailWord_4207862) baseStart_4207862 baseEnd_4207862 := by
    simpa [prefixWord, tailWord_4207862, baseEnd_4207862] using wordTrace_append hprefix tailTrace_4207862
  have hstable : (prefixWord ++ tailWord_4207862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207862).length < 2 ^ (prefixWord ++ tailWord_4207862).sum := by decide
  have hdescent : baseEnd_4207862 < baseStart_4207862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207906 : List Nat := [3, 3, 1, 1, 4, 1, 3, 1, 1, 2, 3]
def baseStart_4207906 : Nat := 118140960795 + 4207906 * 2 ^ 59
def prefixEnd_4207906 : Nat := 4983230072969 + 3 ^ 40 * 4207906 * 2
def baseEnd_4207906 : Nat := 2160678326938118782123199

theorem tailTrace_4207906 : CollatzResearch.WordTrace tailWord_4207906 prefixEnd_4207906 2160678326938118782123199 := by
  unfold tailWord_4207906
  simp only [CollatzResearch.WordTrace]
  refine ⟨38368735073370672493752893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102316626862321793316674381 38368735073370672493752893)
  ·
    refine ⟨14388275652514002185157335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38368735073370672493752893 14388275652514002185157335)
    ·
      refine ⟨21582413478771003277736003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14388275652514002185157335 21582413478771003277736003)
      ·
        refine ⟨32373620218156504916604005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21582413478771003277736003 32373620218156504916604005)
        ·
          refine ⟨6070053790904344671863251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32373620218156504916604005 6070053790904344671863251)
          ·
            refine ⟨9105080686356517007794877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6070053790904344671863251 9105080686356517007794877)
            ·
              refine ⟨3414405257383693877923079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9105080686356517007794877 3414405257383693877923079)
              ·
                refine ⟨5121607886075540816884619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3414405257383693877923079 5121607886075540816884619)
                ·
                  refine ⟨7682411829113311225326929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5121607886075540816884619 7682411829113311225326929)
                  ·
                    refine ⟨5761808871834983418995197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7682411829113311225326929 5761808871834983418995197)
                    ·
                      refine ⟨2160678326938118782123199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5761808871834983418995197 2160678326938118782123199)
                      ·
                        rfl

theorem cell23_4207906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_4207906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207906 prefixEnd_4207906 := by exact prefixLift 4207906
  have htrace : WordTrace (prefixWord ++ tailWord_4207906) baseStart_4207906 baseEnd_4207906 := by
    simpa [prefixWord, tailWord_4207906, baseEnd_4207906] using wordTrace_append hprefix tailTrace_4207906
  have hstable : (prefixWord ++ tailWord_4207906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207906).length < 2 ^ (prefixWord ++ tailWord_4207906).sum := by decide
  have hdescent : baseEnd_4207906 < baseStart_4207906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207925 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_4207925 : Nat := 118140960795 + 4207925 * 2 ^ 59
def prefixEnd_4207925 : Nat := 4983230072969 + 3 ^ 40 * 4207925 * 2
def baseEnd_4207925 : Nat := 2160688083070554207785611

theorem tailTrace_4207925 : CollatzResearch.WordTrace tailWord_4207925 prefixEnd_4207925 2160688083070554207785611 := by
  unfold tailWord_4207925
  simp only [CollatzResearch.WordTrace]
  refine ⟨153475633280413856219953229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102317088853609237479968819 153475633280413856219953229)
  ·
    refine ⟨57553362480155196082482461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153475633280413856219953229 57553362480155196082482461)
    ·
      refine ⟨21582510930058198530930923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57553362480155196082482461 21582510930058198530930923)
      ·
        refine ⟨32373766395087297796396385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21582510930058198530930923 32373766395087297796396385)
        ·
          refine ⟨24280324796315473347297289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32373766395087297796396385 24280324796315473347297289)
          ·
            refine ⟨18210243597236605010472967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24280324796315473347297289 18210243597236605010472967)
            ·
              refine ⟨27315365395854907515709451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18210243597236605010472967 27315365395854907515709451)
              ·
                refine ⟨40973048093782361273564177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27315365395854907515709451 40973048093782361273564177)
                ·
                  refine ⟨30729786070336770955173133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40973048093782361273564177 30729786070336770955173133)
                  ·
                    refine ⟨11523669776376289108189925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30729786070336770955173133 11523669776376289108189925)
                    ·
                      refine ⟨2160688083070554207785611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11523669776376289108189925 2160688083070554207785611)
                      ·
                        rfl

theorem cell23_4207925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_4207925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207925 prefixEnd_4207925 := by exact prefixLift 4207925
  have htrace : WordTrace (prefixWord ++ tailWord_4207925) baseStart_4207925 baseEnd_4207925 := by
    simpa [prefixWord, tailWord_4207925, baseEnd_4207925] using wordTrace_append hprefix tailTrace_4207925
  have hstable : (prefixWord ++ tailWord_4207925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207925).length < 2 ^ (prefixWord ++ tailWord_4207925).sum := by decide
  have hdescent : baseEnd_4207925 < baseStart_4207925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207926 : List Nat := [5, 1, 2, 3, 2, 1, 1, 8]
def baseStart_4207926 : Nat := 118140960795 + 4207926 * 2 ^ 59
def prefixEnd_4207926 : Nat := 4983230072969 + 3 ^ 40 * 4207926 * 2
def baseEnd_4207926 : Nat := 80025503575970692736041

theorem tailTrace_4207926 : CollatzResearch.WordTrace tailWord_4207926 prefixEnd_4207926 80025503575970692736041 := by
  unfold tailWord_4207926
  simp only [CollatzResearch.WordTrace]
  refine ⟨9592229359588139586921227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102317113168940155593826421 9592229359588139586921227)
  ·
    refine ⟨14388344039382209380381841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9592229359588139586921227 14388344039382209380381841)
    ·
      refine ⟨10791258029536657035286381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14388344039382209380381841 10791258029536657035286381)
      ·
        refine ⟨4046721761076246388232393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10791258029536657035286381 4046721761076246388232393)
        ·
          refine ⟨3035041320807184791174295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4046721761076246388232393 3035041320807184791174295)
          ·
            refine ⟨4552561981210777186761443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3035041320807184791174295 4552561981210777186761443)
            ·
              refine ⟨6828842971816165780142165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4552561981210777186761443 6828842971816165780142165)
              ·
                refine ⟨80025503575970692736041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6828842971816165780142165 80025503575970692736041)
                ·
                  rfl

theorem cell23_4207926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_4207926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207926 prefixEnd_4207926 := by exact prefixLift 4207926
  have htrace : WordTrace (prefixWord ++ tailWord_4207926) baseStart_4207926 baseEnd_4207926 := by
    simpa [prefixWord, tailWord_4207926, baseEnd_4207926] using wordTrace_append hprefix tailTrace_4207926
  have hstable : (prefixWord ++ tailWord_4207926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207926).length < 2 ^ (prefixWord ++ tailWord_4207926).sum := by decide
  have hdescent : baseEnd_4207926 < baseStart_4207926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207935 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 2, 6]
def baseStart_4207935 : Nat := 118140960795 + 4207935 * 2 ^ 59
def prefixEnd_4207935 : Nat := 4983230072969 + 3 ^ 40 * 4207935 * 2
def baseEnd_4207935 : Nat := 720231072625699722886855

theorem tailTrace_4207935 : CollatzResearch.WordTrace tailWord_4207935 prefixEnd_4207935 720231072625699722886855 := by
  unfold tailWord_4207935
  simp only [CollatzResearch.WordTrace]
  refine ⟨153475998010377627927817259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102317332006918418618544839 153475998010377627927817259)
  ·
    refine ⟨230213997015566441891725889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153475998010377627927817259 230213997015566441891725889)
    ·
      refine ⟨172660497761674831418794417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230213997015566441891725889 172660497761674831418794417)
      ·
        refine ⟨129495373321256123564095813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172660497761674831418794417 129495373321256123564095813)
        ·
          refine ⟨24280382497735523168267965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129495373321256123564095813 24280382497735523168267965)
          ·
            refine ⟨9105143436650821188100487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24280382497735523168267965 9105143436650821188100487)
            ·
              refine ⟨13657715154976231782150731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9105143436650821188100487 13657715154976231782150731)
              ·
                refine ⟨20486572732464347673226097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13657715154976231782150731 20486572732464347673226097)
                ·
                  refine ⟨15364929549348260754919573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20486572732464347673226097 15364929549348260754919573)
                  ·
                    refine ⟨720231072625699722886855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15364929549348260754919573 720231072625699722886855)
                    ·
                      rfl

theorem cell23_4207935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 6].length) (baseStart_4207935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207935 prefixEnd_4207935 := by exact prefixLift 4207935
  have htrace : WordTrace (prefixWord ++ tailWord_4207935) baseStart_4207935 baseEnd_4207935 := by
    simpa [prefixWord, tailWord_4207935, baseEnd_4207935] using wordTrace_append hprefix tailTrace_4207935
  have hstable : (prefixWord ++ tailWord_4207935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207935).length < 2 ^ (prefixWord ++ tailWord_4207935).sum := by decide
  have hdescent : baseEnd_4207935 < baseStart_4207935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4207976 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 4, 2, 2]
def baseStart_4207976 : Nat := 118140960795 + 4207976 * 2 ^ 59
def prefixEnd_4207976 : Nat := 4983230072969 + 3 ^ 40 * 4207976 * 2
def baseEnd_4207976 : Nat := 2160714270583933508247877

theorem tailTrace_4207976 : CollatzResearch.WordTrace tailWord_4207976 prefixEnd_4207976 2160714270583933508247877 := by
  unfold tailWord_4207976
  simp only [CollatzResearch.WordTrace]
  refine ⟨76738746701614545965029891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102318328935486061286706521 76738746701614545965029891)
  ·
    refine ⟨115108120052421818947544837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76738746701614545965029891 115108120052421818947544837)
    ·
      refine ⟨21582772509829091052664657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115108120052421818947544837 21582772509829091052664657)
      ·
        refine ⟨16187079382371818289498493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21582772509829091052664657 16187079382371818289498493)
        ·
          refine ⟨6070154768389431858561935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16187079382371818289498493 6070154768389431858561935)
          ·
            refine ⟨9105232152584147787842903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6070154768389431858561935 9105232152584147787842903)
            ·
              refine ⟨13657848228876221681764355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9105232152584147787842903 13657848228876221681764355)
              ·
                refine ⟨20486772343314332522646533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13657848228876221681764355 20486772343314332522646533)
                ·
                  refine ⟨3841269814371437347996225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20486772343314332522646533 3841269814371437347996225)
                  ·
                    refine ⟨2880952360778578010997169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3841269814371437347996225 2880952360778578010997169)
                    ·
                      refine ⟨2160714270583933508247877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2880952360778578010997169 2160714270583933508247877)
                      ·
                        rfl

theorem cell23_4207976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_4207976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4207976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4207976 prefixEnd_4207976 := by exact prefixLift 4207976
  have htrace : WordTrace (prefixWord ++ tailWord_4207976) baseStart_4207976 baseEnd_4207976 := by
    simpa [prefixWord, tailWord_4207976, baseEnd_4207976] using wordTrace_append hprefix tailTrace_4207976
  have hstable : (prefixWord ++ tailWord_4207976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4207976).length < 2 ^ (prefixWord ++ tailWord_4207976).sum := by decide
  have hdescent : baseEnd_4207976 < baseStart_4207976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4207976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208032 : List Nat := [2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 4]
def baseStart_4208032 : Nat := 118140960795 + 4208032 * 2 ^ 59
def prefixEnd_4208032 : Nat := 4983230072969 + 3 ^ 40 * 4208032 * 2
def baseEnd_4208032 : Nat := 2160743025500585289147619

theorem tailTrace_4208032 : CollatzResearch.WordTrace tailWord_4208032 prefixEnd_4208032 2160743025500585289147619 := by
  unfold tailWord_4208032
  simp only [CollatzResearch.WordTrace]
  refine ⟨76739767945513106747049175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102319690594017475662732233 76739767945513106747049175)
  ·
    refine ⟨115109651918269660120573763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76739767945513106747049175 115109651918269660120573763)
    ·
      refine ⟨172664477877404490180860645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115109651918269660120573763 172664477877404490180860645)
      ·
        refine ⟨32374589602013341908911371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172664477877404490180860645 32374589602013341908911371)
        ·
          refine ⟨48561884403020012863367057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32374589602013341908911371 48561884403020012863367057)
          ·
            refine ⟨36421413302265009647525293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48561884403020012863367057 36421413302265009647525293)
            ·
              refine ⟨13658029988349378617821985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36421413302265009647525293 13658029988349378617821985)
              ·
                refine ⟨10243522491262033963366489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13658029988349378617821985 10243522491262033963366489)
                ·
                  refine ⟨7682641868446525472524867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10243522491262033963366489 7682641868446525472524867)
                  ·
                    refine ⟨11523962802669788208787301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7682641868446525472524867 11523962802669788208787301)
                    ·
                      refine ⟨2160743025500585289147619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11523962802669788208787301 2160743025500585289147619)
                      ·
                        rfl

theorem cell23_4208032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_4208032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208032 prefixEnd_4208032 := by exact prefixLift 4208032
  have htrace : WordTrace (prefixWord ++ tailWord_4208032) baseStart_4208032 baseEnd_4208032 := by
    simpa [prefixWord, tailWord_4208032, baseEnd_4208032] using wordTrace_append hprefix tailTrace_4208032
  have hstable : (prefixWord ++ tailWord_4208032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208032).length < 2 ^ (prefixWord ++ tailWord_4208032).sum := by decide
  have hdescent : baseEnd_4208032 < baseStart_4208032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208086 : List Nat := [5, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_4208086 : Nat := 118140960795 + 4208086 * 2 ^ 59
def prefixEnd_4208086 : Nat := 4983230072969 + 3 ^ 40 * 4208086 * 2
def baseEnd_4208086 : Nat := 2160770753455928077872371

theorem tailTrace_4208086 : CollatzResearch.WordTrace tailWord_4208086 prefixEnd_4208086 2160770753455928077872371 := by
  unfold tailWord_4208086
  simp only [CollatzResearch.WordTrace]
  refine ⟨9592594089551911294785257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102321003621887053811042741 9592594089551911294785257)
  ·
    refine ⟨7194445567163933471088943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9592594089551911294785257 7194445567163933471088943)
    ·
      refine ⟨10791668350745900206633415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7194445567163933471088943 10791668350745900206633415)
      ·
        refine ⟨16187502526118850309950123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10791668350745900206633415 16187502526118850309950123)
        ·
          refine ⟨24281253789178275464925185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16187502526118850309950123 24281253789178275464925185)
          ·
            refine ⟨18210940341883706598693889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24281253789178275464925185 18210940341883706598693889)
            ·
              refine ⟨13658205256412779949020417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18210940341883706598693889 13658205256412779949020417)
              ·
                refine ⟨10243653942309584961765313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13658205256412779949020417 10243653942309584961765313)
                ·
                  refine ⟨7682740456732188721323985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10243653942309584961765313 7682740456732188721323985)
                  ·
                    refine ⟨5762055342549141540992989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7682740456732188721323985 5762055342549141540992989)
                    ·
                      refine ⟨2160770753455928077872371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5762055342549141540992989 2160770753455928077872371)
                      ·
                        rfl

theorem cell23_4208086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_4208086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208086 prefixEnd_4208086 := by exact prefixLift 4208086
  have htrace : WordTrace (prefixWord ++ tailWord_4208086) baseStart_4208086 baseEnd_4208086 := by
    simpa [prefixWord, tailWord_4208086, baseEnd_4208086] using wordTrace_append hprefix tailTrace_4208086
  have hstable : (prefixWord ++ tailWord_4208086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208086).length < 2 ^ (prefixWord ++ tailWord_4208086).sum := by decide
  have hdescent : baseEnd_4208086 < baseStart_4208086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208093 : List Nat := [1, 4, 3, 1, 1, 2, 4, 2, 1, 4]
def baseStart_4208093 : Nat := 118140960795 + 4208093 * 2 ^ 59
def prefixEnd_4208093 : Nat := 4983230072969 + 3 ^ 40 * 4208093 * 2
def baseEnd_4208093 : Nat := 720258115940169850161613

theorem tailTrace_4208093 : CollatzResearch.WordTrace tailWord_4208093 prefixEnd_4208093 720258115940169850161613 := by
  unfold tailWord_4208093
  simp only [CollatzResearch.WordTrace]
  refine ⟨153481760743805220912068933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102321173829203480608045955 153481760743805220912068933)
  ·
    refine ⟨28777830139463478921012925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153481760743805220912068933 28777830139463478921012925)
    ·
      refine ⟨10791686302298804595379847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28777830139463478921012925 10791686302298804595379847)
      ·
        refine ⟨16187529453448206893069771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10791686302298804595379847 16187529453448206893069771)
        ·
          refine ⟨24281294180172310339604657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16187529453448206893069771 24281294180172310339604657)
          ·
            refine ⟨18210970635129232754703493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24281294180172310339604657 18210970635129232754703493)
            ·
              refine ⟨3414556994086731141506905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18210970635129232754703493 3414556994086731141506905)
              ·
                refine ⟨2560917745565048356130179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3414556994086731141506905 2560917745565048356130179)
                ·
                  refine ⟨3841376618347572534195269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2560917745565048356130179 3841376618347572534195269)
                  ·
                    refine ⟨720258115940169850161613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3841376618347572534195269 720258115940169850161613)
                    ·
                      rfl

theorem cell23_4208093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_4208093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208093 prefixEnd_4208093 := by exact prefixLift 4208093
  have htrace : WordTrace (prefixWord ++ tailWord_4208093) baseStart_4208093 baseEnd_4208093 := by
    simpa [prefixWord, tailWord_4208093, baseEnd_4208093] using wordTrace_append hprefix tailTrace_4208093
  have hstable : (prefixWord ++ tailWord_4208093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208093).length < 2 ^ (prefixWord ++ tailWord_4208093).sum := by decide
  have hdescent : baseEnd_4208093 < baseStart_4208093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208122 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4]
def baseStart_4208122 : Nat := 118140960795 + 4208122 * 2 ^ 59
def prefixEnd_4208122 : Nat := 4983230072969 + 3 ^ 40 * 4208122 * 2
def baseEnd_4208122 : Nat := 2160789238759489937022205

theorem tailTrace_4208122 : CollatzResearch.WordTrace tailWord_4208122 prefixEnd_4208122 2160789238759489937022205 := by
  unfold tailWord_4208122
  simp only [CollatzResearch.WordTrace]
  refine ⟨38370704615175039716218655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102321878973800105909916413 38370704615175039716218655)
  ·
    refine ⟨57556056922762559574327983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38370704615175039716218655 57556056922762559574327983)
    ·
      refine ⟨86334085384143839361491975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57556056922762559574327983 86334085384143839361491975)
      ·
        refine ⟨129501128076215759042237963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86334085384143839361491975 129501128076215759042237963)
        ·
          refine ⟨194251692114323638563356945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129501128076215759042237963 194251692114323638563356945)
          ·
            refine ⟨145688769085742728922517709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194251692114323638563356945 145688769085742728922517709)
            ·
              refine ⟨54633288407153523345944141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145688769085742728922517709 54633288407153523345944141)
              ·
                refine ⟨20487483152682571254729053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54633288407153523345944141 20487483152682571254729053)
                ·
                  refine ⟨7682806182255964220523395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20487483152682571254729053 7682806182255964220523395)
                  ·
                    refine ⟨11524209273383946330785093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7682806182255964220523395 11524209273383946330785093)
                    ·
                      refine ⟨2160789238759489937022205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11524209273383946330785093 2160789238759489937022205)
                      ·
                        rfl

theorem cell23_4208122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_4208122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208122 prefixEnd_4208122 := by exact prefixLift 4208122
  have htrace : WordTrace (prefixWord ++ tailWord_4208122) baseStart_4208122 baseEnd_4208122 := by
    simpa [prefixWord, tailWord_4208122, baseEnd_4208122] using wordTrace_append hprefix tailTrace_4208122
  have hstable : (prefixWord ++ tailWord_4208122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208122).length < 2 ^ (prefixWord ++ tailWord_4208122).sum := by decide
  have hdescent : baseEnd_4208122 < baseStart_4208122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208145 : List Nat := [1, 2, 2, 1, 1, 2, 14]
def baseStart_4208145 : Nat := 118140960795 + 4208145 * 2 ^ 59
def prefixEnd_4208145 : Nat := 4983230072969 + 3 ^ 40 * 4208145 * 2
def baseEnd_4208145 : Nat := 26676556158204238852279

theorem tailTrace_4208145 : CollatzResearch.WordTrace tailWord_4208145 prefixEnd_4208145 26676556158204238852279 := by
  unfold tailWord_4208145
  simp only [CollatzResearch.WordTrace]
  refine ⟨153483657339616833792961889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102322438226411222528641259 153483657339616833792961889)
  ·
    refine ⟨115112743004712625344721417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153483657339616833792961889 115112743004712625344721417)
    ·
      refine ⟨86334557253534469008541063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115112743004712625344721417 86334557253534469008541063)
      ·
        refine ⟨129501835880301703512811595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86334557253534469008541063 129501835880301703512811595)
        ·
          refine ⟨194252753820452555269217393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129501835880301703512811595 194252753820452555269217393)
          ·
            refine ⟨145689565365339416451913045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194252753820452555269217393 145689565365339416451913045)
            ·
              refine ⟨26676556158204238852279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 145689565365339416451913045 26676556158204238852279)
              ·
                rfl

theorem cell23_4208145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 14].length) (baseStart_4208145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208145 prefixEnd_4208145 := by exact prefixLift 4208145
  have htrace : WordTrace (prefixWord ++ tailWord_4208145) baseStart_4208145 baseEnd_4208145 := by
    simpa [prefixWord, tailWord_4208145, baseEnd_4208145] using wordTrace_append hprefix tailTrace_4208145
  have hstable : (prefixWord ++ tailWord_4208145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208145).length < 2 ^ (prefixWord ++ tailWord_4208145).sum := by decide
  have hdescent : baseEnd_4208145 < baseStart_4208145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208149 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 4, 4]
def baseStart_4208149 : Nat := 118140960795 + 4208149 * 2 ^ 59
def prefixEnd_4208149 : Nat := 4983230072969 + 3 ^ 40 * 4208149 * 2
def baseEnd_4208149 : Nat := 720267700912387110461527

theorem tailTrace_4208149 : CollatzResearch.WordTrace tailWord_4208149 prefixEnd_4208149 720267700912387110461527 := by
  unfold tailWord_4208149
  simp only [CollatzResearch.WordTrace]
  refine ⟨153483803231602342476107501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102322535487734894984071667 153483803231602342476107501)
  ·
    refine ⟨57556426211850878428540313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153483803231602342476107501 57556426211850878428540313)
    ·
      refine ⟨43167319658888158821405235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57556426211850878428540313 43167319658888158821405235)
      ·
        refine ⟨64750979488332238232107853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43167319658888158821405235 64750979488332238232107853)
        ·
          refine ⟨24281617308124589337040445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64750979488332238232107853 24281617308124589337040445)
          ·
            refine ⟨9105606490546721001390167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24281617308124589337040445 9105606490546721001390167)
            ·
              refine ⟨13658409735820081502085251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9105606490546721001390167 13658409735820081502085251)
              ·
                refine ⟨20487614603730122253127877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13658409735820081502085251 20487614603730122253127877)
                ·
                  refine ⟨3841427738199397922461477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20487614603730122253127877 3841427738199397922461477)
                  ·
                    refine ⟨720267700912387110461527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3841427738199397922461477 720267700912387110461527)
                    ·
                      rfl

theorem cell23_4208149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_4208149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208149 prefixEnd_4208149 := by exact prefixLift 4208149
  have htrace : WordTrace (prefixWord ++ tailWord_4208149) baseStart_4208149 baseEnd_4208149 := by
    simpa [prefixWord, tailWord_4208149, baseEnd_4208149] using wordTrace_append hprefix tailTrace_4208149
  have hstable : (prefixWord ++ tailWord_4208149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208149).length < 2 ^ (prefixWord ++ tailWord_4208149).sum := by decide
  have hdescent : baseEnd_4208149 < baseStart_4208149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208179 : List Nat := [1, 1, 1, 2, 4, 5, 2, 7]
def baseStart_4208179 : Nat := 118140960795 + 4208179 * 2 ^ 59
def prefixEnd_4208179 : Nat := 4983230072969 + 3 ^ 40 * 4208179 * 2
def baseEnd_4208179 : Nat := 80030315079881341259609

theorem tailTrace_4208179 : CollatzResearch.WordTrace tailWord_4208179 prefixEnd_4208179 80030315079881341259609 := by
  unfold tailWord_4208179
  simp only [CollatzResearch.WordTrace]
  refine ⟨153484897421493657599699591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102323264947662438399799727 153484897421493657599699591)
  ·
    refine ⟨230227346132240486399549387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153484897421493657599699591 230227346132240486399549387)
    ·
      refine ⟨345341019198360729599324081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230227346132240486399549387 345341019198360729599324081)
      ·
        refine ⟨259005764398770547199493061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345341019198360729599324081 259005764398770547199493061)
        ·
          refine ⟨48563580824769477599904949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 259005764398770547199493061 48563580824769477599904949)
          ·
            refine ⟨4552835702322138524991089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48563580824769477599904949 4552835702322138524991089)
            ·
              refine ⟨3414626776741603893743317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4552835702322138524991089 3414626776741603893743317)
              ·
                refine ⟨80030315079881341259609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3414626776741603893743317 80030315079881341259609)
                ·
                  rfl

theorem cell23_4208179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 7].length) (baseStart_4208179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208179 prefixEnd_4208179 := by exact prefixLift 4208179
  have htrace : WordTrace (prefixWord ++ tailWord_4208179) baseStart_4208179 baseEnd_4208179 := by
    simpa [prefixWord, tailWord_4208179, baseEnd_4208179] using wordTrace_append hprefix tailTrace_4208179
  have hstable : (prefixWord ++ tailWord_4208179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208179).length < 2 ^ (prefixWord ++ tailWord_4208179).sum := by decide
  have hdescent : baseEnd_4208179 < baseStart_4208179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208202 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_4208202 : Nat := 118140960795 + 4208202 * 2 ^ 59
def prefixEnd_4208202 : Nat := 4983230072969 + 3 ^ 40 * 4208202 * 2
def baseEnd_4208202 : Nat := 2160830317211849624021837

theorem tailTrace_4208202 : CollatzResearch.WordTrace tailWord_4208202 prefixEnd_4208202 2160830317211849624021837 := by
  unfold tailWord_4208202
  simp only [CollatzResearch.WordTrace]
  refine ⟨38371434075102583131946715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102323824200273555018524573 38371434075102583131946715)
  ·
    refine ⟨57557151112653874697920073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38371434075102583131946715 57557151112653874697920073)
    ·
      refine ⟨43167863334490406023440055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57557151112653874697920073 43167863334490406023440055)
      ·
        refine ⟨64751795001735609035160083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43167863334490406023440055 64751795001735609035160083)
        ·
          refine ⟨97127692502603413552740125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64751795001735609035160083 97127692502603413552740125)
          ·
            refine ⟨36422884688476280082277547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97127692502603413552740125 36422884688476280082277547)
            ·
              refine ⟨54634327032714420123416321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36422884688476280082277547 54634327032714420123416321)
              ·
                refine ⟨40975745274535815092562241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54634327032714420123416321 40975745274535815092562241)
                ·
                  refine ⟨30731808955901861319421681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40975745274535815092562241 30731808955901861319421681)
                  ·
                    refine ⟨23048856716926395989566261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30731808955901861319421681 23048856716926395989566261)
                    ·
                      refine ⟨2160830317211849624021837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23048856716926395989566261 2160830317211849624021837)
                      ·
                        rfl

theorem cell23_4208202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_4208202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208202 prefixEnd_4208202 := by exact prefixLift 4208202
  have htrace : WordTrace (prefixWord ++ tailWord_4208202) baseStart_4208202 baseEnd_4208202 := by
    simpa [prefixWord, tailWord_4208202, baseEnd_4208202] using wordTrace_append hprefix tailTrace_4208202
  have hstable : (prefixWord ++ tailWord_4208202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208202).length < 2 ^ (prefixWord ++ tailWord_4208202).sum := by decide
  have hdescent : baseEnd_4208202 < baseStart_4208202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208206 : List Nat := [4, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3]
def baseStart_4208206 : Nat := 118140960795 + 4208206 * 2 ^ 59
def prefixEnd_4208206 : Nat := 4983230072969 + 3 ^ 40 * 4208206 * 2
def baseEnd_4208206 : Nat := 2160832371134467608371819

theorem tailTrace_4208206 : CollatzResearch.WordTrace tailWord_4208206 prefixEnd_4208206 2160832371134467608371819 := by
  unfold tailWord_4208206
  simp only [CollatzResearch.WordTrace]
  refine ⟨19185735274049480151366559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102323921461597227473954981 19185735274049480151366559)
  ·
    refine ⟨28778602911074220227049839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19185735274049480151366559 28778602911074220227049839)
    ·
      refine ⟨43167904366611330340574759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28778602911074220227049839 43167904366611330340574759)
      ·
        refine ⟨64751856549916995510862139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43167904366611330340574759 64751856549916995510862139)
        ·
          refine ⟨97127784824875493266293209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64751856549916995510862139 97127784824875493266293209)
          ·
            refine ⟨72845838618656619949719907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97127784824875493266293209 72845838618656619949719907)
            ·
              refine ⟨109268757927984929924579861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72845838618656619949719907 109268757927984929924579861)
              ·
                refine ⟨5121973027874293590214681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 109268757927984929924579861 5121973027874293590214681)
                ·
                  refine ⟨3841479770905720192661011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5121973027874293590214681 3841479770905720192661011)
                  ·
                    refine ⟨5762219656358580288991517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3841479770905720192661011 5762219656358580288991517)
                    ·
                      refine ⟨2160832371134467608371819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5762219656358580288991517 2160832371134467608371819)
                      ·
                        rfl

theorem cell23_4208206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_4208206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208206 prefixEnd_4208206 := by exact prefixLift 4208206
  have htrace : WordTrace (prefixWord ++ tailWord_4208206) baseStart_4208206 baseEnd_4208206 := by
    simpa [prefixWord, tailWord_4208206, baseEnd_4208206] using wordTrace_append hprefix tailTrace_4208206
  have hstable : (prefixWord ++ tailWord_4208206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208206).length < 2 ^ (prefixWord ++ tailWord_4208206).sum := by decide
  have hdescent : baseEnd_4208206 < baseStart_4208206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208263 : List Nat := [1, 1, 4, 2, 1, 3, 1, 4, 2, 2, 2]
def baseStart_4208263 : Nat := 118140960795 + 4208263 * 2 ^ 59
def prefixEnd_4208263 : Nat := 4983230072969 + 3 ^ 40 * 4208263 * 2
def baseEnd_4208263 : Nat := 2160861639531773885359057

theorem tailTrace_4208263 : CollatzResearch.WordTrace tailWord_4208263 prefixEnd_4208263 2160861639531773885359057 := by
  unfold tailWord_4208263
  simp only [CollatzResearch.WordTrace]
  refine ⟨153487961153189339945757443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102325307435459559963838295 153487961153189339945757443)
  ·
    refine ⟨230231941729784009918636165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153487961153189339945757443 230231941729784009918636165)
    ·
      refine ⟨43168489074334501859744281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230231941729784009918636165 43168489074334501859744281)
      ·
        refine ⟨32376366805750876394808211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43168489074334501859744281 32376366805750876394808211)
        ·
          refine ⟨48564550208626314592212317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32376366805750876394808211 48564550208626314592212317)
          ·
            refine ⟨18211706328234867972079619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48564550208626314592212317 18211706328234867972079619)
            ·
              refine ⟨27317559492352301958119429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18211706328234867972079619 27317559492352301958119429)
              ·
                refine ⟨5122042404816056617147393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27317559492352301958119429 5122042404816056617147393)
                ·
                  refine ⟨3841531803612042462860545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5122042404816056617147393 3841531803612042462860545)
                  ·
                    refine ⟨2881148852709031847145409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3841531803612042462860545 2881148852709031847145409)
                    ·
                      refine ⟨2160861639531773885359057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2881148852709031847145409 2160861639531773885359057)
                      ·
                        rfl

theorem cell23_4208263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_4208263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208263 prefixEnd_4208263 := by exact prefixLift 4208263
  have htrace : WordTrace (prefixWord ++ tailWord_4208263) baseStart_4208263 baseEnd_4208263 := by
    simpa [prefixWord, tailWord_4208263, baseEnd_4208263] using wordTrace_append hprefix tailTrace_4208263
  have hstable : (prefixWord ++ tailWord_4208263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208263).length < 2 ^ (prefixWord ++ tailWord_4208263).sum := by decide
  have hdescent : baseEnd_4208263 < baseStart_4208263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208279 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 3]
def baseStart_4208279 : Nat := 118140960795 + 4208279 * 2 ^ 59
def prefixEnd_4208279 : Nat := 4983230072969 + 3 ^ 40 * 4208279 * 2
def baseEnd_4208279 : Nat := 2160869855222245822758983

theorem tailTrace_4208279 : CollatzResearch.WordTrace tailWord_4208279 prefixEnd_4208279 2160869855222245822758983 := by
  unfold tailWord_4208279
  simp only [CollatzResearch.WordTrace]
  refine ⟨153488544721131374678339891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102325696480754249785559927 153488544721131374678339891)
  ·
    refine ⟨230232817081697062017509837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153488544721131374678339891 230232817081697062017509837)
    ·
      refine ⟨86337306405636398256566189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230232817081697062017509837 86337306405636398256566189)
      ·
        refine ⟨32376489902113649346212321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86337306405636398256566189 32376489902113649346212321)
        ·
          refine ⟨24282367426585237009659241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32376489902113649346212321 24282367426585237009659241)
          ·
            refine ⟨18211775569938927757244431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24282367426585237009659241 18211775569938927757244431)
            ·
              refine ⟨27317663354908391635866647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18211775569938927757244431 27317663354908391635866647)
              ·
                refine ⟨40976495032362587453799971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27317663354908391635866647 40976495032362587453799971)
                ·
                  refine ⟨61464742548543881180699957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40976495032362587453799971 61464742548543881180699957)
                  ·
                    refine ⟨5762319613925988860690621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61464742548543881180699957 5762319613925988860690621)
                    ·
                      refine ⟨2160869855222245822758983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5762319613925988860690621 2160869855222245822758983)
                      ·
                        rfl

theorem cell23_4208279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_4208279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208279 prefixEnd_4208279 := by exact prefixLift 4208279
  have htrace : WordTrace (prefixWord ++ tailWord_4208279) baseStart_4208279 baseEnd_4208279 := by
    simpa [prefixWord, tailWord_4208279, baseEnd_4208279] using wordTrace_append hprefix tailTrace_4208279
  have hstable : (prefixWord ++ tailWord_4208279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208279).length < 2 ^ (prefixWord ++ tailWord_4208279).sum := by decide
  have hdescent : baseEnd_4208279 < baseStart_4208279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208286 : List Nat := [4, 3, 1, 1, 1, 3, 1, 2, 7]
def baseStart_4208286 : Nat := 118140960795 + 4208286 * 2 ^ 59
def prefixEnd_4208286 : Nat := 4983230072969 + 3 ^ 40 * 4208286 * 2
def baseEnd_4208286 : Nat := 240097049954091921707939

theorem tailTrace_4208286 : CollatzResearch.WordTrace tailWord_4208286 prefixEnd_4208286 240097049954091921707939 := by
  unfold tailWord_4208286
  simp only [CollatzResearch.WordTrace]
  refine ⟨19186100004013251859230589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102325866688070676582563141 19186100004013251859230589)
  ·
    refine ⟨7194787501504969447211471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19186100004013251859230589 7194787501504969447211471)
    ·
      refine ⟨10792181252257454170817207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7194787501504969447211471 10792181252257454170817207)
      ·
        refine ⟨16188271878386181256225811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10792181252257454170817207 16188271878386181256225811)
        ·
          refine ⟨24282407817579271884338717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16188271878386181256225811 24282407817579271884338717)
          ·
            refine ⟨9105902931592226956627019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24282407817579271884338717 9105902931592226956627019)
            ·
              refine ⟨13658854397388340434940529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9105902931592226956627019 13658854397388340434940529)
              ·
                refine ⟨10244140798041255326205397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13658854397388340434940529 10244140798041255326205397)
                ·
                  refine ⟨240097049954091921707939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10244140798041255326205397 240097049954091921707939)
                  ·
                    rfl

theorem cell23_4208286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_4208286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208286 prefixEnd_4208286 := by exact prefixLift 4208286
  have htrace : WordTrace (prefixWord ++ tailWord_4208286) baseStart_4208286 baseEnd_4208286 := by
    simpa [prefixWord, tailWord_4208286, baseEnd_4208286] using wordTrace_append hprefix tailTrace_4208286
  have hstable : (prefixWord ++ tailWord_4208286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208286).length < 2 ^ (prefixWord ++ tailWord_4208286).sum := by decide
  have hdescent : baseEnd_4208286 < baseStart_4208286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208312 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 1, 10]
def baseStart_4208312 : Nat := 118140960795 + 4208312 * 2 ^ 59
def prefixEnd_4208312 : Nat := 4983230072969 + 3 ^ 40 * 4208312 * 2
def baseEnd_4208312 : Nat := 720295600027948064548777

theorem tailTrace_4208312 : CollatzResearch.WordTrace tailWord_4208312 prefixEnd_4208312 720295600027948064548777 := by
  unfold tailWord_4208312
  simp only [CollatzResearch.WordTrace]
  refine ⟨76744874165005910657145595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102326498886674547542860793 76744874165005910657145595)
  ·
    refine ⟨115117311247508865985718393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76744874165005910657145595 115117311247508865985718393)
    ·
      refine ⟨86337983435631649489288795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115117311247508865985718393 86337983435631649489288795)
      ·
        refine ⟨129506975153447474233933193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86337983435631649489288795 129506975153447474233933193)
        ·
          refine ⟨97130231365085605675449895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129506975153447474233933193 97130231365085605675449895)
          ·
            refine ⟨145695347047628408513174843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97130231365085605675449895 145695347047628408513174843)
            ·
              refine ⟨218543020571442612769762265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145695347047628408513174843 218543020571442612769762265)
              ·
                refine ⟨163907265428581959577321699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218543020571442612769762265 163907265428581959577321699)
                ·
                  refine ⟨245860898142872939365982549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163907265428581959577321699 245860898142872939365982549)
                  ·
                    refine ⟨720295600027948064548777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 245860898142872939365982549 720295600027948064548777)
                    ·
                      rfl

theorem cell23_4208312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_4208312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208312 prefixEnd_4208312 := by exact prefixLift 4208312
  have htrace : WordTrace (prefixWord ++ tailWord_4208312) baseStart_4208312 baseEnd_4208312 := by
    simpa [prefixWord, tailWord_4208312, baseEnd_4208312] using wordTrace_append hprefix tailTrace_4208312
  have hstable : (prefixWord ++ tailWord_4208312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208312).length < 2 ^ (prefixWord ++ tailWord_4208312).sum := by decide
  have hdescent : baseEnd_4208312 < baseStart_4208312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208319 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 4]
def baseStart_4208319 : Nat := 118140960795 + 4208319 * 2 ^ 59
def prefixEnd_4208319 : Nat := 4983230072969 + 3 ^ 40 * 4208319 * 2
def baseEnd_4208319 : Nat := 2160890394448425666258799

theorem tailTrace_4208319 : CollatzResearch.WordTrace tailWord_4208319 prefixEnd_4208319 2160890394448425666258799 := by
  unfold tailWord_4208319
  simp only [CollatzResearch.WordTrace]
  refine ⟨153490003640986461509796011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102326669093990974339864007 153490003640986461509796011)
  ·
    refine ⟨230235005461479692264694017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153490003640986461509796011 230235005461479692264694017)
    ·
      refine ⟨172676254096109769198520513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230235005461479692264694017 172676254096109769198520513)
      ·
        refine ⟨129507190572082326898890385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172676254096109769198520513 129507190572082326898890385)
        ·
          refine ⟨97130392929061745174167789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129507190572082326898890385 97130392929061745174167789)
          ·
            refine ⟨36423897348398154440312921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97130392929061745174167789 36423897348398154440312921)
            ·
              refine ⟨27317923011298615830234691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36423897348398154440312921 27317923011298615830234691)
              ·
                refine ⟨40976884516947923745352037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27317923011298615830234691 40976884516947923745352037)
                ·
                  refine ⟨7683165846927735702253507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40976884516947923745352037 7683165846927735702253507)
                  ·
                    refine ⟨11524748770391603553380261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7683165846927735702253507 11524748770391603553380261)
                    ·
                      refine ⟨2160890394448425666258799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11524748770391603553380261 2160890394448425666258799)
                      ·
                        rfl

theorem cell23_4208319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_4208319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208319 prefixEnd_4208319 := by exact prefixLift 4208319
  have htrace : WordTrace (prefixWord ++ tailWord_4208319) baseStart_4208319 baseEnd_4208319 := by
    simpa [prefixWord, tailWord_4208319, baseEnd_4208319] using wordTrace_append hprefix tailTrace_4208319
  have hstable : (prefixWord ++ tailWord_4208319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208319).length < 2 ^ (prefixWord ++ tailWord_4208319).sum := by decide
  have hdescent : baseEnd_4208319 < baseStart_4208319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208346 : List Nat := [3, 1, 1, 2, 2, 3, 2, 2, 3, 4]
def baseStart_4208346 : Nat := 118140960795 + 4208346 * 2 ^ 59
def prefixEnd_4208346 : Nat := 4983230072969 + 3 ^ 40 * 4208346 * 2
def baseEnd_4208346 : Nat := 720301419475365686873725

theorem tailTrace_4208346 : CollatzResearch.WordTrace tailWord_4208346 prefixEnd_4208346 720301419475365686873725 := by
  unfold tailWord_4208346
  simp only [CollatzResearch.WordTrace]
  refine ⟨38372747102972161280257223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102327325607925763414019261 38372747102972161280257223)
  ·
    refine ⟨57559120654458241920385835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38372747102972161280257223 57559120654458241920385835)
    ·
      refine ⟨86338680981687362880578753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57559120654458241920385835 86338680981687362880578753)
      ·
        refine ⟨64754010736265522160434065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86338680981687362880578753 64754010736265522160434065)
        ·
          refine ⟨48565508052199141620325549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64754010736265522160434065 48565508052199141620325549)
          ·
            refine ⟨18212065519574678107622081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48565508052199141620325549 18212065519574678107622081)
            ·
              refine ⟨13659049139681008580716561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18212065519574678107622081 13659049139681008580716561)
              ·
                refine ⟨10244286854760756435537421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13659049139681008580716561 10244286854760756435537421)
                ·
                  refine ⟨3841607570535283663326533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10244286854760756435537421 3841607570535283663326533)
                  ·
                    refine ⟨720301419475365686873725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3841607570535283663326533 720301419475365686873725)
                    ·
                      rfl

theorem cell23_4208346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 3, 4].length) (baseStart_4208346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208346 prefixEnd_4208346 := by exact prefixLift 4208346
  have htrace : WordTrace (prefixWord ++ tailWord_4208346) baseStart_4208346 baseEnd_4208346 := by
    simpa [prefixWord, tailWord_4208346, baseEnd_4208346] using wordTrace_append hprefix tailTrace_4208346
  have hstable : (prefixWord ++ tailWord_4208346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208346).length < 2 ^ (prefixWord ++ tailWord_4208346).sum := by decide
  have hdescent : baseEnd_4208346 < baseStart_4208346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208356 : List Nat := [2, 3, 1, 1, 1, 3, 2, 3, 2, 2, 3]
def baseStart_4208356 : Nat := 118140960795 + 4208356 * 2 ^ 59
def prefixEnd_4208356 : Nat := 4983230072969 + 3 ^ 40 * 4208356 * 2
def baseEnd_4208356 : Nat := 2160909393232642021496129

theorem tailTrace_4208356 : CollatzResearch.WordTrace tailWord_4208356 prefixEnd_4208356 2160909393232642021496129 := by
  unfold tailWord_4208356
  simp only [CollatzResearch.WordTrace]
  refine ⟨76745676570926208414446461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102327568761234944552595281 76745676570926208414446461)
  ·
    refine ⟨28779628714097328155417423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76745676570926208414446461 28779628714097328155417423)
    ·
      refine ⟨43169443071145992233126135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28779628714097328155417423 43169443071145992233126135)
      ·
        refine ⟨64754164606718988349689203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43169443071145992233126135 64754164606718988349689203)
        ·
          refine ⟨97131246910078482524533805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64754164606718988349689203 97131246910078482524533805)
          ·
            refine ⟨36424217591279430946700177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97131246910078482524533805 36424217591279430946700177)
            ·
              refine ⟨27318163193459573210025133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36424217591279430946700177 27318163193459573210025133)
              ·
                refine ⟨10244311197547339953759425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27318163193459573210025133 10244311197547339953759425)
                ·
                  refine ⟨7683233398160504965319569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10244311197547339953759425 7683233398160504965319569)
                  ·
                    refine ⟨5762425048620378723989677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7683233398160504965319569 5762425048620378723989677)
                    ·
                      refine ⟨2160909393232642021496129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5762425048620378723989677 2160909393232642021496129)
                      ·
                        rfl

theorem cell23_4208356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_4208356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208356 prefixEnd_4208356 := by exact prefixLift 4208356
  have htrace : WordTrace (prefixWord ++ tailWord_4208356) baseStart_4208356 baseEnd_4208356 := by
    simpa [prefixWord, tailWord_4208356, baseEnd_4208356] using wordTrace_append hprefix tailTrace_4208356
  have hstable : (prefixWord ++ tailWord_4208356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208356).length < 2 ^ (prefixWord ++ tailWord_4208356).sum := by decide
  have hdescent : baseEnd_4208356 < baseStart_4208356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208363 : List Nat := [1, 1, 1, 1, 2, 4, 5, 3, 1, 4]
def baseStart_4208363 : Nat := 118140960795 + 4208363 * 2 ^ 59
def prefixEnd_4208363 : Nat := 4983230072969 + 3 ^ 40 * 4208363 * 2
def baseEnd_4208363 : Nat := 720304329199074498036199

theorem tailTrace_4208363 : CollatzResearch.WordTrace tailWord_4208363 prefixEnd_4208363 720304329199074498036199 := by
  unfold tailWord_4208363
  simp only [CollatzResearch.WordTrace]
  refine ⟨153491608452827057024397743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102327738968551371349598495 153491608452827057024397743)
  ·
    refine ⟨230237412679240585536596615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153491608452827057024397743 230237412679240585536596615)
    ·
      refine ⟨345356119018860878304894923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230237412679240585536596615 345356119018860878304894923)
      ·
        refine ⟨518034178528291317457342385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345356119018860878304894923 518034178528291317457342385)
        ·
          refine ⟨388525633896218488093006789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 518034178528291317457342385 388525633896218488093006789)
          ·
            refine ⟨72848556355540966517438773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 388525633896218488093006789 72848556355540966517438773)
            ·
              refine ⟨6829552158331965611009885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72848556355540966517438773 6829552158331965611009885)
              ·
                refine ⟨2561082059374487104128707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6829552158331965611009885 2561082059374487104128707)
                ·
                  refine ⟨3841623089061730656193061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2561082059374487104128707 3841623089061730656193061)
                  ·
                    refine ⟨720304329199074498036199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3841623089061730656193061 720304329199074498036199)
                    ·
                      rfl

theorem cell23_4208363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 1, 4].length) (baseStart_4208363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208363 prefixEnd_4208363 := by exact prefixLift 4208363
  have htrace : WordTrace (prefixWord ++ tailWord_4208363) baseStart_4208363 baseEnd_4208363 := by
    simpa [prefixWord, tailWord_4208363, baseEnd_4208363] using wordTrace_append hprefix tailTrace_4208363
  have hstable : (prefixWord ++ tailWord_4208363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208363).length < 2 ^ (prefixWord ++ tailWord_4208363).sum := by decide
  have hdescent : baseEnd_4208363 < baseStart_4208363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208380 : List Nat := [2, 2, 2, 1, 3, 1, 5, 2, 1, 4]
def baseStart_4208380 : Nat := 118140960795 + 4208380 * 2 ^ 59
def prefixEnd_4208380 : Nat := 4983230072969 + 3 ^ 40 * 4208380 * 2
def baseEnd_4208380 : Nat := 720307238922783309198673

theorem tailTrace_4208380 : CollatzResearch.WordTrace tailWord_4208380 prefixEnd_4208380 720307238922783309198673 := by
  unfold tailWord_4208380
  simp only [CollatzResearch.WordTrace]
  refine ⟨76746114246882734463883297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102328152329176979285177729 76746114246882734463883297)
  ·
    refine ⟨57559585685162050847912473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76746114246882734463883297 57559585685162050847912473)
    ·
      refine ⟨43169689263871538135934355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57559585685162050847912473 43169689263871538135934355)
      ·
        refine ⟨64754533895807307203901533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43169689263871538135934355 64754533895807307203901533)
        ·
          refine ⟨24282950210927740201463075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64754533895807307203901533 24282950210927740201463075)
          ·
            refine ⟨36424425316391610302194613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24282950210927740201463075 36424425316391610302194613)
            ·
              refine ⟨3414789873411713465830745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36424425316391610302194613 3414789873411713465830745)
              ·
                refine ⟨2561092405058785099373059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3414789873411713465830745 2561092405058785099373059)
                ·
                  refine ⟨3841638607588177649059589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2561092405058785099373059 3841638607588177649059589)
                  ·
                    refine ⟨720307238922783309198673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3841638607588177649059589 720307238922783309198673)
                    ·
                      rfl

theorem cell23_4208380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_4208380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208380 prefixEnd_4208380 := by exact prefixLift 4208380
  have htrace : WordTrace (prefixWord ++ tailWord_4208380) baseStart_4208380 baseEnd_4208380 := by
    simpa [prefixWord, tailWord_4208380, baseEnd_4208380] using wordTrace_append hprefix tailTrace_4208380
  have hstable : (prefixWord ++ tailWord_4208380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208380).length < 2 ^ (prefixWord ++ tailWord_4208380).sum := by decide
  have hdescent : baseEnd_4208380 < baseStart_4208380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208396 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 3, 5, 2]
def baseStart_4208396 : Nat := 118140960795 + 4208396 * 2 ^ 59
def prefixEnd_4208396 : Nat := 4983230072969 + 3 ^ 40 * 4208396 * 2
def baseEnd_4208396 : Nat := 2160929932458821864995945

theorem tailTrace_4208396 : CollatzResearch.WordTrace tailWord_4208396 prefixEnd_4208396 2160929932458821864995945 := by
  unfold tailWord_4208396
  simp only [CollatzResearch.WordTrace]
  refine ⟨76746406030853751830174521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102328541374471669106899361 76746406030853751830174521)
  ·
    refine ⟨57559804523140313872630891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76746406030853751830174521 57559804523140313872630891)
    ·
      refine ⟨86339706784710470808946337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57559804523140313872630891 86339706784710470808946337)
      ·
        refine ⟨64754780088532853106709753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86339706784710470808946337 64754780088532853106709753)
        ·
          refine ⟨48566085066399639830032315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64754780088532853106709753 48566085066399639830032315)
          ·
            refine ⟨72849127599599459745048473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48566085066399639830032315 72849127599599459745048473)
            ·
              refine ⟨54636845699699594808786355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72849127599599459745048473 54636845699699594808786355)
              ·
                refine ⟨81955268549549392213179533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54636845699699594808786355 81955268549549392213179533)
                ·
                  refine ⟨30733225706081022079942325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81955268549549392213179533 30733225706081022079942325)
                  ·
                    refine ⟨2881239909945095819994593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30733225706081022079942325 2881239909945095819994593)
                    ·
                      refine ⟨2160929932458821864995945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2881239909945095819994593 2160929932458821864995945)
                      ·
                        rfl

theorem cell23_4208396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_4208396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208396 prefixEnd_4208396 := by exact prefixLift 4208396
  have htrace : WordTrace (prefixWord ++ tailWord_4208396) baseStart_4208396 baseEnd_4208396 := by
    simpa [prefixWord, tailWord_4208396, baseEnd_4208396] using wordTrace_append hprefix tailTrace_4208396
  have hstable : (prefixWord ++ tailWord_4208396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208396).length < 2 ^ (prefixWord ++ tailWord_4208396).sum := by decide
  have hdescent : baseEnd_4208396 < baseStart_4208396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208419 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 3, 6]
def baseStart_4208419 : Nat := 118140960795 + 4208419 * 2 ^ 59
def prefixEnd_4208419 : Nat := 4983230072969 + 3 ^ 40 * 4208419 * 2
def baseEnd_4208419 : Nat := 720313914171291758336113

theorem tailTrace_4208419 : CollatzResearch.WordTrace tailWord_4208419 prefixEnd_4208419 720313914171291758336113 := by
  unfold tailWord_4208419
  simp only [CollatzResearch.WordTrace]
  refine ⟨153493650940624178588436311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102329100627082785725624207 153493650940624178588436311)
  ·
    refine ⟨230240476410936267882654467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153493650940624178588436311 230240476410936267882654467)
    ·
      refine ⟨345360714616404401823981701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230240476410936267882654467 345360714616404401823981701)
      ·
        refine ⟨64755133990575825341996569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 345360714616404401823981701 64755133990575825341996569)
        ·
          refine ⟨48566350492931869006497427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64755133990575825341996569 48566350492931869006497427)
          ·
            refine ⟨72849525739397803509746141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48566350492931869006497427 72849525739397803509746141)
            ·
              refine ⟨27318572152274176316154803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72849525739397803509746141 27318572152274176316154803)
              ·
                refine ⟨40977858228411264474232205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27318572152274176316154803 40977858228411264474232205)
                ·
                  refine ⟨15366696835654224177837077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40977858228411264474232205 15366696835654224177837077)
                  ·
                    refine ⟨720313914171291758336113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15366696835654224177837077 720313914171291758336113)
                    ·
                      rfl

theorem cell23_4208419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 6].length) (baseStart_4208419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208419 prefixEnd_4208419 := by exact prefixLift 4208419
  have htrace : WordTrace (prefixWord ++ tailWord_4208419) baseStart_4208419 baseEnd_4208419 := by
    simpa [prefixWord, tailWord_4208419, baseEnd_4208419] using wordTrace_append hprefix tailTrace_4208419
  have hstable : (prefixWord ++ tailWord_4208419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208419).length < 2 ^ (prefixWord ++ tailWord_4208419).sum := by decide
  have hdescent : baseEnd_4208419 < baseStart_4208419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208437 : List Nat := [1, 3, 3, 1, 4, 1, 1, 4, 1, 1, 3]
def baseStart_4208437 : Nat := 118140960795 + 4208437 * 2 ^ 59
def prefixEnd_4208437 : Nat := 4983230072969 + 3 ^ 40 * 4208437 * 2
def baseEnd_4208437 : Nat := 2160950985165656204583257

theorem tailTrace_4208437 : CollatzResearch.WordTrace tailWord_4208437 prefixEnd_4208437 2160950985165656204583257 := by
  unfold tailWord_4208437
  simp only [CollatzResearch.WordTrace]
  refine ⟨153494307454558967662591565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102329538303039311775061043 153494307454558967662591565)
  ·
    refine ⟨57560365295459612873471837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153494307454558967662591565 57560365295459612873471837)
    ·
      refine ⟨21585136985797354827551939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57560365295459612873471837 21585136985797354827551939)
      ·
        refine ⟨32377705478696032241327909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21585136985797354827551939 32377705478696032241327909)
        ·
          refine ⟨6070819777255506045248983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32377705478696032241327909 6070819777255506045248983)
          ·
            refine ⟨9106229665883259067873475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6070819777255506045248983 9106229665883259067873475)
            ·
              refine ⟨13659344498824888601810213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9106229665883259067873475 13659344498824888601810213)
              ·
                refine ⟨2561127093529666612839415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13659344498824888601810213 2561127093529666612839415)
                ·
                  refine ⟨3841690640294499919259123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2561127093529666612839415 3841690640294499919259123)
                  ·
                    refine ⟨5762535960441749878888685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3841690640294499919259123 5762535960441749878888685)
                    ·
                      refine ⟨2160950985165656204583257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5762535960441749878888685 2160950985165656204583257)
                      ·
                        rfl

theorem cell23_4208437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_4208437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208437 prefixEnd_4208437 := by exact prefixLift 4208437
  have htrace : WordTrace (prefixWord ++ tailWord_4208437) baseStart_4208437 baseEnd_4208437 := by
    simpa [prefixWord, tailWord_4208437, baseEnd_4208437] using wordTrace_append hprefix tailTrace_4208437
  have hstable : (prefixWord ++ tailWord_4208437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208437).length < 2 ^ (prefixWord ++ tailWord_4208437).sum := by decide
  have hdescent : baseEnd_4208437 < baseStart_4208437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208439 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 6]
def baseStart_4208439 : Nat := 118140960795 + 4208439 * 2 ^ 59
def prefixEnd_4208439 : Nat := 4983230072969 + 3 ^ 40 * 4208439 * 2
def baseEnd_4208439 : Nat := 2160952012126965196758247

theorem tailTrace_4208439 : CollatzResearch.WordTrace tailWord_4208439 prefixEnd_4208439 2160952012126965196758247 := by
  unfold tailWord_4208439
  simp only [CollatzResearch.WordTrace]
  refine ⟨153494380400551722004164371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102329586933701148002776247 153494380400551722004164371)
  ·
    refine ⟨230241570600827583006246557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153494380400551722004164371 230241570600827583006246557)
    ·
      refine ⟨86340588975310343627342459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230241570600827583006246557 86340588975310343627342459)
      ·
        refine ⟨129510883462965515441013689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86340588975310343627342459 129510883462965515441013689)
        ·
          refine ⟨97133162597224136580760267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129510883462965515441013689 97133162597224136580760267)
          ·
            refine ⟨145699743895836204871140401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97133162597224136580760267 145699743895836204871140401)
            ·
              refine ⟨109274807921877153653355301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145699743895836204871140401 109274807921877153653355301)
              ·
                refine ⟨20489026485351966310004119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109274807921877153653355301 20489026485351966310004119)
                ·
                  refine ⟨30733539728027949465006179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20489026485351966310004119 30733539728027949465006179)
                  ·
                    refine ⟨46100309592041924197509269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30733539728027949465006179 46100309592041924197509269)
                    ·
                      refine ⟨2160952012126965196758247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46100309592041924197509269 2160952012126965196758247)
                      ·
                        rfl

theorem cell23_4208439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_4208439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208439 prefixEnd_4208439 := by exact prefixLift 4208439
  have htrace : WordTrace (prefixWord ++ tailWord_4208439) baseStart_4208439 baseEnd_4208439 := by
    simpa [prefixWord, tailWord_4208439, baseEnd_4208439] using wordTrace_append hprefix tailTrace_4208439
  have hstable : (prefixWord ++ tailWord_4208439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208439).length < 2 ^ (prefixWord ++ tailWord_4208439).sum := by decide
  have hdescent : baseEnd_4208439 < baseStart_4208439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208456 : List Nat := [2, 1, 3, 1, 1, 4, 1, 3, 1, 2, 4]
def baseStart_4208456 : Nat := 118140960795 + 4208456 * 2 ^ 59
def prefixEnd_4208456 : Nat := 4983230072969 + 3 ^ 40 * 4208456 * 2
def baseEnd_4208456 : Nat := 2160960741298091630245669

theorem tailTrace_4208456 : CollatzResearch.WordTrace tailWord_4208456 prefixEnd_4208456 2160960741298091630245669 := by
  unfold tailWord_4208456
  simp only [CollatzResearch.WordTrace]
  refine ⟨76747500220745066953766611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102330000294326755938355481 76747500220745066953766611)
  ·
    refine ⟨115121250331117600430649917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76747500220745066953766611 115121250331117600430649917)
    ·
      refine ⟨43170468874169100161493719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115121250331117600430649917 43170468874169100161493719)
      ·
        refine ⟨64755703311253650242240579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43170468874169100161493719 64755703311253650242240579)
        ·
          refine ⟨97133554966880475363360869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64755703311253650242240579 97133554966880475363360869)
          ·
            refine ⟨18212541556290089130630163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97133554966880475363360869 18212541556290089130630163)
            ·
              refine ⟨27318812334435133695945245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18212541556290089130630163 27318812334435133695945245)
              ·
                refine ⟨10244554625413175135979467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27318812334435133695945245 10244554625413175135979467)
                ·
                  refine ⟨15366831938119762703969201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10244554625413175135979467 15366831938119762703969201)
                  ·
                    refine ⟨11525123953589822027976901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15366831938119762703969201 11525123953589822027976901)
                    ·
                      refine ⟨2160960741298091630245669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11525123953589822027976901 2160960741298091630245669)
                      ·
                        rfl

theorem cell23_4208456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_4208456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208456 prefixEnd_4208456 := by exact prefixLift 4208456
  have htrace : WordTrace (prefixWord ++ tailWord_4208456) baseStart_4208456 baseEnd_4208456 := by
    simpa [prefixWord, tailWord_4208456, baseEnd_4208456] using wordTrace_append hprefix tailTrace_4208456
  have hstable : (prefixWord ++ tailWord_4208456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208456).length < 2 ^ (prefixWord ++ tailWord_4208456).sum := by decide
  have hdescent : baseEnd_4208456 < baseStart_4208456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208480 : List Nat := [2, 1, 1, 3, 3, 2, 4, 1, 1, 2, 3]
def baseStart_4208480 : Nat := 118140960795 + 4208480 * 2 ^ 59
def prefixEnd_4208480 : Nat := 4983230072969 + 3 ^ 40 * 4208480 * 2
def baseEnd_4208480 : Nat := 2160973064833799536345559

theorem tailTrace_4208480 : CollatzResearch.WordTrace tailWord_4208480 prefixEnd_4208480 2160973064833799536345559 := by
  unfold tailWord_4208480
  simp only [CollatzResearch.WordTrace]
  refine ⟨76747937896701593003203447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102330583862268790670937929 76747937896701593003203447)
  ·
    refine ⟨115121906845052389504805171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76747937896701593003203447 115121906845052389504805171)
    ·
      refine ⟨172682860267578584257207757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115121906845052389504805171 172682860267578584257207757)
      ·
        refine ⟨64756072600341969096452909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172682860267578584257207757 64756072600341969096452909)
        ·
          refine ⟨24283527225128238411169841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64756072600341969096452909 24283527225128238411169841)
          ·
            refine ⟨18212645418846178808377381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24283527225128238411169841 18212645418846178808377381)
            ·
              refine ⟨3414871016033658526570759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18212645418846178808377381 3414871016033658526570759)
              ·
                refine ⟨5122306524050487789856139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3414871016033658526570759 5122306524050487789856139)
                ·
                  refine ⟨7683459786075731684784209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5122306524050487789856139 7683459786075731684784209)
                  ·
                    refine ⟨5762594839556798763588157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7683459786075731684784209 5762594839556798763588157)
                    ·
                      refine ⟨2160973064833799536345559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5762594839556798763588157 2160973064833799536345559)
                      ·
                        rfl

theorem cell23_4208480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_4208480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208480 prefixEnd_4208480 := by exact prefixLift 4208480
  have htrace : WordTrace (prefixWord ++ tailWord_4208480) baseStart_4208480 baseEnd_4208480 := by
    simpa [prefixWord, tailWord_4208480, baseEnd_4208480] using wordTrace_append hprefix tailTrace_4208480
  have hstable : (prefixWord ++ tailWord_4208480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208480).length < 2 ^ (prefixWord ++ tailWord_4208480).sum := by decide
  have hdescent : baseEnd_4208480 < baseStart_4208480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208494 : List Nat := [4, 1, 2, 3, 1, 1, 2, 4, 1, 2, 2]
def baseStart_4208494 : Nat := 118140960795 + 4208494 * 2 ^ 59
def prefixEnd_4208494 : Nat := 4983230072969 + 3 ^ 40 * 4208494 * 2
def baseEnd_4208494 : Nat := 2160980253562962481570495

theorem tailTrace_4208494 : CollatzResearch.WordTrace tailWord_4208494 prefixEnd_4208494 2160980253562962481570495 := by
  unfold tailWord_4208494
  simp only [CollatzResearch.WordTrace]
  refine ⟨19187048301919058299677067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102330924276901644264944357 19187048301919058299677067)
  ·
    refine ⟨28780572452878587449515601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19187048301919058299677067 28780572452878587449515601)
    ·
      refine ⟨21585429339658940587136701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28780572452878587449515601 21585429339658940587136701)
      ·
        refine ⟨8094536002372102720176263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21585429339658940587136701 8094536002372102720176263)
        ·
          refine ⟨12141804003558154080264395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8094536002372102720176263 12141804003558154080264395)
          ·
            refine ⟨18212706005337231120396593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12141804003558154080264395 18212706005337231120396593)
            ·
              refine ⟨13659529504002923340297445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18212706005337231120396593 13659529504002923340297445)
              ·
                refine ⟨2561161782000548126305771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13659529504002923340297445 2561161782000548126305771)
                ·
                  refine ⟨3841742673000822189458657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2561161782000548126305771 3841742673000822189458657)
                  ·
                    refine ⟨2881307004750616642093993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3841742673000822189458657 2881307004750616642093993)
                    ·
                      refine ⟨2160980253562962481570495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2881307004750616642093993 2160980253562962481570495)
                      ·
                        rfl

theorem cell23_4208494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_4208494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208494 prefixEnd_4208494 := by exact prefixLift 4208494
  have htrace : WordTrace (prefixWord ++ tailWord_4208494) baseStart_4208494 baseEnd_4208494 := by
    simpa [prefixWord, tailWord_4208494, baseEnd_4208494] using wordTrace_append hprefix tailTrace_4208494
  have hstable : (prefixWord ++ tailWord_4208494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208494).length < 2 ^ (prefixWord ++ tailWord_4208494).sum := by decide
  have hdescent : baseEnd_4208494 < baseStart_4208494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208516 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_4208516 : Nat := 118140960795 + 4208516 * 2 ^ 59
def prefixEnd_4208516 : Nat := 4983230072969 + 3 ^ 40 * 4208516 * 2
def baseEnd_4208516 : Nat := 2160991550137361395495393

theorem tailTrace_4208516 : CollatzResearch.WordTrace tailWord_4208516 prefixEnd_4208516 2160991550137361395495393 := by
  unfold tailWord_4208516
  simp only [CollatzResearch.WordTrace]
  refine ⟨76748594410636382077358701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102331459214181842769811601 76748594410636382077358701)
  ·
    refine ⟨28780722903988643279009513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76748594410636382077358701 28780722903988643279009513)
    ·
      refine ⟨21585542177991482459257135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28780722903988643279009513 21585542177991482459257135)
      ·
        refine ⟨32378313266987223688885703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21585542177991482459257135 32378313266987223688885703)
        ·
          refine ⟨48567469900480835533328555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32378313266987223688885703 48567469900480835533328555)
          ·
            refine ⟨72851204850721253299992833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48567469900480835533328555 72851204850721253299992833)
            ·
              refine ⟨54638403638040939974994625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72851204850721253299992833 54638403638040939974994625)
              ·
                refine ⟨40978802728530704981245969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54638403638040939974994625 40978802728530704981245969)
                ·
                  refine ⟨30734102046398028735934477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40978802728530704981245969 30734102046398028735934477)
                  ·
                    refine ⟨11525288267399260775975429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30734102046398028735934477 11525288267399260775975429)
                    ·
                      refine ⟨2160991550137361395495393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11525288267399260775975429 2160991550137361395495393)
                      ·
                        rfl

theorem cell23_4208516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_4208516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208516 prefixEnd_4208516 := by exact prefixLift 4208516
  have htrace : WordTrace (prefixWord ++ tailWord_4208516) baseStart_4208516 baseEnd_4208516 := by
    simpa [prefixWord, tailWord_4208516, baseEnd_4208516] using wordTrace_append hprefix tailTrace_4208516
  have hstable : (prefixWord ++ tailWord_4208516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208516).length < 2 ^ (prefixWord ++ tailWord_4208516).sum := by decide
  have hdescent : baseEnd_4208516 < baseStart_4208516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208533 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 3, 4, 2]
def baseStart_4208533 : Nat := 118140960795 + 4208533 * 2 ^ 59
def prefixEnd_4208533 : Nat := 4983230072969 + 3 ^ 40 * 4208533 * 2
def baseEnd_4208533 : Nat := 2161000279308487828982815

theorem tailTrace_4208533 : CollatzResearch.WordTrace tailWord_4208533 prefixEnd_4208533 2161000279308487828982815 := by
  unfold tailWord_4208533
  simp only [CollatzResearch.WordTrace]
  refine ⟨153497808862211176058086253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102331872574807450705390835 153497808862211176058086253)
  ·
    refine ⟨57561678323329191021782345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153497808862211176058086253 57561678323329191021782345)
    ·
      refine ⟨43171258742496893266336759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57561678323329191021782345 43171258742496893266336759)
      ·
        refine ⟨64756888113745339899505139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43171258742496893266336759 64756888113745339899505139)
        ·
          refine ⟨97135332170618009849257709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64756888113745339899505139 97135332170618009849257709)
          ·
            refine ⟨36425749563981753693471641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97135332170618009849257709 36425749563981753693471641)
            ·
              refine ⟨27319312172986315270103731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36425749563981753693471641 27319312172986315270103731)
              ·
                refine ⟨40978968259479472905155597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27319312172986315270103731 40978968259479472905155597)
                ·
                  refine ⟨15367113097304802339433349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40978968259479472905155597 15367113097304802339433349)
                  ·
                    refine ⟨2881333705744650438643753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15367113097304802339433349 2881333705744650438643753)
                    ·
                      refine ⟨2161000279308487828982815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2881333705744650438643753 2161000279308487828982815)
                      ·
                        rfl

theorem cell23_4208533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_4208533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208533 prefixEnd_4208533 := by exact prefixLift 4208533
  have htrace : WordTrace (prefixWord ++ tailWord_4208533) baseStart_4208533 baseEnd_4208533 := by
    simpa [prefixWord, tailWord_4208533, baseEnd_4208533] using wordTrace_append hprefix tailTrace_4208533
  have hstable : (prefixWord ++ tailWord_4208533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208533).length < 2 ^ (prefixWord ++ tailWord_4208533).sum := by decide
  have hdescent : baseEnd_4208533 < baseStart_4208533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208586 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 1, 7]
def baseStart_4208586 : Nat := 118140960795 + 4208586 * 2 ^ 59
def prefixEnd_4208586 : Nat := 4983230072969 + 3 ^ 40 * 4208586 * 2
def baseEnd_4208586 : Nat := 720342497927725373873357

theorem tailTrace_4208586 : CollatzResearch.WordTrace tailWord_4208586 prefixEnd_4208586 720342497927725373873357 := by
  unfold tailWord_4208586
  simp only [CollatzResearch.WordTrace]
  refine ⟨38374935482754791527441403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102333161287346110739843741 38374935482754791527441403)
  ·
    refine ⟨57562403224132187291162105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38374935482754791527441403 57562403224132187291162105)
    ·
      refine ⟨43171802418099140468371579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57562403224132187291162105 43171802418099140468371579)
      ·
        refine ⟨64757703627148710702557369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43171802418099140468371579 64757703627148710702557369)
        ·
          refine ⟨48568277720361533026918027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64757703627148710702557369 48568277720361533026918027)
          ·
            refine ⟨72852416580542299540377041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48568277720361533026918027 72852416580542299540377041)
            ·
              refine ⟨54639312435406724655282781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72852416580542299540377041 54639312435406724655282781)
              ·
                refine ⟨20489742163277521745731043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54639312435406724655282781 20489742163277521745731043)
                ·
                  refine ⟨30734613244916282618596565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20489742163277521745731043 30734613244916282618596565)
                  ·
                    refine ⟨720342497927725373873357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30734613244916282618596565 720342497927725373873357)
                    ·
                      rfl

theorem cell23_4208586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_4208586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208586 prefixEnd_4208586 := by exact prefixLift 4208586
  have htrace : WordTrace (prefixWord ++ tailWord_4208586) baseStart_4208586 baseEnd_4208586 := by
    simpa [prefixWord, tailWord_4208586, baseEnd_4208586] using wordTrace_append hprefix tailTrace_4208586
  have hstable : (prefixWord ++ tailWord_4208586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208586).length < 2 ^ (prefixWord ++ tailWord_4208586).sum := by decide
  have hdescent : baseEnd_4208586 < baseStart_4208586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208607 : List Nat := [1, 1, 2, 3, 4, 3, 2, 2, 5]
def baseStart_4208607 : Nat := 118140960795 + 4208607 * 2 ^ 59
def prefixEnd_4208607 : Nat := 4983230072969 + 3 ^ 40 * 4208607 * 2
def baseEnd_4208607 : Nat := 240115364097435615495275

theorem tailTrace_4208607 : CollatzResearch.WordTrace tailWord_4208607 prefixEnd_4208607 240115364097435615495275 := by
  unfold tailWord_4208607
  simp only [CollatzResearch.WordTrace]
  refine ⟨153500507863943086696280075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102333671909295391130853383 153500507863943086696280075)
  ·
    refine ⟨230250761795914630044420113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153500507863943086696280075 230250761795914630044420113)
    ·
      refine ⟨172688071346935972533315085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230250761795914630044420113 172688071346935972533315085)
      ·
        refine ⟨64758026755100989699993157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172688071346935972533315085 64758026755100989699993157)
        ·
          refine ⟨12142130016581435568748717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64758026755100989699993157 12142130016581435568748717)
          ·
            refine ⟨4553298756218038338280769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12142130016581435568748717 4553298756218038338280769)
            ·
              refine ⟨3414974067163528753710577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4553298756218038338280769 3414974067163528753710577)
              ·
                refine ⟨2561230550372646565282933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3414974067163528753710577 2561230550372646565282933)
                ·
                  refine ⟨240115364097435615495275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2561230550372646565282933 240115364097435615495275)
                  ·
                    rfl

theorem cell23_4208607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 5].length) (baseStart_4208607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208607 prefixEnd_4208607 := by exact prefixLift 4208607
  have htrace : WordTrace (prefixWord ++ tailWord_4208607) baseStart_4208607 baseEnd_4208607 := by
    simpa [prefixWord, tailWord_4208607, baseEnd_4208607] using wordTrace_append hprefix tailTrace_4208607
  have hstable : (prefixWord ++ tailWord_4208607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208607).length < 2 ^ (prefixWord ++ tailWord_4208607).sum := by decide
  have hdescent : baseEnd_4208607 < baseStart_4208607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208616 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 2, 8]
def baseStart_4208616 : Nat := 118140960795 + 4208616 * 2 ^ 59
def prefixEnd_4208616 : Nat := 4983230072969 + 3 ^ 40 * 4208616 * 2
def baseEnd_4208616 : Nat := 720347632734270334748311

theorem tailTrace_4208616 : CollatzResearch.WordTrace tailWord_4208616 prefixEnd_4208616 720347632734270334748311 := by
  unfold tailWord_4208616
  simp only [CollatzResearch.WordTrace]
  refine ⟨76750418060455240616678851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102333890747273654155571801 76750418060455240616678851)
  ·
    refine ⟨115125627090682860925018277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76750418060455240616678851 115125627090682860925018277)
    ·
      refine ⟨21586055079503036423440927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115125627090682860925018277 21586055079503036423440927)
      ·
        refine ⟨32379082619254554635161391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21586055079503036423440927 32379082619254554635161391)
        ·
          refine ⟨48568623928881831952742087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32379082619254554635161391 48568623928881831952742087)
          ·
            refine ⟨72852935893322747929113131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48568623928881831952742087 72852935893322747929113131)
            ·
              refine ⟨109279403839984121893669697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72852935893322747929113131 109279403839984121893669697)
              ·
                refine ⟨81959552879988091420252273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109279403839984121893669697 81959552879988091420252273)
                ·
                  refine ⟨61469664659991068565189205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81959552879988091420252273 61469664659991068565189205)
                  ·
                    refine ⟨720347632734270334748311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61469664659991068565189205 720347632734270334748311)
                    ·
                      rfl

theorem cell23_4208616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_4208616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208616 prefixEnd_4208616 := by exact prefixLift 4208616
  have htrace : WordTrace (prefixWord ++ tailWord_4208616) baseStart_4208616 baseEnd_4208616 := by
    simpa [prefixWord, tailWord_4208616, baseEnd_4208616] using wordTrace_append hprefix tailTrace_4208616
  have hstable : (prefixWord ++ tailWord_4208616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208616).length < 2 ^ (prefixWord ++ tailWord_4208616).sum := by decide
  have hdescent : baseEnd_4208616 < baseStart_4208616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208633 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 5, 4]
def baseStart_4208633 : Nat := 118140960795 + 4208633 * 2 ^ 59
def prefixEnd_4208633 : Nat := 4983230072969 + 3 ^ 40 * 4208633 * 2
def baseEnd_4208633 : Nat := 720350542457979145910785

theorem tailTrace_4208633 : CollatzResearch.WordTrace tailWord_4208633 prefixEnd_4208633 720350542457979145910785 := by
  unfold tailWord_4208633
  simp only [CollatzResearch.WordTrace]
  refine ⟨153501456161848893136726553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102334304107899262091151035 153501456161848893136726553)
  ·
    refine ⟨115126092121386669852544915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153501456161848893136726553 115126092121386669852544915)
    ·
      refine ⟨172689138182080004778817373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115126092121386669852544915 172689138182080004778817373)
      ·
        refine ⟨64758426818280001792056515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172689138182080004778817373 64758426818280001792056515)
        ·
          refine ⟨97137640227420002688084773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64758426818280001792056515 97137640227420002688084773)
          ·
            refine ⟨18213307542641250504015895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97137640227420002688084773 18213307542641250504015895)
            ·
              refine ⟨27319961313961875756023843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18213307542641250504015895 27319961313961875756023843)
              ·
                refine ⟨40979941970942813634035765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27319961313961875756023843 40979941970942813634035765)
                ·
                  refine ⟨3841869559775888778190853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40979941970942813634035765 3841869559775888778190853)
                  ·
                    refine ⟨720350542457979145910785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3841869559775888778190853 720350542457979145910785)
                    ·
                      rfl

theorem cell23_4208633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 4].length) (baseStart_4208633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208633 prefixEnd_4208633 := by exact prefixLift 4208633
  have htrace : WordTrace (prefixWord ++ tailWord_4208633) baseStart_4208633 baseEnd_4208633 := by
    simpa [prefixWord, tailWord_4208633, baseEnd_4208633] using wordTrace_append hprefix tailTrace_4208633
  have hstable : (prefixWord ++ tailWord_4208633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208633).length < 2 ^ (prefixWord ++ tailWord_4208633).sum := by decide
  have hdescent : baseEnd_4208633 < baseStart_4208633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208693 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 3, 5]
def baseStart_4208693 : Nat := 118140960795 + 4208693 * 2 ^ 59
def prefixEnd_4208693 : Nat := 4983230072969 + 3 ^ 40 * 4208693 * 2
def baseEnd_4208693 : Nat := 720360812071069067660693

theorem tailTrace_4208693 : CollatzResearch.WordTrace tailWord_4208693 prefixEnd_4208693 720360812071069067660693 := by
  unfold tailWord_4208693
  simp only [CollatzResearch.WordTrace]
  refine ⟨153503644541631523383910733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102335763027754348922607155 153503644541631523383910733)
  ·
    refine ⟨57563866703111821268966525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153503644541631523383910733 57563866703111821268966525)
    ·
      refine ⟨21586450013666932975862447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57563866703111821268966525 21586450013666932975862447)
      ·
        refine ⟨32379675020500399463793671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21586450013666932975862447 32379675020500399463793671)
        ·
          refine ⟨48569512530750599195690507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32379675020500399463793671 48569512530750599195690507)
          ·
            refine ⟨72854268796125898793535761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48569512530750599195690507 72854268796125898793535761)
            ·
              refine ⟨54640701597094424095151821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72854268796125898793535761 54640701597094424095151821)
              ·
                refine ⟨20490263098910409035681933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54640701597094424095151821 20490263098910409035681933)
                ·
                  refine ⟨7683848662091403388380725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20490263098910409035681933 7683848662091403388380725)
                  ·
                    refine ⟨720360812071069067660693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7683848662091403388380725 720360812071069067660693)
                    ·
                      rfl

theorem cell23_4208693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_4208693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208693 prefixEnd_4208693 := by exact prefixLift 4208693
  have htrace : WordTrace (prefixWord ++ tailWord_4208693) baseStart_4208693 baseEnd_4208693 := by
    simpa [prefixWord, tailWord_4208693, baseEnd_4208693] using wordTrace_append hprefix tailTrace_4208693
  have hstable : (prefixWord ++ tailWord_4208693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208693).length < 2 ^ (prefixWord ++ tailWord_4208693).sum := by decide
  have hdescent : baseEnd_4208693 < baseStart_4208693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208700 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 1, 5, 2]
def baseStart_4208700 : Nat := 118140960795 + 4208700 * 2 ^ 59
def prefixEnd_4208700 : Nat := 4983230072969 + 3 ^ 40 * 4208700 * 2
def baseEnd_4208700 : Nat := 2161086030577788675594547

theorem tailTrace_4208700 : CollatzResearch.WordTrace tailWord_4208700 prefixEnd_4208700 2161086030577788675594547 := by
  unfold tailWord_4208700
  simp only [CollatzResearch.WordTrace]
  refine ⟨76751949926303081789707777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102335933235070775719610369 76751949926303081789707777)
  ·
    refine ⟨57563962444727311342280833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76751949926303081789707777 57563962444727311342280833)
    ·
      refine ⟨43172971833545483506710625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57563962444727311342280833 43172971833545483506710625)
      ·
        refine ⟨32379728875159112630032969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43172971833545483506710625 32379728875159112630032969)
        ·
          refine ⟨24284796656369334472524727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32379728875159112630032969 24284796656369334472524727)
          ·
            refine ⟨36427194984554001708787091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24284796656369334472524727 36427194984554001708787091)
            ·
              refine ⟨54640792476831002563180637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36427194984554001708787091 54640792476831002563180637)
              ·
                refine ⟨20490297178811625961192739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54640792476831002563180637 20490297178811625961192739)
                ·
                  refine ⟨30735445768217438941789109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20490297178811625961192739 30735445768217438941789109)
                  ·
                    refine ⟨2881448040770384900792729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30735445768217438941789109 2881448040770384900792729)
                    ·
                      refine ⟨2161086030577788675594547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2881448040770384900792729 2161086030577788675594547)
                      ·
                        rfl

theorem cell23_4208700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_4208700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208700 prefixEnd_4208700 := by exact prefixLift 4208700
  have htrace : WordTrace (prefixWord ++ tailWord_4208700) baseStart_4208700 baseEnd_4208700 := by
    simpa [prefixWord, tailWord_4208700, baseEnd_4208700] using wordTrace_append hprefix tailTrace_4208700
  have hstable : (prefixWord ++ tailWord_4208700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208700).length < 2 ^ (prefixWord ++ tailWord_4208700).sum := by decide
  have hdescent : baseEnd_4208700 < baseStart_4208700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208707 : List Nat := [1, 1, 1, 3, 1, 2, 2, 7, 1, 1, 3]
def baseStart_4208707 : Nat := 118140960795 + 4208707 * 2 ^ 59
def prefixEnd_4208707 : Nat := 4983230072969 + 3 ^ 40 * 4208707 * 2
def baseEnd_4208707 : Nat := 2161089624942370148207015

theorem tailTrace_4208707 : CollatzResearch.WordTrace tailWord_4208707 prefixEnd_4208707 2161089624942370148207015 := by
  unfold tailWord_4208707
  simp only [CollatzResearch.WordTrace]
  refine ⟨153504155163580803774920375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102336103442387202516613583 153504155163580803774920375)
  ·
    refine ⟨230256232745371205662380563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153504155163580803774920375 230256232745371205662380563)
    ·
      refine ⟨345384349118056808493570845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230256232745371205662380563 345384349118056808493570845)
      ·
        refine ⟨129519130919271303185089067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 345384349118056808493570845 129519130919271303185089067)
        ·
          refine ⟨194278696378906954777633601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129519130919271303185089067 194278696378906954777633601)
          ·
            refine ⟨145709022284180216083225201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194278696378906954777633601 145709022284180216083225201)
            ·
              refine ⟨109281766713135162062418901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145709022284180216083225201 109281766713135162062418901)
              ·
                refine ⟨2561291407339105360837943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 109281766713135162062418901 2561291407339105360837943)
                ·
                  refine ⟨3841937111008658041256915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2561291407339105360837943 3841937111008658041256915)
                  ·
                    refine ⟨5762905666512987061885373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3841937111008658041256915 5762905666512987061885373)
                    ·
                      refine ⟨2161089624942370148207015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5762905666512987061885373 2161089624942370148207015)
                      ·
                        rfl

theorem cell23_4208707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 1, 1, 3].length) (baseStart_4208707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208707 prefixEnd_4208707 := by exact prefixLift 4208707
  have htrace : WordTrace (prefixWord ++ tailWord_4208707) baseStart_4208707 baseEnd_4208707 := by
    simpa [prefixWord, tailWord_4208707, baseEnd_4208707] using wordTrace_append hprefix tailTrace_4208707
  have hstable : (prefixWord ++ tailWord_4208707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208707).length < 2 ^ (prefixWord ++ tailWord_4208707).sum := by decide
  have hdescent : baseEnd_4208707 < baseStart_4208707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208723 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 8, 4]
def baseStart_4208723 : Nat := 118140960795 + 4208723 * 2 ^ 59
def prefixEnd_4208723 : Nat := 4983230072969 + 3 ^ 40 * 4208723 * 2
def baseEnd_4208723 : Nat := 720365946877614028535647

theorem tailTrace_4208723 : CollatzResearch.WordTrace tailWord_4208723 prefixEnd_4208723 720365946877614028535647 := by
  unfold tailWord_4208723
  simp only [CollatzResearch.WordTrace]
  refine ⟨153504738731522838507502823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102336492487681892338335215 153504738731522838507502823)
  ·
    refine ⟨230257108097284257761254235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153504738731522838507502823 230257108097284257761254235)
    ·
      refine ⟨345385662145926386641881353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230257108097284257761254235 345385662145926386641881353)
      ·
        refine ⟨259039246609444789981411015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345385662145926386641881353 259039246609444789981411015)
        ·
          refine ⟨388558869914167184972116523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259039246609444789981411015 388558869914167184972116523)
          ·
            refine ⟨582838304871250777458174785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388558869914167184972116523 582838304871250777458174785)
            ·
              refine ⟨437128728653438083093631089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 582838304871250777458174785 437128728653438083093631089)
              ·
                refine ⟨327846546490078562320223317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 437128728653438083093631089 327846546490078562320223317)
                ·
                  refine ⟨3841951716680608152190117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 327846546490078562320223317 3841951716680608152190117)
                  ·
                    refine ⟨720365946877614028535647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3841951716680608152190117 720365946877614028535647)
                    ·
                      rfl

theorem cell23_4208723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 4].length) (baseStart_4208723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208723 prefixEnd_4208723 := by exact prefixLift 4208723
  have htrace : WordTrace (prefixWord ++ tailWord_4208723) baseStart_4208723 baseEnd_4208723 := by
    simpa [prefixWord, tailWord_4208723, baseEnd_4208723] using wordTrace_append hprefix tailTrace_4208723
  have hstable : (prefixWord ++ tailWord_4208723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208723).length < 2 ^ (prefixWord ++ tailWord_4208723).sum := by decide
  have hdescent : baseEnd_4208723 < baseStart_4208723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208743 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_4208743 : Nat := 118140960795 + 4208743 * 2 ^ 59
def prefixEnd_4208743 : Nat := 4983230072969 + 3 ^ 40 * 4208743 * 2
def baseEnd_4208743 : Nat := 2161108110245932007356849

theorem tailTrace_4208743 : CollatzResearch.WordTrace tailWord_4208743 prefixEnd_4208743 2161108110245932007356849 := by
  unfold tailWord_4208743
  simp only [CollatzResearch.WordTrace]
  refine ⟨153505468191450381923230883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102336978794300254615487255 153505468191450381923230883)
  ·
    refine ⟨230258202287175572884846325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153505468191450381923230883 230258202287175572884846325)
    ·
      refine ⟨21586706464422709957954343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 230258202287175572884846325 21586706464422709957954343)
      ·
        refine ⟨32380059696634064936931515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21586706464422709957954343 32380059696634064936931515)
        ·
          refine ⟨48570089544951097405397273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32380059696634064936931515 48570089544951097405397273)
          ·
            refine ⟨36427567158713323054047955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48570089544951097405397273 36427567158713323054047955)
            ·
              refine ⟨54641350738069984581071933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36427567158713323054047955 54641350738069984581071933)
              ·
                refine ⟨20490506526776244217901975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54641350738069984581071933 20490506526776244217901975)
                ·
                  refine ⟨30735759790164366326852963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20490506526776244217901975 30735759790164366326852963)
                  ·
                    refine ⟨46103639685246549490279445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30735759790164366326852963 46103639685246549490279445)
                    ·
                      refine ⟨2161108110245932007356849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46103639685246549490279445 2161108110245932007356849)
                      ·
                        rfl

theorem cell23_4208743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_4208743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208743 prefixEnd_4208743 := by exact prefixLift 4208743
  have htrace : WordTrace (prefixWord ++ tailWord_4208743) baseStart_4208743 baseEnd_4208743 := by
    simpa [prefixWord, tailWord_4208743, baseEnd_4208743] using wordTrace_append hprefix tailTrace_4208743
  have hstable : (prefixWord ++ tailWord_4208743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208743).length < 2 ^ (prefixWord ++ tailWord_4208743).sum := by decide
  have hdescent : baseEnd_4208743 < baseStart_4208743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208797 : List Nat := [1, 4, 2, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_4208797 : Nat := 118140960795 + 4208797 * 2 ^ 59
def prefixEnd_4208797 : Nat := 4983230072969 + 3 ^ 40 * 4208797 * 2
def baseEnd_4208797 : Nat := 2161135838201274796081601

theorem tailTrace_4208797 : CollatzResearch.WordTrace tailWord_4208797 prefixEnd_4208797 2161135838201274796081601 := by
  unfold tailWord_4208797
  simp only [CollatzResearch.WordTrace]
  refine ⟨153507437733254749145696645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102338291822169832763797763 153507437733254749145696645)
  ·
    refine ⟨28782644574985265464818121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153507437733254749145696645 28782644574985265464818121)
    ·
      refine ⟨21586983431238949098613591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28782644574985265464818121 21586983431238949098613591)
      ·
        refine ⟨32380475146858423647920387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21586983431238949098613591 32380475146858423647920387)
        ·
          refine ⟨48570712720287635471880581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32380475146858423647920387 48570712720287635471880581)
          ·
            refine ⟨9107008635053931650977609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48570712720287635471880581 9107008635053931650977609)
            ·
              refine ⟨6830256476290448738233207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9107008635053931650977609 6830256476290448738233207)
              ·
                refine ⟨10245384714435673107349811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6830256476290448738233207 10245384714435673107349811)
                ·
                  refine ⟨15368077071653509661024717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10245384714435673107349811 15368077071653509661024717)
                  ·
                    refine ⟨5763028901870066122884269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15368077071653509661024717 5763028901870066122884269)
                    ·
                      refine ⟨2161135838201274796081601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5763028901870066122884269 2161135838201274796081601)
                      ·
                        rfl

theorem cell23_4208797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_4208797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208797 prefixEnd_4208797 := by exact prefixLift 4208797
  have htrace : WordTrace (prefixWord ++ tailWord_4208797) baseStart_4208797 baseEnd_4208797 := by
    simpa [prefixWord, tailWord_4208797, baseEnd_4208797] using wordTrace_append hprefix tailTrace_4208797
  have hstable : (prefixWord ++ tailWord_4208797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208797).length < 2 ^ (prefixWord ++ tailWord_4208797).sum := by decide
  have hdescent : baseEnd_4208797 < baseStart_4208797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208890 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 4, 5]
def baseStart_4208890 : Nat := 118140960795 + 4208890 * 2 ^ 59
def prefixEnd_4208890 : Nat := 4983230072969 + 3 ^ 40 * 4208890 * 2
def baseEnd_4208890 : Nat := 720394530634047644072891

theorem tailTrace_4208890 : CollatzResearch.WordTrace tailWord_4208890 prefixEnd_4208890 720394530634047644072891 := by
  unfold tailWord_4208890
  simp only [CollatzResearch.WordTrace]
  refine ⟨38377707430479456507208031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102340553147945217352554749 38377707430479456507208031)
  ·
    refine ⟨57566561145719184760812047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38377707430479456507208031 57566561145719184760812047)
    ·
      refine ⟨86349841718578777141218071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57566561145719184760812047 86349841718578777141218071)
      ·
        refine ⟨129524762577868165711827107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86349841718578777141218071 129524762577868165711827107)
        ·
          refine ⟨194287143866802248567740661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129524762577868165711827107 194287143866802248567740661)
          ·
            refine ⟨18214419737512710803225687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 194287143866802248567740661 18214419737512710803225687)
            ·
              refine ⟨27321629606269066204838531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18214419737512710803225687 27321629606269066204838531)
              ·
                refine ⟨40982444409403599307257797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27321629606269066204838531 40982444409403599307257797)
                ·
                  refine ⟨7684208326763174870110837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40982444409403599307257797 7684208326763174870110837)
                  ·
                    refine ⟨720394530634047644072891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7684208326763174870110837 720394530634047644072891)
                    ·
                      rfl

theorem cell23_4208890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_4208890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208890 prefixEnd_4208890 := by exact prefixLift 4208890
  have htrace : WordTrace (prefixWord ++ tailWord_4208890) baseStart_4208890 baseEnd_4208890 := by
    simpa [prefixWord, tailWord_4208890, baseEnd_4208890] using wordTrace_append hprefix tailTrace_4208890
  have hstable : (prefixWord ++ tailWord_4208890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208890).length < 2 ^ (prefixWord ++ tailWord_4208890).sum := by decide
  have hdescent : baseEnd_4208890 < baseStart_4208890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208897 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 2, 5, 2]
def baseStart_4208897 : Nat := 118140960795 + 4208897 * 2 ^ 59
def prefixEnd_4208897 : Nat := 4983230072969 + 3 ^ 40 * 4208897 * 2
def baseEnd_4208897 : Nat := 2161187186266724404831141

theorem tailTrace_4208897 : CollatzResearch.WordTrace tailWord_4208897 prefixEnd_4208897 2161187186266724404831141 := by
  unfold tailWord_4208897
  simp only [CollatzResearch.WordTrace]
  refine ⟨153511085032892466224336945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102340723355261644149557963 153511085032892466224336945)
  ·
    refine ⟨115133313774669349668252709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153511085032892466224336945 115133313774669349668252709)
    ·
      refine ⟨21587496332750503062797383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115133313774669349668252709 21587496332750503062797383)
      ·
        refine ⟨32381244499125754594196075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21587496332750503062797383 32381244499125754594196075)
        ·
          refine ⟨48571866748688631891294113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32381244499125754594196075 48571866748688631891294113)
          ·
            refine ⟨36428900061516473918470585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48571866748688631891294113 36428900061516473918470585)
            ·
              refine ⟨27321675046137355438852939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36428900061516473918470585 27321675046137355438852939)
              ·
                refine ⟨40982512569206033158279409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27321675046137355438852939 40982512569206033158279409)
                ·
                  refine ⟨30736884426904524868709557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40982512569206033158279409 30736884426904524868709557)
                  ·
                    refine ⟨2881582915022299206441521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30736884426904524868709557 2881582915022299206441521)
                    ·
                      refine ⟨2161187186266724404831141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2881582915022299206441521 2161187186266724404831141)
                      ·
                        rfl

theorem cell23_4208897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_4208897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208897 prefixEnd_4208897 := by exact prefixLift 4208897
  have htrace : WordTrace (prefixWord ++ tailWord_4208897) baseStart_4208897 baseEnd_4208897 := by
    simpa [prefixWord, tailWord_4208897, baseEnd_4208897] using wordTrace_append hprefix tailTrace_4208897
  have hstable : (prefixWord ++ tailWord_4208897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208897).length < 2 ^ (prefixWord ++ tailWord_4208897).sum := by decide
  have hdescent : baseEnd_4208897 < baseStart_4208897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208927 : List Nat := [1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 4]
def baseStart_4208927 : Nat := 118140960795 + 4208927 * 2 ^ 59
def prefixEnd_4208927 : Nat := 4983230072969 + 3 ^ 40 * 4208927 * 2
def baseEnd_4208927 : Nat := 2161202590686359287456003

theorem tailTrace_4208927 : CollatzResearch.WordTrace tailWord_4208927 prefixEnd_4208927 2161202590686359287456003 := by
  unfold tailWord_4208927
  simp only [CollatzResearch.WordTrace]
  refine ⟨153512179222783781347929035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102341452815189187565286023 153512179222783781347929035)
  ·
    refine ⟨230268268834175672021893553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153512179222783781347929035 230268268834175672021893553)
    ·
      refine ⟨172701201625631754016420165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230268268834175672021893553 172701201625631754016420165)
      ·
        refine ⟨32381475304805953878078781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172701201625631754016420165 32381475304805953878078781)
        ·
          refine ⟨12143053239302232704279543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32381475304805953878078781 12143053239302232704279543)
          ·
            refine ⟨18214579858953349056419315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12143053239302232704279543 18214579858953349056419315)
            ·
              refine ⟨27321869788430023584628973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18214579858953349056419315 27321869788430023584628973)
              ·
                refine ⟨10245701170661258844235865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27321869788430023584628973 10245701170661258844235865)
                ·
                  refine ⟨7684275877995944133176899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10245701170661258844235865 7684275877995944133176899)
                  ·
                    refine ⟨11526413816993916199765349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7684275877995944133176899 11526413816993916199765349)
                    ·
                      refine ⟨2161202590686359287456003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11526413816993916199765349 2161202590686359287456003)
                      ·
                        rfl

theorem cell23_4208927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_4208927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208927 prefixEnd_4208927 := by exact prefixLift 4208927
  have htrace : WordTrace (prefixWord ++ tailWord_4208927) baseStart_4208927 baseEnd_4208927 := by
    simpa [prefixWord, tailWord_4208927, baseEnd_4208927] using wordTrace_append hprefix tailTrace_4208927
  have hstable : (prefixWord ++ tailWord_4208927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208927).length < 2 ^ (prefixWord ++ tailWord_4208927).sum := by decide
  have hdescent : baseEnd_4208927 < baseStart_4208927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208947 : List Nat := [1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 3]
def baseStart_4208947 : Nat := 118140960795 + 4208947 * 2 ^ 59
def prefixEnd_4208947 : Nat := 4983230072969 + 3 ^ 40 * 4208947 * 2
def baseEnd_4208947 : Nat := 2161212860299449209205911

theorem tailTrace_4208947 : CollatzResearch.WordTrace tailWord_4208947 prefixEnd_4208947 2161212860299449209205911 := by
  unfold tailWord_4208947
  simp only [CollatzResearch.WordTrace]
  refine ⟨153512908682711324763657095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102341939121807549842438063 153512908682711324763657095)
  ·
    refine ⟨230269363024066987145485643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153512908682711324763657095 230269363024066987145485643)
    ·
      refine ⟨345404044536100480718228465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230269363024066987145485643 345404044536100480718228465)
      ·
        refine ⟨259053033402075360538671349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345404044536100480718228465 259053033402075360538671349)
        ·
          refine ⟨24286221881444565050500439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 259053033402075360538671349 24286221881444565050500439)
          ·
            refine ⟨36429332822166847575750659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24286221881444565050500439 36429332822166847575750659)
            ·
              refine ⟨54643999233250271363625989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36429332822166847575750659 54643999233250271363625989)
              ·
                refine ⟨10245749856234425880679873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54643999233250271363625989 10245749856234425880679873)
                ·
                  refine ⟨7684312392175819410509905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10245749856234425880679873 7684312392175819410509905)
                  ·
                    refine ⟨5763234294131864557882429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7684312392175819410509905 5763234294131864557882429)
                    ·
                      refine ⟨2161212860299449209205911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5763234294131864557882429 2161212860299449209205911)
                      ·
                        rfl

theorem cell23_4208947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 3].length) (baseStart_4208947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208947 prefixEnd_4208947 := by exact prefixLift 4208947
  have htrace : WordTrace (prefixWord ++ tailWord_4208947) baseStart_4208947 baseEnd_4208947 := by
    simpa [prefixWord, tailWord_4208947, baseEnd_4208947] using wordTrace_append hprefix tailTrace_4208947
  have hstable : (prefixWord ++ tailWord_4208947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208947).length < 2 ^ (prefixWord ++ tailWord_4208947).sum := by decide
  have hdescent : baseEnd_4208947 < baseStart_4208947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208961 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_4208961 : Nat := 118140960795 + 4208961 * 2 ^ 59
def prefixEnd_4208961 : Nat := 4983230072969 + 3 ^ 40 * 4208961 * 2
def baseEnd_4208961 : Nat := 2161220049028612154430847

theorem tailTrace_4208961 : CollatzResearch.WordTrace tailWord_4208961 prefixEnd_4208961 2161220049028612154430847 := by
  unfold tailWord_4208961
  simp only [CollatzResearch.WordTrace]
  refine ⟨153513419304660605154666737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102342279536440403436444491 153513419304660605154666737)
  ·
    refine ⟨115135064478495453866000053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153513419304660605154666737 115135064478495453866000053)
    ·
      refine ⟨10793912294858948799937505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115135064478495453866000053 10793912294858948799937505)
      ·
        refine ⟨8095434221144211599953129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10793912294858948799937505 8095434221144211599953129)
        ·
          refine ⟨6071575665858158699964847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8095434221144211599953129 6071575665858158699964847)
          ·
            refine ⟨9107363498787238049947271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6071575665858158699964847 9107363498787238049947271)
            ·
              refine ⟨13661045248180857074920907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9107363498787238049947271 13661045248180857074920907)
              ·
                refine ⟨20491567872271285612381361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13661045248180857074920907 20491567872271285612381361)
                ·
                  refine ⟨15368675904203464209286021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20491567872271285612381361 15368675904203464209286021)
                  ·
                    refine ⟨2881626732038149539241129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15368675904203464209286021 2881626732038149539241129)
                    ·
                      refine ⟨2161220049028612154430847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2881626732038149539241129 2161220049028612154430847)
                      ·
                        rfl

theorem cell23_4208961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_4208961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208961 prefixEnd_4208961 := by exact prefixLift 4208961
  have htrace : WordTrace (prefixWord ++ tailWord_4208961) baseStart_4208961 baseEnd_4208961 := by
    simpa [prefixWord, tailWord_4208961, baseEnd_4208961] using wordTrace_append hprefix tailTrace_4208961
  have hstable : (prefixWord ++ tailWord_4208961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208961).length < 2 ^ (prefixWord ++ tailWord_4208961).sum := by decide
  have hdescent : baseEnd_4208961 < baseStart_4208961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4208981 : List Nat := [1, 3, 2, 2, 4, 2, 1, 1, 2, 2, 3]
def baseStart_4208981 : Nat := 118140960795 + 4208981 * 2 ^ 59
def prefixEnd_4208981 : Nat := 4983230072969 + 3 ^ 40 * 4208981 * 2
def baseEnd_4208981 : Nat := 2161230318641702076180755

theorem tailTrace_4208981 : CollatzResearch.WordTrace tailWord_4208981 prefixEnd_4208981 2161230318641702076180755 := by
  unfold tailWord_4208981
  simp only [CollatzResearch.WordTrace]
  refine ⟨153514148764588148570394797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102342765843058765713596531 153514148764588148570394797)
  ·
    refine ⟨57567805786720555713898049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153514148764588148570394797 57567805786720555713898049)
    ·
      refine ⟨43175854340040416785423537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57567805786720555713898049 43175854340040416785423537)
      ·
        refine ⟨32381890755030312589067653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43175854340040416785423537 32381890755030312589067653)
        ·
          refine ⟨6071604516568183610450185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32381890755030312589067653 6071604516568183610450185)
          ·
            refine ⟨4553703387426137707837639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6071604516568183610450185 4553703387426137707837639)
            ·
              refine ⟨6830555081139206561756459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4553703387426137707837639 6830555081139206561756459)
              ·
                refine ⟨10245832621708809842634689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6830555081139206561756459 10245832621708809842634689)
                ·
                  refine ⟨7684374466281607381976017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10245832621708809842634689 7684374466281607381976017)
                  ·
                    refine ⟨5763280849711205536482013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7684374466281607381976017 5763280849711205536482013)
                    ·
                      refine ⟨2161230318641702076180755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5763280849711205536482013 2161230318641702076180755)
                      ·
                        rfl

theorem cell23_4208981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_4208981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4208981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4208981 prefixEnd_4208981 := by exact prefixLift 4208981
  have htrace : WordTrace (prefixWord ++ tailWord_4208981) baseStart_4208981 baseEnd_4208981 := by
    simpa [prefixWord, tailWord_4208981, baseEnd_4208981] using wordTrace_append hprefix tailTrace_4208981
  have hstable : (prefixWord ++ tailWord_4208981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4208981).length < 2 ^ (prefixWord ++ tailWord_4208981).sum := by decide
  have hdescent : baseEnd_4208981 < baseStart_4208981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4208981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209047 : List Nat := [1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 4]
def baseStart_4209047 : Nat := 118140960795 + 4209047 * 2 ^ 59
def prefixEnd_4209047 : Nat := 4983230072969 + 3 ^ 40 * 4209047 * 2
def baseEnd_4209047 : Nat := 2161264208364898817955451

theorem tailTrace_4209047 : CollatzResearch.WordTrace tailWord_4209047 prefixEnd_4209047 2161264208364898817955451 := by
  unfold tailWord_4209047
  simp only [CollatzResearch.WordTrace]
  refine ⟨153516555982349041842297395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102344370654899361228198263 153516555982349041842297395)
  ·
    refine ⟨230274833973523562763446093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153516555982349041842297395 230274833973523562763446093)
    ·
      refine ⟨86353062740071336036292285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230274833973523562763446093 86353062740071336036292285)
      ·
        refine ⟨32382398527526751013609607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86353062740071336036292285 32382398527526751013609607)
        ·
          refine ⟨48573597791290126520414411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32382398527526751013609607 48573597791290126520414411)
          ·
            refine ⟨72860396686935189780621617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48573597791290126520414411 72860396686935189780621617)
            ·
              refine ⟨54645297515201392335466213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72860396686935189780621617 54645297515201392335466213)
              ·
                refine ⟨10245993284100261062899915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54645297515201392335466213 10245993284100261062899915)
                ·
                  refine ⟨15368989926150391594349873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10245993284100261062899915 15368989926150391594349873)
                  ·
                    refine ⟨11526742444612793695762405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15368989926150391594349873 11526742444612793695762405)
                    ·
                      refine ⟨2161264208364898817955451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11526742444612793695762405 2161264208364898817955451)
                      ·
                        rfl

theorem cell23_4209047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_4209047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209047 prefixEnd_4209047 := by exact prefixLift 4209047
  have htrace : WordTrace (prefixWord ++ tailWord_4209047) baseStart_4209047 baseEnd_4209047 := by
    simpa [prefixWord, tailWord_4209047, baseEnd_4209047] using wordTrace_append hprefix tailTrace_4209047
  have hstable : (prefixWord ++ tailWord_4209047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209047).length < 2 ^ (prefixWord ++ tailWord_4209047).sum := by decide
  have hdescent : baseEnd_4209047 < baseStart_4209047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209064 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_4209064 : Nat := 118140960795 + 4209064 * 2 ^ 59
def prefixEnd_4209064 : Nat := 4983230072969 + 3 ^ 40 * 4209064 * 2
def baseEnd_4209064 : Nat := 2161272937536025251442873

theorem tailTrace_4209064 : CollatzResearch.WordTrace tailWord_4209064 prefixEnd_4209064 2161272937536025251442873 := by
  unfold tailWord_4209064
  simp only [CollatzResearch.WordTrace]
  refine ⟨76758588011643726872833123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102344784015524969163777497 76758588011643726872833123)
  ·
    refine ⟨115137882017465590309249685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76758588011643726872833123 115137882017465590309249685)
    ·
      refine ⟨5397088219568699545746079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 115137882017465590309249685 5397088219568699545746079)
      ·
        refine ⟨8095632329353049318619119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5397088219568699545746079 8095632329353049318619119)
        ·
          refine ⟨12143448494029573977928679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8095632329353049318619119 12143448494029573977928679)
          ·
            refine ⟨18215172741044360966893019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12143448494029573977928679 18215172741044360966893019)
            ·
              refine ⟨27322759111566541450339529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18215172741044360966893019 27322759111566541450339529)
              ·
                refine ⟨20492069333674906087754647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27322759111566541450339529 20492069333674906087754647)
                ·
                  refine ⟨30738104000512359131631971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20492069333674906087754647 30738104000512359131631971)
                  ·
                    refine ⟨46107156000768538697447957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30738104000512359131631971 46107156000768538697447957)
                    ·
                      refine ⟨2161272937536025251442873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46107156000768538697447957 2161272937536025251442873)
                      ·
                        rfl

theorem cell23_4209064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_4209064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209064 prefixEnd_4209064 := by exact prefixLift 4209064
  have htrace : WordTrace (prefixWord ++ tailWord_4209064) baseStart_4209064 baseEnd_4209064 := by
    simpa [prefixWord, tailWord_4209064, baseEnd_4209064] using wordTrace_append hprefix tailTrace_4209064
  have hstable : (prefixWord ++ tailWord_4209064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209064).length < 2 ^ (prefixWord ++ tailWord_4209064).sum := by decide
  have hdescent : baseEnd_4209064 < baseStart_4209064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209134 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 2, 6]
def baseStart_4209134 : Nat := 118140960795 + 4209134 * 2 ^ 59
def prefixEnd_4209134 : Nat := 4983230072969 + 3 ^ 40 * 4209134 * 2
def baseEnd_4209134 : Nat := 720436293727279992522517

theorem tailTrace_4209134 : CollatzResearch.WordTrace tailWord_4209134 prefixEnd_4209134 720436293727279992522517 := by
  unfold tailWord_4209134
  simp only [CollatzResearch.WordTrace]
  refine ⟨19189966141629231962589307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102346486088689237133809637 19189966141629231962589307)
  ·
    refine ⟨28784949212443847943883961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19189966141629231962589307 28784949212443847943883961)
    ·
      refine ⟨21588711909332885957912971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28784949212443847943883961 21588711909332885957912971)
      ·
        refine ⟨32383067863999328936869457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21588711909332885957912971 32383067863999328936869457)
        ·
          refine ⟨24287300897999496702652093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32383067863999328936869457 24287300897999496702652093)
          ·
            refine ⟨9107737836749811263494535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24287300897999496702652093 9107737836749811263494535)
            ·
              refine ⟨13661606755124716895241803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9107737836749811263494535 13661606755124716895241803)
              ·
                refine ⟨20492410132687075342862705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13661606755124716895241803 20492410132687075342862705)
                ·
                  refine ⟨15369307599515306507147029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20492410132687075342862705 15369307599515306507147029)
                  ·
                    refine ⟨720436293727279992522517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15369307599515306507147029 720436293727279992522517)
                    ·
                      rfl

theorem cell23_4209134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_4209134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209134 prefixEnd_4209134 := by exact prefixLift 4209134
  have htrace : WordTrace (prefixWord ++ tailWord_4209134) baseStart_4209134 baseEnd_4209134 := by
    simpa [prefixWord, tailWord_4209134, baseEnd_4209134] using wordTrace_append hprefix tailTrace_4209134
  have hstable : (prefixWord ++ tailWord_4209134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209134).length < 2 ^ (prefixWord ++ tailWord_4209134).sum := by decide
  have hdescent : baseEnd_4209134 < baseStart_4209134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209175 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 4, 2, 2]
def baseStart_4209175 : Nat := 118140960795 + 4209175 * 2 ^ 59
def prefixEnd_4209175 : Nat := 4983230072969 + 3 ^ 40 * 4209175 * 2
def baseEnd_4209175 : Nat := 2161329933888674317154863

theorem tailTrace_4209175 : CollatzResearch.WordTrace tailWord_4209175 prefixEnd_4209175 2161329933888674317154863 := by
  unfold tailWord_4209175
  simp only [CollatzResearch.WordTrace]
  refine ⟨153521224525885319702956979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102347483017256879801971319 153521224525885319702956979)
  ·
    refine ⟨230281836788827979554435469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153521224525885319702956979 230281836788827979554435469)
    ·
      refine ⟨86355688795810492332913301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230281836788827979554435469 86355688795810492332913301)
      ·
        refine ⟨4047922912303616828105311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 86355688795810492332913301 4047922912303616828105311)
        ·
          refine ⟨6071884368455425242157967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4047922912303616828105311 6071884368455425242157967)
          ·
            refine ⟨9107826552683137863236951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6071884368455425242157967 9107826552683137863236951)
            ·
              refine ⟨13661739829024706794855427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9107826552683137863236951 13661739829024706794855427)
              ·
                refine ⟨20492609743537060192283141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13661739829024706794855427 20492609743537060192283141)
                ·
                  refine ⟨3842364326913198786053089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20492609743537060192283141 3842364326913198786053089)
                  ·
                    refine ⟨2881773245184899089539817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3842364326913198786053089 2881773245184899089539817)
                    ·
                      refine ⟨2161329933888674317154863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2881773245184899089539817 2161329933888674317154863)
                      ·
                        rfl

theorem cell23_4209175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_4209175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209175 prefixEnd_4209175 := by exact prefixLift 4209175
  have htrace : WordTrace (prefixWord ++ tailWord_4209175) baseStart_4209175 baseEnd_4209175 := by
    simpa [prefixWord, tailWord_4209175, baseEnd_4209175] using wordTrace_append hprefix tailTrace_4209175
  have hstable : (prefixWord ++ tailWord_4209175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209175).length < 2 ^ (prefixWord ++ tailWord_4209175).sum := by decide
  have hdescent : baseEnd_4209175 < baseStart_4209175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209181 : List Nat := [1, 4, 2, 2, 1, 2, 2, 4, 5]
def baseStart_4209181 : Nat := 118140960795 + 4209181 * 2 ^ 59
def prefixEnd_4209181 : Nat := 4983230072969 + 3 ^ 40 * 4209181 * 2
def baseEnd_4209181 : Nat := 240148112752511254853315

theorem tailTrace_4209181 : CollatzResearch.WordTrace tailWord_4209181 prefixEnd_4209181 240148112752511254853315 := by
  unfold tailWord_4209181
  simp only [CollatzResearch.WordTrace]
  refine ⟨153521443363863582727675397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102347628909242388485116931 153521443363863582727675397)
  ·
    refine ⟨28785270630724421761439137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153521443363863582727675397 28785270630724421761439137)
    ·
      refine ⟨21588952973043316321079353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28785270630724421761439137 21588952973043316321079353)
      ·
        refine ⟨16191714729782487240809515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21588952973043316321079353 16191714729782487240809515)
        ·
          refine ⟨24287572094673730861214273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16191714729782487240809515 24287572094673730861214273)
          ·
            refine ⟨18215679071005298145910705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24287572094673730861214273 18215679071005298145910705)
            ·
              refine ⟨13661759303253973609433029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18215679071005298145910705 13661759303253973609433029)
              ·
                refine ⟨2561579869360120051768693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13661759303253973609433029 2561579869360120051768693)
                ·
                  refine ⟨240148112752511254853315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2561579869360120051768693 240148112752511254853315)
                  ·
                    rfl

theorem cell23_4209181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_4209181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209181 prefixEnd_4209181 := by exact prefixLift 4209181
  have htrace : WordTrace (prefixWord ++ tailWord_4209181) baseStart_4209181 baseEnd_4209181 := by
    simpa [prefixWord, tailWord_4209181, baseEnd_4209181] using wordTrace_append hprefix tailTrace_4209181
  have hstable : (prefixWord ++ tailWord_4209181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209181).length < 2 ^ (prefixWord ++ tailWord_4209181).sum := by decide
  have hdescent : baseEnd_4209181 < baseStart_4209181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209192 : List Nat := [2, 1, 5, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_4209192 : Nat := 118140960795 + 4209192 * 2 ^ 59
def prefixEnd_4209192 : Nat := 4983230072969 + 3 ^ 40 * 4209192 * 2
def baseEnd_4209192 : Nat := 2161338663059800750642285

theorem tailTrace_4209192 : CollatzResearch.WordTrace tailWord_4209192 prefixEnd_4209192 2161338663059800750642285 := by
  unfold tailWord_4209192
  simp only [CollatzResearch.WordTrace]
  refine ⟨76760922283411865803162915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102347896377882487737550553 76760922283411865803162915)
  ·
    refine ⟨115141383425117798704744373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76760922283411865803162915 115141383425117798704744373)
    ·
      refine ⟨10794504696104793628569785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115141383425117798704744373 10794504696104793628569785)
      ·
        refine ⟨8095878522078595221427339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10794504696104793628569785 8095878522078595221427339)
        ·
          refine ⟨12143817783117892832141009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8095878522078595221427339 12143817783117892832141009)
          ·
            refine ⟨9107863337338419624105757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12143817783117892832141009 9107863337338419624105757)
            ·
              refine ⟨3415448751501907359039659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9107863337338419624105757 3415448751501907359039659)
              ·
                refine ⟨5123173127252861038559489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3415448751501907359039659 5123173127252861038559489)
                ·
                  refine ⟨3842379845439645778919617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5123173127252861038559489 3842379845439645778919617)
                  ·
                    refine ⟨2881784884079734334189713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3842379845439645778919617 2881784884079734334189713)
                    ·
                      refine ⟨2161338663059800750642285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2881784884079734334189713 2161338663059800750642285)
                      ·
                        rfl

theorem cell23_4209192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_4209192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209192 prefixEnd_4209192 := by exact prefixLift 4209192
  have htrace : WordTrace (prefixWord ++ tailWord_4209192) baseStart_4209192 baseEnd_4209192 := by
    simpa [prefixWord, tailWord_4209192, baseEnd_4209192] using wordTrace_append hprefix tailTrace_4209192
  have hstable : (prefixWord ++ tailWord_4209192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209192).length < 2 ^ (prefixWord ++ tailWord_4209192).sum := by decide
  have hdescent : baseEnd_4209192 < baseStart_4209192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209194 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 1, 7]
def baseStart_4209194 : Nat := 118140960795 + 4209194 * 2 ^ 59
def prefixEnd_4209194 : Nat := 4983230072969 + 3 ^ 40 * 4209194 * 2
def baseEnd_4209194 : Nat := 720446563340369914272425

theorem tailTrace_4209194 : CollatzResearch.WordTrace tailWord_4209194 prefixEnd_4209194 720446563340369914272425 := by
  unfold tailWord_4209194
  simp only [CollatzResearch.WordTrace]
  refine ⟨38380479378204121486974659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102347945008544323965265757 38380479378204121486974659)
  ·
    refine ⟨57570719067306182230461989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38380479378204121486974659 57570719067306182230461989)
    ·
      refine ⟨10794509825119909168211623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57570719067306182230461989 10794509825119909168211623)
      ·
        refine ⟨16191764737679863752317435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10794509825119909168211623 16191764737679863752317435)
        ·
          refine ⟨24287647106519795628476153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16191764737679863752317435 24287647106519795628476153)
          ·
            refine ⟨18215735329889846721357115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24287647106519795628476153 18215735329889846721357115)
            ·
              refine ⟨27323602994834770082035673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18215735329889846721357115 27323602994834770082035673)
              ·
                refine ⟨20492702246126077561526755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27323602994834770082035673 20492702246126077561526755)
                ·
                  refine ⟨30739053369189116342290133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20492702246126077561526755 30739053369189116342290133)
                  ·
                    refine ⟨720446563340369914272425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30739053369189116342290133 720446563340369914272425)
                    ·
                      rfl

theorem cell23_4209194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_4209194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209194 prefixEnd_4209194 := by exact prefixLift 4209194
  have htrace : WordTrace (prefixWord ++ tailWord_4209194) baseStart_4209194 baseEnd_4209194 := by
    simpa [prefixWord, tailWord_4209194, baseEnd_4209194] using wordTrace_append hprefix tailTrace_4209194
  have hstable : (prefixWord ++ tailWord_4209194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209194).length < 2 ^ (prefixWord ++ tailWord_4209194).sum := by decide
  have hdescent : baseEnd_4209194 < baseStart_4209194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209207 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 2, 8]
def baseStart_4209207 : Nat := 118140960795 + 4209207 * 2 ^ 59
def prefixEnd_4209207 : Nat := 4983230072969 + 3 ^ 40 * 4209207 * 2
def baseEnd_4209207 : Nat := 720448788423206063984905

theorem tailTrace_4209207 : CollatzResearch.WordTrace tailWord_4209207 prefixEnd_4209207 720448788423206063984905 := by
  unfold tailWord_4209207
  simp only [CollatzResearch.WordTrace]
  refine ⟨153522391661769389168121875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102348261107846259445414583 153522391661769389168121875)
  ·
    refine ⟨230283587492654083752182813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153522391661769389168121875 230283587492654083752182813)
    ·
      refine ⟨86356345309745281407068555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230283587492654083752182813 86356345309745281407068555)
      ·
        refine ⟨129534517964617922110602833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86356345309745281407068555 129534517964617922110602833)
        ·
          refine ⟨97150888473463441582952125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129534517964617922110602833 97150888473463441582952125)
          ·
            refine ⟨36431583177548790593607047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97150888473463441582952125 36431583177548790593607047)
            ·
              refine ⟨54647374766323185890410571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36431583177548790593607047 54647374766323185890410571)
              ·
                refine ⟨81971062149484778835615857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54647374766323185890410571 81971062149484778835615857)
                ·
                  refine ⟨61478296612113584126711893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81971062149484778835615857 61478296612113584126711893)
                  ·
                    refine ⟨720448788423206063984905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61478296612113584126711893 720448788423206063984905)
                    ·
                      rfl

theorem cell23_4209207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_4209207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209207 prefixEnd_4209207 := by exact prefixLift 4209207
  have htrace : WordTrace (prefixWord ++ tailWord_4209207) baseStart_4209207 baseEnd_4209207 := by
    simpa [prefixWord, tailWord_4209207, baseEnd_4209207] using wordTrace_append hprefix tailTrace_4209207
  have hstable : (prefixWord ++ tailWord_4209207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209207).length < 2 ^ (prefixWord ++ tailWord_4209207).sum := by decide
  have hdescent : baseEnd_4209207 < baseStart_4209207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209224 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 5, 4]
def baseStart_4209224 : Nat := 118140960795 + 4209224 * 2 ^ 59
def prefixEnd_4209224 : Nat := 4983230072969 + 3 ^ 40 * 4209224 * 2
def baseEnd_4209224 : Nat := 720451698146914875147379

theorem tailTrace_4209224 : CollatzResearch.WordTrace tailWord_4209224 prefixEnd_4209224 720451698146914875147379 := by
  unfold tailWord_4209224
  simp only [CollatzResearch.WordTrace]
  refine ⟨76761505851353900535745363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102348674468471867380993817 76761505851353900535745363)
  ·
    refine ⟨115142258777030850803618045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76761505851353900535745363 115142258777030850803618045)
    ·
      refine ⟨43178347041386569051356767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115142258777030850803618045 43178347041386569051356767)
      ·
        refine ⟨64767520562079853577035151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43178347041386569051356767 64767520562079853577035151)
        ·
          refine ⟨97151280843119780365552727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64767520562079853577035151 97151280843119780365552727)
          ·
            refine ⟨145726921264679670548329091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97151280843119780365552727 145726921264679670548329091)
            ·
              refine ⟨218590381897019505822493637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145726921264679670548329091 218590381897019505822493637)
              ·
                refine ⟨40985696605691157341717557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218590381897019505822493637 40985696605691157341717557)
                ·
                  refine ⟨3842409056783546000786021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40985696605691157341717557 3842409056783546000786021)
                  ·
                    refine ⟨720451698146914875147379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3842409056783546000786021 720451698146914875147379)
                    ·
                      rfl

theorem cell23_4209224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_4209224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209224 prefixEnd_4209224 := by exact prefixLift 4209224
  have htrace : WordTrace (prefixWord ++ tailWord_4209224) baseStart_4209224 baseEnd_4209224 := by
    simpa [prefixWord, tailWord_4209224, baseEnd_4209224] using wordTrace_append hprefix tailTrace_4209224
  have hstable : (prefixWord ++ tailWord_4209224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209224).length < 2 ^ (prefixWord ++ tailWord_4209224).sum := by decide
  have hdescent : baseEnd_4209224 < baseStart_4209224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209227 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 6]
def baseStart_4209227 : Nat := 118140960795 + 4209227 * 2 ^ 59
def prefixEnd_4209227 : Nat := 4983230072969 + 3 ^ 40 * 4209227 * 2
def baseEnd_4209227 : Nat := 2161356634882708113704623

theorem tailTrace_4209227 : CollatzResearch.WordTrace tailWord_4209227 prefixEnd_4209227 2161356634882708113704623 := by
  unfold tailWord_4209227
  simp only [CollatzResearch.WordTrace]
  refine ⟨153523121121696932583849935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102348747414464621722566623 153523121121696932583849935)
  ·
    refine ⟨230284681682545398875774903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153523121121696932583849935 230284681682545398875774903)
    ·
      refine ⟨345427022523818098313662355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230284681682545398875774903 345427022523818098313662355)
      ·
        refine ⟨518140533785727147470493533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345427022523818098313662355 518140533785727147470493533)
        ·
          refine ⟨194302700169647680301435075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 518140533785727147470493533 194302700169647680301435075)
          ·
            refine ⟨291454050254471520452152613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194302700169647680301435075 291454050254471520452152613)
            ·
              refine ⟨54647634422713410084778615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 291454050254471520452152613 54647634422713410084778615)
              ·
                refine ⟨81971451634070115127167923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54647634422713410084778615 81971451634070115127167923)
                ·
                  refine ⟨122957177451105172690751885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81971451634070115127167923 122957177451105172690751885)
                  ·
                    refine ⟨46108941544164439759031957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122957177451105172690751885 46108941544164439759031957)
                    ·
                      refine ⟨2161356634882708113704623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46108941544164439759031957 2161356634882708113704623)
                      ·
                        rfl

theorem cell23_4209227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 6].length) (baseStart_4209227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209227 prefixEnd_4209227 := by exact prefixLift 4209227
  have htrace : WordTrace (prefixWord ++ tailWord_4209227) baseStart_4209227 baseEnd_4209227 := by
    simpa [prefixWord, tailWord_4209227, baseEnd_4209227] using wordTrace_append hprefix tailTrace_4209227
  have hstable : (prefixWord ++ tailWord_4209227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209227).length < 2 ^ (prefixWord ++ tailWord_4209227).sum := by decide
  have hdescent : baseEnd_4209227 < baseStart_4209227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209291 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 4, 3, 2]
def baseStart_4209291 : Nat := 118140960795 + 4209291 * 2 ^ 59
def prefixEnd_4209291 : Nat := 4983230072969 + 3 ^ 40 * 4209291 * 2
def baseEnd_4209291 : Nat := 2161389497644595863304329

theorem tailTrace_4209291 : CollatzResearch.WordTrace tailWord_4209291 prefixEnd_4209291 2161389497644595863304329 := by
  unfold tailWord_4209291
  simp only [CollatzResearch.WordTrace]
  refine ⟨153525455393465071514179727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102350303595643381009453151 153525455393465071514179727)
  ·
    refine ⟨230288183090197607271269591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153525455393465071514179727 230288183090197607271269591)
    ·
      refine ⟨345432274635296410906904387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230288183090197607271269591 345432274635296410906904387)
      ·
        refine ⟨518148411952944616360356581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345432274635296410906904387 518148411952944616360356581)
        ·
          refine ⟨97152827241177115567566859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 518148411952944616360356581 97152827241177115567566859)
          ·
            refine ⟨145729240861765673351350289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97152827241177115567566859 145729240861765673351350289)
            ·
              refine ⟨109296930646324255013512717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145729240861765673351350289 109296930646324255013512717)
              ·
                refine ⟨40986348992371595630067269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109296930646324255013512717 40986348992371595630067269)
                ·
                  refine ⟨7684940436069674180637613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40986348992371595630067269 7684940436069674180637613)
                  ·
                    refine ⟨2881852663526127817739105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7684940436069674180637613 2881852663526127817739105)
                    ·
                      refine ⟨2161389497644595863304329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2881852663526127817739105 2161389497644595863304329)
                      ·
                        rfl

theorem cell23_4209291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 3, 2].length) (baseStart_4209291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209291 prefixEnd_4209291 := by exact prefixLift 4209291
  have htrace : WordTrace (prefixWord ++ tailWord_4209291) baseStart_4209291 baseEnd_4209291 := by
    simpa [prefixWord, tailWord_4209291, baseEnd_4209291] using wordTrace_append hprefix tailTrace_4209291
  have hstable : (prefixWord ++ tailWord_4209291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209291).length < 2 ^ (prefixWord ++ tailWord_4209291).sum := by decide
  have hdescent : baseEnd_4209291 < baseStart_4209291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209325 : List Nat := [1, 5, 2, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_4209325 : Nat := 118140960795 + 4209325 * 2 ^ 59
def prefixEnd_4209325 : Nat := 4983230072969 + 3 ^ 40 * 4209325 * 2
def baseEnd_4209325 : Nat := 2161406955986848730279173

theorem tailTrace_4209325 : CollatzResearch.WordTrace tailWord_4209325 prefixEnd_4209325 2161406955986848730279173 := by
  unfold tailWord_4209325
  simp only [CollatzResearch.WordTrace]
  refine ⟨153526695475341895320917429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102351130316894596880611619 153526695475341895320917429)
  ·
    refine ⟨14393127700813302686336009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153526695475341895320917429 14393127700813302686336009)
    ·
      refine ⟨10794845775609977014752007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14393127700813302686336009 10794845775609977014752007)
      ·
        refine ⟨16192268663414965522128011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10794845775609977014752007 16192268663414965522128011)
        ·
          refine ⟨24288402995122448283192017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16192268663414965522128011 24288402995122448283192017)
          ·
            refine ⟨18216302246341836212394013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24288402995122448283192017 18216302246341836212394013)
            ·
              refine ⟨6831113342378188579647755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18216302246341836212394013 6831113342378188579647755)
              ·
                refine ⟨10246670013567282869471633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6831113342378188579647755 10246670013567282869471633)
                ·
                  refine ⟨7685002510175462152103725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10246670013567282869471633 7685002510175462152103725)
                  ·
                    refine ⟨2881875941315798307038897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7685002510175462152103725 2881875941315798307038897)
                    ·
                      refine ⟨2161406955986848730279173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2881875941315798307038897 2161406955986848730279173)
                      ·
                        rfl

theorem cell23_4209325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_4209325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209325 prefixEnd_4209325 := by exact prefixLift 4209325
  have htrace : WordTrace (prefixWord ++ tailWord_4209325) baseStart_4209325 baseEnd_4209325 := by
    simpa [prefixWord, tailWord_4209325, baseEnd_4209325] using wordTrace_append hprefix tailTrace_4209325
  have hstable : (prefixWord ++ tailWord_4209325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209325).length < 2 ^ (prefixWord ++ tailWord_4209325).sum := by decide
  have hdescent : baseEnd_4209325 < baseStart_4209325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209335 : List Nat := [1, 1, 3, 1, 6, 2, 2, 1, 1, 5]
def baseStart_4209335 : Nat := 118140960795 + 4209335 * 2 ^ 59
def prefixEnd_4209335 : Nat := 4983230072969 + 3 ^ 40 * 4209335 * 2
def baseEnd_4209335 : Nat := 720470696931131230384709

theorem tailTrace_4209335 : CollatzResearch.WordTrace tailWord_4209335 prefixEnd_4209335 720470696931131230384709 := by
  unfold tailWord_4209335
  simp only [CollatzResearch.WordTrace]
  refine ⟨153527060205305667028781459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102351373470203778019187639 153527060205305667028781459)
  ·
    refine ⟨230290590307958500543172189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153527060205305667028781459 230290590307958500543172189)
    ·
      refine ⟨86358971365484437703689571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230290590307958500543172189 86358971365484437703689571)
      ·
        refine ⟨129538457048226656555534357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86358971365484437703689571 129538457048226656555534357)
        ·
          refine ⟨6072115174135624526040673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 129538457048226656555534357 6072115174135624526040673)
          ·
            refine ⟨4554086380601718394530505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6072115174135624526040673 4554086380601718394530505)
            ·
              refine ⟨3415564785451288795897879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4554086380601718394530505 3415564785451288795897879)
              ·
                refine ⟨5123347178176933193846819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3415564785451288795897879 5123347178176933193846819)
                ·
                  refine ⟨7685020767265399790770229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5123347178176933193846819 7685020767265399790770229)
                  ·
                    refine ⟨720470696931131230384709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7685020767265399790770229 720470696931131230384709)
                    ·
                      rfl

theorem cell23_4209335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 1, 5].length) (baseStart_4209335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209335 prefixEnd_4209335 := by exact prefixLift 4209335
  have htrace : WordTrace (prefixWord ++ tailWord_4209335) baseStart_4209335 baseEnd_4209335 := by
    simpa [prefixWord, tailWord_4209335, baseEnd_4209335] using wordTrace_append hprefix tailTrace_4209335
  have hstable : (prefixWord ++ tailWord_4209335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209335).length < 2 ^ (prefixWord ++ tailWord_4209335).sum := by decide
  have hdescent : baseEnd_4209335 < baseStart_4209335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209338 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2]
def baseStart_4209338 : Nat := 118140960795 + 4209338 * 2 ^ 59
def prefixEnd_4209338 : Nat := 4983230072969 + 3 ^ 40 * 4209338 * 2
def baseEnd_4209338 : Nat := 2161413631235357179416613

theorem tailTrace_4209338 : CollatzResearch.WordTrace tailWord_4209338 prefixEnd_4209338 2161413631235357179416613 := by
  unfold tailWord_4209338
  simp only [CollatzResearch.WordTrace]
  refine ⟨38381792406073699635285167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102351446416196532360760445 38381792406073699635285167)
  ·
    refine ⟨57572688609110549452927751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38381792406073699635285167 57572688609110549452927751)
    ·
      refine ⟨86359032913665824179391627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57572688609110549452927751 86359032913665824179391627)
      ·
        refine ⟨129538549370498736269087441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86359032913665824179391627 129538549370498736269087441)
        ·
          refine ⟨97153912027874052201815581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129538549370498736269087441 97153912027874052201815581)
          ·
            refine ⟨36432717010452769575680843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97153912027874052201815581 36432717010452769575680843)
            ·
              refine ⟨54649075515679154363521265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36432717010452769575680843 54649075515679154363521265)
              ·
                refine ⟨40986806636759365772640949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54649075515679154363521265 40986806636759365772640949)
                ·
                  refine ⟨3842513122196190541185089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40986806636759365772640949 3842513122196190541185089)
                  ·
                    refine ⟨2881884841647142905888817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3842513122196190541185089 2881884841647142905888817)
                    ·
                      refine ⟨2161413631235357179416613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2881884841647142905888817 2161413631235357179416613)
                      ·
                        rfl

theorem cell23_4209338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2].length) (baseStart_4209338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209338 prefixEnd_4209338 := by exact prefixLift 4209338
  have htrace : WordTrace (prefixWord ++ tailWord_4209338) baseStart_4209338 baseEnd_4209338 := by
    simpa [prefixWord, tailWord_4209338, baseEnd_4209338] using wordTrace_append hprefix tailTrace_4209338
  have hstable : (prefixWord ++ tailWord_4209338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209338).length < 2 ^ (prefixWord ++ tailWord_4209338).sum := by decide
  have hdescent : baseEnd_4209338 < baseStart_4209338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209344 : List Nat := [2, 1, 1, 2, 4, 3, 10]
def baseStart_4209344 : Nat := 118140960795 + 4209344 * 2 ^ 59
def prefixEnd_4209344 : Nat := 4983230072969 + 3 ^ 40 * 4209344 * 2
def baseEnd_4209344 : Nat := 26684156939744248838785

theorem tailTrace_4209344 : CollatzResearch.WordTrace tailWord_4209344 prefixEnd_4209344 26684156939744248838785 := by
  unfold tailWord_4209344
  simp only [CollatzResearch.WordTrace]
  refine ⟨76763694231136530782929543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102351592308182041043906057 76763694231136530782929543)
  ·
    refine ⟨115145541346704796174394315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76763694231136530782929543 115145541346704796174394315)
    ·
      refine ⟨172718312020057194261591473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115145541346704796174394315 172718312020057194261591473)
      ·
        refine ⟨129538734015042895696193605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172718312020057194261591473 129538734015042895696193605)
        ·
          refine ⟨24288512627820542943036301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129538734015042895696193605 24288512627820542943036301)
          ·
            refine ⟨9108192235432703603638613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24288512627820542943036301 9108192235432703603638613)
            ·
              refine ⟨26684156939744248838785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9108192235432703603638613 26684156939744248838785)
              ·
                rfl

theorem cell23_4209344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 10].length) (baseStart_4209344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209344 prefixEnd_4209344 := by exact prefixLift 4209344
  have htrace : WordTrace (prefixWord ++ tailWord_4209344) baseStart_4209344 baseEnd_4209344 := by
    simpa [prefixWord, tailWord_4209344, baseEnd_4209344] using wordTrace_append hprefix tailTrace_4209344
  have hstable : (prefixWord ++ tailWord_4209344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209344).length < 2 ^ (prefixWord ++ tailWord_4209344).sum := by decide
  have hdescent : baseEnd_4209344 < baseStart_4209344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209348 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 4, 4]
def baseStart_4209348 : Nat := 118140960795 + 4209348 * 2 ^ 59
def prefixEnd_4209348 : Nat := 4983230072969 + 3 ^ 40 * 4209348 * 2
def baseEnd_4209348 : Nat := 720472922013967380097189

theorem tailTrace_4209348 : CollatzResearch.WordTrace tailWord_4209348 prefixEnd_4209348 720472922013967380097189 := by
  unfold tailWord_4209348
  simp only [CollatzResearch.WordTrace]
  refine ⟨76763767177129285124502349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102351689569505713499336465 76763767177129285124502349)
  ·
    refine ⟨28786412691423481921688381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76763767177129285124502349 28786412691423481921688381)
    ·
      refine ⟨10794904759283805720633143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28786412691423481921688381 10794904759283805720633143)
      ·
        refine ⟨16192357138925708580949715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10794904759283805720633143 16192357138925708580949715)
        ·
          refine ⟨24288535708388562871424573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16192357138925708580949715 24288535708388562871424573)
          ·
            refine ⟨9108200890645711076784215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24288535708388562871424573 9108200890645711076784215)
            ·
              refine ⟨13662301335968566615176323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9108200890645711076784215 13662301335968566615176323)
              ·
                refine ⟨20493452003952849922764485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13662301335968566615176323 20493452003952849922764485)
                ·
                  refine ⟨3842522250741159360518341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20493452003952849922764485 3842522250741159360518341)
                  ·
                    refine ⟨720472922013967380097189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3842522250741159360518341 720472922013967380097189)
                    ·
                      rfl

theorem cell23_4209348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_4209348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209348 prefixEnd_4209348 := by exact prefixLift 4209348
  have htrace : WordTrace (prefixWord ++ tailWord_4209348) baseStart_4209348 baseEnd_4209348 := by
    simpa [prefixWord, tailWord_4209348, baseEnd_4209348] using wordTrace_append hprefix tailTrace_4209348
  have hstable : (prefixWord ++ tailWord_4209348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209348).length < 2 ^ (prefixWord ++ tailWord_4209348).sum := by decide
  have hdescent : baseEnd_4209348 < baseStart_4209348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209365 : List Nat := [1, 3, 2, 5, 1, 2, 1, 1, 1, 6]
def baseStart_4209365 : Nat := 118140960795 + 4209365 * 2 ^ 59
def prefixEnd_4209365 : Nat := 4983230072969 + 3 ^ 40 * 4209365 * 2
def baseEnd_4209365 : Nat := 720475831737676191259663

theorem tailTrace_4209365 : CollatzResearch.WordTrace tailWord_4209365 prefixEnd_4209365 720475831737676191259663 := by
  unfold tailWord_4209365
  simp only [CollatzResearch.WordTrace]
  refine ⟨153528154395196982152373549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102352102930131321434915699 153528154395196982152373549)
  ·
    refine ⟨57573057898198868307140081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153528154395196982152373549 57573057898198868307140081)
    ·
      refine ⟨43179793423649151230355061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57573057898198868307140081 43179793423649151230355061)
      ·
        refine ⟨4048105633467107927845787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43179793423649151230355061 4048105633467107927845787)
        ·
          refine ⟨6072158450200661891768681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4048105633467107927845787 6072158450200661891768681)
          ·
            refine ⟨4554118837650496418826511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6072158450200661891768681 4554118837650496418826511)
            ·
              refine ⟨6831178256475744628239767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4554118837650496418826511 6831178256475744628239767)
              ·
                refine ⟨10246767384713616942359651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6831178256475744628239767 10246767384713616942359651)
                ·
                  refine ⟨15370151077070425413539477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10246767384713616942359651 15370151077070425413539477)
                  ·
                    refine ⟨720475831737676191259663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15370151077070425413539477 720475831737676191259663)
                    ·
                      rfl

theorem cell23_4209365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_4209365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209365 prefixEnd_4209365 := by exact prefixLift 4209365
  have htrace : WordTrace (prefixWord ++ tailWord_4209365) baseStart_4209365 baseEnd_4209365 := by
    simpa [prefixWord, tailWord_4209365, baseEnd_4209365] using wordTrace_append hprefix tailTrace_4209365
  have hstable : (prefixWord ++ tailWord_4209365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209365).length < 2 ^ (prefixWord ++ tailWord_4209365).sum := by decide
  have hdescent : baseEnd_4209365 < baseStart_4209365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209368 : List Nat := [2, 1, 2, 2, 3, 4, 1, 1, 1, 2, 4]
def baseStart_4209368 : Nat := 118140960795 + 4209368 * 2 ^ 59
def prefixEnd_4209368 : Nat := 4983230072969 + 3 ^ 40 * 4209368 * 2
def baseEnd_4209368 : Nat := 2161429035654992062041475

theorem tailTrace_4209368 : CollatzResearch.WordTrace tailWord_4209368 prefixEnd_4209368 2161429035654992062041475 := by
  unfold tailWord_4209368
  simp only [CollatzResearch.WordTrace]
  refine ⟨76764131907093056832366379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102352175876124075776488505 76764131907093056832366379)
  ·
    refine ⟨115146197860639585248549569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76764131907093056832366379 115146197860639585248549569)
    ·
      refine ⟨86359648395479688936412177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115146197860639585248549569 86359648395479688936412177)
      ·
        refine ⟨64769736296609766702309133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86359648395479688936412177 64769736296609766702309133)
        ·
          refine ⟨24288651111228662513365925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64769736296609766702309133 24288651111228662513365925)
          ·
            refine ⟨4554122083355374221256111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24288651111228662513365925 4554122083355374221256111)
            ·
              refine ⟨6831183125033061331884167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4554122083355374221256111 6831183125033061331884167)
              ·
                refine ⟨10246774687549591997826251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6831183125033061331884167 10246774687549591997826251)
                ·
                  refine ⟨15370162031324387996739377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10246774687549591997826251 15370162031324387996739377)
                  ·
                    refine ⟨11527621523493290997554533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15370162031324387996739377 11527621523493290997554533)
                    ·
                      refine ⟨2161429035654992062041475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11527621523493290997554533 2161429035654992062041475)
                      ·
                        rfl

theorem cell23_4209368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_4209368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209368 prefixEnd_4209368 := by exact prefixLift 4209368
  have htrace : WordTrace (prefixWord ++ tailWord_4209368) baseStart_4209368 baseEnd_4209368 := by
    simpa [prefixWord, tailWord_4209368, baseEnd_4209368] using wordTrace_append hprefix tailTrace_4209368
  have hstable : (prefixWord ++ tailWord_4209368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209368).length < 2 ^ (prefixWord ++ tailWord_4209368).sum := by decide
  have hdescent : baseEnd_4209368 < baseStart_4209368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209372 : List Nat := [2, 2, 5, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_4209372 : Nat := 118140960795 + 4209372 * 2 ^ 59
def prefixEnd_4209372 : Nat := 4983230072969 + 3 ^ 40 * 4209372 * 2
def baseEnd_4209372 : Nat := 2161431089577610046391457

theorem tailTrace_4209372 : CollatzResearch.WordTrace tailWord_4209372 prefixEnd_4209372 2161431089577610046391457 := by
  unfold tailWord_4209372
  simp only [CollatzResearch.WordTrace]
  refine ⟨76764204853085811173939185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102352273137447748231918913 76764204853085811173939185)
  ·
    refine ⟨57573153639814358380454389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76764204853085811173939185 57573153639814358380454389)
    ·
      refine ⟨5397483153732596098167599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57573153639814358380454389 5397483153732596098167599)
      ·
        refine ⟨8096224730598894147251399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5397483153732596098167599 8096224730598894147251399)
        ·
          refine ⟨12144337095898341220877099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8096224730598894147251399 12144337095898341220877099)
          ·
            refine ⟨18216505643847511831315649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12144337095898341220877099 18216505643847511831315649)
            ·
              refine ⟨13662379232885633873486737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18216505643847511831315649 13662379232885633873486737)
              ·
                refine ⟨10246784424664225405115053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13662379232885633873486737 10246784424664225405115053)
                ·
                  refine ⟨3842544159249084526918145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10246784424664225405115053 3842544159249084526918145)
                  ·
                    refine ⟨2881908119436813395188609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3842544159249084526918145 2881908119436813395188609)
                    ·
                      refine ⟨2161431089577610046391457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2881908119436813395188609 2161431089577610046391457)
                      ·
                        rfl

theorem cell23_4209372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_4209372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209372 prefixEnd_4209372 := by exact prefixLift 4209372
  have htrace : WordTrace (prefixWord ++ tailWord_4209372) baseStart_4209372 baseEnd_4209372 := by
    simpa [prefixWord, tailWord_4209372, baseEnd_4209372] using wordTrace_append hprefix tailTrace_4209372
  have hstable : (prefixWord ++ tailWord_4209372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209372).length < 2 ^ (prefixWord ++ tailWord_4209372).sum := by decide
  have hdescent : baseEnd_4209372 < baseStart_4209372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209406 : List Nat := [4, 2, 2, 1, 2, 2, 3, 2, 1, 2, 2]
def baseStart_4209406 : Nat := 118140960795 + 4209406 * 2 ^ 59
def prefixEnd_4209406 : Nat := 4983230072969 + 3 ^ 40 * 4209406 * 2
def baseEnd_4209406 : Nat := 2161448547919862913366301

theorem tailTrace_4209406 : CollatzResearch.WordTrace tailWord_4209406 prefixEnd_4209406 2161448547919862913366301 := by
  unfold tailWord_4209406
  simp only [CollatzResearch.WordTrace]
  refine ⟨19191206223506055769327009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102353099858698964103077381 19191206223506055769327009)
  ·
    refine ⟨14393404667629541826995257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19191206223506055769327009 14393404667629541826995257)
    ·
      refine ⟨10795053500722156370246443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14393404667629541826995257 10795053500722156370246443)
      ·
        refine ⟨16192580251083234555369665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10795053500722156370246443 16192580251083234555369665)
        ·
          refine ⟨12144435188312425916527249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16192580251083234555369665 12144435188312425916527249)
          ·
            refine ⟨9108326391234319437395437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12144435188312425916527249 9108326391234319437395437)
            ·
              refine ⟨3415622396712869789023289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9108326391234319437395437 3415622396712869789023289)
              ·
                refine ⟨2561716797534652341767467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3415622396712869789023289 2561716797534652341767467)
                ·
                  refine ⟨3842575196301978512651201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2561716797534652341767467 3842575196301978512651201)
                  ·
                    refine ⟨2881931397226483884488401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3842575196301978512651201 2881931397226483884488401)
                    ·
                      refine ⟨2161448547919862913366301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2881931397226483884488401 2161448547919862913366301)
                      ·
                        rfl

theorem cell23_4209406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_4209406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209406 prefixEnd_4209406 := by exact prefixLift 4209406
  have htrace : WordTrace (prefixWord ++ tailWord_4209406) baseStart_4209406 baseEnd_4209406 := by
    simpa [prefixWord, tailWord_4209406, baseEnd_4209406] using wordTrace_append hprefix tailTrace_4209406
  have hstable : (prefixWord ++ tailWord_4209406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209406).length < 2 ^ (prefixWord ++ tailWord_4209406).sum := by decide
  have hdescent : baseEnd_4209406 < baseStart_4209406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209485 : List Nat := [1, 6, 1, 2, 2, 1, 1, 2, 7]
def baseStart_4209485 : Nat := 118140960795 + 4209485 * 2 ^ 59
def prefixEnd_4209485 : Nat := 4983230072969 + 3 ^ 40 * 4209485 * 2
def baseEnd_4209485 : Nat := 240165456987952011586493

theorem tailTrace_4209485 : CollatzResearch.WordTrace tailWord_4209485 prefixEnd_4209485 240165456987952011586493 := by
  unfold tailWord_4209485
  simp only [CollatzResearch.WordTrace]
  refine ⟨153532531154762242646741909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102355020769841495097827939 153532531154762242646741909)
  ·
    refine ⟨7196837397879480124066027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 153532531154762242646741909 7196837397879480124066027)
    ·
      refine ⟨10795256096819220186099041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7196837397879480124066027 10795256096819220186099041)
      ·
        refine ⟨8096442072614415139574281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10795256096819220186099041 8096442072614415139574281)
        ·
          refine ⟨6072331554460811354680711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8096442072614415139574281 6072331554460811354680711)
          ·
            refine ⟨9108497331691217032021067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6072331554460811354680711 9108497331691217032021067)
            ·
              refine ⟨13662745997536825548031601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9108497331691217032021067 13662745997536825548031601)
              ·
                refine ⟨10247059498152619161023701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13662745997536825548031601 10247059498152619161023701)
                ·
                  refine ⟨240165456987952011586493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10247059498152619161023701 240165456987952011586493)
                  ·
                    rfl

theorem cell23_4209485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_4209485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209485 prefixEnd_4209485 := by exact prefixLift 4209485
  have htrace : WordTrace (prefixWord ++ tailWord_4209485) baseStart_4209485 baseEnd_4209485 := by
    simpa [prefixWord, tailWord_4209485, baseEnd_4209485] using wordTrace_append hprefix tailTrace_4209485
  have hstable : (prefixWord ++ tailWord_4209485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209485).length < 2 ^ (prefixWord ++ tailWord_4209485).sum := by decide
  have hdescent : baseEnd_4209485 < baseStart_4209485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209498 : List Nat := [3, 1, 1, 2, 1, 4, 3, 1, 2, 5]
def baseStart_4209498 : Nat := 118140960795 + 4209498 * 2 ^ 59
def prefixEnd_4209498 : Nat := 4983230072969 + 3 ^ 40 * 4209498 * 2
def baseEnd_4209498 : Nat := 720498596046692184471959

theorem tailTrace_4209498 : CollatzResearch.WordTrace tailWord_4209498 prefixEnd_4209498 720498596046692184471959 := by
  unfold tailWord_4209498
  simp only [CollatzResearch.WordTrace]
  refine ⟨38383251325928786466741287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102355336869143430577976765 38383251325928786466741287)
  ·
    refine ⟨57574876988893179700111931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38383251325928786466741287 57574876988893179700111931)
    ·
      refine ⟨86362315483339769550167897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57574876988893179700111931 86362315483339769550167897)
      ·
        refine ⟨64771736612504827162625923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86362315483339769550167897 64771736612504827162625923)
        ·
          refine ⟨97157604918757240743938885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64771736612504827162625923 97157604918757240743938885)
          ·
            refine ⟨18217050922266982639488541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97157604918757240743938885 18217050922266982639488541)
            ·
              refine ⟨6831394095850118489808203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18217050922266982639488541 6831394095850118489808203)
              ·
                refine ⟨10247091143775177734712305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6831394095850118489808203 10247091143775177734712305)
                ·
                  refine ⟨7685318357831383301034229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10247091143775177734712305 7685318357831383301034229)
                  ·
                    refine ⟨720498596046692184471959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7685318357831383301034229 720498596046692184471959)
                    ·
                      rfl

theorem cell23_4209498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_4209498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209498 prefixEnd_4209498 := by exact prefixLift 4209498
  have htrace : WordTrace (prefixWord ++ tailWord_4209498) baseStart_4209498 baseEnd_4209498 := by
    simpa [prefixWord, tailWord_4209498, baseEnd_4209498] using wordTrace_append hprefix tailTrace_4209498
  have hstable : (prefixWord ++ tailWord_4209498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209498).length < 2 ^ (prefixWord ++ tailWord_4209498).sum := by decide
  have hdescent : baseEnd_4209498 < baseStart_4209498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209612 : List Nat := [2, 2, 1, 4, 1, 1, 4, 1, 2, 3, 2]
def baseStart_4209612 : Nat := 118140960795 + 4209612 * 2 ^ 59
def prefixEnd_4209612 : Nat := 4983230072969 + 3 ^ 40 * 4209612 * 2
def baseEnd_4209612 : Nat := 2161554324934689107390353

theorem tailTrace_4209612 : CollatzResearch.WordTrace tailWord_4209612 prefixEnd_4209612 2161554324934689107390353 := by
  unfold tailWord_4209612
  simp only [CollatzResearch.WordTrace]
  refine ⟨76768581612651071668307545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102358108816868095557743393 76768581612651071668307545)
  ·
    refine ⟨57576436209488303751230659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76768581612651071668307545 57576436209488303751230659)
    ·
      refine ⟨86364654314232455626845989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57576436209488303751230659 86364654314232455626845989)
      ·
        refine ⟨16193372683918585430033623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86364654314232455626845989 16193372683918585430033623)
        ·
          refine ⟨24290059025877878145050435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16193372683918585430033623 24290059025877878145050435)
          ·
            refine ⟨36435088538816817217575653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24290059025877878145050435 36435088538816817217575653)
            ·
              refine ⟨6831579101028153228295435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36435088538816817217575653 6831579101028153228295435)
              ·
                refine ⟨10247368651542229842443153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6831579101028153228295435 10247368651542229842443153)
                ·
                  refine ⟨7685526488656672381832365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10247368651542229842443153 7685526488656672381832365)
                  ·
                    refine ⟨2882072433246252143187137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7685526488656672381832365 2882072433246252143187137)
                    ·
                      refine ⟨2161554324934689107390353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2882072433246252143187137 2161554324934689107390353)
                      ·
                        rfl

theorem cell23_4209612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_4209612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209612 prefixEnd_4209612 := by exact prefixLift 4209612
  have htrace : WordTrace (prefixWord ++ tailWord_4209612) baseStart_4209612 baseEnd_4209612 := by
    simpa [prefixWord, tailWord_4209612, baseEnd_4209612] using wordTrace_append hprefix tailTrace_4209612
  have hstable : (prefixWord ++ tailWord_4209612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209612).length < 2 ^ (prefixWord ++ tailWord_4209612).sum := by decide
  have hdescent : baseEnd_4209612 < baseStart_4209612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209631 : List Nat := [1, 1, 2, 3, 16]
def baseStart_4209631 : Nat := 118140960795 + 4209631 * 2 ^ 59
def prefixEnd_4209631 : Nat := 4983230072969 + 3 ^ 40 * 4209631 * 2
def baseEnd_4209631 : Nat := 2965108478830074805285

theorem tailTrace_4209631 : CollatzResearch.WordTrace tailWord_4209631 prefixEnd_4209631 2965108478830074805285 := by
  unfold tailWord_4209631
  simp only [CollatzResearch.WordTrace]
  refine ⟨153537856212233309581556747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102358570808155539721037831 153537856212233309581556747)
  ·
    refine ⟨230306784318349964372335121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153537856212233309581556747 230306784318349964372335121)
    ·
      refine ⟨172730088238762473279251341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230306784318349964372335121 172730088238762473279251341)
      ·
        refine ⟨64773783089535927479719253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172730088238762473279251341 64773783089535927479719253)
        ·
          refine ⟨2965108478830074805285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 64773783089535927479719253 2965108478830074805285)
          ·
            rfl

theorem cell23_4209631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 16].length) (baseStart_4209631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209631 prefixEnd_4209631 := by exact prefixLift 4209631
  have htrace : WordTrace (prefixWord ++ tailWord_4209631) baseStart_4209631 baseEnd_4209631 := by
    simpa [prefixWord, tailWord_4209631, baseEnd_4209631] using wordTrace_append hprefix tailTrace_4209631
  have hstable : (prefixWord ++ tailWord_4209631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209631).length < 2 ^ (prefixWord ++ tailWord_4209631).sum := by decide
  have hdescent : baseEnd_4209631 < baseStart_4209631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209665 : List Nat := [1, 2, 4, 1, 2, 3, 3, 7]
def baseStart_4209665 : Nat := 118140960795 + 4209665 * 2 ^ 59
def prefixEnd_4209665 : Nat := 4983230072969 + 3 ^ 40 * 4209665 * 2
def baseEnd_4209665 : Nat := 80058575533680644445467

theorem tailTrace_4209665 : CollatzResearch.WordTrace tailWord_4209665 prefixEnd_4209665 80058575533680644445467 := by
  unfold tailWord_4209665
  simp only [CollatzResearch.WordTrace]
  refine ⟨153539096294110133388294449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102359397529406755592196299 153539096294110133388294449)
  ·
    refine ⟨115154322220582600041220837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153539096294110133388294449 115154322220582600041220837)
    ·
      refine ⟨21591435416359237507728907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115154322220582600041220837 21591435416359237507728907)
      ·
        refine ⟨32387153124538856261593361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21591435416359237507728907 32387153124538856261593361)
        ·
          refine ⟨24290364843404142196195021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32387153124538856261593361 24290364843404142196195021)
          ·
            refine ⟨9108886816276553323573133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24290364843404142196195021 9108886816276553323573133)
            ·
              refine ⟨3415832556103707496339925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9108886816276553323573133 3415832556103707496339925)
              ·
                refine ⟨80058575533680644445467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3415832556103707496339925 80058575533680644445467)
                ·
                  rfl

theorem cell23_4209665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 7].length) (baseStart_4209665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209665 prefixEnd_4209665 := by exact prefixLift 4209665
  have htrace : WordTrace (prefixWord ++ tailWord_4209665) baseStart_4209665 baseEnd_4209665 := by
    simpa [prefixWord, tailWord_4209665, baseEnd_4209665] using wordTrace_append hprefix tailTrace_4209665
  have hstable : (prefixWord ++ tailWord_4209665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209665).length < 2 ^ (prefixWord ++ tailWord_4209665).sum := by decide
  have hdescent : baseEnd_4209665 < baseStart_4209665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209675 : List Nat := [1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 3]
def baseStart_4209675 : Nat := 118140960795 + 4209675 * 2 ^ 59
def prefixEnd_4209675 : Nat := 4983230072969 + 3 ^ 40 * 4209675 * 2
def baseEnd_4209675 : Nat := 2161586674215922360902563

theorem tailTrace_4209675 : CollatzResearch.WordTrace tailWord_4209675 prefixEnd_4209675 2161586674215922360902563 := by
  unfold tailWord_4209675
  simp only [CollatzResearch.WordTrace]
  refine ⟨153539461024073905096158479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102359640682715936730772319 153539461024073905096158479)
  ·
    refine ⟨230309191536110857644237719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153539461024073905096158479 230309191536110857644237719)
    ·
      refine ⟨345463787304166286466356579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230309191536110857644237719 345463787304166286466356579)
      ·
        refine ⟨518195680956249429699534869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345463787304166286466356579 518195680956249429699534869)
        ·
          refine ⟨24290422544824192017165697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 518195680956249429699534869 24290422544824192017165697)
          ·
            refine ⟨18217816908618144012874273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24290422544824192017165697 18217816908618144012874273)
            ·
              refine ⟨13663362681463608009655705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18217816908618144012874273 13663362681463608009655705)
              ·
                refine ⟨10247522011097706007241779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13663362681463608009655705 10247522011097706007241779)
                ·
                  refine ⟨15371283016646559010862669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10247522011097706007241779 15371283016646559010862669)
                  ·
                    refine ⟨5764231131242459629073501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15371283016646559010862669 5764231131242459629073501)
                    ·
                      refine ⟨2161586674215922360902563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5764231131242459629073501 2161586674215922360902563)
                      ·
                        rfl

theorem cell23_4209675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 3].length) (baseStart_4209675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209675 prefixEnd_4209675 := by exact prefixLift 4209675
  have htrace : WordTrace (prefixWord ++ tailWord_4209675) baseStart_4209675 baseEnd_4209675 := by
    simpa [prefixWord, tailWord_4209675, baseEnd_4209675] using wordTrace_append hprefix tailTrace_4209675
  have hstable : (prefixWord ++ tailWord_4209675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209675).length < 2 ^ (prefixWord ++ tailWord_4209675).sum := by decide
  have hdescent : baseEnd_4209675 < baseStart_4209675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209676 : List Nat := [2, 2, 1, 2, 3, 3, 2, 3, 1, 2, 2]
def baseStart_4209676 : Nat := 118140960795 + 4209676 * 2 ^ 59
def prefixEnd_4209676 : Nat := 4983230072969 + 3 ^ 40 * 4209676 * 2
def baseEnd_4209676 : Nat := 2161587187696576856990059

theorem tailTrace_4209676 : CollatzResearch.WordTrace tailWord_4209676 prefixEnd_4209676 2161587187696576856990059 := by
  unfold tailWord_4209676
  simp only [CollatzResearch.WordTrace]
  refine ⟨76769748748535141133472441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102359664998046854844629921 76769748748535141133472441)
  ·
    refine ⟨57577311561401355850104331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76769748748535141133472441 57577311561401355850104331)
    ·
      refine ⟨86365967342102033775156497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57577311561401355850104331 86365967342102033775156497)
      ·
        refine ⟨64774475506576525331367373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86365967342102033775156497 64774475506576525331367373)
        ·
          refine ⟨24290428314966196999262765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64774475506576525331367373 24290428314966196999262765)
          ·
            refine ⟨9108910618112323874723537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24290428314966196999262765 9108910618112323874723537)
            ·
              refine ⟨6831682963584242906042653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9108910618112323874723537 6831682963584242906042653)
              ·
                refine ⟨2561881111344091089765995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6831682963584242906042653 2561881111344091089765995)
                ·
                  refine ⟨3842821667016136634648993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2561881111344091089765995 3842821667016136634648993)
                  ·
                    refine ⟨2882116250262102475986745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3842821667016136634648993 2882116250262102475986745)
                    ·
                      refine ⟨2161587187696576856990059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2882116250262102475986745 2161587187696576856990059)
                      ·
                        rfl

theorem cell23_4209676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 1, 2, 2].length) (baseStart_4209676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209676 prefixEnd_4209676 := by exact prefixLift 4209676
  have htrace : WordTrace (prefixWord ++ tailWord_4209676) baseStart_4209676 baseEnd_4209676 := by
    simpa [prefixWord, tailWord_4209676, baseEnd_4209676] using wordTrace_append hprefix tailTrace_4209676
  have hstable : (prefixWord ++ tailWord_4209676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209676).length < 2 ^ (prefixWord ++ tailWord_4209676).sum := by decide
  have hdescent : baseEnd_4209676 < baseStart_4209676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209708 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 2, 6]
def baseStart_4209708 : Nat := 118140960795 + 4209708 * 2 ^ 59
def prefixEnd_4209708 : Nat := 4983230072969 + 3 ^ 40 * 4209708 * 2
def baseEnd_4209708 : Nat := 720534539692506910596637

theorem tailTrace_4209708 : CollatzResearch.WordTrace tailWord_4209708 prefixEnd_4209708 720534539692506910596637 := by
  unfold tailWord_4209708
  simp only [CollatzResearch.WordTrace]
  refine ⟨76770332316477175866054889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102360443088636234488073185 76770332316477175866054889)
  ·
    refine ⟨57577749237357881899541167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76770332316477175866054889 57577749237357881899541167)
    ·
      refine ⟨86366623856036822849311751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57577749237357881899541167 86366623856036822849311751)
      ·
        refine ⟨129549935784055234273967627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86366623856036822849311751 129549935784055234273967627)
        ·
          refine ⟨194324903676082851410951441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129549935784055234273967627 194324903676082851410951441)
          ·
            refine ⟨145743677757062138558213581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194324903676082851410951441 145743677757062138558213581)
            ·
              refine ⟨54653879158898301959330093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145743677757062138558213581 54653879158898301959330093)
              ·
                refine ⟨20495204684586863234748785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54653879158898301959330093 20495204684586863234748785)
                ·
                  refine ⟨15371403513440147426061589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20495204684586863234748785 15371403513440147426061589)
                  ·
                    refine ⟨720534539692506910596637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15371403513440147426061589 720534539692506910596637)
                    ·
                      rfl

theorem cell23_4209708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_4209708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209708 prefixEnd_4209708 := by exact prefixLift 4209708
  have htrace : WordTrace (prefixWord ++ tailWord_4209708) baseStart_4209708 baseEnd_4209708 := by
    simpa [prefixWord, tailWord_4209708, baseEnd_4209708] using wordTrace_append hprefix tailTrace_4209708
  have hstable : (prefixWord ++ tailWord_4209708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209708).length < 2 ^ (prefixWord ++ tailWord_4209708).sum := by decide
  have hdescent : baseEnd_4209708 < baseStart_4209708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209735 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 5]
def baseStart_4209735 : Nat := 118140960795 + 4209735 * 2 ^ 59
def prefixEnd_4209735 : Nat := 4983230072969 + 3 ^ 40 * 4209735 * 2
def baseEnd_4209735 : Nat := 2161617483055192126152287

theorem tailTrace_4209735 : CollatzResearch.WordTrace tailWord_4209735 prefixEnd_4209735 2161617483055192126152287 := by
  unfold tailWord_4209735
  simp only [CollatzResearch.WordTrace]
  refine ⟨153541649403856535343342659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102361099602571023562228439 153541649403856535343342659)
  ·
    refine ⟨230312474105784803015013989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153541649403856535343342659 230312474105784803015013989)
    ·
      refine ⟨43183588894834650565315123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230312474105784803015013989 43183588894834650565315123)
      ·
        refine ⟨64775383342251975847972685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43183588894834650565315123 64775383342251975847972685)
        ·
          refine ⟨24290768753344490942989757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64775383342251975847972685 24290768753344490942989757)
          ·
            refine ⟨9109038282504184103621159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24290768753344490942989757 9109038282504184103621159)
            ·
              refine ⟨13663557423756276155431739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9109038282504184103621159 13663557423756276155431739)
              ·
                refine ⟨20495336135634414233147609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13663557423756276155431739 20495336135634414233147609)
                ·
                  refine ⟨15371502101725810674860707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20495336135634414233147609 15371502101725810674860707)
                  ·
                    refine ⟨23057253152588716012291061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15371502101725810674860707 23057253152588716012291061)
                    ·
                      refine ⟨2161617483055192126152287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23057253152588716012291061 2161617483055192126152287)
                      ·
                        rfl

theorem cell23_4209735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_4209735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209735 prefixEnd_4209735 := by exact prefixLift 4209735
  have htrace : WordTrace (prefixWord ++ tailWord_4209735) baseStart_4209735 baseEnd_4209735 := by
    simpa [prefixWord, tailWord_4209735, baseEnd_4209735] using wordTrace_append hprefix tailTrace_4209735
  have hstable : (prefixWord ++ tailWord_4209735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209735).length < 2 ^ (prefixWord ++ tailWord_4209735).sum := by decide
  have hdescent : baseEnd_4209735 < baseStart_4209735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209738 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 9]
def baseStart_4209738 : Nat := 118140960795 + 4209738 * 2 ^ 59
def prefixEnd_4209738 : Nat := 4983230072969 + 3 ^ 40 * 4209738 * 2
def baseEnd_4209738 : Nat := 240179891499683957157197

theorem tailTrace_4209738 : CollatzResearch.WordTrace tailWord_4209738 prefixEnd_4209738 240179891499683957157197 := by
  unfold tailWord_4209738
  simp only [CollatzResearch.WordTrace]
  refine ⟨38385439705711416713925467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102361172548563777903801245 38385439705711416713925467)
  ·
    refine ⟨57578159558567125070888201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38385439705711416713925467 57578159558567125070888201)
    ·
      refine ⟨43183619668925343803166151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57578159558567125070888201 43183619668925343803166151)
      ·
        refine ⟨64775429503388015704749227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43183619668925343803166151 64775429503388015704749227)
        ·
          refine ⟨97163144255082023557123841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64775429503388015704749227 97163144255082023557123841)
          ·
            refine ⟨72872358191311517667842881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97163144255082023557123841 72872358191311517667842881)
            ·
              refine ⟨54654268643483638250882161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72872358191311517667842881 54654268643483638250882161)
              ·
                refine ⟨40990701482612728688161621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54654268643483638250882161 40990701482612728688161621)
                ·
                  refine ⟨240179891499683957157197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40990701482612728688161621 240179891499683957157197)
                  ·
                    rfl

theorem cell23_4209738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 9].length) (baseStart_4209738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209738 prefixEnd_4209738 := by exact prefixLift 4209738
  have htrace : WordTrace (prefixWord ++ tailWord_4209738) baseStart_4209738 baseEnd_4209738 := by
    simpa [prefixWord, tailWord_4209738, baseEnd_4209738] using wordTrace_append hprefix tailTrace_4209738
  have hstable : (prefixWord ++ tailWord_4209738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209738).length < 2 ^ (prefixWord ++ tailWord_4209738).sum := by decide
  have hdescent : baseEnd_4209738 < baseStart_4209738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
