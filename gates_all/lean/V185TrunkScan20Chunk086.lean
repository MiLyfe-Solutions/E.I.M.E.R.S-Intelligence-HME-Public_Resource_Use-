import V185TrunkScan20Chunk085

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_523393 : List Nat := [1, 2, 4, 2, 2, 2, 2, 1, 4]
def baseStart_523393 : Nat := 118140960795 + 523393 * 2 ^ 59
def prefixEnd_523393 : Nat := 4983230072969 + 3 ^ 40 * 523393 * 2
def baseEnd_523393 : Nat := 238890826843356405493747

theorem tailTrace_523393 : CollatzResearch.WordTrace tailWord_523393 prefixEnd_523393 238890826843356405493747 := by
  unfold tailWord_523393
  simp only [CollatzResearch.WordTrace]
  refine ⟨19089710992844024252934833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12726473995229349501956555 19089710992844024252934833)
  ·
    refine ⟨14317283244633018189701125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19089710992844024252934833 14317283244633018189701125)
    ·
      refine ⟨2684490608368690910568961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14317283244633018189701125 2684490608368690910568961)
      ·
        refine ⟨2013367956276518182926721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2684490608368690910568961 2013367956276518182926721)
        ·
          refine ⟨1510025967207388637195041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2013367956276518182926721 1510025967207388637195041)
          ·
            refine ⟨1132519475405541477896281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1510025967207388637195041 1132519475405541477896281)
            ·
              refine ⟨849389606554156108422211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1132519475405541477896281 849389606554156108422211)
              ·
                refine ⟨1274084409831234162633317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849389606554156108422211 1274084409831234162633317)
                ·
                  refine ⟨238890826843356405493747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1274084409831234162633317 238890826843356405493747)
                  ·
                    rfl

theorem cell20_523393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_523393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523393 prefixEnd_523393 := by exact prefixLift 523393
  have htrace : WordTrace (prefixWord ++ tailWord_523393) baseStart_523393 baseEnd_523393 := by
    simpa [prefixWord, tailWord_523393, baseEnd_523393] using wordTrace_append hprefix tailTrace_523393
  have hstable : (prefixWord ++ tailWord_523393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523393).length < 2 ^ (prefixWord ++ tailWord_523393).sum := by decide
  have hdescent : baseEnd_523393 < baseStart_523393 := by decide
  rcases family_descends (prefixWord ++ tailWord_523393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523421 : List Nat := [1, 4, 2, 1, 1, 2, 3, 6]
def baseStart_523421 : Nat := 118140960795 + 523421 * 2 ^ 59
def prefixEnd_523421 : Nat := 4983230072969 + 3 ^ 40 * 523421 * 2
def baseEnd_523421 : Nat := 79634535602104250853433

theorem tailTrace_523421 : CollatzResearch.WordTrace tailWord_523421 prefixEnd_523421 79634535602104250853433 := by
  unfold tailWord_523421
  simp only [CollatzResearch.WordTrace]
  refine ⟨19090732236742585034954117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12727154824495056689969411 19090732236742585034954117)
  ·
    refine ⟨3579512294389234694053897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19090732236742585034954117 3579512294389234694053897)
    ·
      refine ⟨2684634220791926020540423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3579512294389234694053897 2684634220791926020540423)
      ·
        refine ⟨4026951331187889030810635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2684634220791926020540423 4026951331187889030810635)
        ·
          refine ⟨6040426996781833546215953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4026951331187889030810635 6040426996781833546215953)
          ·
            refine ⟨4530320247586375159661965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6040426996781833546215953 4530320247586375159661965)
            ·
              refine ⟨1698870092844890684873237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4530320247586375159661965 1698870092844890684873237)
              ·
                refine ⟨79634535602104250853433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1698870092844890684873237 79634535602104250853433)
                ·
                  rfl

theorem cell20_523421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 6].length) (baseStart_523421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523421 prefixEnd_523421 := by exact prefixLift 523421
  have htrace : WordTrace (prefixWord ++ tailWord_523421) baseStart_523421 baseEnd_523421 := by
    simpa [prefixWord, tailWord_523421, baseEnd_523421] using wordTrace_append hprefix tailTrace_523421
  have hstable : (prefixWord ++ tailWord_523421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523421).length < 2 ^ (prefixWord ++ tailWord_523421).sum := by decide
  have hdescent : baseEnd_523421 < baseStart_523421 := by decide
  rcases family_descends (prefixWord ++ tailWord_523421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523458 : List Nat := [3, 5, 1, 1, 2, 1, 1, 3, 3]
def baseStart_523458 : Nat := 118140960795 + 523458 * 2 ^ 59
def prefixEnd_523458 : Nat := 4983230072969 + 3 ^ 40 * 523458 * 2
def baseEnd_523458 : Nat := 238920494614505068326815

theorem tailTrace_523458 : CollatzResearch.WordTrace tailWord_523458 prefixEnd_523458 238920494614505068326815 := by
  unfold tailWord_523458
  simp only [CollatzResearch.WordTrace]
  refine ⟨4773020434402135088512757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12728054491739026902700685 4773020434402135088512757)
  ·
    refine ⟨447470665725200164548071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4773020434402135088512757 447470665725200164548071)
    ·
      refine ⟨671205998587800246822107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447470665725200164548071 671205998587800246822107)
      ·
        refine ⟨1006808997881700370233161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671205998587800246822107 1006808997881700370233161)
        ·
          refine ⟨755106748411275277674871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1006808997881700370233161 755106748411275277674871)
          ·
            refine ⟨1132660122616912916512307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755106748411275277674871 1132660122616912916512307)
            ·
              refine ⟨1698990183925369374768461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132660122616912916512307 1698990183925369374768461)
              ·
                refine ⟨637121318972013515538173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1698990183925369374768461 637121318972013515538173)
                ·
                  refine ⟨238920494614505068326815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 637121318972013515538173 238920494614505068326815)
                  ·
                    rfl

theorem cell20_523458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_523458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523458 prefixEnd_523458 := by exact prefixLift 523458
  have htrace : WordTrace (prefixWord ++ tailWord_523458) baseStart_523458 baseEnd_523458 := by
    simpa [prefixWord, tailWord_523458, baseEnd_523458] using wordTrace_append hprefix tailTrace_523458
  have hstable : (prefixWord ++ tailWord_523458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523458).length < 2 ^ (prefixWord ++ tailWord_523458).sum := by decide
  have hdescent : baseEnd_523458 < baseStart_523458 := by decide
  rcases family_descends (prefixWord ++ tailWord_523458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523473 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 6]
def baseStart_523473 : Nat := 118140960795 + 523473 * 2 ^ 59
def prefixEnd_523473 : Nat := 4983230072969 + 3 ^ 40 * 523473 * 2
def baseEnd_523473 : Nat := 238927341023231682826753

theorem tailTrace_523473 : CollatzResearch.WordTrace tailWord_523473 prefixEnd_523473 238927341023231682826753 := by
  unfold tailWord_523473
  simp only [CollatzResearch.WordTrace]
  refine ⟨19092628832554197915847073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12728419221702798610564715 19092628832554197915847073)
  ·
    refine ⟨14319471624415648436885305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19092628832554197915847073 14319471624415648436885305)
    ·
      refine ⟨10739603718311736327663979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14319471624415648436885305 10739603718311736327663979)
      ·
        refine ⟨16109405577467604491495969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10739603718311736327663979 16109405577467604491495969)
        ·
          refine ⟨12082054183100703368621977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16109405577467604491495969 12082054183100703368621977)
          ·
            refine ⟨9061540637325527526466483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12082054183100703368621977 9061540637325527526466483)
            ·
              refine ⟨13592310955988291289699725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9061540637325527526466483 13592310955988291289699725)
              ·
                refine ⟨5097116608495609233637397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13592310955988291289699725 5097116608495609233637397)
                ·
                  refine ⟨238927341023231682826753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5097116608495609233637397 238927341023231682826753)
                  ·
                    rfl

theorem cell20_523473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_523473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523473 prefixEnd_523473 := by exact prefixLift 523473
  have htrace : WordTrace (prefixWord ++ tailWord_523473) baseStart_523473 baseEnd_523473 := by
    simpa [prefixWord, tailWord_523473, baseEnd_523473] using wordTrace_append hprefix tailTrace_523473
  have hstable : (prefixWord ++ tailWord_523473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523473).length < 2 ^ (prefixWord ++ tailWord_523473).sum := by decide
  have hdescent : baseEnd_523473 < baseStart_523473 := by decide
  rcases family_descends (prefixWord ++ tailWord_523473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523503 : List Nat := [1, 1, 2, 1, 7, 2, 2, 2, 2]
def baseStart_523503 : Nat := 118140960795 + 523503 * 2 ^ 59
def prefixEnd_523503 : Nat := 4983230072969 + 3 ^ 40 * 523503 * 2
def baseEnd_523503 : Nat := 238941033840684911826631

theorem tailTrace_523503 : CollatzResearch.WordTrace tailWord_523503 prefixEnd_523503 238941033840684911826631 := by
  unfold tailWord_523503
  simp only [CollatzResearch.WordTrace]
  refine ⟨19093723022445513039439163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12729148681630342026292775 19093723022445513039439163)
  ·
    refine ⟨28640584533668269559158745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19093723022445513039439163 28640584533668269559158745)
    ·
      refine ⟨21480438400251202169369059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28640584533668269559158745 21480438400251202169369059)
      ·
        refine ⟨32220657600376803254053589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21480438400251202169369059 32220657600376803254053589)
        ·
          refine ⟨755171662508831326266881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 32220657600376803254053589 755171662508831326266881)
          ·
            refine ⟨566378746881623494700161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 755171662508831326266881 566378746881623494700161)
            ·
              refine ⟨424784060161217621025121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 566378746881623494700161 424784060161217621025121)
              ·
                refine ⟨318588045120913215768841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424784060161217621025121 318588045120913215768841)
                ·
                  refine ⟨238941033840684911826631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318588045120913215768841 238941033840684911826631)
                  ·
                    rfl

theorem cell20_523503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 2].length) (baseStart_523503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523503 prefixEnd_523503 := by exact prefixLift 523503
  have htrace : WordTrace (prefixWord ++ tailWord_523503) baseStart_523503 baseEnd_523503 := by
    simpa [prefixWord, tailWord_523503, baseEnd_523503] using wordTrace_append hprefix tailTrace_523503
  have hstable : (prefixWord ++ tailWord_523503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523503).length < 2 ^ (prefixWord ++ tailWord_523503).sum := by decide
  have hdescent : baseEnd_523503 < baseStart_523503 := by decide
  rcases family_descends (prefixWord ++ tailWord_523503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523507 : List Nat := [1, 1, 1, 2, 2, 6, 1, 4, 2]
def baseStart_523507 : Nat := 118140960795 + 523507 * 2 ^ 59
def prefixEnd_523507 : Nat := 4983230072969 + 3 ^ 40 * 523507 * 2
def baseEnd_523507 : Nat := 238942859549678675693281

theorem tailTrace_523507 : CollatzResearch.WordTrace tailWord_523507 prefixEnd_523507 238942859549678675693281 := by
  unfold tailWord_523507
  simp only [CollatzResearch.WordTrace]
  refine ⟨19093868914431021722584775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12729245942954014481723183 19093868914431021722584775)
  ·
    refine ⟨28640803371646532583877163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19093868914431021722584775 28640803371646532583877163)
    ·
      refine ⟨42961205057469798875815745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28640803371646532583877163 42961205057469798875815745)
      ·
        refine ⟨32220903793102349156861809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42961205057469798875815745 32220903793102349156861809)
        ·
          refine ⟨24165677844826761867646357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32220903793102349156861809 24165677844826761867646357)
          ·
            refine ⟨1132766148976254462545923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24165677844826761867646357 1132766148976254462545923)
            ·
              refine ⟨1699149223464381693818885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132766148976254462545923 1699149223464381693818885)
              ·
                refine ⟨318590479399571567591041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1699149223464381693818885 318590479399571567591041)
                ·
                  refine ⟨238942859549678675693281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318590479399571567591041 238942859549678675693281)
                  ·
                    rfl

theorem cell20_523507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 2].length) (baseStart_523507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523507 prefixEnd_523507 := by exact prefixLift 523507
  have htrace : WordTrace (prefixWord ++ tailWord_523507) baseStart_523507 baseEnd_523507 := by
    simpa [prefixWord, tailWord_523507, baseEnd_523507] using wordTrace_append hprefix tailTrace_523507
  have hstable : (prefixWord ++ tailWord_523507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523507).length < 2 ^ (prefixWord ++ tailWord_523507).sum := by decide
  have hdescent : baseEnd_523507 < baseStart_523507 := by decide
  rcases family_descends (prefixWord ++ tailWord_523507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523521 : List Nat := [1, 2, 4, 1, 1, 3, 2, 3, 3]
def baseStart_523521 : Nat := 118140960795 + 523521 * 2 ^ 59
def prefixEnd_523521 : Nat := 4983230072969 + 3 ^ 40 * 523521 * 2
def baseEnd_523521 : Nat := 238949249531156849226557

theorem tailTrace_523521 : CollatzResearch.WordTrace tailWord_523521 prefixEnd_523521 238949249531156849226557 := by
  unfold tailWord_523521
  simp only [CollatzResearch.WordTrace]
  refine ⟨19094379536380302113594417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12729586357586868075729611 19094379536380302113594417)
  ·
    refine ⟨14320784652285226585195813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19094379536380302113594417 14320784652285226585195813)
    ·
      refine ⟨2685147122303479984724215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14320784652285226585195813 2685147122303479984724215)
      ·
        refine ⟨4027720683455219977086323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2685147122303479984724215 4027720683455219977086323)
        ·
          refine ⟨6041581025182829965629485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4027720683455219977086323 6041581025182829965629485)
          ·
            refine ⟨2265592884443561237111057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6041581025182829965629485 2265592884443561237111057)
            ·
              refine ⟨1699194663332670927833293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2265592884443561237111057 1699194663332670927833293)
              ·
                refine ⟨637197998749751597937485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1699194663332670927833293 637197998749751597937485)
                ·
                  refine ⟨238949249531156849226557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 637197998749751597937485 238949249531156849226557)
                  ·
                    rfl

theorem cell20_523521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_523521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523521 prefixEnd_523521 := by exact prefixLift 523521
  have htrace : WordTrace (prefixWord ++ tailWord_523521) baseStart_523521 baseEnd_523521 := by
    simpa [prefixWord, tailWord_523521, baseEnd_523521] using wordTrace_append hprefix tailTrace_523521
  have hstable : (prefixWord ++ tailWord_523521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523521).length < 2 ^ (prefixWord ++ tailWord_523521).sum := by decide
  have hdescent : baseEnd_523521 < baseStart_523521 := by decide
  rcases family_descends (prefixWord ++ tailWord_523521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523562 : List Nat := [3, 1, 4, 2, 1, 1, 2, 4, 2]
def baseStart_523562 : Nat := 118140960795 + 523562 * 2 ^ 59
def prefixEnd_523562 : Nat := 4983230072969 + 3 ^ 40 * 523562 * 2
def baseEnd_523562 : Nat := 238967963048342928859723

theorem tailTrace_523562 : CollatzResearch.WordTrace tailWord_523562 prefixEnd_523562 238967963048342928859723 := by
  unfold tailWord_523562
  simp only [CollatzResearch.WordTrace]
  refine ⟨4773968732307941528959235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12730583286154510743891293 4773968732307941528959235)
  ·
    refine ⟨7160953098461912293438853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4773968732307941528959235 7160953098461912293438853)
    ·
      refine ⟨1342678705961608555019785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7160953098461912293438853 1342678705961608555019785)
      ·
        refine ⟨1007009029471206416264839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1342678705961608555019785 1007009029471206416264839)
        ·
          refine ⟨1510513544206809624397259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007009029471206416264839 1510513544206809624397259)
          ·
            refine ⟨2265770316310214436595889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510513544206809624397259 2265770316310214436595889)
            ·
              refine ⟨1699327737232660827446917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2265770316310214436595889 1699327737232660827446917)
              ·
                refine ⟨318623950731123905146297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1699327737232660827446917 318623950731123905146297)
                ·
                  refine ⟨238967963048342928859723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318623950731123905146297 238967963048342928859723)
                  ·
                    rfl

theorem cell20_523562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_523562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523562 prefixEnd_523562 := by exact prefixLift 523562
  have htrace : WordTrace (prefixWord ++ tailWord_523562) baseStart_523562 baseEnd_523562 := by
    simpa [prefixWord, tailWord_523562, baseEnd_523562] using wordTrace_append hprefix tailTrace_523562
  have hstable : (prefixWord ++ tailWord_523562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523562).length < 2 ^ (prefixWord ++ tailWord_523562).sum := by decide
  have hdescent : baseEnd_523562 < baseStart_523562 := by decide
  rcases family_descends (prefixWord ++ tailWord_523562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523613 : List Nat := [1, 4, 5, 1, 1, 1, 3, 2, 2]
def baseStart_523613 : Nat := 118140960795 + 523613 * 2 ^ 59
def prefixEnd_523613 : Nat := 4983230072969 + 3 ^ 40 * 523613 * 2
def baseEnd_523613 : Nat := 238991240838013418159515

theorem tailTrace_523613 : CollatzResearch.WordTrace tailWord_523613 prefixEnd_523613 238991240838013418159515 := by
  unfold tailWord_523613
  simp only [CollatzResearch.WordTrace]
  refine ⟨19097735052047001825943493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12731823368031334550628995 19097735052047001825943493)
  ·
    refine ⟨3580825322258812842364405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19097735052047001825943493 3580825322258812842364405)
    ·
      refine ⟨335702373961763703971663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3580825322258812842364405 335702373961763703971663)
      ·
        refine ⟨503553560942645555957495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335702373961763703971663 503553560942645555957495)
        ·
          refine ⟨755330341413968333936243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503553560942645555957495 755330341413968333936243)
          ·
            refine ⟨1132995512120952500904365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755330341413968333936243 1132995512120952500904365)
            ·
              refine ⟨424873317045357187839137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1132995512120952500904365 424873317045357187839137)
              ·
                refine ⟨318654987784017890879353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424873317045357187839137 318654987784017890879353)
                ·
                  refine ⟨238991240838013418159515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318654987784017890879353 238991240838013418159515)
                  ·
                    rfl

theorem cell20_523613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_523613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523613 prefixEnd_523613 := by exact prefixLift 523613
  have htrace : WordTrace (prefixWord ++ tailWord_523613) baseStart_523613 baseEnd_523613 := by
    simpa [prefixWord, tailWord_523613, baseEnd_523613] using wordTrace_append hprefix tailTrace_523613
  have hstable : (prefixWord ++ tailWord_523613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523613).length < 2 ^ (prefixWord ++ tailWord_523613).sum := by decide
  have hdescent : baseEnd_523613 < baseStart_523613 := by decide
  rcases family_descends (prefixWord ++ tailWord_523613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523625 : List Nat := [1, 2, 1, 1, 1, 3, 2, 5, 4]
def baseStart_523625 : Nat := 118140960795 + 523625 * 2 ^ 59
def prefixEnd_523625 : Nat := 4983230072969 + 3 ^ 40 * 523625 * 2
def baseEnd_523625 : Nat := 238996717964994709759465

theorem tailTrace_523625 : CollatzResearch.WordTrace tailWord_523625 prefixEnd_523625 238996717964994709759465 := by
  unfold tailWord_523625
  simp only [CollatzResearch.WordTrace]
  refine ⟨19098172728003527875380329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12732115152002351916920219 19098172728003527875380329)
  ·
    refine ⟨14323629546002645906535247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19098172728003527875380329 14323629546002645906535247)
    ·
      refine ⟨21485444319003968859802871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14323629546002645906535247 21485444319003968859802871)
      ·
        refine ⟨32228166478505953289704307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21485444319003968859802871 32228166478505953289704307)
        ·
          refine ⟨48342249717758929934556461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32228166478505953289704307 48342249717758929934556461)
          ·
            refine ⟨18128343644159598725458673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48342249717758929934556461 18128343644159598725458673)
            ·
              refine ⟨13596257733119699044094005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18128343644159598725458673 13596257733119699044094005)
              ·
                refine ⟨1274649162479971785383813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13596257733119699044094005 1274649162479971785383813)
                ·
                  refine ⟨238996717964994709759465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1274649162479971785383813 238996717964994709759465)
                  ·
                    rfl

theorem cell20_523625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_523625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523625 prefixEnd_523625 := by exact prefixLift 523625
  have htrace : WordTrace (prefixWord ++ tailWord_523625) baseStart_523625 baseEnd_523625 := by
    simpa [prefixWord, tailWord_523625, baseEnd_523625] using wordTrace_append hprefix tailTrace_523625
  have hstable : (prefixWord ++ tailWord_523625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523625).length < 2 ^ (prefixWord ++ tailWord_523625).sum := by decide
  have hdescent : baseEnd_523625 < baseStart_523625 := by decide
  rcases family_descends (prefixWord ++ tailWord_523625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523666 : List Nat := [3, 2, 3, 3, 1, 8]
def baseStart_523666 : Nat := 118140960795 + 523666 * 2 ^ 59
def prefixEnd_523666 : Nat := 4983230072969 + 3 ^ 40 * 523666 * 2
def baseEnd_523666 : Nat := 8852423388228918125653

theorem tailTrace_523666 : CollatzResearch.WordTrace tailWord_523666 prefixEnd_523666 8852423388228918125653 := by
  unfold tailWord_523666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4774917030213747969405713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12733112080569994585081901 4774917030213747969405713)
  ·
    refine ⟨3581187772660310977054285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4774917030213747969405713 3581187772660310977054285)
    ·
      refine ⟨1342945414747616616395357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3581187772660310977054285 1342945414747616616395357)
      ·
        refine ⟨503604530530356231148259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1342945414747616616395357 503604530530356231148259)
        ·
          refine ⟨755406795795534346722389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503604530530356231148259 755406795795534346722389)
          ·
            refine ⟨8852423388228918125653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 755406795795534346722389 8852423388228918125653)
            ·
              rfl

theorem cell20_523666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 8].length) (baseStart_523666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523666 prefixEnd_523666 := by exact prefixLift 523666
  have htrace : WordTrace (prefixWord ++ tailWord_523666) baseStart_523666 baseEnd_523666 := by
    simpa [prefixWord, tailWord_523666, baseEnd_523666] using wordTrace_append hprefix tailTrace_523666
  have hstable : (prefixWord ++ tailWord_523666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523666).length < 2 ^ (prefixWord ++ tailWord_523666).sum := by decide
  have hdescent : baseEnd_523666 < baseStart_523666 := by decide
  rcases family_descends (prefixWord ++ tailWord_523666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523672 : List Nat := [2, 1, 2, 5, 3, 1, 2, 2, 2]
def baseStart_523672 : Nat := 118140960795 + 523672 * 2 ^ 59
def prefixEnd_523672 : Nat := 4983230072969 + 3 ^ 40 * 523672 * 2
def baseEnd_523672 : Nat := 239018170045671435192607

theorem tailTrace_523672 : CollatzResearch.WordTrace tailWord_523672 prefixEnd_523672 239018170045671435192607 := by
  unfold tailWord_523672
  simp only [CollatzResearch.WordTrace]
  refine ⟨9549943479416627451170635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12733257972555503268227513 9549943479416627451170635)
  ·
    refine ⟨14324915219124941176755953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9549943479416627451170635 14324915219124941176755953)
    ·
      refine ⟨10743686414343705882566965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14324915219124941176755953 10743686414343705882566965)
      ·
        refine ⟨1007220601344722426490653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10743686414343705882566965 1007220601344722426490653)
        ·
          refine ⟨377707725504270909933995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1007220601344722426490653 377707725504270909933995)
          ·
            refine ⟨566561588256406364900993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377707725504270909933995 566561588256406364900993)
            ·
              refine ⟨424921191192304773675745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 566561588256406364900993 424921191192304773675745)
              ·
                refine ⟨318690893394228580256809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424921191192304773675745 318690893394228580256809)
                ·
                  refine ⟨239018170045671435192607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318690893394228580256809 239018170045671435192607)
                  ·
                    rfl

theorem cell20_523672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 2].length) (baseStart_523672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523672 prefixEnd_523672 := by exact prefixLift 523672
  have htrace : WordTrace (prefixWord ++ tailWord_523672) baseStart_523672 baseEnd_523672 := by
    simpa [prefixWord, tailWord_523672, baseEnd_523672] using wordTrace_append hprefix tailTrace_523672
  have hstable : (prefixWord ++ tailWord_523672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523672).length < 2 ^ (prefixWord ++ tailWord_523672).sum := by decide
  have hdescent : baseEnd_523672 < baseStart_523672 := by decide
  rcases family_descends (prefixWord ++ tailWord_523672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523673 : List Nat := [1, 2, 1, 2, 1, 6, 2, 2, 3]
def baseStart_523673 : Nat := 118140960795 + 523673 * 2 ^ 59
def prefixEnd_523673 : Nat := 4983230072969 + 3 ^ 40 * 523673 * 2
def baseEnd_523673 : Nat := 239018626472919876159269

theorem tailTrace_523673 : CollatzResearch.WordTrace tailWord_523673 prefixEnd_523673 239018626472919876159269 := by
  unfold tailWord_523673
  simp only [CollatzResearch.WordTrace]
  refine ⟨19099923431829632073127673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12733282287886421382085115 19099923431829632073127673)
  ·
    refine ⟨14324942573872224054845755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19099923431829632073127673 14324942573872224054845755)
    ·
      refine ⟨21487413860808336082268633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14324942573872224054845755 21487413860808336082268633)
      ·
        refine ⟨16115560395606252061701475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21487413860808336082268633 16115560395606252061701475)
        ·
          refine ⟨24173340593409378092552213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16115560395606252061701475 24173340593409378092552213)
          ·
            refine ⟨1133125340316064598088385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24173340593409378092552213 1133125340316064598088385)
            ·
              refine ⟨849844005237048448566289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1133125340316064598088385 849844005237048448566289)
              ·
                refine ⟨637383003927786336424717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 849844005237048448566289 637383003927786336424717)
                ·
                  refine ⟨239018626472919876159269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 637383003927786336424717 239018626472919876159269)
                  ·
                    rfl

theorem cell20_523673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_523673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523673 prefixEnd_523673 := by exact prefixLift 523673
  have htrace : WordTrace (prefixWord ++ tailWord_523673) baseStart_523673 baseEnd_523673 := by
    simpa [prefixWord, tailWord_523673, baseEnd_523673] using wordTrace_append hprefix tailTrace_523673
  have hstable : (prefixWord ++ tailWord_523673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523673).length < 2 ^ (prefixWord ++ tailWord_523673).sum := by decide
  have hdescent : baseEnd_523673 < baseStart_523673 := by decide
  rcases family_descends (prefixWord ++ tailWord_523673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523773 : List Nat := [1, 4, 1, 1, 1, 4, 3, 3, 2]
def baseStart_523773 : Nat := 118140960795 + 523773 * 2 ^ 59
def prefixEnd_523773 : Nat := 4983230072969 + 3 ^ 40 * 523773 * 2
def baseEnd_523773 : Nat := 239064269197763972825527

theorem tailTrace_523773 : CollatzResearch.WordTrace tailWord_523773 prefixEnd_523773 239064269197763972825527 := by
  unfold tailWord_523773
  simp only [CollatzResearch.WordTrace]
  refine ⟨19103570731467349151767973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12735713820978232767845315 19103570731467349151767973)
  ·
    refine ⟨3581919512150127965956495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19103570731467349151767973 3581919512150127965956495)
    ·
      refine ⟨5372879268225191948934743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3581919512150127965956495 5372879268225191948934743)
      ·
        refine ⟨8059318902337787923402115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5372879268225191948934743 8059318902337787923402115)
        ·
          refine ⟨12088978353506681885103173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8059318902337787923402115 12088978353506681885103173)
          ·
            refine ⟨2266683441282502853456845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12088978353506681885103173 2266683441282502853456845)
            ·
              refine ⟨850006290480938570046317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2266683441282502853456845 850006290480938570046317)
              ·
                refine ⟨318752358930351963767369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 850006290480938570046317 318752358930351963767369)
                ·
                  refine ⟨239064269197763972825527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318752358930351963767369 239064269197763972825527)
                  ·
                    rfl

theorem cell20_523773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_523773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523773 prefixEnd_523773 := by exact prefixLift 523773
  have htrace : WordTrace (prefixWord ++ tailWord_523773) baseStart_523773 baseEnd_523773 := by
    simpa [prefixWord, tailWord_523773, baseEnd_523773] using wordTrace_append hprefix tailTrace_523773
  have hstable : (prefixWord ++ tailWord_523773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523773).length < 2 ^ (prefixWord ++ tailWord_523773).sum := by decide
  have hdescent : baseEnd_523773 < baseStart_523773 := by decide
  rcases family_descends (prefixWord ++ tailWord_523773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523780 : List Nat := [2, 3, 2, 3, 2, 2, 6]
def baseStart_523780 : Nat := 118140960795 + 523780 * 2 ^ 59
def prefixEnd_523780 : Nat := 4983230072969 + 3 ^ 40 * 523780 * 2
def baseEnd_523780 : Nat := 26563051576500339954685

theorem tailTrace_523780 : CollatzResearch.WordTrace tailWord_523780 prefixEnd_523780 26563051576500339954685 := by
  unfold tailWord_523780
  simp only [CollatzResearch.WordTrace]
  refine ⟨9551913021220994673636397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12735884028294659564848529 9551913021220994673636397)
  ·
    refine ⟨3581967382957873002613649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9551913021220994673636397 3581967382957873002613649)
    ·
      refine ⟨2686475537218404751960237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3581967382957873002613649 2686475537218404751960237)
      ·
        refine ⟨1007428326456901781985089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2686475537218404751960237 1007428326456901781985089)
        ·
          refine ⟨755571244842676336488817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1007428326456901781985089 755571244842676336488817)
          ·
            refine ⟨566678433632007252366613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 755571244842676336488817 566678433632007252366613)
            ·
              refine ⟨26563051576500339954685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 566678433632007252366613 26563051576500339954685)
              ·
                rfl

theorem cell20_523780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 6].length) (baseStart_523780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523780 prefixEnd_523780 := by exact prefixLift 523780
  have htrace : WordTrace (prefixWord ++ tailWord_523780) baseStart_523780 baseEnd_523780 := by
    simpa [prefixWord, tailWord_523780, baseEnd_523780] using wordTrace_append hprefix tailTrace_523780
  have hstable : (prefixWord ++ tailWord_523780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523780).length < 2 ^ (prefixWord ++ tailWord_523780).sum := by decide
  have hdescent : baseEnd_523780 < baseStart_523780 := by decide
  rcases family_descends (prefixWord ++ tailWord_523780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523784 : List Nat := [2, 1, 3, 2, 1, 1, 10]
def baseStart_523784 : Nat := 118140960795 + 523784 * 2 ^ 59
def prefixEnd_523784 : Nat := 4983230072969 + 3 ^ 40 * 523784 * 2
def baseEnd_523784 : Nat := 26563254433055202606535

theorem tailTrace_523784 : CollatzResearch.WordTrace tailWord_523784 prefixEnd_523784 26563254433055202606535 := by
  unfold tailWord_523784
  simp only [CollatzResearch.WordTrace]
  refine ⟨9551985967213749015209203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12735981289618332020278937 9551985967213749015209203)
  ·
    refine ⟨14327978950820623522813805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9551985967213749015209203 14327978950820623522813805)
    ·
      refine ⟨5372992106557733821055177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14327978950820623522813805 5372992106557733821055177)
      ·
        refine ⟨4029744079918300365791383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5372992106557733821055177 4029744079918300365791383)
        ·
          refine ⟨6044616119877450548687075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4029744079918300365791383 6044616119877450548687075)
          ·
            refine ⟨9066924179816175823030613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6044616119877450548687075 9066924179816175823030613)
            ·
              refine ⟨26563254433055202606535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9066924179816175823030613 26563254433055202606535)
              ·
                rfl

theorem cell20_523784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 10].length) (baseStart_523784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523784 prefixEnd_523784 := by exact prefixLift 523784
  have htrace : WordTrace (prefixWord ++ tailWord_523784) baseStart_523784 baseEnd_523784 := by
    simpa [prefixWord, tailWord_523784, baseEnd_523784] using wordTrace_append hprefix tailTrace_523784
  have hstable : (prefixWord ++ tailWord_523784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523784).length < 2 ^ (prefixWord ++ tailWord_523784).sum := by decide
  have hdescent : baseEnd_523784 < baseStart_523784 := by decide
  rcases family_descends (prefixWord ++ tailWord_523784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523790 : List Nat := [4, 1, 1, 2, 5, 1, 1, 1, 4]
def baseStart_523790 : Nat := 118140960795 + 523790 * 2 ^ 59
def prefixEnd_523790 : Nat := 4983230072969 + 3 ^ 40 * 523790 * 2
def baseEnd_523790 : Nat := 239072028460987469258791

theorem tailTrace_523790 : CollatzResearch.WordTrace tailWord_523790 prefixEnd_523790 239072028460987469258791 := by
  unfold tailWord_523790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2388023846550720131892103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12736127181603840703424549 2388023846550720131892103)
  ·
    refine ⟨3582035769826080197838155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2388023846550720131892103 3582035769826080197838155)
    ·
      refine ⟨5373053654739120296757233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3582035769826080197838155 5373053654739120296757233)
      ·
        refine ⟨4029790241054340222567925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5373053654739120296757233 4029790241054340222567925)
        ·
          refine ⟨377792835098844395865743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4029790241054340222567925 377792835098844395865743)
          ·
            refine ⟨566689252648266593798615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377792835098844395865743 566689252648266593798615)
            ·
              refine ⟨850033878972399890697923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566689252648266593798615 850033878972399890697923)
              ·
                refine ⟨1275050818458599836046885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850033878972399890697923 1275050818458599836046885)
                ·
                  refine ⟨239072028460987469258791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1275050818458599836046885 239072028460987469258791)
                  ·
                    rfl

theorem cell20_523790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_523790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523790 prefixEnd_523790 := by exact prefixLift 523790
  have htrace : WordTrace (prefixWord ++ tailWord_523790) baseStart_523790 baseEnd_523790 := by
    simpa [prefixWord, tailWord_523790, baseEnd_523790] using wordTrace_append hprefix tailTrace_523790
  have hstable : (prefixWord ++ tailWord_523790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523790).length < 2 ^ (prefixWord ++ tailWord_523790).sum := by decide
  have hdescent : baseEnd_523790 < baseStart_523790 := by decide
  rcases family_descends (prefixWord ++ tailWord_523790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523791 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 9]
def baseStart_523791 : Nat := 118140960795 + 523791 * 2 ^ 59
def prefixEnd_523791 : Nat := 4983230072969 + 3 ^ 40 * 523791 * 2
def baseEnd_523791 : Nat := 239072484888235910225453

theorem tailTrace_523791 : CollatzResearch.WordTrace tailWord_523791 prefixEnd_523791 239072484888235910225453 := by
  unfold tailWord_523791
  simp only [CollatzResearch.WordTrace]
  refine ⟨19104227245402138225923227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12736151496934758817282151 19104227245402138225923227)
  ·
    refine ⟨28656340868103207338884841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19104227245402138225923227 28656340868103207338884841)
    ·
      refine ⟨21492255651077405504163631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28656340868103207338884841 21492255651077405504163631)
      ·
        refine ⟨32238383476616108256245447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21492255651077405504163631 32238383476616108256245447)
        ·
          refine ⟨48357575214924162384368171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32238383476616108256245447 48357575214924162384368171)
          ·
            refine ⟨72536362822386243576552257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48357575214924162384368171 72536362822386243576552257)
            ·
              refine ⟨54402272116789682682414193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72536362822386243576552257 54402272116789682682414193)
              ·
                refine ⟨40801704087592262011810645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54402272116789682682414193 40801704087592262011810645)
                ·
                  refine ⟨239072484888235910225453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40801704087592262011810645 239072484888235910225453)
                  ·
                    rfl

theorem cell20_523791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_523791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523791 prefixEnd_523791 := by exact prefixLift 523791
  have htrace : WordTrace (prefixWord ++ tailWord_523791) baseStart_523791 baseEnd_523791 := by
    simpa [prefixWord, tailWord_523791, baseEnd_523791] using wordTrace_append hprefix tailTrace_523791
  have hstable : (prefixWord ++ tailWord_523791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523791).length < 2 ^ (prefixWord ++ tailWord_523791).sum := by decide
  have hdescent : baseEnd_523791 < baseStart_523791 := by decide
  rcases family_descends (prefixWord ++ tailWord_523791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523901 : List Nat := [1, 4, 1, 1, 4, 1, 3, 2, 3]
def baseStart_523901 : Nat := 118140960795 + 523901 * 2 ^ 59
def prefixEnd_523901 : Nat := 4983230072969 + 3 ^ 40 * 523901 * 2
def baseEnd_523901 : Nat := 239122691885564416558337

theorem tailTrace_523901 : CollatzResearch.WordTrace tailWord_523901 prefixEnd_523901 239122691885564416558337 := by
  unfold tailWord_523901
  simp only [CollatzResearch.WordTrace]
  refine ⟨19108239275003627012427557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12738826183335751341618371 19108239275003627012427557)
  ·
    refine ⟨3582794864063180064830167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19108239275003627012427557 3582794864063180064830167)
    ·
      refine ⟨5374192296094770097245251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3582794864063180064830167 5374192296094770097245251)
      ·
        refine ⟨8061288444142155145867877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5374192296094770097245251 8061288444142155145867877)
        ·
          refine ⟨1511491583276654089850227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8061288444142155145867877 1511491583276654089850227)
          ·
            refine ⟨2267237374914981134775341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1511491583276654089850227 2267237374914981134775341)
            ·
              refine ⟨850214015593117925540753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2267237374914981134775341 850214015593117925540753)
              ·
                refine ⟨637660511694838444155565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 850214015593117925540753 637660511694838444155565)
                ·
                  refine ⟨239122691885564416558337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 637660511694838444155565 239122691885564416558337)
                  ·
                    rfl

theorem cell20_523901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_523901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523901 prefixEnd_523901 := by exact prefixLift 523901
  have htrace : WordTrace (prefixWord ++ tailWord_523901) baseStart_523901 baseEnd_523901 := by
    simpa [prefixWord, tailWord_523901, baseEnd_523901] using wordTrace_append hprefix tailTrace_523901
  have hstable : (prefixWord ++ tailWord_523901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523901).length < 2 ^ (prefixWord ++ tailWord_523901).sum := by decide
  have hdescent : baseEnd_523901 < baseStart_523901 := by decide
  rcases family_descends (prefixWord ++ tailWord_523901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523918 : List Nat := [4, 1, 1, 3, 1, 3, 3, 1, 3]
def baseStart_523918 : Nat := 118140960795 + 523918 * 2 ^ 59
def prefixEnd_523918 : Nat := 4983230072969 + 3 ^ 40 * 523918 * 2
def baseEnd_523918 : Nat := 239130451148787912991601

theorem tailTrace_523918 : CollatzResearch.WordTrace tailWord_523918 prefixEnd_523918 239130451148787912991601 := by
  unfold tailWord_523918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2388607414492754864474551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12739239543961359277197605 2388607414492754864474551)
  ·
    refine ⟨3582911121739132296711827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2388607414492754864474551 3582911121739132296711827)
    ·
      refine ⟨5374366682608698445067741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3582911121739132296711827 5374366682608698445067741)
      ·
        refine ⟨2015387505978261916900403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5374366682608698445067741 2015387505978261916900403)
        ·
          refine ⟨3023081258967392875350605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2015387505978261916900403 3023081258967392875350605)
          ·
            refine ⟨1133655472112772328256477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3023081258967392875350605 1133655472112772328256477)
            ·
              refine ⟨425120802042289623096179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1133655472112772328256477 425120802042289623096179)
              ·
                refine ⟨637681203063434434644269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425120802042289623096179 637681203063434434644269)
                ·
                  refine ⟨239130451148787912991601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 637681203063434434644269 239130451148787912991601)
                  ·
                    rfl

theorem cell20_523918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_523918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523918 prefixEnd_523918 := by exact prefixLift 523918
  have htrace : WordTrace (prefixWord ++ tailWord_523918) baseStart_523918 baseEnd_523918 := by
    simpa [prefixWord, tailWord_523918, baseEnd_523918] using wordTrace_append hprefix tailTrace_523918
  have hstable : (prefixWord ++ tailWord_523918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523918).length < 2 ^ (prefixWord ++ tailWord_523918).sum := by decide
  have hdescent : baseEnd_523918 < baseStart_523918 := by decide
  rcases family_descends (prefixWord ++ tailWord_523918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523938 : List Nat := [3, 3, 1, 4, 2, 1, 1, 3, 2]
def baseStart_523938 : Nat := 118140960795 + 523938 * 2 ^ 59
def prefixEnd_523938 : Nat := 4983230072969 + 3 ^ 40 * 523938 * 2
def baseEnd_523938 : Nat := 239139579693756732324853

theorem tailTrace_523938 : CollatzResearch.WordTrace tailWord_523938 prefixEnd_523938 239139579693756732324853 := by
  unfold tailWord_523938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4777397193967395582881117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12739725850579721554349645 4777397193967395582881117)
  ·
    refine ⟨1791523947737773343580419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4777397193967395582881117 1791523947737773343580419)
    ·
      refine ⟨2687285921606660015370629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1791523947737773343580419 2687285921606660015370629)
      ·
        refine ⟨503866110301248752881993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2687285921606660015370629 503866110301248752881993)
        ·
          refine ⟨377899582725936564661495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503866110301248752881993 377899582725936564661495)
          ·
            refine ⟨566849374088904846992243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377899582725936564661495 566849374088904846992243)
            ·
              refine ⟨850274061133357270488365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566849374088904846992243 850274061133357270488365)
              ·
                refine ⟨318852772925008976433137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 850274061133357270488365 318852772925008976433137)
                ·
                  refine ⟨239139579693756732324853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318852772925008976433137 239139579693756732324853)
                  ·
                    rfl

theorem cell20_523938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_523938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523938 prefixEnd_523938 := by exact prefixLift 523938
  have htrace : WordTrace (prefixWord ++ tailWord_523938) baseStart_523938 baseEnd_523938 := by
    simpa [prefixWord, tailWord_523938, baseEnd_523938] using wordTrace_append hprefix tailTrace_523938
  have hstable : (prefixWord ++ tailWord_523938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523938).length < 2 ^ (prefixWord ++ tailWord_523938).sum := by decide
  have hdescent : baseEnd_523938 < baseStart_523938 := by decide
  rcases family_descends (prefixWord ++ tailWord_523938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524019 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 5]
def baseStart_524019 : Nat := 118140960795 + 524019 * 2 ^ 59
def prefixEnd_524019 : Nat := 4983230072969 + 3 ^ 40 * 524019 * 2
def baseEnd_524019 : Nat := 239176550300880450624521

theorem tailTrace_524019 : CollatzResearch.WordTrace tailWord_524019 prefixEnd_524019 239176550300880450624521 := by
  unfold tailWord_524019
  simp only [CollatzResearch.WordTrace]
  refine ⟨19112543088576133165223111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12741695392384088776815407 19112543088576133165223111)
  ·
    refine ⟨28668814632864199747834667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19112543088576133165223111 28668814632864199747834667)
    ·
      refine ⟨43003221949296299621752001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28668814632864199747834667 43003221949296299621752001)
      ·
        refine ⟨32252416461972224716314001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43003221949296299621752001 32252416461972224716314001)
        ·
          refine ⟨24189312346479168537235501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32252416461972224716314001 24189312346479168537235501)
          ·
            refine ⟨9070992129929688201463313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24189312346479168537235501 9070992129929688201463313)
            ·
              refine ⟨6803244097447266151097485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9070992129929688201463313 6803244097447266151097485)
              ·
                refine ⟨2551216536542724806661557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6803244097447266151097485 2551216536542724806661557)
                ·
                  refine ⟨239176550300880450624521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2551216536542724806661557 239176550300880450624521)
                  ·
                    rfl

theorem cell20_524019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_524019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524019 prefixEnd_524019 := by exact prefixLift 524019
  have htrace : WordTrace (prefixWord ++ tailWord_524019) baseStart_524019 baseEnd_524019 := by
    simpa [prefixWord, tailWord_524019, baseEnd_524019] using wordTrace_append hprefix tailTrace_524019
  have hstable : (prefixWord ++ tailWord_524019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524019).length < 2 ^ (prefixWord ++ tailWord_524019).sum := by decide
  have hdescent : baseEnd_524019 < baseStart_524019 := by decide
  rcases family_descends (prefixWord ++ tailWord_524019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524038 : List Nat := [6, 2, 2, 1, 1, 1, 3, 4]
def baseStart_524038 : Nat := 118140960795 + 524038 * 2 ^ 59
def prefixEnd_524038 : Nat := 4983230072969 + 3 ^ 40 * 524038 * 2
def baseEnd_524038 : Nat := 79728407472866942997037

theorem tailTrace_524038 : CollatzResearch.WordTrace tailWord_524038 prefixEnd_524038 79728407472866942997037 := by
  unfold tailWord_524038
  simp only [CollatzResearch.WordTrace]
  refine ⟨597288627359603106567649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12742157383671532940109845 597288627359603106567649)
  ·
    refine ⟨447966470519702329925737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 597288627359603106567649 447966470519702329925737)
    ·
      refine ⟨335974852889776747444303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447966470519702329925737 335974852889776747444303)
      ·
        refine ⟨503962279334665121166455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335974852889776747444303 503962279334665121166455)
        ·
          refine ⟨755943419001997681749683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503962279334665121166455 755943419001997681749683)
          ·
            refine ⟨1133915128502996522624525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755943419001997681749683 1133915128502996522624525)
            ·
              refine ⟨425218173188623695984197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1133915128502996522624525 425218173188623695984197)
              ·
                refine ⟨79728407472866942997037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 425218173188623695984197 79728407472866942997037)
                ·
                  rfl

theorem cell20_524038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_524038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524038 prefixEnd_524038 := by exact prefixLift 524038
  have htrace : WordTrace (prefixWord ++ tailWord_524038) baseStart_524038 baseEnd_524038 := by
    simpa [prefixWord, tailWord_524038, baseEnd_524038] using wordTrace_append hprefix tailTrace_524038
  have hstable : (prefixWord ++ tailWord_524038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524038).length < 2 ^ (prefixWord ++ tailWord_524038).sum := by decide
  have hdescent : baseEnd_524038 < baseStart_524038 := by decide
  rcases family_descends (prefixWord ++ tailWord_524038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524052 : List Nat := [2, 4, 4, 1, 1, 1, 2, 3, 2]
def baseStart_524052 : Nat := 118140960795 + 524052 * 2 ^ 59
def prefixEnd_524052 : Nat := 4983230072969 + 3 ^ 40 * 524052 * 2
def baseEnd_524052 : Nat := 239191612400079002524387

theorem tailTrace_524052 : CollatzResearch.WordTrace tailWord_524052 prefixEnd_524052 239191612400079002524387 := by
  unfold tailWord_524052
  simp only [CollatzResearch.WordTrace]
  refine ⟨9556873348728289900587205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12742497798304386534116273 9556873348728289900587205)
  ·
    refine ⟨1791913752886554356360101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9556873348728289900587205 1791913752886554356360101)
    ·
      refine ⟨335983828666228941817519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1791913752886554356360101 335983828666228941817519)
      ·
        refine ⟨503975742999343412726279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335983828666228941817519 503975742999343412726279)
        ·
          refine ⟨755963614499015119089419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503975742999343412726279 755963614499015119089419)
          ·
            refine ⟨1133945421748522678634129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755963614499015119089419 1133945421748522678634129)
            ·
              refine ⟨850459066311392008975597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1133945421748522678634129 850459066311392008975597)
              ·
                refine ⟨318922149866772003365849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 850459066311392008975597 318922149866772003365849)
                ·
                  refine ⟨239191612400079002524387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318922149866772003365849 239191612400079002524387)
                  ·
                    rfl

theorem cell20_524052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_524052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524052 prefixEnd_524052 := by exact prefixLift 524052
  have htrace : WordTrace (prefixWord ++ tailWord_524052) baseStart_524052 baseEnd_524052 := by
    simpa [prefixWord, tailWord_524052, baseEnd_524052] using wordTrace_append hprefix tailTrace_524052
  have hstable : (prefixWord ++ tailWord_524052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524052).length < 2 ^ (prefixWord ++ tailWord_524052).sum := by decide
  have hdescent : baseEnd_524052 < baseStart_524052 := by decide
  rcases family_descends (prefixWord ++ tailWord_524052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524081 : List Nat := [1, 2, 2, 3, 2, 2, 1, 3, 4]
def baseStart_524081 : Nat := 118140960795 + 524081 * 2 ^ 59
def prefixEnd_524081 : Nat := 4983230072969 + 3 ^ 40 * 524081 * 2
def baseEnd_524081 : Nat := 239204848790283790557601

theorem tailTrace_524081 : CollatzResearch.WordTrace tailWord_524081 prefixEnd_524081 239204848790283790557601 := by
  unfold tailWord_524081
  simp only [CollatzResearch.WordTrace]
  refine ⟨19114804414351517753980097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12743202942901011835986731 19114804414351517753980097)
  ·
    refine ⟨14336103310763638315485073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19114804414351517753980097 14336103310763638315485073)
    ·
      refine ⟨10752077483072728736613805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14336103310763638315485073 10752077483072728736613805)
      ·
        refine ⟨4032029056152273276230177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10752077483072728736613805 4032029056152273276230177)
        ·
          refine ⟨3024021792114204957172633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4032029056152273276230177 3024021792114204957172633)
          ·
            refine ⟨2268016344085653717879475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3024021792114204957172633 2268016344085653717879475)
            ·
              refine ⟨3402024516128480576819213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2268016344085653717879475 3402024516128480576819213)
              ·
                refine ⟨1275759193548180216307205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3402024516128480576819213 1275759193548180216307205)
                ·
                  refine ⟨239204848790283790557601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1275759193548180216307205 239204848790283790557601)
                  ·
                    rfl

theorem cell20_524081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_524081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524081 prefixEnd_524081 := by exact prefixLift 524081
  have htrace : WordTrace (prefixWord ++ tailWord_524081) baseStart_524081 baseEnd_524081 := by
    simpa [prefixWord, tailWord_524081, baseEnd_524081] using wordTrace_append hprefix tailTrace_524081
  have hstable : (prefixWord ++ tailWord_524081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524081).length < 2 ^ (prefixWord ++ tailWord_524081).sum := by decide
  have hdescent : baseEnd_524081 < baseStart_524081 := by decide
  rcases family_descends (prefixWord ++ tailWord_524081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524132 : List Nat := [2, 3, 1, 1, 5, 1, 3, 2, 2]
def baseStart_524132 : Nat := 118140960795 + 524132 * 2 ^ 59
def prefixEnd_524132 : Nat := 4983230072969 + 3 ^ 40 * 524132 * 2
def baseEnd_524132 : Nat := 239228126579954279857393

theorem tailTrace_524132 : CollatzResearch.WordTrace tailWord_524132 prefixEnd_524132 239228126579954279857393 := by
  unfold tailWord_524132
  simp only [CollatzResearch.WordTrace]
  refine ⟨9558332268583376732043325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12744443024777835642724433 9558332268583376732043325)
  ·
    refine ⟨3584374600718766274516247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9558332268583376732043325 3584374600718766274516247)
    ·
      refine ⟨5376561901078149411774371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3584374600718766274516247 5376561901078149411774371)
      ·
        refine ⟨8064842851617224117661557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5376561901078149411774371 8064842851617224117661557)
        ·
          refine ⟨756079017339114761030771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8064842851617224117661557 756079017339114761030771)
          ·
            refine ⟨1134118526008672141546157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756079017339114761030771 1134118526008672141546157)
            ·
              refine ⟨425294447253252053079809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1134118526008672141546157 425294447253252053079809)
              ·
                refine ⟨318970835439939039809857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 425294447253252053079809 318970835439939039809857)
                ·
                  refine ⟨239228126579954279857393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318970835439939039809857 239228126579954279857393)
                  ·
                    rfl

theorem cell20_524132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_524132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524132 prefixEnd_524132 := by exact prefixLift 524132
  have htrace : WordTrace (prefixWord ++ tailWord_524132) baseStart_524132 baseEnd_524132 := by
    simpa [prefixWord, tailWord_524132, baseEnd_524132] using wordTrace_append hprefix tailTrace_524132
  have hstable : (prefixWord ++ tailWord_524132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524132).length < 2 ^ (prefixWord ++ tailWord_524132).sum := by decide
  have hdescent : baseEnd_524132 < baseStart_524132 := by decide
  rcases family_descends (prefixWord ++ tailWord_524132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524164 : List Nat := [2, 3, 2, 1, 1, 1, 4, 6]
def baseStart_524164 : Nat := 118140960795 + 524164 * 2 ^ 59
def prefixEnd_524164 : Nat := 4983230072969 + 3 ^ 40 * 524164 * 2
def baseEnd_524164 : Nat := 79747577417301463596865

theorem tailTrace_524164 : CollatzResearch.WordTrace tailWord_524164 prefixEnd_524164 79747577417301463596865 := by
  unfold tailWord_524164
  simp only [CollatzResearch.WordTrace]
  refine ⟨9558915836525411464625773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12745221115367215286167697 9558915836525411464625773)
  ·
    refine ⟨3584593438697029299234665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9558915836525411464625773 3584593438697029299234665)
    ·
      refine ⟨2688445079022771974425999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3584593438697029299234665 2688445079022771974425999)
      ·
        refine ⟨4032667618534157961638999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2688445079022771974425999 4032667618534157961638999)
        ·
          refine ⟨6049001427801236942458499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4032667618534157961638999 6049001427801236942458499)
          ·
            refine ⟨9073502141701855413687749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6049001427801236942458499 9073502141701855413687749)
            ·
              refine ⟨1701281651569097890066453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9073502141701855413687749 1701281651569097890066453)
              ·
                refine ⟨79747577417301463596865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1701281651569097890066453 79747577417301463596865)
                ·
                  rfl

theorem cell20_524164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_524164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524164 prefixEnd_524164 := by exact prefixLift 524164
  have htrace : WordTrace (prefixWord ++ tailWord_524164) baseStart_524164 baseEnd_524164 := by
    simpa [prefixWord, tailWord_524164, baseEnd_524164] using wordTrace_append hprefix tailTrace_524164
  have hstable : (prefixWord ++ tailWord_524164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524164).length < 2 ^ (prefixWord ++ tailWord_524164).sum := by decide
  have hdescent : baseEnd_524164 < baseStart_524164 := by decide
  rcases family_descends (prefixWord ++ tailWord_524164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524184 : List Nat := [2, 1, 2, 6, 1, 1, 2, 2, 3]
def baseStart_524184 : Nat := 118140960795 + 524184 * 2 ^ 59
def prefixEnd_524184 : Nat := 4983230072969 + 3 ^ 40 * 524184 * 2
def baseEnd_524184 : Nat := 239251860796873210123847

theorem tailTrace_524184 : CollatzResearch.WordTrace tailWord_524184 prefixEnd_524184 239251860796873210123847 := by
  unfold tailWord_524184
  simp only [CollatzResearch.WordTrace]
  refine ⟨9559280566489183172489803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12745707421985577563319737 9559280566489183172489803)
  ·
    refine ⟨14338920849733774758734705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9559280566489183172489803 14338920849733774758734705)
    ·
      refine ⟨10754190637300331069051029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14338920849733774758734705 10754190637300331069051029)
      ·
        refine ⟨504102686123453018861767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10754190637300331069051029 504102686123453018861767)
        ·
          refine ⟨756154029185179528292651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504102686123453018861767 756154029185179528292651)
          ·
            refine ⟨1134231043777769292438977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756154029185179528292651 1134231043777769292438977)
            ·
              refine ⟨850673282833326969329233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1134231043777769292438977 850673282833326969329233)
              ·
                refine ⟨638004962124995226996925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 850673282833326969329233 638004962124995226996925)
                ·
                  refine ⟨239251860796873210123847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 638004962124995226996925 239251860796873210123847)
                  ·
                    rfl

theorem cell20_524184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 3].length) (baseStart_524184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524184 prefixEnd_524184 := by exact prefixLift 524184
  have htrace : WordTrace (prefixWord ++ tailWord_524184) baseStart_524184 baseEnd_524184 := by
    simpa [prefixWord, tailWord_524184, baseEnd_524184] using wordTrace_append hprefix tailTrace_524184
  have hstable : (prefixWord ++ tailWord_524184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524184).length < 2 ^ (prefixWord ++ tailWord_524184).sum := by decide
  have hdescent : baseEnd_524184 < baseStart_524184 := by decide
  rcases family_descends (prefixWord ++ tailWord_524184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524191 : List Nat := [1, 1, 2, 5, 3, 1, 1, 4, 2]
def baseStart_524191 : Nat := 118140960795 + 524191 * 2 ^ 59
def prefixEnd_524191 : Nat := 4983230072969 + 3 ^ 40 * 524191 * 2
def baseEnd_524191 : Nat := 239255055787612296890485

theorem tailTrace_524191 : CollatzResearch.WordTrace tailWord_524191 prefixEnd_524191 239255055787612296890485 := by
  unfold tailWord_524191
  simp only [CollatzResearch.WordTrace]
  refine ⟨19118816443953006540484427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12745877629302004360322951 19118816443953006540484427)
  ·
    refine ⟨28678224665929509810726641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19118816443953006540484427 28678224665929509810726641)
    ·
      refine ⟨21508668499447132358044981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28678224665929509810726641 21508668499447132358044981)
      ·
        refine ⟨2016437671823168658566717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21508668499447132358044981 2016437671823168658566717)
        ·
          refine ⟨756164126933688246962519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2016437671823168658566717 756164126933688246962519)
          ·
            refine ⟨1134246190400532370443779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756164126933688246962519 1134246190400532370443779)
            ·
              refine ⟨1701369285600798555665669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1134246190400532370443779 1701369285600798555665669)
              ·
                refine ⟨319006741050149729187313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1701369285600798555665669 319006741050149729187313)
                ·
                  refine ⟨239255055787612296890485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319006741050149729187313 239255055787612296890485)
                  ·
                    rfl

theorem cell20_524191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 2].length) (baseStart_524191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524191 prefixEnd_524191 := by exact prefixLift 524191
  have htrace : WordTrace (prefixWord ++ tailWord_524191) baseStart_524191 baseEnd_524191 := by
    simpa [prefixWord, tailWord_524191, baseEnd_524191] using wordTrace_append hprefix tailTrace_524191
  have hstable : (prefixWord ++ tailWord_524191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524191).length < 2 ^ (prefixWord ++ tailWord_524191).sum := by decide
  have hdescent : baseEnd_524191 < baseStart_524191 := by decide
  rcases family_descends (prefixWord ++ tailWord_524191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524247 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 5]
def baseStart_524247 : Nat := 118140960795 + 524247 * 2 ^ 59
def prefixEnd_524247 : Nat := 4983230072969 + 3 ^ 40 * 524247 * 2
def baseEnd_524247 : Nat := 239280615713524991023589

theorem tailTrace_524247 : CollatzResearch.WordTrace tailWord_524247 prefixEnd_524247 239280615713524991023589 := by
  unfold tailWord_524247
  simp only [CollatzResearch.WordTrace]
  refine ⟨19120858931750128104522995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12747239287833418736348663 19120858931750128104522995)
  ·
    refine ⟨28681288397625192156784493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19120858931750128104522995 28681288397625192156784493)
    ·
      refine ⟨10755483149109447058794185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28681288397625192156784493 10755483149109447058794185)
      ·
        refine ⟨8066612361832085294095639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10755483149109447058794185 8066612361832085294095639)
        ·
          refine ⟨12099918542748127941143459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8066612361832085294095639 12099918542748127941143459)
          ·
            refine ⟨18149877814122191911715189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12099918542748127941143459 18149877814122191911715189)
            ·
              refine ⟨1701551045073955491723299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18149877814122191911715189 1701551045073955491723299)
              ·
                refine ⟨2552326567610933237584949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1701551045073955491723299 2552326567610933237584949)
                ·
                  refine ⟨239280615713524991023589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2552326567610933237584949 239280615713524991023589)
                  ·
                    rfl

theorem cell20_524247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 5].length) (baseStart_524247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524247 prefixEnd_524247 := by exact prefixLift 524247
  have htrace : WordTrace (prefixWord ++ tailWord_524247) baseStart_524247 baseEnd_524247 := by
    simpa [prefixWord, tailWord_524247, baseEnd_524247] using wordTrace_append hprefix tailTrace_524247
  have hstable : (prefixWord ++ tailWord_524247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524247).length < 2 ^ (prefixWord ++ tailWord_524247).sum := by decide
  have hdescent : baseEnd_524247 < baseStart_524247 := by decide
  rcases family_descends (prefixWord ++ tailWord_524247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524250 : List Nat := [3, 1, 1, 2, 5, 1, 2, 1, 4]
def baseStart_524250 : Nat := 118140960795 + 524250 * 2 ^ 59
def prefixEnd_524250 : Nat := 4983230072969 + 3 ^ 40 * 524250 * 2
def baseEnd_524250 : Nat := 239281984995270313923577

theorem tailTrace_524250 : CollatzResearch.WordTrace tailWord_524250 prefixEnd_524250 239281984995270313923577 := by
  unfold tailWord_524250
  simp only [CollatzResearch.WordTrace]
  refine ⟨4780242087684814904220551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12747312233826173077921469 4780242087684814904220551)
  ·
    refine ⟨7170363131527222356330827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4780242087684814904220551 7170363131527222356330827)
    ·
      refine ⟨10755544697290833534496241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7170363131527222356330827 10755544697290833534496241)
      ·
        refine ⟨8066658522968125150872181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10755544697290833534496241 8066658522968125150872181)
        ·
          refine ⟨756249236528261732894267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8066658522968125150872181 756249236528261732894267)
          ·
            refine ⟨1134373854792392599341401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756249236528261732894267 1134373854792392599341401)
            ·
              refine ⟨850780391094294449506051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1134373854792392599341401 850780391094294449506051)
              ·
                refine ⟨1276170586641441674259077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850780391094294449506051 1276170586641441674259077)
                ·
                  refine ⟨239281984995270313923577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1276170586641441674259077 239281984995270313923577)
                  ·
                    rfl

theorem cell20_524250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_524250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524250 prefixEnd_524250 := by exact prefixLift 524250
  have htrace : WordTrace (prefixWord ++ tailWord_524250) baseStart_524250 baseEnd_524250 := by
    simpa [prefixWord, tailWord_524250, baseEnd_524250] using wordTrace_append hprefix tailTrace_524250
  have hstable : (prefixWord ++ tailWord_524250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524250).length < 2 ^ (prefixWord ++ tailWord_524250).sum := by decide
  have hdescent : baseEnd_524250 < baseStart_524250 := by decide
  rcases family_descends (prefixWord ++ tailWord_524250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524285 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 5]
def baseStart_524285 : Nat := 118140960795 + 524285 * 2 ^ 59
def prefixEnd_524285 : Nat := 4983230072969 + 3 ^ 40 * 524285 * 2
def baseEnd_524285 : Nat := 239297959948965747756767

theorem tailTrace_524285 : CollatzResearch.WordTrace tailWord_524285 prefixEnd_524285 239297959948965747756767 := by
  unfold tailWord_524285
  simp only [CollatzResearch.WordTrace]
  refine ⟨19122244905612460594406309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12748163270408307062937539 19122244905612460594406309)
  ·
    refine ⟨3585420919802336361451183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19122244905612460594406309 3585420919802336361451183)
    ·
      refine ⟨5378131379703504542176775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3585420919802336361451183 5378131379703504542176775)
      ·
        refine ⟨8067197069555256813265163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5378131379703504542176775 8067197069555256813265163)
        ·
          refine ⟨12100795604332885219897745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8067197069555256813265163 12100795604332885219897745)
          ·
            refine ⟨9075596703249663914923309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12100795604332885219897745 9075596703249663914923309)
            ·
              refine ⟨3403348763718623968096241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9075596703249663914923309 3403348763718623968096241)
              ·
                refine ⟨2552511572788967976072181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3403348763718623968096241 2552511572788967976072181)
                ·
                  refine ⟨239297959948965747756767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2552511572788967976072181 239297959948965747756767)
                  ·
                    rfl

theorem cell20_524285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_524285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524285 prefixEnd_524285 := by exact prefixLift 524285
  have htrace : WordTrace (prefixWord ++ tailWord_524285) baseStart_524285 baseEnd_524285 := by
    simpa [prefixWord, tailWord_524285, baseEnd_524285] using wordTrace_append hprefix tailTrace_524285
  have hstable : (prefixWord ++ tailWord_524285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524285).length < 2 ^ (prefixWord ++ tailWord_524285).sum := by decide
  have hdescent : baseEnd_524285 < baseStart_524285 := by decide
  rcases family_descends (prefixWord ++ tailWord_524285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524301 : List Nat := [1, 7, 1, 2, 1, 2, 1, 1, 4]
def baseStart_524301 : Nat := 118140960795 + 524301 * 2 ^ 59
def prefixEnd_524301 : Nat := 4983230072969 + 3 ^ 40 * 524301 * 2
def baseEnd_524301 : Nat := 239305262784940803223369

theorem tailTrace_524301 : CollatzResearch.WordTrace tailWord_524301 prefixEnd_524301 239305262784940803223369 := by
  unfold tailWord_524301
  simp only [CollatzResearch.WordTrace]
  refine ⟨19122828473554495326988757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12748552315702996884659171 19122828473554495326988757)
  ·
    refine ⟨448191292348933484226299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 19122828473554495326988757 448191292348933484226299)
    ·
      refine ⟨672286938523400226339449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448191292348933484226299 672286938523400226339449)
      ·
        refine ⟨504215203892550169754587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672286938523400226339449 504215203892550169754587)
        ·
          refine ⟨756322805838825254631881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504215203892550169754587 756322805838825254631881)
          ·
            refine ⟨567242104379118940973911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 756322805838825254631881 567242104379118940973911)
            ·
              refine ⟨850863156568678411460867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567242104379118940973911 850863156568678411460867)
              ·
                refine ⟨1276294734853017617191301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850863156568678411460867 1276294734853017617191301)
                ·
                  refine ⟨239305262784940803223369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1276294734853017617191301 239305262784940803223369)
                  ·
                    rfl

theorem cell20_524301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_524301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524301 prefixEnd_524301 := by exact prefixLift 524301
  have htrace : WordTrace (prefixWord ++ tailWord_524301) baseStart_524301 baseEnd_524301 := by
    simpa [prefixWord, tailWord_524301, baseEnd_524301] using wordTrace_append hprefix tailTrace_524301
  have hstable : (prefixWord ++ tailWord_524301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524301).length < 2 ^ (prefixWord ++ tailWord_524301).sum := by decide
  have hdescent : baseEnd_524301 < baseStart_524301 := by decide
  rcases family_descends (prefixWord ++ tailWord_524301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524302 : List Nat := [4, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_524302 : Nat := 118140960795 + 524302 * 2 ^ 59
def prefixEnd_524302 : Nat := 4983230072969 + 3 ^ 40 * 524302 * 2
def baseEnd_524302 : Nat := 239305719212189244190031

theorem tailTrace_524302 : CollatzResearch.WordTrace tailWord_524302 prefixEnd_524302 239305719212189244190031 := by
  unfold tailWord_524302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2390358118318859062221895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12748576631033914998516773 2390358118318859062221895)
  ·
    refine ⟨3585537177478288593332843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2390358118318859062221895 3585537177478288593332843)
    ·
      refine ⟨5378305766217432889999265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3585537177478288593332843 5378305766217432889999265)
      ·
        refine ⟨4033729324663074667499449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5378305766217432889999265 4033729324663074667499449)
        ·
          refine ⟨3025296993497306000624587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4033729324663074667499449 3025296993497306000624587)
          ·
            refine ⟨4537945490245959000936881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3025296993497306000624587 4537945490245959000936881)
            ·
              refine ⟨3403459117684469250702661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4537945490245959000936881 3403459117684469250702661)
              ·
                refine ⟨638148584565837984506749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3403459117684469250702661 638148584565837984506749)
                ·
                  refine ⟨239305719212189244190031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 638148584565837984506749 239305719212189244190031)
                  ·
                    rfl

theorem cell20_524302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_524302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524302 prefixEnd_524302 := by exact prefixLift 524302
  have htrace : WordTrace (prefixWord ++ tailWord_524302) baseStart_524302 baseEnd_524302 := by
    simpa [prefixWord, tailWord_524302, baseEnd_524302] using wordTrace_append hprefix tailTrace_524302
  have hstable : (prefixWord ++ tailWord_524302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524302).length < 2 ^ (prefixWord ++ tailWord_524302).sum := by decide
  have hdescent : baseEnd_524302 < baseStart_524302 := by decide
  rcases family_descends (prefixWord ++ tailWord_524302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524316 : List Nat := [2, 2, 3, 1, 3, 1, 1, 7]
def baseStart_524316 : Nat := 118140960795 + 524316 * 2 ^ 59
def prefixEnd_524316 : Nat := 4983230072969 + 3 ^ 40 * 524316 * 2
def baseEnd_524316 : Nat := 79770703064555805907769

theorem tailTrace_524316 : CollatzResearch.WordTrace tailWord_524316 prefixEnd_524316 79770703064555805907769 := by
  unfold tailWord_524316
  simp only [CollatzResearch.WordTrace]
  refine ⟨9561687784250076444392401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12748917045666768592523201 9561687784250076444392401)
  ·
    refine ⟨7171265838187557333294301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9561687784250076444392401 7171265838187557333294301)
    ·
      refine ⟨2689224689320333999985363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7171265838187557333294301 2689224689320333999985363)
      ·
        refine ⟨4033837033980500999978045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2689224689320333999985363 4033837033980500999978045)
        ·
          refine ⟨1512688887742687874991767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4033837033980500999978045 1512688887742687874991767)
          ·
            refine ⟨2269033331614031812487651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1512688887742687874991767 2269033331614031812487651)
            ·
              refine ⟨3403549997421047718731477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2269033331614031812487651 3403549997421047718731477)
              ·
                refine ⟨79770703064555805907769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3403549997421047718731477 79770703064555805907769)
                ·
                  rfl

theorem cell20_524316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_524316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524316 prefixEnd_524316 := by exact prefixLift 524316
  have htrace : WordTrace (prefixWord ++ tailWord_524316) baseStart_524316 baseEnd_524316 := by
    simpa [prefixWord, tailWord_524316, baseEnd_524316] using wordTrace_append hprefix tailTrace_524316
  have hstable : (prefixWord ++ tailWord_524316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524316).length < 2 ^ (prefixWord ++ tailWord_524316).sum := by decide
  have hdescent : baseEnd_524316 < baseStart_524316 := by decide
  rcases family_descends (prefixWord ++ tailWord_524316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524374 : List Nat := [5, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_524374 : Nat := 118140960795 + 524374 * 2 ^ 59
def prefixEnd_524374 : Nat := 4983230072969 + 3 ^ 40 * 524374 * 2
def baseEnd_524374 : Nat := 239338581974076993789737

theorem tailTrace_524374 : CollatzResearch.WordTrace tailWord_524374 prefixEnd_524374 239338581974076993789737 := by
  unfold tailWord_524374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1195343187643126799649761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12750327334860019196264117 1195343187643126799649761)
  ·
    refine ⟨896507390732345099737321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1195343187643126799649761 896507390732345099737321)
    ·
      refine ⟨672380543049258824802991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 896507390732345099737321 672380543049258824802991)
      ·
        refine ⟨1008570814573888237204487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672380543049258824802991 1008570814573888237204487)
        ·
          refine ⟨1512856221860832355806731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008570814573888237204487 1512856221860832355806731)
          ·
            refine ⟨2269284332791248533710097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1512856221860832355806731 2269284332791248533710097)
            ·
              refine ⟨1701963249593436400282573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2269284332791248533710097 1701963249593436400282573)
              ·
                refine ⟨638236218597538650105965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1701963249593436400282573 638236218597538650105965)
                ·
                  refine ⟨239338581974076993789737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 638236218597538650105965 239338581974076993789737)
                  ·
                    rfl

theorem cell20_524374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_524374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524374 prefixEnd_524374 := by exact prefixLift 524374
  have htrace : WordTrace (prefixWord ++ tailWord_524374) baseStart_524374 baseEnd_524374 := by
    simpa [prefixWord, tailWord_524374, baseEnd_524374] using wordTrace_append hprefix tailTrace_524374
  have hstable : (prefixWord ++ tailWord_524374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524374).length < 2 ^ (prefixWord ++ tailWord_524374).sum := by decide
  have hdescent : baseEnd_524374 < baseStart_524374 := by decide
  rcases family_descends (prefixWord ++ tailWord_524374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524402 : List Nat := [3, 2, 1, 2, 2, 2, 1, 5, 2]
def baseStart_524402 : Nat := 118140960795 + 524402 * 2 ^ 59
def prefixEnd_524402 : Nat := 4983230072969 + 3 ^ 40 * 524402 * 2
def baseEnd_524402 : Nat := 239351361937033340856289

theorem tailTrace_524402 : CollatzResearch.WordTrace tailWord_524402 prefixEnd_524402 239351361937033340856289 := by
  unfold tailWord_524402
  simp only [CollatzResearch.WordTrace]
  refine ⟨4781628061547147394103865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12751008164125726384276973 4781628061547147394103865)
  ·
    refine ⟨3586221046160360545577899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4781628061547147394103865 3586221046160360545577899)
    ·
      refine ⟨5379331569240540818366849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3586221046160360545577899 5379331569240540818366849)
      ·
        refine ⟨4034498676930405613775137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5379331569240540818366849 4034498676930405613775137)
        ·
          refine ⟨3025874007697804210331353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4034498676930405613775137 3025874007697804210331353)
          ·
            refine ⟨2269405505773353157748515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3025874007697804210331353 2269405505773353157748515)
            ·
              refine ⟨3404108258660029736622773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2269405505773353157748515 3404108258660029736622773)
              ·
                refine ⟨319135149249377787808385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3404108258660029736622773 319135149249377787808385)
                ·
                  refine ⟨239351361937033340856289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319135149249377787808385 239351361937033340856289)
                  ·
                    rfl

theorem cell20_524402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_524402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524402 prefixEnd_524402 := by exact prefixLift 524402
  have htrace : WordTrace (prefixWord ++ tailWord_524402) baseStart_524402 baseEnd_524402 := by
    simpa [prefixWord, tailWord_524402, baseEnd_524402] using wordTrace_append hprefix tailTrace_524402
  have hstable : (prefixWord ++ tailWord_524402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524402).length < 2 ^ (prefixWord ++ tailWord_524402).sum := by decide
  have hdescent : baseEnd_524402 < baseStart_524402 := by decide
  rcases family_descends (prefixWord ++ tailWord_524402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524447 : List Nat := [1, 1, 2, 6, 1, 1, 4, 4]
def baseStart_524447 : Nat := 118140960795 + 524447 * 2 ^ 59
def prefixEnd_524447 : Nat := 4983230072969 + 3 ^ 40 * 524447 * 2
def baseEnd_524447 : Nat := 79790633721071061452035

theorem tailTrace_524447 : CollatzResearch.WordTrace tailWord_524447 prefixEnd_524447 79790633721071061452035 := by
  unfold tailWord_524447
  simp only [CollatzResearch.WordTrace]
  refine ⟨19128153531025562261803595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12752102354017041507869063 19128153531025562261803595)
  ·
    refine ⟨28692230296538343392705393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19128153531025562261803595 28692230296538343392705393)
    ·
      refine ⟨21519172722403757544529045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28692230296538343392705393 21519172722403757544529045)
      ·
        refine ⟨1008711221362676134899799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21519172722403757544529045 1008711221362676134899799)
        ·
          refine ⟨1513066832044014202349699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008711221362676134899799 1513066832044014202349699)
          ·
            refine ⟨2269600248066021303524549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513066832044014202349699 2269600248066021303524549)
            ·
              refine ⟨425550046512378994410853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2269600248066021303524549 425550046512378994410853)
              ·
                refine ⟨79790633721071061452035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 425550046512378994410853 79790633721071061452035)
                ·
                  rfl

theorem cell20_524447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 4].length) (baseStart_524447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524447 prefixEnd_524447 := by exact prefixLift 524447
  have htrace : WordTrace (prefixWord ++ tailWord_524447) baseStart_524447 baseEnd_524447 := by
    simpa [prefixWord, tailWord_524447, baseEnd_524447] using wordTrace_append hprefix tailTrace_524447
  have hstable : (prefixWord ++ tailWord_524447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524447).length < 2 ^ (prefixWord ++ tailWord_524447).sum := by decide
  have hdescent : baseEnd_524447 < baseStart_524447 := by decide
  rcases family_descends (prefixWord ++ tailWord_524447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524475 : List Nat := [1, 1, 1, 1, 1, 2, 6, 4, 3]
def baseStart_524475 : Nat := 118140960795 + 524475 * 2 ^ 59
def prefixEnd_524475 : Nat := 4983230072969 + 3 ^ 40 * 524475 * 2
def baseEnd_524475 : Nat := 239384681126169531422657

theorem tailTrace_524475 : CollatzResearch.WordTrace tailWord_524475 prefixEnd_524475 239384681126169531422657 := by
  unfold tailWord_524475
  simp only [CollatzResearch.WordTrace]
  refine ⟨19129174774924123043822879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12752783183282748695881919 19129174774924123043822879)
  ·
    refine ⟨28693762162386184565734319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19129174774924123043822879 28693762162386184565734319)
    ·
      refine ⟨43040643243579276848601479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28693762162386184565734319 43040643243579276848601479)
      ·
        refine ⟨64560964865368915272902219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43040643243579276848601479 64560964865368915272902219)
        ·
          refine ⟨96841447298053372909353329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64560964865368915272902219 96841447298053372909353329)
          ·
            refine ⟨72631085473540029682014997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96841447298053372909353329 72631085473540029682014997)
            ·
              refine ⟨3404582131572188891344453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72631085473540029682014997 3404582131572188891344453)
              ·
                refine ⟨638359149669785417127085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3404582131572188891344453 638359149669785417127085)
                ·
                  refine ⟨239384681126169531422657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 638359149669785417127085 239384681126169531422657)
                  ·
                    rfl

theorem cell20_524475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 3].length) (baseStart_524475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524475 prefixEnd_524475 := by exact prefixLift 524475
  have htrace : WordTrace (prefixWord ++ tailWord_524475) baseStart_524475 baseEnd_524475 := by
    simpa [prefixWord, tailWord_524475, baseEnd_524475] using wordTrace_append hprefix tailTrace_524475
  have hstable : (prefixWord ++ tailWord_524475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524475).length < 2 ^ (prefixWord ++ tailWord_524475).sum := by decide
  have hdescent : baseEnd_524475 < baseStart_524475 := by decide
  rcases family_descends (prefixWord ++ tailWord_524475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524527 : List Nat := [1, 1, 2, 1, 6, 9]
def baseStart_524527 : Nat := 118140960795 + 524527 * 2 ^ 59
def prefixEnd_524527 : Nat := 4983230072969 + 3 ^ 40 * 524527 * 2
def baseEnd_524527 : Nat := 8866978346040313395893

theorem tailTrace_524527 : CollatzResearch.WordTrace tailWord_524527 prefixEnd_524527 8866978346040313395893 := by
  unfold tailWord_524527
  simp only [CollatzResearch.WordTrace]
  refine ⟨19131071370735735924715835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12754047580490490616477223 19131071370735735924715835)
  ·
    refine ⟨28696607056103603887073753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19131071370735735924715835 28696607056103603887073753)
    ·
      refine ⟨21522455292077702915305315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28696607056103603887073753 21522455292077702915305315)
      ·
        refine ⟨32283682938116554372957973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21522455292077702915305315 32283682938116554372957973)
        ·
          refine ⟨1513297637724213486232405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32283682938116554372957973 1513297637724213486232405)
          ·
            refine ⟨8866978346040313395893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1513297637724213486232405 8866978346040313395893)
            ·
              rfl

theorem cell20_524527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 9].length) (baseStart_524527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524527 prefixEnd_524527 := by exact prefixLift 524527
  have htrace : WordTrace (prefixWord ++ tailWord_524527) baseStart_524527 baseEnd_524527 := by
    simpa [prefixWord, tailWord_524527, baseEnd_524527] using wordTrace_append hprefix tailTrace_524527
  have hstable : (prefixWord ++ tailWord_524527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524527).length < 2 ^ (prefixWord ++ tailWord_524527).sum := by decide
  have hdescent : baseEnd_524527 < baseStart_524527 := by decide
  rcases family_descends (prefixWord ++ tailWord_524527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524530 : List Nat := [3, 2, 1, 3, 2, 1, 1, 4, 3]
def baseStart_524530 : Nat := 118140960795 + 524530 * 2 ^ 59
def prefixEnd_524530 : Nat := 4983230072969 + 3 ^ 40 * 524530 * 2
def baseEnd_524530 : Nat := 239409784624833784589099

theorem tailTrace_524530 : CollatzResearch.WordTrace tailWord_524530 prefixEnd_524530 239409784624833784589099 := by
  unfold tailWord_524530
  simp only [CollatzResearch.WordTrace]
  refine ⟨4782795197431216859268761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12754120526483244958050029 4782795197431216859268761)
  ·
    refine ⟨3587096398073412644451571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4782795197431216859268761 3587096398073412644451571)
    ·
      refine ⟨5380644597110118966677357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3587096398073412644451571 5380644597110118966677357)
      ·
        refine ⟨2017741723916294612504009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5380644597110118966677357 2017741723916294612504009)
        ·
          refine ⟨1513306292937220959378007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2017741723916294612504009 1513306292937220959378007)
          ·
            refine ⟨2269959439405831439067011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513306292937220959378007 2269959439405831439067011)
            ·
              refine ⟨3404939159108747158600517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2269959439405831439067011 3404939159108747158600517)
              ·
                refine ⟨638426092332890092237597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3404939159108747158600517 638426092332890092237597)
                ·
                  refine ⟨239409784624833784589099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 638426092332890092237597 239409784624833784589099)
                  ·
                    rfl

theorem cell20_524530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_524530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524530 prefixEnd_524530 := by exact prefixLift 524530
  have htrace : WordTrace (prefixWord ++ tailWord_524530) baseStart_524530 baseEnd_524530 := by
    simpa [prefixWord, tailWord_524530, baseEnd_524530] using wordTrace_append hprefix tailTrace_524530
  have hstable : (prefixWord ++ tailWord_524530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524530).length < 2 ^ (prefixWord ++ tailWord_524530).sum := by decide
  have hdescent : baseEnd_524530 < baseStart_524530 := by decide
  rcases family_descends (prefixWord ++ tailWord_524530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524565 : List Nat := [1, 3, 2, 1, 2, 1, 2, 8]
def baseStart_524565 : Nat := 118140960795 + 524565 * 2 ^ 59
def prefixEnd_524565 : Nat := 4983230072969 + 3 ^ 40 * 524565 * 2
def baseEnd_524565 : Nat := 79808586526176406140763

theorem tailTrace_524565 : CollatzResearch.WordTrace tailWord_524565 prefixEnd_524565 79808586526176406140763 := by
  unfold tailWord_524565
  simp only [CollatzResearch.WordTrace]
  refine ⟨19132457344598068414599149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12754971563065378943066099 19132457344598068414599149)
  ·
    refine ⟨7174671504224275655474681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19132457344598068414599149 7174671504224275655474681)
    ·
      refine ⟨5381003628168206741606011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7174671504224275655474681 5381003628168206741606011)
      ·
        refine ⟨8071505442252310112409017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5381003628168206741606011 8071505442252310112409017)
        ·
          refine ⟨6053629081689232584306763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8071505442252310112409017 6053629081689232584306763)
          ·
            refine ⟨9080443622533848876460145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6053629081689232584306763 9080443622533848876460145)
            ·
              refine ⟨6810332716900386657345109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9080443622533848876460145 6810332716900386657345109)
              ·
                refine ⟨79808586526176406140763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6810332716900386657345109 79808586526176406140763)
                ·
                  rfl

theorem cell20_524565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 8].length) (baseStart_524565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524565 prefixEnd_524565 := by exact prefixLift 524565
  have htrace : WordTrace (prefixWord ++ tailWord_524565) baseStart_524565 baseEnd_524565 := by
    simpa [prefixWord, tailWord_524565, baseEnd_524565] using wordTrace_append hprefix tailTrace_524565
  have hstable : (prefixWord ++ tailWord_524565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524565).length < 2 ^ (prefixWord ++ tailWord_524565).sum := by decide
  have hdescent : baseEnd_524565 < baseStart_524565 := by decide
  rcases family_descends (prefixWord ++ tailWord_524565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524647 : List Nat := [1, 1, 5, 1, 3, 2, 3, 2, 2]
def baseStart_524647 : Nat := 118140960795 + 524647 * 2 ^ 59
def prefixEnd_524647 : Nat := 4983230072969 + 3 ^ 40 * 524647 * 2
def baseEnd_524647 : Nat := 239463186612901377688621

theorem tailTrace_524647 : CollatzResearch.WordTrace tailWord_524647 prefixEnd_524647 239463186612901377688621 := by
  unfold tailWord_524647
  simp only [CollatzResearch.WordTrace]
  refine ⟨19135448130300996419084195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12756965420200664279389463 19135448130300996419084195)
  ·
    refine ⟨28703172195451494628626293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19135448130300996419084195 28703172195451494628626293)
    ·
      refine ⟨2690922393323577621433715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28703172195451494628626293 2690922393323577621433715)
      ·
        refine ⟨4036383589985366432150573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2690922393323577621433715 4036383589985366432150573)
        ·
          refine ⟨1513643846244512412056465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4036383589985366432150573 1513643846244512412056465)
          ·
            refine ⟨1135232884683384309042349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1513643846244512412056465 1135232884683384309042349)
            ·
              refine ⟨425712331756269115890881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1135232884683384309042349 425712331756269115890881)
              ·
                refine ⟨319284248817201836918161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 425712331756269115890881 319284248817201836918161)
                ·
                  refine ⟨239463186612901377688621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319284248817201836918161 239463186612901377688621)
                  ·
                    rfl

theorem cell20_524647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 2].length) (baseStart_524647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524647 prefixEnd_524647 := by exact prefixLift 524647
  have htrace : WordTrace (prefixWord ++ tailWord_524647) baseStart_524647 baseEnd_524647 := by
    simpa [prefixWord, tailWord_524647, baseEnd_524647] using wordTrace_append hprefix tailTrace_524647
  have hstable : (prefixWord ++ tailWord_524647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524647).length < 2 ^ (prefixWord ++ tailWord_524647).sum := by decide
  have hdescent : baseEnd_524647 < baseStart_524647 := by decide
  rcases family_descends (prefixWord ++ tailWord_524647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524658 : List Nat := [3, 2, 1, 2, 1, 4, 2, 5]
def baseStart_524658 : Nat := 118140960795 + 524658 * 2 ^ 59
def prefixEnd_524658 : Nat := 4983230072969 + 3 ^ 40 * 524658 * 2
def baseEnd_524658 : Nat := 79822735770878076107303

theorem tailTrace_524658 : CollatzResearch.WordTrace tailWord_524658 prefixEnd_524658 79822735770878076107303 := by
  unfold tailWord_524658
  simp only [CollatzResearch.WordTrace]
  refine ⟨4783962333315286324433657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12757232888840763531823085 4783962333315286324433657)
  ·
    refine ⟨3587971749986464743325243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4783962333315286324433657 3587971749986464743325243)
    ·
      refine ⟨5381957624979697114987865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3587971749986464743325243 5381957624979697114987865)
      ·
        refine ⟨4036468218734772836240899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5381957624979697114987865 4036468218734772836240899)
        ·
          refine ⟨6054702328102159254361349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4036468218734772836240899 6054702328102159254361349)
          ·
            refine ⟨1135256686519154860192753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6054702328102159254361349 1135256686519154860192753)
            ·
              refine ⟨851442514889366145144565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1135256686519154860192753 851442514889366145144565)
              ·
                refine ⟨79822735770878076107303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 851442514889366145144565 79822735770878076107303)
                ·
                  rfl

theorem cell20_524658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_524658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524658 prefixEnd_524658 := by exact prefixLift 524658
  have htrace : WordTrace (prefixWord ++ tailWord_524658) baseStart_524658 baseEnd_524658 := by
    simpa [prefixWord, tailWord_524658, baseEnd_524658] using wordTrace_append hprefix tailTrace_524658
  have hstable : (prefixWord ++ tailWord_524658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524658).length < 2 ^ (prefixWord ++ tailWord_524658).sum := by decide
  have hdescent : baseEnd_524658 < baseStart_524658 := by decide
  rcases family_descends (prefixWord ++ tailWord_524658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524661 : List Nat := [1, 3, 4, 1, 2, 1, 4, 1, 3]
def baseStart_524661 : Nat := 118140960795 + 524661 * 2 ^ 59
def prefixEnd_524661 : Nat := 4983230072969 + 3 ^ 40 * 524661 * 2
def baseEnd_524661 : Nat := 239469576594379551221897

theorem tailTrace_524661 : CollatzResearch.WordTrace tailWord_524661 prefixEnd_524661 239469576594379551221897 := by
  unfold tailWord_524661
  simp only [CollatzResearch.WordTrace]
  refine ⟨19135958752250276810093837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12757305834833517873395891 19135958752250276810093837)
  ·
    refine ⟨7175984532093853803785189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19135958752250276810093837 7175984532093853803785189)
    ·
      refine ⟨1345497099767597588209723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7175984532093853803785189 1345497099767597588209723)
      ·
        refine ⟨2018245649651396382314585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1345497099767597588209723 2018245649651396382314585)
        ·
          refine ⟨1513684237238547286735939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2018245649651396382314585 1513684237238547286735939)
          ·
            refine ⟨2270526355857820930103909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513684237238547286735939 2270526355857820930103909)
            ·
              refine ⟨425723691723341424394483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2270526355857820930103909 425723691723341424394483)
              ·
                refine ⟨638585537585012136591725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425723691723341424394483 638585537585012136591725)
                ·
                  refine ⟨239469576594379551221897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 638585537585012136591725 239469576594379551221897)
                  ·
                    rfl

theorem cell20_524661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_524661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524661 prefixEnd_524661 := by exact prefixLift 524661
  have htrace : WordTrace (prefixWord ++ tailWord_524661) baseStart_524661 baseEnd_524661 := by
    simpa [prefixWord, tailWord_524661, baseEnd_524661] using wordTrace_append hprefix tailTrace_524661
  have hstable : (prefixWord ++ tailWord_524661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524661).length < 2 ^ (prefixWord ++ tailWord_524661).sum := by decide
  have hdescent : baseEnd_524661 < baseStart_524661 := by decide
  rcases family_descends (prefixWord ++ tailWord_524661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524679 : List Nat := [1, 1, 4, 2, 2, 1, 1, 8]
def baseStart_524679 : Nat := 118140960795 + 524679 * 2 ^ 59
def prefixEnd_524679 : Nat := 4983230072969 + 3 ^ 40 * 524679 * 2
def baseEnd_524679 : Nat := 79825930761617162873941

theorem tailTrace_524679 : CollatzResearch.WordTrace tailWord_524679 prefixEnd_524679 79825930761617162873941 := by
  unfold tailWord_524679
  simp only [CollatzResearch.WordTrace]
  refine ⟨19136615266185065884249091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12757743510790043922832727 19136615266185065884249091)
  ·
    refine ⟨28704922899277598826373637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19136615266185065884249091 28704922899277598826373637)
    ·
      refine ⟨5382173043614549779945057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28704922899277598826373637 5382173043614549779945057)
      ·
        refine ⟨4036629782710912334958793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5382173043614549779945057 4036629782710912334958793)
        ·
          refine ⟨3027472337033184251219095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4036629782710912334958793 3027472337033184251219095)
          ·
            refine ⟨4541208505549776376828643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3027472337033184251219095 4541208505549776376828643)
            ·
              refine ⟨6811812758324664565242965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4541208505549776376828643 6811812758324664565242965)
              ·
                refine ⟨79825930761617162873941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6811812758324664565242965 79825930761617162873941)
                ·
                  rfl

theorem cell20_524679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 8].length) (baseStart_524679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524679 prefixEnd_524679 := by exact prefixLift 524679
  have htrace : WordTrace (prefixWord ++ tailWord_524679) baseStart_524679 baseEnd_524679 := by
    simpa [prefixWord, tailWord_524679, baseEnd_524679] using wordTrace_append hprefix tailTrace_524679
  have hstable : (prefixWord ++ tailWord_524679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524679).length < 2 ^ (prefixWord ++ tailWord_524679).sum := by decide
  have hdescent : baseEnd_524679 < baseStart_524679 := by decide
  rcases family_descends (prefixWord ++ tailWord_524679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524702 : List Nat := [4, 3, 1, 2, 1, 1, 4, 2, 2]
def baseStart_524702 : Nat := 118140960795 + 524702 * 2 ^ 59
def prefixEnd_524702 : Nat := 4983230072969 + 3 ^ 40 * 524702 * 2
def baseEnd_524702 : Nat := 239488290111565630855063

theorem tailTrace_524702 : CollatzResearch.WordTrace tailWord_524702 prefixEnd_524702 239488290111565630855063 := by
  unfold tailWord_524702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2392181768137717601542045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12758302763401160541557573 2392181768137717601542045)
  ·
    refine ⟨897068163051644100578267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2392181768137717601542045 897068163051644100578267)
    ·
      refine ⟨1345602244577466150867401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 897068163051644100578267 1345602244577466150867401)
      ·
        refine ⟨1009201683433099613150551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1345602244577466150867401 1009201683433099613150551)
        ·
          refine ⟨1513802525149649419725827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009201683433099613150551 1513802525149649419725827)
          ·
            refine ⟨2270703787724474129588741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513802525149649419725827 2270703787724474129588741)
            ·
              refine ⟨425756960198338899297889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2270703787724474129588741 425756960198338899297889)
              ·
                refine ⟨319317720148754174473417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 425756960198338899297889 319317720148754174473417)
                ·
                  refine ⟨239488290111565630855063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319317720148754174473417 239488290111565630855063)
                  ·
                    rfl

theorem cell20_524702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_524702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524702 prefixEnd_524702 := by exact prefixLift 524702
  have htrace : WordTrace (prefixWord ++ tailWord_524702) baseStart_524702 baseEnd_524702 := by
    simpa [prefixWord, tailWord_524702, baseEnd_524702] using wordTrace_append hprefix tailTrace_524702
  have hstable : (prefixWord ++ tailWord_524702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524702).length < 2 ^ (prefixWord ++ tailWord_524702).sum := by decide
  have hdescent : baseEnd_524702 < baseStart_524702 := by decide
  rcases family_descends (prefixWord ++ tailWord_524702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524706 : List Nat := [3, 3, 1, 2, 1, 1, 3, 4, 2]
def baseStart_524706 : Nat := 118140960795 + 524706 * 2 ^ 59
def prefixEnd_524706 : Nat := 4983230072969 + 3 ^ 40 * 524706 * 2
def baseEnd_524706 : Nat := 239490115820559394721713

theorem tailTrace_524706 : CollatzResearch.WordTrace tailWord_524706 prefixEnd_524706 239490115820559394721713 := by
  unfold tailWord_524706
  simp only [CollatzResearch.WordTrace]
  refine ⟨4784400009271812373870493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12758400024724832996987981 4784400009271812373870493)
  ·
    refine ⟨1794150003476929640201435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4784400009271812373870493 1794150003476929640201435)
    ·
      refine ⟨2691225005215394460302153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1794150003476929640201435 2691225005215394460302153)
      ·
        refine ⟨2018418753911545845226615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2691225005215394460302153 2018418753911545845226615)
        ·
          refine ⟨3027628130867318767839923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2018418753911545845226615 3027628130867318767839923)
          ·
            refine ⟨4541442196300978151759885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3027628130867318767839923 4541442196300978151759885)
            ·
              refine ⟨1703040823612866806909957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4541442196300978151759885 1703040823612866806909957)
              ·
                refine ⟨319320154427412526295617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1703040823612866806909957 319320154427412526295617)
                ·
                  refine ⟨239490115820559394721713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319320154427412526295617 239490115820559394721713)
                  ·
                    rfl

theorem cell20_524706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_524706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524706 prefixEnd_524706 := by exact prefixLift 524706
  have htrace : WordTrace (prefixWord ++ tailWord_524706) baseStart_524706 baseEnd_524706 := by
    simpa [prefixWord, tailWord_524706, baseEnd_524706] using wordTrace_append hprefix tailTrace_524706
  have hstable : (prefixWord ++ tailWord_524706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524706).length < 2 ^ (prefixWord ++ tailWord_524706).sum := by decide
  have hdescent : baseEnd_524706 < baseStart_524706 := by decide
  rcases family_descends (prefixWord ++ tailWord_524706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524744 : List Nat := [2, 1, 3, 1, 3, 3, 2, 3, 2]
def baseStart_524744 : Nat := 118140960795 + 524744 * 2 ^ 59
def prefixEnd_524744 : Nat := 4983230072969 + 3 ^ 40 * 524744 * 2
def baseEnd_524744 : Nat := 239507460056000151454891

theorem tailTrace_524744 : CollatzResearch.WordTrace tailWord_524744 prefixEnd_524744 239507460056000151454891 := by
  unfold tailWord_524744
  simp only [CollatzResearch.WordTrace]
  refine ⟨9569493005474790992682643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12759324007299721323576857 9569493005474790992682643)
  ·
    refine ⟨14354239508212186489023965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9569493005474790992682643 14354239508212186489023965)
    ·
      refine ⟨5382839815579569933383987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14354239508212186489023965 5382839815579569933383987)
      ·
        refine ⟨8074259723369354900075981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5382839815579569933383987 8074259723369354900075981)
        ·
          refine ⟨3027847396263508087528493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8074259723369354900075981 3027847396263508087528493)
          ·
            refine ⟨1135442773598815532823185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3027847396263508087528493 1135442773598815532823185)
            ·
              refine ⟨851582080199111649617389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1135442773598815532823185 851582080199111649617389)
              ·
                refine ⟨319343280074666868606521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 851582080199111649617389 319343280074666868606521)
                ·
                  refine ⟨239507460056000151454891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319343280074666868606521 239507460056000151454891)
                  ·
                    rfl

theorem cell20_524744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 2].length) (baseStart_524744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524744 prefixEnd_524744 := by exact prefixLift 524744
  have htrace : WordTrace (prefixWord ++ tailWord_524744) baseStart_524744 baseEnd_524744 := by
    simpa [prefixWord, tailWord_524744, baseEnd_524744] using wordTrace_append hprefix tailTrace_524744
  have hstable : (prefixWord ++ tailWord_524744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524744).length < 2 ^ (prefixWord ++ tailWord_524744).sum := by decide
  have hdescent : baseEnd_524744 < baseStart_524744 := by decide
  rcases family_descends (prefixWord ++ tailWord_524744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524754 : List Nat := [3, 2, 2, 4, 1, 2, 1, 2, 3]
def baseStart_524754 : Nat := 118140960795 + 524754 * 2 ^ 59
def prefixEnd_524754 : Nat := 4983230072969 + 3 ^ 40 * 524754 * 2
def baseEnd_524754 : Nat := 239512024328484561121517

theorem tailTrace_524754 : CollatzResearch.WordTrace tailWord_524754 prefixEnd_524754 239512024328484561121517 := by
  unfold tailWord_524754
  simp only [CollatzResearch.WordTrace]
  refine ⟨4784837685228338423307329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12759567160608902462152877 4784837685228338423307329)
  ·
    refine ⟨3588628263921253817480497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4784837685228338423307329 3588628263921253817480497)
    ·
      refine ⟨2691471197940940363110373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3588628263921253817480497 2691471197940940363110373)
      ·
        refine ⟨504650849613926318083195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2691471197940940363110373 504650849613926318083195)
        ·
          refine ⟨756976274420889477124793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504650849613926318083195 756976274420889477124793)
          ·
            refine ⟨567732205815667107843595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 756976274420889477124793 567732205815667107843595)
            ·
              refine ⟨851598308723500661765393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567732205815667107843595 851598308723500661765393)
              ·
                refine ⟨638698731542625496324045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 851598308723500661765393 638698731542625496324045)
                ·
                  refine ⟨239512024328484561121517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 638698731542625496324045 239512024328484561121517)
                  ·
                    rfl

theorem cell20_524754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_524754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524754 prefixEnd_524754 := by exact prefixLift 524754
  have htrace : WordTrace (prefixWord ++ tailWord_524754) baseStart_524754 baseEnd_524754 := by
    simpa [prefixWord, tailWord_524754, baseEnd_524754] using wordTrace_append hprefix tailTrace_524754
  have hstable : (prefixWord ++ tailWord_524754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524754).length < 2 ^ (prefixWord ++ tailWord_524754).sum := by decide
  have hdescent : baseEnd_524754 < baseStart_524754 := by decide
  rcases family_descends (prefixWord ++ tailWord_524754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524758 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_524758 : Nat := 118140960795 + 524758 * 2 ^ 59
def prefixEnd_524758 : Nat := 4983230072969 + 3 ^ 40 * 524758 * 2
def baseEnd_524758 : Nat := 239513850037478324988167

theorem tailTrace_524758 : CollatzResearch.WordTrace tailWord_524758 prefixEnd_524758 239513850037478324988167 := by
  unfold tailWord_524758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1196218539556178898523433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12759664421932574917583285 1196218539556178898523433)
  ·
    refine ⟨897163904667134173892575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1196218539556178898523433 897163904667134173892575)
    ·
      refine ⟨1345745857000701260838863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 897163904667134173892575 1345745857000701260838863)
      ·
        refine ⟨2018618785501051891258295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1345745857000701260838863 2018618785501051891258295)
        ·
          refine ⟨3027928178251577836887443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2018618785501051891258295 3027928178251577836887443)
          ·
            refine ⟨4541892267377366755331165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3027928178251577836887443 4541892267377366755331165)
            ·
              refine ⟨1703209600266512533249187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4541892267377366755331165 1703209600266512533249187)
              ·
                refine ⟨2554814400399768799873781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1703209600266512533249187 2554814400399768799873781)
                ·
                  refine ⟨239513850037478324988167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2554814400399768799873781 239513850037478324988167)
                  ·
                    rfl

theorem cell20_524758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_524758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524758 prefixEnd_524758 := by exact prefixLift 524758
  have htrace : WordTrace (prefixWord ++ tailWord_524758) baseStart_524758 baseEnd_524758 := by
    simpa [prefixWord, tailWord_524758, baseEnd_524758] using wordTrace_append hprefix tailTrace_524758
  have hstable : (prefixWord ++ tailWord_524758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524758).length < 2 ^ (prefixWord ++ tailWord_524758).sum := by decide
  have hdescent : baseEnd_524758 < baseStart_524758 := by decide
  rcases family_descends (prefixWord ++ tailWord_524758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524765 : List Nat := [1, 4, 3, 1, 1, 1, 4, 1, 4]
def baseStart_524765 : Nat := 118140960795 + 524765 * 2 ^ 59
def prefixEnd_524765 : Nat := 4983230072969 + 3 ^ 40 * 524765 * 2
def baseEnd_524765 : Nat := 239517045028217411754805

theorem tailTrace_524765 : CollatzResearch.WordTrace tailWord_524765 prefixEnd_524765 239517045028217411754805 := by
  unfold tailWord_524765
  simp only [CollatzResearch.WordTrace]
  refine ⟨19139751943873502571879749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12759834629249001714586499 19139751943873502571879749)
  ·
    refine ⟨3588703489476281732227453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19139751943873502571879749 3588703489476281732227453)
    ·
      refine ⟨1345763808553605649585295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3588703489476281732227453 1345763808553605649585295)
      ·
        refine ⟨2018645712830408474377943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1345763808553605649585295 2018645712830408474377943)
        ·
          refine ⟨3027968569245612711566915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2018645712830408474377943 3027968569245612711566915)
          ·
            refine ⟨4541952853868419067350373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3027968569245612711566915 4541952853868419067350373)
            ·
              refine ⟨851616160100328575128195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4541952853868419067350373 851616160100328575128195)
              ·
                refine ⟨1277424240150492862692293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851616160100328575128195 1277424240150492862692293)
                ·
                  refine ⟨239517045028217411754805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1277424240150492862692293 239517045028217411754805)
                  ·
                    rfl

theorem cell20_524765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_524765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524765 prefixEnd_524765 := by exact prefixLift 524765
  have htrace : WordTrace (prefixWord ++ tailWord_524765) baseStart_524765 baseEnd_524765 := by
    simpa [prefixWord, tailWord_524765, baseEnd_524765] using wordTrace_append hprefix tailTrace_524765
  have hstable : (prefixWord ++ tailWord_524765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524765).length < 2 ^ (prefixWord ++ tailWord_524765).sum := by decide
  have hdescent : baseEnd_524765 < baseStart_524765 := by decide
  rcases family_descends (prefixWord ++ tailWord_524765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524789 : List Nat := [1, 3, 5, 1, 2, 1, 1, 6]
def baseStart_524789 : Nat := 118140960795 + 524789 * 2 ^ 59
def prefixEnd_524789 : Nat := 4983230072969 + 3 ^ 40 * 524789 * 2
def baseEnd_524789 : Nat := 79842666427393331651569

theorem tailTrace_524789 : CollatzResearch.WordTrace tailWord_524789 prefixEnd_524789 79842666427393331651569 := by
  unfold tailWord_524789
  simp only [CollatzResearch.WordTrace]
  refine ⟨19140627295786554670753421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12760418197191036447168947 19140627295786554670753421)
  ·
    refine ⟨7177735235919958001532533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19140627295786554670753421 7177735235919958001532533)
    ·
      refine ⟨672912678367496062643675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7177735235919958001532533 672912678367496062643675)
      ·
        refine ⟨1009369017551244093965513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672912678367496062643675 1009369017551244093965513)
        ·
          refine ⟨757026763163433070474135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1009369017551244093965513 757026763163433070474135)
          ·
            refine ⟨1135540144745149605711203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757026763163433070474135 1135540144745149605711203)
            ·
              refine ⟨1703310217117724408566805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1135540144745149605711203 1703310217117724408566805)
              ·
                refine ⟨79842666427393331651569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1703310217117724408566805 79842666427393331651569)
                ·
                  rfl

theorem cell20_524789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 6].length) (baseStart_524789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524789 prefixEnd_524789 := by exact prefixLift 524789
  have htrace : WordTrace (prefixWord ++ tailWord_524789) baseStart_524789 baseEnd_524789 := by
    simpa [prefixWord, tailWord_524789, baseEnd_524789] using wordTrace_append hprefix tailTrace_524789
  have hstable : (prefixWord ++ tailWord_524789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524789).length < 2 ^ (prefixWord ++ tailWord_524789).sum := by decide
  have hdescent : baseEnd_524789 < baseStart_524789 := by decide
  rcases family_descends (prefixWord ++ tailWord_524789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524806 : List Nat := [6, 2, 1, 1, 1, 1, 8]
def baseStart_524806 : Nat := 118140960795 + 524806 * 2 ^ 59
def prefixEnd_524806 : Nat := 4983230072969 + 3 ^ 40 * 524806 * 2
def baseEnd_524806 : Nat := 26615084282822610154219

theorem tailTrace_524806 : CollatzResearch.WordTrace tailWord_524806 prefixEnd_524806 26615084282822610154219 := by
  unfold tailWord_524806
  simp only [CollatzResearch.WordTrace]
  refine ⟨598163979272655205441321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12760831557816644382748181 598163979272655205441321)
  ·
    refine ⟨448622984454491404080991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 598163979272655205441321 448622984454491404080991)
    ·
      refine ⟨672934476681737106121487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448622984454491404080991 672934476681737106121487)
      ·
        refine ⟨1009401715022605659182231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672934476681737106121487 1009401715022605659182231)
        ·
          refine ⟨1514102572533908488773347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009401715022605659182231 1514102572533908488773347)
          ·
            refine ⟨2271153858800862733160021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514102572533908488773347 2271153858800862733160021)
            ·
              refine ⟨26615084282822610154219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2271153858800862733160021 26615084282822610154219)
              ·
                rfl

theorem cell20_524806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 8].length) (baseStart_524806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524806 prefixEnd_524806 := by exact prefixLift 524806
  have htrace : WordTrace (prefixWord ++ tailWord_524806) baseStart_524806 baseEnd_524806 := by
    simpa [prefixWord, tailWord_524806, baseEnd_524806] using wordTrace_append hprefix tailTrace_524806
  have hstable : (prefixWord ++ tailWord_524806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524806).length < 2 ^ (prefixWord ++ tailWord_524806).sum := by decide
  have hdescent : baseEnd_524806 < baseStart_524806 := by decide
  rcases family_descends (prefixWord ++ tailWord_524806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524813 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 5]
def baseStart_524813 : Nat := 118140960795 + 524813 * 2 ^ 59
def prefixEnd_524813 : Nat := 4983230072969 + 3 ^ 40 * 524813 * 2
def baseEnd_524813 : Nat := 239538953536142578154609

theorem tailTrace_524813 : CollatzResearch.WordTrace tailWord_524813 prefixEnd_524813 239538953536142578154609 := by
  unfold tailWord_524813
  simp only [CollatzResearch.WordTrace]
  refine ⟨19141502647699606769627093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12761001765133071179751395 19141502647699606769627093)
  ·
    refine ⟨448628968305459533663135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 19141502647699606769627093 448628968305459533663135)
    ·
      refine ⟨672943452458189300494703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448628968305459533663135 672943452458189300494703)
      ·
        refine ⟨1009415178687283950742055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672943452458189300494703 1009415178687283950742055)
        ·
          refine ⟨1514122768030925926113083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009415178687283950742055 1514122768030925926113083)
          ·
            refine ⟨2271184152046388889169625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514122768030925926113083 2271184152046388889169625)
            ·
              refine ⟨1703388114034791666877219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2271184152046388889169625 1703388114034791666877219)
              ·
                refine ⟨2555082171052187500315829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1703388114034791666877219 2555082171052187500315829)
                ·
                  refine ⟨239538953536142578154609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2555082171052187500315829 239538953536142578154609)
                  ·
                    rfl

theorem cell20_524813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_524813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524813 prefixEnd_524813 := by exact prefixLift 524813
  have htrace : WordTrace (prefixWord ++ tailWord_524813) baseStart_524813 baseEnd_524813 := by
    simpa [prefixWord, tailWord_524813, baseEnd_524813] using wordTrace_append hprefix tailTrace_524813
  have hstable : (prefixWord ++ tailWord_524813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524813).length < 2 ^ (prefixWord ++ tailWord_524813).sum := by decide
  have hdescent : baseEnd_524813 < baseStart_524813 := by decide
  rcases family_descends (prefixWord ++ tailWord_524813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524820 : List Nat := [2, 4, 3, 1, 1, 1, 3, 1, 4]
def baseStart_524820 : Nat := 118140960795 + 524820 * 2 ^ 59
def prefixEnd_524820 : Nat := 4983230072969 + 3 ^ 40 * 524820 * 2
def baseEnd_524820 : Nat := 239542148526881664921247

theorem tailTrace_524820 : CollatzResearch.WordTrace tailWord_524820 prefixEnd_524820 239542148526881664921247 := by
  unfold tailWord_524820
  simp only [CollatzResearch.WordTrace]
  refine ⟨9570878979337123482565957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12761171972449497976754609 9570878979337123482565957)
  ·
    refine ⟨1794539808625710652981117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9570878979337123482565957 1794539808625710652981117)
    ·
      refine ⟨672952428234641494867919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1794539808625710652981117 672952428234641494867919)
      ·
        refine ⟨1009428642351962242301879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672952428234641494867919 1009428642351962242301879)
        ·
          refine ⟨1514142963527943363452819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009428642351962242301879 1514142963527943363452819)
          ·
            refine ⟨2271214445291915045179229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514142963527943363452819 2271214445291915045179229)
            ·
              refine ⟨851705416984468141942211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2271214445291915045179229 851705416984468141942211)
              ·
                refine ⟨1277558125476702212913317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851705416984468141942211 1277558125476702212913317)
                ·
                  refine ⟨239542148526881664921247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1277558125476702212913317 239542148526881664921247)
                  ·
                    rfl

theorem cell20_524820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_524820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524820 prefixEnd_524820 := by exact prefixLift 524820
  have htrace : WordTrace (prefixWord ++ tailWord_524820) baseStart_524820 baseEnd_524820 := by
    simpa [prefixWord, tailWord_524820, baseEnd_524820] using wordTrace_append hprefix tailTrace_524820
  have hstable : (prefixWord ++ tailWord_524820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524820).length < 2 ^ (prefixWord ++ tailWord_524820).sum := by decide
  have hdescent : baseEnd_524820 < baseStart_524820 := by decide
  rcases family_descends (prefixWord ++ tailWord_524820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524900 : List Nat := [2, 3, 1, 1, 2, 2, 3, 2, 4]
def baseStart_524900 : Nat := 118140960795 + 524900 * 2 ^ 59
def prefixEnd_524900 : Nat := 4983230072969 + 3 ^ 40 * 524900 * 2
def baseEnd_524900 : Nat := 239578662706756942254253

theorem tailTrace_524900 : CollatzResearch.WordTrace tailWord_524900 prefixEnd_524900 239578662706756942254253 := by
  unfold tailWord_524900
  simp only [CollatzResearch.WordTrace]
  refine ⟨9572337899192210314022077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12763117198922947085362769 9572337899192210314022077)
  ·
    refine ⟨3589626712197078867758279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9572337899192210314022077 3589626712197078867758279)
    ·
      refine ⟨5384440068295618301637419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3589626712197078867758279 5384440068295618301637419)
      ·
        refine ⟨8076660102443427452456129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5384440068295618301637419 8076660102443427452456129)
        ·
          refine ⟨6057495076832570589342097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8076660102443427452456129 6057495076832570589342097)
          ·
            refine ⟨4543121307624427942006573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6057495076832570589342097 4543121307624427942006573)
            ·
              refine ⟨1703670490359160478252465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4543121307624427942006573 1703670490359160478252465)
              ·
                refine ⟨1277752867769370358689349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1703670490359160478252465 1277752867769370358689349)
                ·
                  refine ⟨239578662706756942254253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1277752867769370358689349 239578662706756942254253)
                  ·
                    rfl

theorem cell20_524900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_524900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524900 prefixEnd_524900 := by exact prefixLift 524900
  have htrace : WordTrace (prefixWord ++ tailWord_524900) baseStart_524900 baseEnd_524900 := by
    simpa [prefixWord, tailWord_524900, baseEnd_524900] using wordTrace_append hprefix tailTrace_524900
  have hstable : (prefixWord ++ tailWord_524900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524900).length < 2 ^ (prefixWord ++ tailWord_524900).sum := by decide
  have hdescent : baseEnd_524900 < baseStart_524900 := by decide
  rcases family_descends (prefixWord ++ tailWord_524900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524930 : List Nat := [3, 4, 3, 1, 1, 1, 2, 1, 4]
def baseStart_524930 : Nat := 118140960795 + 524930 * 2 ^ 59
def prefixEnd_524930 : Nat := 4983230072969 + 3 ^ 40 * 524930 * 2
def baseEnd_524930 : Nat := 239592355524210171254131

theorem tailTrace_524930 : CollatzResearch.WordTrace tailWord_524930 prefixEnd_524930 239592355524210171254131 := by
  unfold tailWord_524930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4786442497068933937909061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12763846658850490501090829 4786442497068933937909061)
  ·
    refine ⟨897457968200425113357949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4786442497068933937909061 897457968200425113357949)
    ·
      refine ⟨336546738075159417509231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 897457968200425113357949 336546738075159417509231)
      ·
        refine ⟨504820107112739126263847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336546738075159417509231 504820107112739126263847)
        ·
          refine ⟨757230160669108689395771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504820107112739126263847 757230160669108689395771)
          ·
            refine ⟨1135845241003663034093657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757230160669108689395771 1135845241003663034093657)
            ·
              refine ⟨851883930752747275570243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1135845241003663034093657 851883930752747275570243)
              ·
                refine ⟨1277825896129120913355365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851883930752747275570243 1277825896129120913355365)
                ·
                  refine ⟨239592355524210171254131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1277825896129120913355365 239592355524210171254131)
                  ·
                    rfl

theorem cell20_524930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_524930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524930 prefixEnd_524930 := by exact prefixLift 524930
  have htrace : WordTrace (prefixWord ++ tailWord_524930) baseStart_524930 baseEnd_524930 := by
    simpa [prefixWord, tailWord_524930, baseEnd_524930] using wordTrace_append hprefix tailTrace_524930
  have hstable : (prefixWord ++ tailWord_524930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524930).length < 2 ^ (prefixWord ++ tailWord_524930).sum := by decide
  have hdescent : baseEnd_524930 < baseStart_524930 := by decide
  rcases family_descends (prefixWord ++ tailWord_524930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524931 : List Nat := [1, 1, 1, 3, 3, 1, 5, 2, 3]
def baseStart_524931 : Nat := 118140960795 + 524931 * 2 ^ 59
def prefixEnd_524931 : Nat := 4983230072969 + 3 ^ 40 * 524931 * 2
def baseEnd_524931 : Nat := 239592811951458612220793

theorem tailTrace_524931 : CollatzResearch.WordTrace tailWord_524931 prefixEnd_524931 239592811951458612220793 := by
  unfold tailWord_524931
  simp only [CollatzResearch.WordTrace]
  refine ⟨19145806461272112922422647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12763870974181408614948431 19145806461272112922422647)
  ·
    refine ⟨28718709691908169383633971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19145806461272112922422647 28718709691908169383633971)
    ·
      refine ⟨43078064537862254075450957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28718709691908169383633971 43078064537862254075450957)
      ·
        refine ⟨16154274201698345278294109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43078064537862254075450957 16154274201698345278294109)
        ·
          refine ⟨6057852825636879479360291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16154274201698345278294109 6057852825636879479360291)
          ·
            refine ⟨9086779238455319219040437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6057852825636879479360291 9086779238455319219040437)
            ·
              refine ⟨851885553605186176785041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9086779238455319219040437 851885553605186176785041)
              ·
                refine ⟨638914165203889632588781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 851885553605186176785041 638914165203889632588781)
                ·
                  refine ⟨239592811951458612220793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 638914165203889632588781 239592811951458612220793)
                  ·
                    rfl

theorem cell20_524931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 3].length) (baseStart_524931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_524931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_524931 prefixEnd_524931 := by exact prefixLift 524931
  have htrace : WordTrace (prefixWord ++ tailWord_524931) baseStart_524931 baseEnd_524931 := by
    simpa [prefixWord, tailWord_524931, baseEnd_524931] using wordTrace_append hprefix tailTrace_524931
  have hstable : (prefixWord ++ tailWord_524931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524931).length < 2 ^ (prefixWord ++ tailWord_524931).sum := by decide
  have hdescent : baseEnd_524931 < baseStart_524931 := by decide
  rcases family_descends (prefixWord ++ tailWord_524931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525044 : List Nat := [2, 6, 1, 1, 2, 1, 1, 4, 2]
def baseStart_525044 : Nat := 118140960795 + 525044 * 2 ^ 59
def prefixEnd_525044 : Nat := 4983230072969 + 3 ^ 40 * 525044 * 2
def baseEnd_525044 : Nat := 239644388230532441453665

theorem tailTrace_525044 : CollatzResearch.WordTrace tailWord_525044 prefixEnd_525044 239644388230532441453665 := by
  unfold tailWord_525044
  simp only [CollatzResearch.WordTrace]
  refine ⟨9574963954931366610643093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12766618606575155480857457 9574963954931366610643093)
  ·
    refine ⟨448826435387407809873895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9574963954931366610643093 448826435387407809873895)
    ·
      refine ⟨673239653081111714810843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448826435387407809873895 673239653081111714810843)
      ·
        refine ⟨1009859479621667572216265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673239653081111714810843 1009859479621667572216265)
        ·
          refine ⟨757394609716250679162199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1009859479621667572216265 757394609716250679162199)
          ·
            refine ⟨1136091914574376018743299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757394609716250679162199 1136091914574376018743299)
            ·
              refine ⟨1704137871861564028114949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1136091914574376018743299 1704137871861564028114949)
              ·
                refine ⟨319525850974043255271553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1704137871861564028114949 319525850974043255271553)
                ·
                  refine ⟨239644388230532441453665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319525850974043255271553 239644388230532441453665)
                  ·
                    rfl

theorem cell20_525044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_525044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525044 prefixEnd_525044 := by exact prefixLift 525044
  have htrace : WordTrace (prefixWord ++ tailWord_525044) baseStart_525044 baseEnd_525044 := by
    simpa [prefixWord, tailWord_525044, baseEnd_525044] using wordTrace_append hprefix tailTrace_525044
  have hstable : (prefixWord ++ tailWord_525044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525044).length < 2 ^ (prefixWord ++ tailWord_525044).sum := by decide
  have hdescent : baseEnd_525044 < baseStart_525044 := by decide
  rcases family_descends (prefixWord ++ tailWord_525044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525073 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 6]
def baseStart_525073 : Nat := 118140960795 + 525073 * 2 ^ 59
def prefixEnd_525073 : Nat := 4983230072969 + 3 ^ 40 * 525073 * 2
def baseEnd_525073 : Nat := 239657624620737229486879

theorem tailTrace_525073 : CollatzResearch.WordTrace tailWord_525073 prefixEnd_525073 239657624620737229486879 := by
  unfold tailWord_525073
  simp only [CollatzResearch.WordTrace]
  refine ⟨19150985626757671174091873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12767323751171780782727915 19150985626757671174091873)
  ·
    refine ⟨14363239220068253380568905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19150985626757671174091873 14363239220068253380568905)
    ·
      refine ⟨10772429415051190035426679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14363239220068253380568905 10772429415051190035426679)
      ·
        refine ⟨16158644122576785053140019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10772429415051190035426679 16158644122576785053140019)
        ·
          refine ⟨24237966183865177579710029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16158644122576785053140019 24237966183865177579710029)
          ·
            refine ⟨9089237318949441592391261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24237966183865177579710029 9089237318949441592391261)
            ·
              refine ⟨3408463994606040597146723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9089237318949441592391261 3408463994606040597146723)
              ·
                refine ⟨5112695991909060895720085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3408463994606040597146723 5112695991909060895720085)
                ·
                  refine ⟨239657624620737229486879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5112695991909060895720085 239657624620737229486879)
                  ·
                    rfl

theorem cell20_525073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_525073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525073 prefixEnd_525073 := by exact prefixLift 525073
  have htrace : WordTrace (prefixWord ++ tailWord_525073) baseStart_525073 baseEnd_525073 := by
    simpa [prefixWord, tailWord_525073, baseEnd_525073] using wordTrace_append hprefix tailTrace_525073
  have hstable : (prefixWord ++ tailWord_525073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525073).length < 2 ^ (prefixWord ++ tailWord_525073).sum := by decide
  have hdescent : baseEnd_525073 < baseStart_525073 := by decide
  rcases family_descends (prefixWord ++ tailWord_525073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525107 : List Nat := [1, 1, 1, 2, 6, 1, 2, 4, 2]
def baseStart_525107 : Nat := 118140960795 + 525107 * 2 ^ 59
def prefixEnd_525107 : Nat := 4983230072969 + 3 ^ 40 * 525107 * 2
def baseEnd_525107 : Nat := 239673143147184222353407

theorem tailTrace_525107 : CollatzResearch.WordTrace tailWord_525107 prefixEnd_525107 239673143147184222353407 := by
  unfold tailWord_525107
  simp only [CollatzResearch.WordTrace]
  refine ⟨19152225708634494980829575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12768150472422996653886383 19152225708634494980829575)
  ·
    refine ⟨28728338562951742471244363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19152225708634494980829575 28728338562951742471244363)
    ·
      refine ⟨43092507844427613706866545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28728338562951742471244363 43092507844427613706866545)
      ·
        refine ⟨32319380883320710280149909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43092507844427613706866545 32319380883320710280149909)
        ·
          refine ⟨1514970978905658294382027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32319380883320710280149909 1514970978905658294382027)
          ·
            refine ⟨2272456468358487441573041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514970978905658294382027 2272456468358487441573041)
            ·
              refine ⟨1704342351268865581179781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2272456468358487441573041 1704342351268865581179781)
              ·
                refine ⟨319564190862912296471209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1704342351268865581179781 319564190862912296471209)
                ·
                  refine ⟨239673143147184222353407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319564190862912296471209 239673143147184222353407)
                  ·
                    rfl

theorem cell20_525107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 2].length) (baseStart_525107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525107 prefixEnd_525107 := by exact prefixLift 525107
  have htrace : WordTrace (prefixWord ++ tailWord_525107) baseStart_525107 baseEnd_525107 := by
    simpa [prefixWord, tailWord_525107, baseEnd_525107] using wordTrace_append hprefix tailTrace_525107
  have hstable : (prefixWord ++ tailWord_525107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525107).length < 2 ^ (prefixWord ++ tailWord_525107).sum := by decide
  have hdescent : baseEnd_525107 < baseStart_525107 := by decide
  rcases family_descends (prefixWord ++ tailWord_525107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525117 : List Nat := [1, 4, 1, 4, 2, 1, 3, 1, 3]
def baseStart_525117 : Nat := 118140960795 + 525117 * 2 ^ 59
def prefixEnd_525117 : Nat := 4983230072969 + 3 ^ 40 * 525117 * 2
def baseEnd_525117 : Nat := 239677707419668632020033

theorem tailTrace_525117 : CollatzResearch.WordTrace tailWord_525117 prefixEnd_525117 239677707419668632020033 := by
  unfold tailWord_525117
  simp only [CollatzResearch.WordTrace]
  refine ⟨19152590438598266688693605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12768393625732177792462403 19152590438598266688693605)
  ·
    refine ⟨3591110707237175004130051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19152590438598266688693605 3591110707237175004130051)
    ·
      refine ⟨5386666060855762506195077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3591110707237175004130051 5386666060855762506195077)
      ·
        refine ⟨1009999886410455469911577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5386666060855762506195077 1009999886410455469911577)
        ·
          refine ⟨757499914807841602433683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1009999886410455469911577 757499914807841602433683)
          ·
            refine ⟨1136249872211762403650525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757499914807841602433683 1136249872211762403650525)
            ·
              refine ⟨426093702079410901368947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1136249872211762403650525 426093702079410901368947)
              ·
                refine ⟨639140553119116352053421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426093702079410901368947 639140553119116352053421)
                ·
                  refine ⟨239677707419668632020033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 639140553119116352053421 239677707419668632020033)
                  ·
                    rfl

theorem cell20_525117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_525117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525117 prefixEnd_525117 := by exact prefixLift 525117
  have htrace : WordTrace (prefixWord ++ tailWord_525117) baseStart_525117 baseEnd_525117 := by
    simpa [prefixWord, tailWord_525117, baseEnd_525117] using wordTrace_append hprefix tailTrace_525117
  have hstable : (prefixWord ++ tailWord_525117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525117).length < 2 ^ (prefixWord ++ tailWord_525117).sum := by decide
  have hdescent : baseEnd_525117 < baseStart_525117 := by decide
  rcases family_descends (prefixWord ++ tailWord_525117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525145 : List Nat := [1, 2, 1, 2, 2, 4, 3, 3, 2]
def baseStart_525145 : Nat := 118140960795 + 525145 * 2 ^ 59
def prefixEnd_525145 : Nat := 4983230072969 + 3 ^ 40 * 525145 * 2
def baseEnd_525145 : Nat := 239690487382624979086585

theorem tailTrace_525145 : CollatzResearch.WordTrace tailWord_525145 prefixEnd_525145 239690487382624979086585 := by
  unfold tailWord_525145
  simp only [CollatzResearch.WordTrace]
  refine ⟨19153611682496827470712889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12769074454997884980475259 19153611682496827470712889)
  ·
    refine ⟨14365208761872620603034667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19153611682496827470712889 14365208761872620603034667)
    ·
      refine ⟨21547813142808930904552001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14365208761872620603034667 21547813142808930904552001)
      ·
        refine ⟨16160859857106698178414001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21547813142808930904552001 16160859857106698178414001)
        ·
          refine ⟨12120644892830023633810501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16160859857106698178414001 12120644892830023633810501)
          ·
            refine ⟨2272620917405629431339469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12120644892830023633810501 2272620917405629431339469)
            ·
              refine ⟨852232844027111036752301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2272620917405629431339469 852232844027111036752301)
              ·
                refine ⟨319587316510166638782113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 852232844027111036752301 319587316510166638782113)
                ·
                  refine ⟨239690487382624979086585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319587316510166638782113 239690487382624979086585)
                  ·
                    rfl

theorem cell20_525145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 2].length) (baseStart_525145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525145 prefixEnd_525145 := by exact prefixLift 525145
  have htrace : WordTrace (prefixWord ++ tailWord_525145) baseStart_525145 baseEnd_525145 := by
    simpa [prefixWord, tailWord_525145, baseEnd_525145] using wordTrace_append hprefix tailTrace_525145
  have hstable : (prefixWord ++ tailWord_525145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525145).length < 2 ^ (prefixWord ++ tailWord_525145).sum := by decide
  have hdescent : baseEnd_525145 < baseStart_525145 := by decide
  rcases family_descends (prefixWord ++ tailWord_525145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525173 : List Nat := [1, 3, 4, 1, 1, 2, 1, 7]
def baseStart_525173 : Nat := 118140960795 + 525173 * 2 ^ 59
def prefixEnd_525173 : Nat := 4983230072969 + 3 ^ 40 * 525173 * 2
def baseEnd_525173 : Nat := 79901089115193775384379

theorem tailTrace_525173 : CollatzResearch.WordTrace tailWord_525173 prefixEnd_525173 79901089115193775384379 := by
  unfold tailWord_525173
  simp only [CollatzResearch.WordTrace]
  refine ⟨19154632926395388252732173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12769755284263592168488115 19154632926395388252732173)
  ·
    refine ⟨7182987347398270594774565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19154632926395388252732173 7182987347398270594774565)
    ·
      refine ⟨1346810127637175736520231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7182987347398270594774565 1346810127637175736520231)
      ·
        refine ⟨2020215191455763604780347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1346810127637175736520231 2020215191455763604780347)
        ·
          refine ⟨3030322787183645407170521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2020215191455763604780347 3030322787183645407170521)
          ·
            refine ⟨2272742090387734055377891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3030322787183645407170521 2272742090387734055377891)
            ·
              refine ⟨3409113135581601083066837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2272742090387734055377891 3409113135581601083066837)
              ·
                refine ⟨79901089115193775384379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3409113135581601083066837 79901089115193775384379)
                ·
                  rfl

theorem cell20_525173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 7].length) (baseStart_525173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525173 prefixEnd_525173 := by exact prefixLift 525173
  have htrace : WordTrace (prefixWord ++ tailWord_525173) baseStart_525173 baseEnd_525173 := by
    simpa [prefixWord, tailWord_525173, baseEnd_525173] using wordTrace_append hprefix tailTrace_525173
  have hstable : (prefixWord ++ tailWord_525173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525173).length < 2 ^ (prefixWord ++ tailWord_525173).sum := by decide
  have hdescent : baseEnd_525173 < baseStart_525173 := by decide
  rcases family_descends (prefixWord ++ tailWord_525173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525187 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 6]
def baseStart_525187 : Nat := 118140960795 + 525187 * 2 ^ 59
def prefixEnd_525187 : Nat := 4983230072969 + 3 ^ 40 * 525187 * 2
def baseEnd_525187 : Nat := 239709657327059499686413

theorem tailTrace_525187 : CollatzResearch.WordTrace tailWord_525187 prefixEnd_525187 239709657327059499686413 := by
  unfold tailWord_525187
  simp only [CollatzResearch.WordTrace]
  refine ⟨19155143548344668643741815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12770095698896445762494543 19155143548344668643741815)
  ·
    refine ⟨28732715322517002965612723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19155143548344668643741815 28732715322517002965612723)
    ·
      refine ⟨43099072983775504448419085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28732715322517002965612723 43099072983775504448419085)
      ·
        refine ⟨16162152368915814168157157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43099072983775504448419085 16162152368915814168157157)
        ·
          refine ⟨3030403569171715156529467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16162152368915814168157157 3030403569171715156529467)
          ·
            refine ⟨4545605353757572734794201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3030403569171715156529467 4545605353757572734794201)
            ·
              refine ⟨3409204015318179551095651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4545605353757572734794201 3409204015318179551095651)
              ·
                refine ⟨5113806022977269326643477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3409204015318179551095651 5113806022977269326643477)
                ·
                  refine ⟨239709657327059499686413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5113806022977269326643477 239709657327059499686413)
                  ·
                    rfl

theorem cell20_525187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_525187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525187 prefixEnd_525187 := by exact prefixLift 525187
  have htrace : WordTrace (prefixWord ++ tailWord_525187) baseStart_525187 baseEnd_525187 := by
    simpa [prefixWord, tailWord_525187, baseEnd_525187] using wordTrace_append hprefix tailTrace_525187
  have hstable : (prefixWord ++ tailWord_525187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525187).length < 2 ^ (prefixWord ++ tailWord_525187).sum := by decide
  have hdescent : baseEnd_525187 < baseStart_525187 := by decide
  rcases family_descends (prefixWord ++ tailWord_525187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525217 : List Nat := [1, 2, 3, 4, 1, 3, 2, 2, 2]
def baseStart_525217 : Nat := 118140960795 + 525217 * 2 ^ 59
def prefixEnd_525217 : Nat := 4983230072969 + 3 ^ 40 * 525217 * 2
def baseEnd_525217 : Nat := 239723350144512728686291

theorem tailTrace_525217 : CollatzResearch.WordTrace tailWord_525217 prefixEnd_525217 239723350144512728686291 := by
  unfold tailWord_525217
  simp only [CollatzResearch.WordTrace]
  refine ⟨19156237738235983767333905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12770825158823989178222603 19156237738235983767333905)
  ·
    refine ⟨14367178303676987825500429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19156237738235983767333905 14367178303676987825500429)
    ·
      refine ⟨5387691863878870434562661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14367178303676987825500429 5387691863878870434562661)
      ·
        refine ⟨1010192224477288206480499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5387691863878870434562661 1010192224477288206480499)
        ·
          refine ⟨1515288336715932309720749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010192224477288206480499 1515288336715932309720749)
          ·
            refine ⟨568233126268474616145281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1515288336715932309720749 568233126268474616145281)
            ·
              refine ⟨426174844701355962108961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568233126268474616145281 426174844701355962108961)
              ·
                refine ⟨319631133526016971581721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426174844701355962108961 319631133526016971581721)
                ·
                  refine ⟨239723350144512728686291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319631133526016971581721 239723350144512728686291)
                  ·
                    rfl

theorem cell20_525217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 2].length) (baseStart_525217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525217 prefixEnd_525217 := by exact prefixLift 525217
  have htrace : WordTrace (prefixWord ++ tailWord_525217) baseStart_525217 baseEnd_525217 := by
    simpa [prefixWord, tailWord_525217, baseEnd_525217] using wordTrace_append hprefix tailTrace_525217
  have hstable : (prefixWord ++ tailWord_525217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525217).length < 2 ^ (prefixWord ++ tailWord_525217).sum := by decide
  have hdescent : baseEnd_525217 < baseStart_525217 := by decide
  rcases family_descends (prefixWord ++ tailWord_525217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525225 : List Nat := [1, 2, 1, 1, 1, 1, 6, 3, 4]
def baseStart_525225 : Nat := 118140960795 + 525225 * 2 ^ 59
def prefixEnd_525225 : Nat := 4983230072969 + 3 ^ 40 * 525225 * 2
def baseEnd_525225 : Nat := 239727001562500256419591

theorem tailTrace_525225 : CollatzResearch.WordTrace tailWord_525225 prefixEnd_525225 239727001562500256419591 := by
  unfold tailWord_525225
  simp only [CollatzResearch.WordTrace]
  refine ⟨19156529522207001133625129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12771019681471334089083419 19156529522207001133625129)
  ·
    refine ⟨14367397141655250850218847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19156529522207001133625129 14367397141655250850218847)
    ·
      refine ⟨21551095712482876275328271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14367397141655250850218847 21551095712482876275328271)
      ·
        refine ⟨32326643568724314412992407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21551095712482876275328271 32326643568724314412992407)
        ·
          refine ⟨48489965353086471619488611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32326643568724314412992407 48489965353086471619488611)
          ·
            refine ⟨72734948029629707429232917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48489965353086471619488611 72734948029629707429232917)
            ·
              refine ⟨3409450688888892535745293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72734948029629707429232917 3409450688888892535745293)
              ·
                refine ⟨1278544008333334700904485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3409450688888892535745293 1278544008333334700904485)
                ·
                  refine ⟨239727001562500256419591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1278544008333334700904485 239727001562500256419591)
                  ·
                    rfl

theorem cell20_525225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_525225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525225 prefixEnd_525225 := by exact prefixLift 525225
  have htrace : WordTrace (prefixWord ++ tailWord_525225) baseStart_525225 baseEnd_525225 := by
    simpa [prefixWord, tailWord_525225, baseEnd_525225] using wordTrace_append hprefix tailTrace_525225
  have hstable : (prefixWord ++ tailWord_525225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525225).length < 2 ^ (prefixWord ++ tailWord_525225).sum := by decide
  have hdescent : baseEnd_525225 < baseStart_525225 := by decide
  rcases family_descends (prefixWord ++ tailWord_525225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525259 : List Nat := [1, 1, 1, 1, 3, 6, 2, 3, 2]
def baseStart_525259 : Nat := 118140960795 + 525259 * 2 ^ 59
def prefixEnd_525259 : Nat := 4983230072969 + 3 ^ 40 * 525259 * 2
def baseEnd_525259 : Nat := 239742520088947249286119

theorem tailTrace_525259 : CollatzResearch.WordTrace tailWord_525259 prefixEnd_525259 239742520088947249286119 := by
  unfold tailWord_525259
  simp only [CollatzResearch.WordTrace]
  refine ⟨19157769604083824940362831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12771846402722549960241887 19157769604083824940362831)
  ·
    refine ⟨28736654406125737410544247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19157769604083824940362831 28736654406125737410544247)
    ·
      refine ⟨43104981609188606115816371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28736654406125737410544247 43104981609188606115816371)
      ·
        refine ⟨64657472413782909173724557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43104981609188606115816371 64657472413782909173724557)
        ·
          refine ⟨24246552155168590940146709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64657472413782909173724557 24246552155168590940146709)
          ·
            refine ⟨1136557132273527700319377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24246552155168590940146709 1136557132273527700319377)
            ·
              refine ⟨852417849205145775239533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1136557132273527700319377 852417849205145775239533)
              ·
                refine ⟨319656693451929665714825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 852417849205145775239533 319656693451929665714825)
                ·
                  refine ⟨239742520088947249286119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319656693451929665714825 239742520088947249286119)
                  ·
                    rfl

theorem cell20_525259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 2].length) (baseStart_525259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525259 prefixEnd_525259 := by exact prefixLift 525259
  have htrace : WordTrace (prefixWord ++ tailWord_525259) baseStart_525259 baseEnd_525259 := by
    simpa [prefixWord, tailWord_525259, baseEnd_525259] using wordTrace_append hprefix tailTrace_525259
  have hstable : (prefixWord ++ tailWord_525259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525259).length < 2 ^ (prefixWord ++ tailWord_525259).sum := by decide
  have hdescent : baseEnd_525259 < baseStart_525259 := by decide
  rcases family_descends (prefixWord ++ tailWord_525259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525269 : List Nat := [1, 3, 2, 3, 4, 1, 1, 2, 3]
def baseStart_525269 : Nat := 118140960795 + 525269 * 2 ^ 59
def prefixEnd_525269 : Nat := 4983230072969 + 3 ^ 40 * 525269 * 2
def baseEnd_525269 : Nat := 239747084361431658952745

theorem tailTrace_525269 : CollatzResearch.WordTrace tailWord_525269 prefixEnd_525269 239747084361431658952745 := by
  unfold tailWord_525269
  simp only [CollatzResearch.WordTrace]
  refine ⟨19158134334047596648226861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12772089556031731098817907 19158134334047596648226861)
  ·
    refine ⟨7184300375267848743085073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19158134334047596648226861 7184300375267848743085073)
    ·
      refine ⟨5388225281450886557313805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7184300375267848743085073 5388225281450886557313805)
      ·
        refine ⟨2020584480544082458992677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5388225281450886557313805 2020584480544082458992677)
        ·
          refine ⟨378859590102015461061127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2020584480544082458992677 378859590102015461061127)
          ·
            refine ⟨568289385153023191591691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378859590102015461061127 568289385153023191591691)
            ·
              refine ⟨852434077729534787387537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568289385153023191591691 852434077729534787387537)
              ·
                refine ⟨639325558297151090540653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 852434077729534787387537 639325558297151090540653)
                ·
                  refine ⟨239747084361431658952745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 639325558297151090540653 239747084361431658952745)
                  ·
                    rfl

theorem cell20_525269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_525269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525269 prefixEnd_525269 := by exact prefixLift 525269
  have htrace : WordTrace (prefixWord ++ tailWord_525269) baseStart_525269 baseEnd_525269 := by
    simpa [prefixWord, tailWord_525269, baseEnd_525269] using wordTrace_append hprefix tailTrace_525269
  have hstable : (prefixWord ++ tailWord_525269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525269).length < 2 ^ (prefixWord ++ tailWord_525269).sum := by decide
  have hdescent : baseEnd_525269 < baseStart_525269 := by decide
  rcases family_descends (prefixWord ++ tailWord_525269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525273 : List Nat := [1, 2, 1, 2, 5, 1, 3, 2, 3]
def baseStart_525273 : Nat := 118140960795 + 525273 * 2 ^ 59
def prefixEnd_525273 : Nat := 4983230072969 + 3 ^ 40 * 525273 * 2
def baseEnd_525273 : Nat := 239748910070425422819395

theorem tailTrace_525273 : CollatzResearch.WordTrace tailWord_525273 prefixEnd_525273 239748910070425422819395 := by
  unfold tailWord_525273
  simp only [CollatzResearch.WordTrace]
  refine ⟨19158280226033105331372473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12772186817355403554248315 19158280226033105331372473)
  ·
    refine ⟨14368710169524828998529355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19158280226033105331372473 14368710169524828998529355)
    ·
      refine ⟨21553065254287243497794033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14368710169524828998529355 21553065254287243497794033)
      ·
        refine ⟨16164798940715432623345525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21553065254287243497794033 16164798940715432623345525)
        ·
          refine ⟨1515449900692071808438643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16164798940715432623345525 1515449900692071808438643)
          ·
            refine ⟨2273174851038107712657965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515449900692071808438643 2273174851038107712657965)
            ·
              refine ⟨852440569139290392246737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2273174851038107712657965 852440569139290392246737)
              ·
                refine ⟨639330426854467794185053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 852440569139290392246737 639330426854467794185053)
                ·
                  refine ⟨239748910070425422819395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 639330426854467794185053 239748910070425422819395)
                  ·
                    rfl

theorem cell20_525273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_525273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525273 prefixEnd_525273 := by exact prefixLift 525273
  have htrace : WordTrace (prefixWord ++ tailWord_525273) baseStart_525273 baseEnd_525273 := by
    simpa [prefixWord, tailWord_525273, baseEnd_525273] using wordTrace_append hprefix tailTrace_525273
  have hstable : (prefixWord ++ tailWord_525273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525273).length < 2 ^ (prefixWord ++ tailWord_525273).sum := by decide
  have hdescent : baseEnd_525273 < baseStart_525273 := by decide
  rcases family_descends (prefixWord ++ tailWord_525273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525290 : List Nat := [3, 1, 3, 1, 2, 3, 3, 1, 3]
def baseStart_525290 : Nat := 118140960795 + 525290 * 2 ^ 59
def prefixEnd_525290 : Nat := 4983230072969 + 3 ^ 40 * 525290 * 2
def baseEnd_525290 : Nat := 239756669333648919252659

theorem tailTrace_525290 : CollatzResearch.WordTrace tailWord_525290 prefixEnd_525290 239756669333648919252659 := by
  unfold tailWord_525290
  simp only [CollatzResearch.WordTrace]
  refine ⟨4789725066742879308685331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12772600177981011489827549 4789725066742879308685331)
  ·
    refine ⟨7184587600114318963027997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4789725066742879308685331 7184587600114318963027997)
    ·
      refine ⟨2694220350042869611135499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7184587600114318963027997 2694220350042869611135499)
      ·
        refine ⟨4041330525064304416703249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2694220350042869611135499 4041330525064304416703249)
        ·
          refine ⟨3030997893798228312527437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4041330525064304416703249 3030997893798228312527437)
          ·
            refine ⟨1136624210174335617197789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3030997893798228312527437 1136624210174335617197789)
            ·
              refine ⟨426234078815375856449171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1136624210174335617197789 426234078815375856449171)
              ·
                refine ⟨639351118223063784673757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426234078815375856449171 639351118223063784673757)
                ·
                  refine ⟨239756669333648919252659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 639351118223063784673757 239756669333648919252659)
                  ·
                    rfl

theorem cell20_525290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_525290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525290 prefixEnd_525290 := by exact prefixLift 525290
  have htrace : WordTrace (prefixWord ++ tailWord_525290) baseStart_525290 baseEnd_525290 := by
    simpa [prefixWord, tailWord_525290, baseEnd_525290] using wordTrace_append hprefix tailTrace_525290
  have hstable : (prefixWord ++ tailWord_525290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525290).length < 2 ^ (prefixWord ++ tailWord_525290).sum := by decide
  have hdescent : baseEnd_525290 < baseStart_525290 := by decide
  rcases family_descends (prefixWord ++ tailWord_525290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525310 : List Nat := [4, 2, 2, 2, 3, 1, 1, 3, 2]
def baseStart_525310 : Nat := 118140960795 + 525310 * 2 ^ 59
def prefixEnd_525310 : Nat := 4983230072969 + 3 ^ 40 * 525310 * 2
def baseEnd_525310 : Nat := 239765797878617738585911

theorem tailTrace_525310 : CollatzResearch.WordTrace tailWord_525310 prefixEnd_525310 239765797878617738585911 := by
  unfold tailWord_525310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2394953715862382581308673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12773086484599373766979589 2394953715862382581308673)
  ·
    refine ⟨1796215286896786935981505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2394953715862382581308673 1796215286896786935981505)
    ·
      refine ⟨1347161465172590201986129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1796215286896786935981505 1347161465172590201986129)
      ·
        refine ⟨1010371098879442651489597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1347161465172590201986129 1010371098879442651489597)
        ·
          refine ⟨378889162079790994308599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1010371098879442651489597 378889162079790994308599)
          ·
            refine ⟨568333743119686491462899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378889162079790994308599 568333743119686491462899)
            ·
              refine ⟨852500614679529737194349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568333743119686491462899 852500614679529737194349)
              ·
                refine ⟨319687730504823651447881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 852500614679529737194349 319687730504823651447881)
                ·
                  refine ⟨239765797878617738585911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319687730504823651447881 239765797878617738585911)
                  ·
                    rfl

theorem cell20_525310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_525310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525310 prefixEnd_525310 := by exact prefixLift 525310
  have htrace : WordTrace (prefixWord ++ tailWord_525310) baseStart_525310 baseEnd_525310 := by
    simpa [prefixWord, tailWord_525310, baseEnd_525310] using wordTrace_append hprefix tailTrace_525310
  have hstable : (prefixWord ++ tailWord_525310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525310).length < 2 ^ (prefixWord ++ tailWord_525310).sum := by decide
  have hdescent : baseEnd_525310 < baseStart_525310 := by decide
  rcases family_descends (prefixWord ++ tailWord_525310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525335 : List Nat := [1, 1, 3, 5, 1, 3, 1, 1, 4]
def baseStart_525335 : Nat := 118140960795 + 525335 * 2 ^ 59
def prefixEnd_525335 : Nat := 4983230072969 + 3 ^ 40 * 525335 * 2
def baseEnd_525335 : Nat := 239777208559828762752475

theorem tailTrace_525335 : CollatzResearch.WordTrace tailWord_525335 prefixEnd_525335 239777208559828762752475 := by
  unfold tailWord_525335
  simp only [CollatzResearch.WordTrace]
  refine ⟨19160541551808489920129459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12773694367872326613419639 19160541551808489920129459)
  ·
    refine ⟨28740812327712734880194189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19160541551808489920129459 28740812327712734880194189)
    ·
      refine ⟨10777804622892275580072821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28740812327712734880194189 10777804622892275580072821)
      ·
        refine ⟨1010419183396150835631827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10777804622892275580072821 1010419183396150835631827)
        ·
          refine ⟨1515628775094226253447741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010419183396150835631827 1515628775094226253447741)
          ·
            refine ⟨568360790660334845042903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1515628775094226253447741 568360790660334845042903)
            ·
              refine ⟨852541185990502267564355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568360790660334845042903 852541185990502267564355)
              ·
                refine ⟨1278811778985753401346533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 852541185990502267564355 1278811778985753401346533)
                ·
                  refine ⟨239777208559828762752475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1278811778985753401346533 239777208559828762752475)
                  ·
                    rfl

theorem cell20_525335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 4].length) (baseStart_525335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525335 prefixEnd_525335 := by exact prefixLift 525335
  have htrace : WordTrace (prefixWord ++ tailWord_525335) baseStart_525335 baseEnd_525335 := by
    simpa [prefixWord, tailWord_525335, baseEnd_525335] using wordTrace_append hprefix tailTrace_525335
  have hstable : (prefixWord ++ tailWord_525335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525335).length < 2 ^ (prefixWord ++ tailWord_525335).sum := by decide
  have hdescent : baseEnd_525335 < baseStart_525335 := by decide
  rcases family_descends (prefixWord ++ tailWord_525335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525408 : List Nat := [2, 1, 1, 3, 2, 2, 1, 5, 3]
def baseStart_525408 : Nat := 118140960795 + 525408 * 2 ^ 59
def prefixEnd_525408 : Nat := 4983230072969 + 3 ^ 40 * 525408 * 2
def baseEnd_525408 : Nat := 239810527748964953318843

theorem tailTrace_525408 : CollatzResearch.WordTrace tailWord_525408 prefixEnd_525408 239810527748964953318843 := by
  unfold tailWord_525408
  simp only [CollatzResearch.WordTrace]
  refine ⟨9581602040272011693768439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12775469387029348925024585 9581602040272011693768439)
  ·
    refine ⟨14372403060408017540652659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9581602040272011693768439 14372403060408017540652659)
    ·
      refine ⟨21558604590612026310978989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14372403060408017540652659 21558604590612026310978989)
      ·
        refine ⟨8084476721479509866617121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21558604590612026310978989 8084476721479509866617121)
        ·
          refine ⟨6063357541109632399962841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8084476721479509866617121 6063357541109632399962841)
          ·
            refine ⟨4547518155832224299972131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6063357541109632399962841 4547518155832224299972131)
            ·
              refine ⟨6821277233748336449958197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4547518155832224299972131 6821277233748336449958197)
              ·
                refine ⟨639494740663906542183581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6821277233748336449958197 639494740663906542183581)
                ·
                  refine ⟨239810527748964953318843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 639494740663906542183581 239810527748964953318843)
                  ·
                    rfl

theorem cell20_525408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_525408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525408 prefixEnd_525408 := by exact prefixLift 525408
  have htrace : WordTrace (prefixWord ++ tailWord_525408) baseStart_525408 baseEnd_525408 := by
    simpa [prefixWord, tailWord_525408, baseEnd_525408] using wordTrace_append hprefix tailTrace_525408
  have hstable : (prefixWord ++ tailWord_525408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525408).length < 2 ^ (prefixWord ++ tailWord_525408).sum := by decide
  have hdescent : baseEnd_525408 < baseStart_525408 := by decide
  rcases family_descends (prefixWord ++ tailWord_525408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525415 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 6]
def baseStart_525415 : Nat := 118140960795 + 525415 * 2 ^ 59
def prefixEnd_525415 : Nat := 4983230072969 + 3 ^ 40 * 525415 * 2
def baseEnd_525415 : Nat := 239813722739704040085481

theorem tailTrace_525415 : CollatzResearch.WordTrace tailWord_525415 prefixEnd_525415 239813722739704040085481 := by
  unfold tailWord_525415
  simp only [CollatzResearch.WordTrace]
  refine ⟨19163459391518663583041699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12775639594345775722027799 19163459391518663583041699)
  ·
    refine ⟨28745189087277995374562549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19163459391518663583041699 28745189087277995374562549)
    ·
      refine ⟨2694861476932312066365239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28745189087277995374562549 2694861476932312066365239)
      ·
        refine ⟨4042292215398468099547859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2694861476932312066365239 4042292215398468099547859)
        ·
          refine ⟨6063438323097702149321789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4042292215398468099547859 6063438323097702149321789)
          ·
            refine ⟨2273789371161638305995671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6063438323097702149321789 2273789371161638305995671)
            ·
              refine ⟨3410684056742457458993507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2273789371161638305995671 3410684056742457458993507)
              ·
                refine ⟨5116026085113686188490261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3410684056742457458993507 5116026085113686188490261)
                ·
                  refine ⟨239813722739704040085481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5116026085113686188490261 239813722739704040085481)
                  ·
                    rfl

theorem cell20_525415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_525415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525415 prefixEnd_525415 := by exact prefixLift 525415
  have htrace : WordTrace (prefixWord ++ tailWord_525415) baseStart_525415 baseEnd_525415 := by
    simpa [prefixWord, tailWord_525415, baseEnd_525415] using wordTrace_append hprefix tailTrace_525415
  have hstable : (prefixWord ++ tailWord_525415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525415).length < 2 ^ (prefixWord ++ tailWord_525415).sum := by decide
  have hdescent : baseEnd_525415 < baseStart_525415 := by decide
  rcases family_descends (prefixWord ++ tailWord_525415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525418 : List Nat := [3, 1, 3, 2, 2, 2, 3, 4]
def baseStart_525418 : Nat := 118140960795 + 525418 * 2 ^ 59
def prefixEnd_525418 : Nat := 4983230072969 + 3 ^ 40 * 525418 * 2
def baseEnd_525418 : Nat := 79938364007149787661823

theorem tailTrace_525418 : CollatzResearch.WordTrace tailWord_525418 prefixEnd_525418 79938364007149787661823 := by
  unfold tailWord_525418
  simp only [CollatzResearch.WordTrace]
  refine ⟨4790892202626948773850227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12775712540338530063600605 4790892202626948773850227)
  ·
    refine ⟨7186338303940423160775341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4790892202626948773850227 7186338303940423160775341)
    ·
      refine ⟨2694876863977658685290753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7186338303940423160775341 2694876863977658685290753)
      ·
        refine ⟨2021157647983244013968065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2694876863977658685290753 2021157647983244013968065)
        ·
          refine ⟨1515868235987433010476049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2021157647983244013968065 1515868235987433010476049)
          ·
            refine ⟨1136901176990574757857037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1515868235987433010476049 1136901176990574757857037)
            ·
              refine ⟨426337941371465534196389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1136901176990574757857037 426337941371465534196389)
              ·
                refine ⟨79938364007149787661823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 426337941371465534196389 79938364007149787661823)
                ·
                  rfl

theorem cell20_525418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_525418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525418 prefixEnd_525418 := by exact prefixLift 525418
  have htrace : WordTrace (prefixWord ++ tailWord_525418) baseStart_525418 baseEnd_525418 := by
    simpa [prefixWord, tailWord_525418, baseEnd_525418] using wordTrace_append hprefix tailTrace_525418
  have hstable : (prefixWord ++ tailWord_525418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525418).length < 2 ^ (prefixWord ++ tailWord_525418).sum := by decide
  have hdescent : baseEnd_525418 < baseStart_525418 := by decide
  rcases family_descends (prefixWord ++ tailWord_525418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525432 : List Nat := [2, 1, 2, 1, 1, 1, 5, 5, 2]
def baseStart_525432 : Nat := 118140960795 + 525432 * 2 ^ 59
def prefixEnd_525432 : Nat := 4983230072969 + 3 ^ 40 * 525432 * 2
def baseEnd_525432 : Nat := 239821482002927536518745

theorem tailTrace_525432 : CollatzResearch.WordTrace tailWord_525432 prefixEnd_525432 239821482002927536518745 := by
  unfold tailWord_525432
  simp only [CollatzResearch.WordTrace]
  refine ⟨9582039716228537743205275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12776052954971383657607033 9582039716228537743205275)
  ·
    refine ⟨14373059574342806614807913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9582039716228537743205275 14373059574342806614807913)
    ·
      refine ⟨10779794680757104961105935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14373059574342806614807913 10779794680757104961105935)
      ·
        refine ⟨16169692021135657441658903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10779794680757104961105935 16169692021135657441658903)
        ·
          refine ⟨24254538031703486162488355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16169692021135657441658903 24254538031703486162488355)
          ·
            refine ⟨36381807047555229243732533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24254538031703486162488355 36381807047555229243732533)
            ·
              refine ⟨3410794410708302741599925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36381807047555229243732533 3410794410708302741599925)
              ·
                refine ⟨319761976003903382024993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3410794410708302741599925 319761976003903382024993)
                ·
                  refine ⟨239821482002927536518745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319761976003903382024993 239821482002927536518745)
                  ·
                    rfl

theorem cell20_525432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 2].length) (baseStart_525432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525432 prefixEnd_525432 := by exact prefixLift 525432
  have htrace : WordTrace (prefixWord ++ tailWord_525432) baseStart_525432 baseEnd_525432 := by
    simpa [prefixWord, tailWord_525432, baseEnd_525432] using wordTrace_append hprefix tailTrace_525432
  have hstable : (prefixWord ++ tailWord_525432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525432).length < 2 ^ (prefixWord ++ tailWord_525432).sum := by decide
  have hdescent : baseEnd_525432 < baseStart_525432 := by decide
  rcases family_descends (prefixWord ++ tailWord_525432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525477 : List Nat := [1, 3, 1, 2, 1, 4, 4, 4]
def baseStart_525477 : Nat := 118140960795 + 525477 * 2 ^ 59
def prefixEnd_525477 : Nat := 4983230072969 + 3 ^ 40 * 525477 * 2
def baseEnd_525477 : Nat := 79947340409702460006187

theorem tailTrace_525477 : CollatzResearch.WordTrace tailWord_525477 prefixEnd_525477 79947340409702460006187 := by
  unfold tailWord_525477
  simp only [CollatzResearch.WordTrace]
  refine ⟨19165720717294048171798685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12777147144862698781199123 19165720717294048171798685)
  ·
    refine ⟨7187145268985268064424507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19165720717294048171798685 7187145268985268064424507)
    ·
      refine ⟨10780717903477902096636761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7187145268985268064424507 10780717903477902096636761)
      ·
        refine ⟨8085538427608426572477571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10780717903477902096636761 8085538427608426572477571)
        ·
          refine ⟨12128307641412639858716357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8085538427608426572477571 12128307641412639858716357)
          ·
            refine ⟨2274057682764869973509317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12128307641412639858716357 2274057682764869973509317)
            ·
              refine ⟨426385815518413120032997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2274057682764869973509317 426385815518413120032997)
              ·
                refine ⟨79947340409702460006187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 426385815518413120032997 79947340409702460006187)
                ·
                  rfl

theorem cell20_525477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 4].length) (baseStart_525477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525477 prefixEnd_525477 := by exact prefixLift 525477
  have htrace : WordTrace (prefixWord ++ tailWord_525477) baseStart_525477 baseEnd_525477 := by
    simpa [prefixWord, tailWord_525477, baseEnd_525477] using wordTrace_append hprefix tailTrace_525477
  have hstable : (prefixWord ++ tailWord_525477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525477).length < 2 ^ (prefixWord ++ tailWord_525477).sum := by decide
  have hdescent : baseEnd_525477 < baseStart_525477 := by decide
  rcases family_descends (prefixWord ++ tailWord_525477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525504 : List Nat := [2, 1, 1, 2, 6, 1, 3, 2, 2]
def baseStart_525504 : Nat := 118140960795 + 525504 * 2 ^ 59
def prefixEnd_525504 : Nat := 4983230072969 + 3 ^ 40 * 525504 * 2
def baseEnd_525504 : Nat := 239854344764815286118451

theorem tailTrace_525504 : CollatzResearch.WordTrace tailWord_525504 prefixEnd_525504 239854344764815286118451 := by
  unfold tailWord_525504
  simp only [CollatzResearch.WordTrace]
  refine ⟨9583352744098115891515783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12777803658797487855354377 9583352744098115891515783)
  ·
    refine ⟨14375029116147173837273675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9583352744098115891515783 14375029116147173837273675)
    ·
      refine ⟨21562543674220760755910513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14375029116147173837273675 21562543674220760755910513)
      ·
        refine ⟨16171907755665570566932885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21562543674220760755910513 16171907755665570566932885)
        ·
          refine ⟨758058176046823620324979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16171907755665570566932885 758058176046823620324979)
          ·
            refine ⟨1137087264070235430487469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758058176046823620324979 1137087264070235430487469)
            ·
              refine ⟨426407724026338286432801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1137087264070235430487469 426407724026338286432801)
              ·
                refine ⟨319805793019753714824601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426407724026338286432801 319805793019753714824601)
                ·
                  refine ⟨239854344764815286118451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319805793019753714824601 239854344764815286118451)
                  ·
                    rfl

theorem cell20_525504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 2].length) (baseStart_525504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525504 prefixEnd_525504 := by exact prefixLift 525504
  have htrace : WordTrace (prefixWord ++ tailWord_525504) baseStart_525504 baseEnd_525504 := by
    simpa [prefixWord, tailWord_525504, baseEnd_525504] using wordTrace_append hprefix tailTrace_525504
  have hstable : (prefixWord ++ tailWord_525504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525504).length < 2 ^ (prefixWord ++ tailWord_525504).sum := by decide
  have hdescent : baseEnd_525504 < baseStart_525504 := by decide
  rcases family_descends (prefixWord ++ tailWord_525504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525510 : List Nat := [6, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_525510 : Nat := 118140960795 + 525510 * 2 ^ 59
def prefixEnd_525510 : Nat := 4983230072969 + 3 ^ 40 * 525510 * 2
def baseEnd_525510 : Nat := 239857083328305931918427

theorem tailTrace_525510 : CollatzResearch.WordTrace tailWord_525510 prefixEnd_525510 239857083328305931918427 := by
  unfold tailWord_525510
  simp only [CollatzResearch.WordTrace]
  refine ⟨598966385192952962742187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12777949550782996538499989 598966385192952962742187)
  ·
    refine ⟨898449577789429444113281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 598966385192952962742187 898449577789429444113281)
    ·
      refine ⟨673837183342072083084961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 898449577789429444113281 673837183342072083084961)
      ·
        refine ⟨505377887506554062313721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 673837183342072083084961 505377887506554062313721)
        ·
          refine ⟨379033415629915546735291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505377887506554062313721 379033415629915546735291)
          ·
            refine ⟨568550123444873320102937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379033415629915546735291 568550123444873320102937)
            ·
              refine ⟨426412592583654990077203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568550123444873320102937 426412592583654990077203)
              ·
                refine ⟨639618888875482485115805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426412592583654990077203 639618888875482485115805)
                ·
                  refine ⟨239857083328305931918427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 639618888875482485115805 239857083328305931918427)
                  ·
                    rfl

theorem cell20_525510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_525510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525510 prefixEnd_525510 := by exact prefixLift 525510
  have htrace : WordTrace (prefixWord ++ tailWord_525510) baseStart_525510 baseEnd_525510 := by
    simpa [prefixWord, tailWord_525510, baseEnd_525510] using wordTrace_append hprefix tailTrace_525510
  have hstable : (prefixWord ++ tailWord_525510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525510).length < 2 ^ (prefixWord ++ tailWord_525510).sum := by decide
  have hdescent : baseEnd_525510 < baseStart_525510 := by decide
  rcases family_descends (prefixWord ++ tailWord_525510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525536 : List Nat := [2, 1, 1, 3, 1, 4, 2, 6]
def baseStart_525536 : Nat := 118140960795 + 525536 * 2 ^ 59
def prefixEnd_525536 : Nat := 4983230072969 + 3 ^ 40 * 525536 * 2
def baseEnd_525536 : Nat := 79956316812255132350551

theorem tailTrace_525536 : CollatzResearch.WordTrace tailWord_525536 prefixEnd_525536 79956316812255132350551 := by
  unfold tailWord_525536
  simp only [CollatzResearch.WordTrace]
  refine ⟨9583936312040150624098231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12778581749386867498797641 9583936312040150624098231)
  ·
    refine ⟨14375904468060225936147347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9583936312040150624098231 14375904468060225936147347)
    ·
      refine ⟨21563856702090338904221021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14375904468060225936147347 21563856702090338904221021)
      ·
        refine ⟨8086446263283877089082883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21563856702090338904221021 8086446263283877089082883)
        ·
          refine ⟨12129669394925815633624325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8086446263283877089082883 12129669394925815633624325)
          ·
            refine ⟨2274313011548590431304561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12129669394925815633624325 2274313011548590431304561)
            ·
              refine ⟨1705734758661442823478421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2274313011548590431304561 1705734758661442823478421)
              ·
                refine ⟨79956316812255132350551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1705734758661442823478421 79956316812255132350551)
                ·
                  rfl

theorem cell20_525536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_525536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525536 prefixEnd_525536 := by exact prefixLift 525536
  have htrace : WordTrace (prefixWord ++ tailWord_525536) baseStart_525536 baseEnd_525536 := by
    simpa [prefixWord, tailWord_525536, baseEnd_525536] using wordTrace_append hprefix tailTrace_525536
  have hstable : (prefixWord ++ tailWord_525536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525536).length < 2 ^ (prefixWord ++ tailWord_525536).sum := by decide
  have hdescent : baseEnd_525536 < baseStart_525536 := by decide
  rcases family_descends (prefixWord ++ tailWord_525536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525591 : List Nat := [1, 1, 3, 4, 1, 1, 5, 4]
def baseStart_525591 : Nat := 118140960795 + 525591 * 2 ^ 59
def prefixEnd_525591 : Nat := 4983230072969 + 3 ^ 40 * 525591 * 2
def baseEnd_525591 : Nat := 79964684645143216739365

theorem tailTrace_525591 : CollatzResearch.WordTrace tailWord_525591 prefixEnd_525591 79964684645143216739365 := by
  unfold tailWord_525591
  simp only [CollatzResearch.WordTrace]
  refine ⟨19169878638881045641448627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12779919092587363760965751 19169878638881045641448627)
  ·
    refine ⟨28754817958321568462172941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19169878638881045641448627 28754817958321568462172941)
    ·
      refine ⟨10783056734370588173314853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28754817958321568462172941 10783056734370588173314853)
      ·
        refine ⟨2021823137694485282496535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10783056734370588173314853 2021823137694485282496535)
        ·
          refine ⟨3032734706541727923744803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2021823137694485282496535 3032734706541727923744803)
          ·
            refine ⟨4549102059812591885617205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3032734706541727923744803 4549102059812591885617205)
            ·
              refine ⟨426478318107430489276613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4549102059812591885617205 426478318107430489276613)
              ·
                refine ⟨79964684645143216739365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 426478318107430489276613 79964684645143216739365)
                ·
                  rfl

theorem cell20_525591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 4].length) (baseStart_525591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525591 prefixEnd_525591 := by exact prefixLift 525591
  have htrace : WordTrace (prefixWord ++ tailWord_525591) baseStart_525591 baseEnd_525591 := by
    simpa [prefixWord, tailWord_525591, baseEnd_525591] using wordTrace_append hprefix tailTrace_525591
  have hstable : (prefixWord ++ tailWord_525591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525591).length < 2 ^ (prefixWord ++ tailWord_525591).sum := by decide
  have hdescent : baseEnd_525591 < baseStart_525591 := by decide
  rcases family_descends (prefixWord ++ tailWord_525591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525657 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 5]
def baseStart_525657 : Nat := 118140960795 + 525657 * 2 ^ 59
def prefixEnd_525657 : Nat := 4983230072969 + 3 ^ 40 * 525657 * 2
def baseEnd_525657 : Nat := 239924178133826754017825

theorem tailTrace_525657 : CollatzResearch.WordTrace tailWord_525657 prefixEnd_525657 239924178133826754017825 := by
  unfold tailWord_525657
  simp only [CollatzResearch.WordTrace]
  refine ⟨19172285856641938913351225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12781523904427959275567483 19172285856641938913351225)
  ·
    refine ⟨14379214392481454185013419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19172285856641938913351225 14379214392481454185013419)
    ·
      refine ⟨21568821588722181277520129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14379214392481454185013419 21568821588722181277520129)
      ·
        refine ⟨16176616191541635958140097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21568821588722181277520129 16176616191541635958140097)
        ·
          refine ⟨12132462143656226968605073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16176616191541635958140097 12132462143656226968605073)
          ·
            refine ⟨9099346607742170226453805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12132462143656226968605073 9099346607742170226453805)
            ·
              refine ⟨3412254977903313834920177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9099346607742170226453805 3412254977903313834920177)
              ·
                refine ⟨2559191233427485376190133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3412254977903313834920177 2559191233427485376190133)
                ·
                  refine ⟨239924178133826754017825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2559191233427485376190133 239924178133826754017825)
                  ·
                    rfl

theorem cell20_525657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_525657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525657 prefixEnd_525657 := by exact prefixLift 525657
  have htrace : WordTrace (prefixWord ++ tailWord_525657) baseStart_525657 baseEnd_525657 := by
    simpa [prefixWord, tailWord_525657, baseEnd_525657] using wordTrace_append hprefix tailTrace_525657
  have hstable : (prefixWord ++ tailWord_525657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525657).length < 2 ^ (prefixWord ++ tailWord_525657).sum := by decide
  have hdescent : baseEnd_525657 < baseStart_525657 := by decide
  rcases family_descends (prefixWord ++ tailWord_525657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525681 : List Nat := [1, 2, 2, 2, 1, 2, 5, 1, 4]
def baseStart_525681 : Nat := 118140960795 + 525681 * 2 ^ 59
def prefixEnd_525681 : Nat := 4983230072969 + 3 ^ 40 * 525681 * 2
def baseEnd_525681 : Nat := 239935132387789337217727

theorem tailTrace_525681 : CollatzResearch.WordTrace tailWord_525681 prefixEnd_525681 239935132387789337217727 := by
  unfold tailWord_525681
  simp only [CollatzResearch.WordTrace]
  refine ⟨19173161208554991012224897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12782107472369994008149931 19173161208554991012224897)
  ·
    refine ⟨14379870906416243259168673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19173161208554991012224897 14379870906416243259168673)
    ·
      refine ⟨10784903179812182444376505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14379870906416243259168673 10784903179812182444376505)
      ·
        refine ⟨8088677384859136833282379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10784903179812182444376505 8088677384859136833282379)
        ·
          refine ⟨12133016077288705249923569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8088677384859136833282379 12133016077288705249923569)
          ·
            refine ⟨9099762057966528937442677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12133016077288705249923569 9099762057966528937442677)
            ·
              refine ⟨853102692934362087885251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9099762057966528937442677 853102692934362087885251)
              ·
                refine ⟨1279654039401543131827877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853102692934362087885251 1279654039401543131827877)
                ·
                  refine ⟨239935132387789337217727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1279654039401543131827877 239935132387789337217727)
                  ·
                    rfl

theorem cell20_525681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_525681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525681 prefixEnd_525681 := by exact prefixLift 525681
  have htrace : WordTrace (prefixWord ++ tailWord_525681) baseStart_525681 baseEnd_525681 := by
    simpa [prefixWord, tailWord_525681, baseEnd_525681] using wordTrace_append hprefix tailTrace_525681
  have hstable : (prefixWord ++ tailWord_525681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525681).length < 2 ^ (prefixWord ++ tailWord_525681).sum := by decide
  have hdescent : baseEnd_525681 < baseStart_525681 := by decide
  rcases family_descends (prefixWord ++ tailWord_525681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525757 : List Nat := [1, 4, 1, 2, 2, 1, 3, 2, 4]
def baseStart_525757 : Nat := 118140960795 + 525757 * 2 ^ 59
def prefixEnd_525757 : Nat := 4983230072969 + 3 ^ 40 * 525757 * 2
def baseEnd_525757 : Nat := 239969820858670850684083

theorem tailTrace_525757 : CollatzResearch.WordTrace tailWord_525757 prefixEnd_525757 239969820858670850684083 := by
  unfold tailWord_525757
  simp only [CollatzResearch.WordTrace]
  refine ⟨19175933156279655991991525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12783955437519770661327683 19175933156279655991991525)
  ·
    refine ⟨3595487466802435498498411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19175933156279655991991525 3595487466802435498498411)
    ·
      refine ⟨5393231200203653247747617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3595487466802435498498411 5393231200203653247747617)
      ·
        refine ⟨4044923400152739935810713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5393231200203653247747617 4044923400152739935810713)
        ·
          refine ⟨3033692550114554951858035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4044923400152739935810713 3033692550114554951858035)
          ·
            refine ⟨4550538825171832427787053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3033692550114554951858035 4550538825171832427787053)
            ·
              refine ⟨1706452059439437160420145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4550538825171832427787053 1706452059439437160420145)
              ·
                refine ⟨1279839044579577870315109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1706452059439437160420145 1279839044579577870315109)
                ·
                  refine ⟨239969820858670850684083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1279839044579577870315109 239969820858670850684083)
                  ·
                    rfl

theorem cell20_525757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_525757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525757 prefixEnd_525757 := by exact prefixLift 525757
  have htrace : WordTrace (prefixWord ++ tailWord_525757) baseStart_525757 baseEnd_525757 := by
    simpa [prefixWord, tailWord_525757, baseEnd_525757] using wordTrace_append hprefix tailTrace_525757
  have hstable : (prefixWord ++ tailWord_525757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525757).length < 2 ^ (prefixWord ++ tailWord_525757).sum := by decide
  have hdescent : baseEnd_525757 < baseStart_525757 := by decide
  rcases family_descends (prefixWord ++ tailWord_525757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525774 : List Nat := [4, 1, 1, 1, 2, 1, 3, 5, 2]
def baseStart_525774 : Nat := 118140960795 + 525774 * 2 ^ 59
def prefixEnd_525774 : Nat := 4983230072969 + 3 ^ 40 * 525774 * 2
def baseEnd_525774 : Nat := 239977580121894347117347

theorem tailTrace_525774 : CollatzResearch.WordTrace tailWord_525774 prefixEnd_525774 239977580121894347117347 := by
  unfold tailWord_525774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2397069149652258486920047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12784368798145378596906917 2397069149652258486920047)
  ·
    refine ⟨3595603724478387730380071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2397069149652258486920047 3595603724478387730380071)
    ·
      refine ⟨5393405586717581595570107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3595603724478387730380071 5393405586717581595570107)
      ·
        refine ⟨8090108380076372393355161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5393405586717581595570107 8090108380076372393355161)
        ·
          refine ⟨6067581285057279295016371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8090108380076372393355161 6067581285057279295016371)
          ·
            refine ⟨9101371927585918942524557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6067581285057279295016371 9101371927585918942524557)
            ·
              refine ⟨3413014472844719603446709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9101371927585918942524557 3413014472844719603446709)
              ·
                refine ⟨319970106829192462823129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3413014472844719603446709 319970106829192462823129)
                ·
                  refine ⟨239977580121894347117347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319970106829192462823129 239977580121894347117347)
                  ·
                    rfl

theorem cell20_525774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_525774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525774 prefixEnd_525774 := by exact prefixLift 525774
  have htrace : WordTrace (prefixWord ++ tailWord_525774) baseStart_525774 baseEnd_525774 := by
    simpa [prefixWord, tailWord_525774, baseEnd_525774] using wordTrace_append hprefix tailTrace_525774
  have hstable : (prefixWord ++ tailWord_525774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525774).length < 2 ^ (prefixWord ++ tailWord_525774).sum := by decide
  have hdescent : baseEnd_525774 < baseStart_525774 := by decide
  rcases family_descends (prefixWord ++ tailWord_525774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525795 : List Nat := [1, 1, 1, 6, 2, 1, 1, 3, 4]
def baseStart_525795 : Nat := 118140960795 + 525795 * 2 ^ 59
def prefixEnd_525795 : Nat := 4983230072969 + 3 ^ 40 * 525795 * 2
def baseEnd_525795 : Nat := 239987165094111607417261

theorem tailTrace_525795 : CollatzResearch.WordTrace tailWord_525795 prefixEnd_525795 239987165094111607417261 := by
  unfold tailWord_525795
  simp only [CollatzResearch.WordTrace]
  refine ⟨19177319130141988481874839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12784879420094658987916559 19177319130141988481874839)
  ·
    refine ⟨28765978695212982722812259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19177319130141988481874839 28765978695212982722812259)
    ·
      refine ⟨43148968042819474084218389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28765978695212982722812259 43148968042819474084218389)
      ·
        refine ⟨2022607877007162847697737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43148968042819474084218389 2022607877007162847697737)
        ·
          refine ⟨1516955907755372135773303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2022607877007162847697737 1516955907755372135773303)
          ·
            refine ⟨2275433861633058203659955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1516955907755372135773303 2275433861633058203659955)
            ·
              refine ⟨3413150792449587305489933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2275433861633058203659955 3413150792449587305489933)
              ·
                refine ⟨1279931547168595239558725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3413150792449587305489933 1279931547168595239558725)
                ·
                  refine ⟨239987165094111607417261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1279931547168595239558725 239987165094111607417261)
                  ·
                    rfl

theorem cell20_525795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 4].length) (baseStart_525795 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525795 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525795 prefixEnd_525795 := by exact prefixLift 525795
  have htrace : WordTrace (prefixWord ++ tailWord_525795) baseStart_525795 baseEnd_525795 := by
    simpa [prefixWord, tailWord_525795, baseEnd_525795] using wordTrace_append hprefix tailTrace_525795
  have hstable : (prefixWord ++ tailWord_525795).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525795).length < 2 ^ (prefixWord ++ tailWord_525795).sum := by decide
  have hdescent : baseEnd_525795 < baseStart_525795 := by decide
  rcases family_descends (prefixWord ++ tailWord_525795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525901 : List Nat := [1, 6, 1, 1, 3, 2, 2, 2, 2]
def baseStart_525901 : Nat := 118140960795 + 525901 * 2 ^ 59
def prefixEnd_525901 : Nat := 4983230072969 + 3 ^ 40 * 525901 * 2
def baseEnd_525901 : Nat := 240035546382446349883495

theorem tailTrace_525901 : CollatzResearch.WordTrace tailWord_525901 prefixEnd_525901 240035546382446349883495 := by
  unfold tailWord_525901
  simp only [CollatzResearch.WordTrace]
  refine ⟨19181185267757968585233557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12787456845171979056822371 19181185267757968585233557)
  ·
    refine ⟨899118059426154777432823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19181185267757968585233557 899118059426154777432823)
    ·
      refine ⟨1348677089139232166149235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 899118059426154777432823 1348677089139232166149235)
      ·
        refine ⟨2023015633708848249223853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1348677089139232166149235 2023015633708848249223853)
        ·
          refine ⟨758630862640818093458945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2023015633708848249223853 758630862640818093458945)
          ·
            refine ⟨568973146980613570094209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 758630862640818093458945 568973146980613570094209)
            ·
              refine ⟨426729860235460177570657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568973146980613570094209 426729860235460177570657)
              ·
                refine ⟨320047395176595133177993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426729860235460177570657 320047395176595133177993)
                ·
                  refine ⟨240035546382446349883495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320047395176595133177993 240035546382446349883495)
                  ·
                    rfl

theorem cell20_525901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_525901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525901 prefixEnd_525901 := by exact prefixLift 525901
  have htrace : WordTrace (prefixWord ++ tailWord_525901) baseStart_525901 baseEnd_525901 := by
    simpa [prefixWord, tailWord_525901, baseEnd_525901] using wordTrace_append hprefix tailTrace_525901
  have hstable : (prefixWord ++ tailWord_525901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525901).length < 2 ^ (prefixWord ++ tailWord_525901).sum := by decide
  have hdescent : baseEnd_525901 < baseStart_525901 := by decide
  rcases family_descends (prefixWord ++ tailWord_525901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525937 : List Nat := [1, 2, 2, 2, 1, 1, 1, 10]
def baseStart_525937 : Nat := 118140960795 + 525937 * 2 ^ 59
def prefixEnd_525937 : Nat := 4983230072969 + 3 ^ 40 * 525937 * 2
def baseEnd_525937 : Nat := 80017325921130074894449

theorem tailTrace_525937 : CollatzResearch.WordTrace tailWord_525937 prefixEnd_525937 80017325921130074894449 := by
  unfold tailWord_525937
  simp only [CollatzResearch.WordTrace]
  refine ⟨19182498295627546733544065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12788332197085031155696043 19182498295627546733544065)
  ·
    refine ⟨14386873721720660050158049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19182498295627546733544065 14386873721720660050158049)
    ·
      refine ⟨10790155291290495037618537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14386873721720660050158049 10790155291290495037618537)
      ·
        refine ⟨8092616468467871278213903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10790155291290495037618537 8092616468467871278213903)
        ·
          refine ⟨12138924702701806917320855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8092616468467871278213903 12138924702701806917320855)
          ·
            refine ⟨18208387054052710375981283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12138924702701806917320855 18208387054052710375981283)
            ·
              refine ⟨27312580581079065563971925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18208387054052710375981283 27312580581079065563971925)
              ·
                refine ⟨80017325921130074894449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27312580581079065563971925 80017325921130074894449)
                ·
                  rfl

theorem cell20_525937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 10].length) (baseStart_525937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525937 prefixEnd_525937 := by exact prefixLift 525937
  have htrace : WordTrace (prefixWord ++ tailWord_525937) baseStart_525937 baseEnd_525937 := by
    simpa [prefixWord, tailWord_525937, baseEnd_525937] using wordTrace_append hprefix tailTrace_525937
  have hstable : (prefixWord ++ tailWord_525937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525937).length < 2 ^ (prefixWord ++ tailWord_525937).sum := by decide
  have hdescent : baseEnd_525937 < baseStart_525937 := by decide
  rcases family_descends (prefixWord ++ tailWord_525937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_525985 : List Nat := [1, 2, 3, 3, 2, 1, 2, 2, 4]
def baseStart_525985 : Nat := 118140960795 + 525985 * 2 ^ 59
def prefixEnd_525985 : Nat := 4983230072969 + 3 ^ 40 * 525985 * 2
def baseEnd_525985 : Nat := 240073886271315391083151

theorem tailTrace_525985 : CollatzResearch.WordTrace tailWord_525985 prefixEnd_525985 240073886271315391083151 := by
  unfold tailWord_525985
  simp only [CollatzResearch.WordTrace]
  refine ⟨19184248999453650931291409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12789499332969100620860939 19184248999453650931291409)
  ·
    refine ⟨14388186749590238198468557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19184248999453650931291409 14388186749590238198468557)
    ·
      refine ⟨5395570031096339324425709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14388186749590238198468557 5395570031096339324425709)
      ·
        refine ⟨2023338761661127246659641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5395570031096339324425709 2023338761661127246659641)
        ·
          refine ⟨1517504071245845434994731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2023338761661127246659641 1517504071245845434994731)
          ·
            refine ⟨2276256106868768152492097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517504071245845434994731 2276256106868768152492097)
            ·
              refine ⟨1707192080151576114369073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2276256106868768152492097 1707192080151576114369073)
              ·
                refine ⟨1280394060113682085776805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1707192080151576114369073 1280394060113682085776805)
                ·
                  refine ⟨240073886271315391083151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1280394060113682085776805 240073886271315391083151)
                  ·
                    rfl

theorem cell20_525985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_525985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_525985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_525985 prefixEnd_525985 := by exact prefixLift 525985
  have htrace : WordTrace (prefixWord ++ tailWord_525985) baseStart_525985 baseEnd_525985 := by
    simpa [prefixWord, tailWord_525985, baseEnd_525985] using wordTrace_append hprefix tailTrace_525985
  have hstable : (prefixWord ++ tailWord_525985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_525985).length < 2 ^ (prefixWord ++ tailWord_525985).sum := by decide
  have hdescent : baseEnd_525985 < baseStart_525985 := by decide
  rcases family_descends (prefixWord ++ tailWord_525985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526002 : List Nat := [3, 2, 1, 1, 1, 2, 5, 3, 2]
def baseStart_526002 : Nat := 118140960795 + 526002 * 2 ^ 59
def prefixEnd_526002 : Nat := 4983230072969 + 3 ^ 40 * 526002 * 2
def baseEnd_526002 : Nat := 240081645534538887516415

theorem tailTrace_526002 : CollatzResearch.WordTrace tailWord_526002 prefixEnd_526002 240081645534538887516415 := by
  unfold tailWord_526002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4796217260098015708665065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12789912693594708556440173 4796217260098015708665065)
  ·
    refine ⟨3597162945073511781498799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4796217260098015708665065 3597162945073511781498799)
    ·
      refine ⟨5395744417610267672248199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3597162945073511781498799 5395744417610267672248199)
      ·
        refine ⟨8093616626415401508372299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5395744417610267672248199 8093616626415401508372299)
        ·
          refine ⟨12140424939623102262558449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8093616626415401508372299 12140424939623102262558449)
          ·
            refine ⟨9105318704717326696918837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12140424939623102262558449 9105318704717326696918837)
            ·
              refine ⟨853623628567249377836141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9105318704717326696918837 853623628567249377836141)
              ·
                refine ⟨320108860712718516688553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 853623628567249377836141 320108860712718516688553)
                ·
                  refine ⟨240081645534538887516415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320108860712718516688553 240081645534538887516415)
                  ·
                    rfl

theorem cell20_526002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_526002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526002 prefixEnd_526002 := by exact prefixLift 526002
  have htrace : WordTrace (prefixWord ++ tailWord_526002) baseStart_526002 baseEnd_526002 := by
    simpa [prefixWord, tailWord_526002, baseEnd_526002] using wordTrace_append hprefix tailTrace_526002
  have hstable : (prefixWord ++ tailWord_526002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526002).length < 2 ^ (prefixWord ++ tailWord_526002).sum := by decide
  have hdescent : baseEnd_526002 < baseStart_526002 := by decide
  rcases family_descends (prefixWord ++ tailWord_526002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526029 : List Nat := [1, 6, 2, 1, 1, 3, 2, 1, 3]
def baseStart_526029 : Nat := 118140960795 + 526029 * 2 ^ 59
def prefixEnd_526029 : Nat := 4983230072969 + 3 ^ 40 * 526029 * 2
def baseEnd_526029 : Nat := 240093969070246793616305

theorem tailTrace_526029 : CollatzResearch.WordTrace tailWord_526029 prefixEnd_526029 240093969070246793616305 := by
  unfold tailWord_526029
  simp only [CollatzResearch.WordTrace]
  refine ⟨19185853811294246445893141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12790569207529497630595427 19185853811294246445893141)
  ·
    refine ⟨899336897404417802151241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19185853811294246445893141 899336897404417802151241)
    ·
      refine ⟨674502673053313351613431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 899336897404417802151241 674502673053313351613431)
      ·
        refine ⟨1011754009579970027420147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674502673053313351613431 1011754009579970027420147)
        ·
          refine ⟨1517631014369955041130221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011754009579970027420147 1517631014369955041130221)
          ·
            refine ⟨569111630388733140423833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1517631014369955041130221 569111630388733140423833)
            ·
              refine ⟨426833722791549855317875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 569111630388733140423833 426833722791549855317875)
              ·
                refine ⟨640250584187324782976813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426833722791549855317875 640250584187324782976813)
                ·
                  refine ⟨240093969070246793616305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 640250584187324782976813 240093969070246793616305)
                  ·
                    rfl

theorem cell20_526029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_526029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526029 prefixEnd_526029 := by exact prefixLift 526029
  have htrace : WordTrace (prefixWord ++ tailWord_526029) baseStart_526029 baseEnd_526029 := by
    simpa [prefixWord, tailWord_526029, baseEnd_526029] using wordTrace_append hprefix tailTrace_526029
  have hstable : (prefixWord ++ tailWord_526029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526029).length < 2 ^ (prefixWord ++ tailWord_526029).sum := by decide
  have hdescent : baseEnd_526029 < baseStart_526029 := by decide
  rcases family_descends (prefixWord ++ tailWord_526029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526030 : List Nat := [4, 1, 1, 1, 3, 1, 4, 5]
def baseStart_526030 : Nat := 118140960795 + 526030 * 2 ^ 59
def prefixEnd_526030 : Nat := 4983230072969 + 3 ^ 40 * 526030 * 2
def baseEnd_526030 : Nat := 80031475165831744860989

theorem tailTrace_526030 : CollatzResearch.WordTrace tailWord_526030 prefixEnd_526030 80031475165831744860989 := by
  unfold tailWord_526030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2398236285536327952084943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12790593522860415744453029 2398236285536327952084943)
  ·
    refine ⟨3597354428304491928127415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2398236285536327952084943 3597354428304491928127415)
    ·
      refine ⟨5396031642456737892191123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3597354428304491928127415 5396031642456737892191123)
      ·
        refine ⟨8094047463685106838286685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5396031642456737892191123 8094047463685106838286685)
        ·
          refine ⟨3035267798881915064357507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8094047463685106838286685 3035267798881915064357507)
          ·
            refine ⟨4552901698322872596536261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3035267798881915064357507 4552901698322872596536261)
            ·
              refine ⟨853669068435538611850549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4552901698322872596536261 853669068435538611850549)
              ·
                refine ⟨80031475165831744860989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 853669068435538611850549 80031475165831744860989)
                ·
                  rfl

theorem cell20_526030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_526030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526030 prefixEnd_526030 := by exact prefixLift 526030
  have htrace : WordTrace (prefixWord ++ tailWord_526030) baseStart_526030 baseEnd_526030 := by
    simpa [prefixWord, tailWord_526030, baseEnd_526030] using wordTrace_append hprefix tailTrace_526030
  have hstable : (prefixWord ++ tailWord_526030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526030).length < 2 ^ (prefixWord ++ tailWord_526030).sum := by decide
  have hdescent : baseEnd_526030 < baseStart_526030 := by decide
  rcases family_descends (prefixWord ++ tailWord_526030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526033 : List Nat := [1, 2, 2, 1, 2, 6, 2, 1, 3]
def baseStart_526033 : Nat := 118140960795 + 526033 * 2 ^ 59
def prefixEnd_526033 : Nat := 4983230072969 + 3 ^ 40 * 526033 * 2
def baseEnd_526033 : Nat := 240095794779240557482955

theorem tailTrace_526033 : CollatzResearch.WordTrace tailWord_526033 prefixEnd_526033 240095794779240557482955 := by
  unfold tailWord_526033
  simp only [CollatzResearch.WordTrace]
  refine ⟨19185999703279755129038753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12790666468853170086025835 19185999703279755129038753)
  ·
    refine ⟨14389499777459816346779065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19185999703279755129038753 14389499777459816346779065)
    ·
      refine ⟨10792124833094862260084299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14389499777459816346779065 10792124833094862260084299)
      ·
        refine ⟨16188187249642293390126449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10792124833094862260084299 16188187249642293390126449)
        ·
          refine ⟨12141140437231720042594837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16188187249642293390126449 12141140437231720042594837)
          ·
            refine ⟨569115957995236876996633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12141140437231720042594837 569115957995236876996633)
            ·
              refine ⟨426836968496427657747475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 569115957995236876996633 426836968496427657747475)
              ·
                refine ⟨640255452744641486621213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426836968496427657747475 640255452744641486621213)
                ·
                  refine ⟨240095794779240557482955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 640255452744641486621213 240095794779240557482955)
                  ·
                    rfl

theorem cell20_526033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 3].length) (baseStart_526033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526033 prefixEnd_526033 := by exact prefixLift 526033
  have htrace : WordTrace (prefixWord ++ tailWord_526033) baseStart_526033 baseEnd_526033 := by
    simpa [prefixWord, tailWord_526033, baseEnd_526033] using wordTrace_append hprefix tailTrace_526033
  have hstable : (prefixWord ++ tailWord_526033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526033).length < 2 ^ (prefixWord ++ tailWord_526033).sum := by decide
  have hdescent : baseEnd_526033 < baseStart_526033 := by decide
  rcases family_descends (prefixWord ++ tailWord_526033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526116 : List Nat := [2, 3, 1, 3, 2, 1, 1, 5, 2]
def baseStart_526116 : Nat := 118140960795 + 526116 * 2 ^ 59
def prefixEnd_526116 : Nat := 4983230072969 + 3 ^ 40 * 526116 * 2
def baseEnd_526116 : Nat := 240133678240861157715949

theorem tailTrace_526116 : CollatzResearch.WordTrace tailWord_526116 prefixEnd_526116 240133678240861157715949 := by
  unfold tailWord_526116
  simp only [CollatzResearch.WordTrace]
  refine ⟨9594513480989530152155101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12792684641319373536206801 9594513480989530152155101)
  ·
    refine ⟨3597942555371073807058163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9594513480989530152155101 3597942555371073807058163)
    ·
      refine ⟨5396913833056610710587245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3597942555371073807058163 5396913833056610710587245)
      ·
        refine ⟨2023842687396229016470217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5396913833056610710587245 2023842687396229016470217)
        ·
          refine ⟨1517882015547171762352663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2023842687396229016470217 1517882015547171762352663)
          ·
            refine ⟨2276823023320757643528995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517882015547171762352663 2276823023320757643528995)
            ·
              refine ⟨3415234534981136465293493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276823023320757643528995 3415234534981136465293493)
              ·
                refine ⟨320178237654481543621265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3415234534981136465293493 320178237654481543621265)
                ·
                  refine ⟨240133678240861157715949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320178237654481543621265 240133678240861157715949)
                  ·
                    rfl

theorem cell20_526116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_526116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526116 prefixEnd_526116 := by exact prefixLift 526116
  have htrace : WordTrace (prefixWord ++ tailWord_526116) baseStart_526116 baseEnd_526116 := by
    simpa [prefixWord, tailWord_526116, baseEnd_526116] using wordTrace_append hprefix tailTrace_526116
  have hstable : (prefixWord ++ tailWord_526116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526116).length < 2 ^ (prefixWord ++ tailWord_526116).sum := by decide
  have hdescent : baseEnd_526116 < baseStart_526116 := by decide
  rcases family_descends (prefixWord ++ tailWord_526116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526126 : List Nat := [4, 1, 3, 2, 2, 2, 1, 2, 3]
def baseStart_526126 : Nat := 118140960795 + 526126 * 2 ^ 59
def prefixEnd_526126 : Nat := 4983230072969 + 3 ^ 40 * 526126 * 2
def baseEnd_526126 : Nat := 240138242513345567382575

theorem tailTrace_526126 : CollatzResearch.WordTrace tailWord_526126 prefixEnd_526126 240138242513345567382575 := by
  unfold tailWord_526126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2398673961492854001521779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12792927794628554674782821 2398673961492854001521779)
  ·
    refine ⟨3598010942239281002282669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2398673961492854001521779 3598010942239281002282669)
    ·
      refine ⟨1349254103339730375856001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3598010942239281002282669 1349254103339730375856001)
      ·
        refine ⟨1011940577504797781892001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1349254103339730375856001 1011940577504797781892001)
        ·
          refine ⟨758955433128598336419001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1011940577504797781892001 758955433128598336419001)
          ·
            refine ⟨569216574846448752314251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 758955433128598336419001 569216574846448752314251)
            ·
              refine ⟨853824862269673128471377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569216574846448752314251 853824862269673128471377)
              ·
                refine ⟨640368646702254846353533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 853824862269673128471377 640368646702254846353533)
                ·
                  refine ⟨240138242513345567382575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 640368646702254846353533 240138242513345567382575)
                  ·
                    rfl

theorem cell20_526126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_526126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526126 prefixEnd_526126 := by exact prefixLift 526126
  have htrace : WordTrace (prefixWord ++ tailWord_526126) baseStart_526126 baseEnd_526126 := by
    simpa [prefixWord, tailWord_526126, baseEnd_526126] using wordTrace_append hprefix tailTrace_526126
  have hstable : (prefixWord ++ tailWord_526126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526126).length < 2 ^ (prefixWord ++ tailWord_526126).sum := by decide
  have hdescent : baseEnd_526126 < baseStart_526126 := by decide
  rcases family_descends (prefixWord ++ tailWord_526126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526130 : List Nat := [3, 2, 1, 1, 3, 2, 3, 2, 3]
def baseStart_526130 : Nat := 118140960795 + 526130 * 2 ^ 59
def prefixEnd_526130 : Nat := 4983230072969 + 3 ^ 40 * 526130 * 2
def baseEnd_526130 : Nat := 240140068222339331249225

theorem tailTrace_526130 : CollatzResearch.WordTrace tailWord_526130 prefixEnd_526130 240140068222339331249225 := by
  unfold tailWord_526130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4797384395982085173829961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12793025055952227130213229 4797384395982085173829961)
  ·
    refine ⟨3598038296986563880372471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4797384395982085173829961 3598038296986563880372471)
    ·
      refine ⟨5397057445479845820558707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3598038296986563880372471 5397057445479845820558707)
      ·
        refine ⟨8095586168219768730838061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5397057445479845820558707 8095586168219768730838061)
        ·
          refine ⟨3035844813082413274064273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8095586168219768730838061 3035844813082413274064273)
          ·
            refine ⟨2276883609811809955548205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3035844813082413274064273 2276883609811809955548205)
            ·
              refine ⟨853831353679428733330577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2276883609811809955548205 853831353679428733330577)
              ·
                refine ⟨640373515259571549997933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 853831353679428733330577 640373515259571549997933)
                ·
                  refine ⟨240140068222339331249225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 640373515259571549997933 240140068222339331249225)
                  ·
                    rfl

theorem cell20_526130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_526130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526130 prefixEnd_526130 := by exact prefixLift 526130
  have htrace : WordTrace (prefixWord ++ tailWord_526130) baseStart_526130 baseEnd_526130 := by
    simpa [prefixWord, tailWord_526130, baseEnd_526130] using wordTrace_append hprefix tailTrace_526130
  have hstable : (prefixWord ++ tailWord_526130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526130).length < 2 ^ (prefixWord ++ tailWord_526130).sum := by decide
  have hdescent : baseEnd_526130 < baseStart_526130 := by decide
  rcases family_descends (prefixWord ++ tailWord_526130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526151 : List Nat := [1, 1, 4, 1, 2, 1, 2, 5, 3]
def baseStart_526151 : Nat := 118140960795 + 526151 * 2 ^ 59
def prefixEnd_526151 : Nat := 4983230072969 + 3 ^ 40 * 526151 * 2
def baseEnd_526151 : Nat := 240149653194556591549139

theorem tailTrace_526151 : CollatzResearch.WordTrace tailWord_526151 prefixEnd_526151 240149653194556591549139 := by
  unfold tailWord_526151
  simp only [CollatzResearch.WordTrace]
  refine ⟨19190303516852261281834307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12793535677901507521222871 19190303516852261281834307)
  ·
    refine ⟨28785455275278391922751461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19190303516852261281834307 28785455275278391922751461)
    ·
      refine ⟨5397272864114698485515899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28785455275278391922751461 5397272864114698485515899)
      ·
        refine ⟨8095909296172047728273849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5397272864114698485515899 8095909296172047728273849)
        ·
          refine ⟨6071931972129035796205387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8095909296172047728273849 6071931972129035796205387)
          ·
            refine ⟨9107897958193553694308081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6071931972129035796205387 9107897958193553694308081)
            ·
              refine ⟨6830923468645165270731061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9107897958193553694308081 6830923468645165270731061)
              ·
                refine ⟨640399075185484244131037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6830923468645165270731061 640399075185484244131037)
                ·
                  refine ⟨240149653194556591549139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 640399075185484244131037 240149653194556591549139)
                  ·
                    rfl

theorem cell20_526151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 3].length) (baseStart_526151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526151 prefixEnd_526151 := by exact prefixLift 526151
  have htrace : WordTrace (prefixWord ++ tailWord_526151) baseStart_526151 baseEnd_526151 := by
    simpa [prefixWord, tailWord_526151, baseEnd_526151] using wordTrace_append hprefix tailTrace_526151
  have hstable : (prefixWord ++ tailWord_526151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526151).length < 2 ^ (prefixWord ++ tailWord_526151).sum := by decide
  have hdescent : baseEnd_526151 < baseStart_526151 := by decide
  rcases family_descends (prefixWord ++ tailWord_526151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526161 : List Nat := [1, 2, 2, 1, 5, 3, 2, 4]
def baseStart_526161 : Nat := 118140960795 + 526161 * 2 ^ 59
def prefixEnd_526161 : Nat := 4983230072969 + 3 ^ 40 * 526161 * 2
def baseEnd_526161 : Nat := 80051405822347000405255

theorem tailTrace_526161 : CollatzResearch.WordTrace tailWord_526161 prefixEnd_526161 80051405822347000405255 := by
  unfold tailWord_526161
  simp only [CollatzResearch.WordTrace]
  refine ⟨19190668246816032989698337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12793778831210688659798891 19190668246816032989698337)
  ·
    refine ⟨14393001185112024742273753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19190668246816032989698337 14393001185112024742273753)
    ·
      refine ⟨10794750888834018556705315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14393001185112024742273753 10794750888834018556705315)
      ·
        refine ⟨16192126333251027835057973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10794750888834018556705315 16192126333251027835057973)
        ·
          refine ⟨1518011843742283859536685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16192126333251027835057973 1518011843742283859536685)
          ·
            refine ⟨569254441403356447326257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1518011843742283859536685 569254441403356447326257)
            ·
              refine ⟨426940831052517335494693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 569254441403356447326257 426940831052517335494693)
              ·
                refine ⟨80051405822347000405255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 426940831052517335494693 80051405822347000405255)
                ·
                  rfl

theorem cell20_526161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 4].length) (baseStart_526161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526161 prefixEnd_526161 := by exact prefixLift 526161
  have htrace : WordTrace (prefixWord ++ tailWord_526161) baseStart_526161 baseEnd_526161 := by
    simpa [prefixWord, tailWord_526161, baseEnd_526161] using wordTrace_append hprefix tailTrace_526161
  have hstable : (prefixWord ++ tailWord_526161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526161).length < 2 ^ (prefixWord ++ tailWord_526161).sum := by decide
  have hdescent : baseEnd_526161 < baseStart_526161 := by decide
  rcases family_descends (prefixWord ++ tailWord_526161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526189 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 5]
def baseStart_526189 : Nat := 118140960795 + 526189 * 2 ^ 59
def prefixEnd_526189 : Nat := 4983230072969 + 3 ^ 40 * 526189 * 2
def baseEnd_526189 : Nat := 240166997429997348282317

theorem tailTrace_526189 : CollatzResearch.WordTrace tailWord_526189 prefixEnd_526189 240166997429997348282317 := by
  unfold tailWord_526189
  simp only [CollatzResearch.WordTrace]
  refine ⟨19191689490714593771717621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12794459660476395847811747 19191689490714593771717621)
  ·
    refine ⟨1799220889754493166098527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19191689490714593771717621 1799220889754493166098527)
    ·
      refine ⟨2698831334631739749147791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1799220889754493166098527 2698831334631739749147791)
      ·
        refine ⟨4048247001947609623721687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2698831334631739749147791 4048247001947609623721687)
        ·
          refine ⟨6072370502921414435582531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4048247001947609623721687 6072370502921414435582531)
          ·
            refine ⟨9108555754382121653373797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6072370502921414435582531 9108555754382121653373797)
            ·
              refine ⟨1707854203946647810007587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9108555754382121653373797 1707854203946647810007587)
              ·
                refine ⟨2561781305919971715011381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1707854203946647810007587 2561781305919971715011381)
                ·
                  refine ⟨240166997429997348282317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2561781305919971715011381 240166997429997348282317)
                  ·
                    rfl

theorem cell20_526189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_526189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526189 prefixEnd_526189 := by exact prefixLift 526189
  have htrace : WordTrace (prefixWord ++ tailWord_526189) baseStart_526189 baseEnd_526189 := by
    simpa [prefixWord, tailWord_526189, baseEnd_526189] using wordTrace_append hprefix tailTrace_526189
  have hstable : (prefixWord ++ tailWord_526189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526189).length < 2 ^ (prefixWord ++ tailWord_526189).sum := by decide
  have hdescent : baseEnd_526189 < baseStart_526189 := by decide
  rcases family_descends (prefixWord ++ tailWord_526189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526241 : List Nat := [1, 2, 3, 4, 10]
def baseStart_526241 : Nat := 118140960795 + 526241 * 2 ^ 59
def prefixEnd_526241 : Nat := 4983230072969 + 3 ^ 40 * 526241 * 2
def baseEnd_526241 : Nat := 2965317674653287389491

theorem tailTrace_526241 : CollatzResearch.WordTrace tailWord_526241 prefixEnd_526241 2965317674653287389491 := by
  unfold tailWord_526241
  simp only [CollatzResearch.WordTrace]
  refine ⟨19193586086526206652610577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12795724057684137768407051 19193586086526206652610577)
  ·
    refine ⟨14395189564894654989457933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19193586086526206652610577 14395189564894654989457933)
    ·
      refine ⟨5398196086835495621046725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14395189564894654989457933 5398196086835495621046725)
      ·
        refine ⟨1012161766281655428946261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5398196086835495621046725 1012161766281655428946261)
        ·
          refine ⟨2965317674653287389491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1012161766281655428946261 2965317674653287389491)
          ·
            rfl

theorem cell20_526241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 10].length) (baseStart_526241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526241 prefixEnd_526241 := by exact prefixLift 526241
  have htrace : WordTrace (prefixWord ++ tailWord_526241) baseStart_526241 baseEnd_526241 := by
    simpa [prefixWord, tailWord_526241, baseEnd_526241] using wordTrace_append hprefix tailTrace_526241
  have hstable : (prefixWord ++ tailWord_526241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526241).length < 2 ^ (prefixWord ++ tailWord_526241).sum := by decide
  have hdescent : baseEnd_526241 < baseStart_526241 := by decide
  rcases family_descends (prefixWord ++ tailWord_526241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526244 : List Nat := [2, 3, 1, 2, 1, 4, 2, 2, 3]
def baseStart_526244 : Nat := 118140960795 + 526244 * 2 ^ 59
def prefixEnd_526244 : Nat := 4983230072969 + 3 ^ 40 * 526244 * 2
def baseEnd_526244 : Nat := 240192100928661601448759

theorem tailTrace_526244 : CollatzResearch.WordTrace tailWord_526244 prefixEnd_526244 240192100928661601448759 := by
  unfold tailWord_526244
  simp only [CollatzResearch.WordTrace]
  refine ⟨9596847752757669082484893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12795797003676892109979857 9596847752757669082484893)
  ·
    refine ⟨3598817907284125905931835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9596847752757669082484893 3598817907284125905931835)
    ·
      refine ⟨5398226860926188858897753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3598817907284125905931835 5398226860926188858897753)
      ·
        refine ⟨4048670145694641644173315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5398226860926188858897753 4048670145694641644173315)
        ·
          refine ⟨6073005218541962466259973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4048670145694641644173315 6073005218541962466259973)
          ·
            refine ⟨1138688478476617962423745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6073005218541962466259973 1138688478476617962423745)
            ·
              refine ⟨854016358857463471817809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1138688478476617962423745 854016358857463471817809)
              ·
                refine ⟨640512269143097603863357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 854016358857463471817809 640512269143097603863357)
                ·
                  refine ⟨240192100928661601448759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 640512269143097603863357 240192100928661601448759)
                  ·
                    rfl

theorem cell20_526244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_526244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526244 prefixEnd_526244 := by exact prefixLift 526244
  have htrace : WordTrace (prefixWord ++ tailWord_526244) baseStart_526244 baseEnd_526244 := by
    simpa [prefixWord, tailWord_526244, baseEnd_526244] using wordTrace_append hprefix tailTrace_526244
  have hstable : (prefixWord ++ tailWord_526244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526244).length < 2 ^ (prefixWord ++ tailWord_526244).sum := by decide
  have hdescent : baseEnd_526244 < baseStart_526244 := by decide
  rcases family_descends (prefixWord ++ tailWord_526244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526247 : List Nat := [1, 1, 6, 1, 2, 1, 4, 2, 2]
def baseStart_526247 : Nat := 118140960795 + 526247 * 2 ^ 59
def prefixEnd_526247 : Nat := 4983230072969 + 3 ^ 40 * 526247 * 2
def baseEnd_526247 : Nat := 240193470210406924348747

theorem tailTrace_526247 : CollatzResearch.WordTrace tailWord_526247 prefixEnd_526247 240193470210406924348747 := by
  unfold tailWord_526247
  simp only [CollatzResearch.WordTrace]
  refine ⟨19193804924504469677328995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12795869949669646451552663 19193804924504469677328995)
  ·
    refine ⟨28790707386756704515993493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19193804924504469677328995 28790707386756704515993493)
    ·
      refine ⟨1349564408754220524187195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28790707386756704515993493 1349564408754220524187195)
      ·
        refine ⟨2024346613131330786280793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1349564408754220524187195 2024346613131330786280793)
        ·
          refine ⟨1518259959848498089710595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2024346613131330786280793 1518259959848498089710595)
          ·
            refine ⟨2277389939772747134565893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1518259959848498089710595 2277389939772747134565893)
            ·
              refine ⟨427010613707390087731105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2277389939772747134565893 427010613707390087731105)
              ·
                refine ⟨320257960280542565798329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427010613707390087731105 320257960280542565798329)
                ·
                  refine ⟨240193470210406924348747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320257960280542565798329 240193470210406924348747)
                  ·
                    rfl

theorem cell20_526247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 2].length) (baseStart_526247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526247 prefixEnd_526247 := by exact prefixLift 526247
  have htrace : WordTrace (prefixWord ++ tailWord_526247) baseStart_526247 baseEnd_526247 := by
    simpa [prefixWord, tailWord_526247, baseEnd_526247] using wordTrace_append hprefix tailTrace_526247
  have hstable : (prefixWord ++ tailWord_526247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526247).length < 2 ^ (prefixWord ++ tailWord_526247).sum := by decide
  have hdescent : baseEnd_526247 < baseStart_526247 := by decide
  rcases family_descends (prefixWord ++ tailWord_526247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526265 : List Nat := [1, 2, 1, 4, 2, 1, 1, 5, 3]
def baseStart_526265 : Nat := 118140960795 + 526265 * 2 ^ 59
def prefixEnd_526265 : Nat := 4983230072969 + 3 ^ 40 * 526265 * 2
def baseEnd_526265 : Nat := 240201685900878861748673

theorem tailTrace_526265 : CollatzResearch.WordTrace tailWord_526265 prefixEnd_526265 240201685900878861748673 := by
  unfold tailWord_526265
  simp only [CollatzResearch.WordTrace]
  refine ⟨19194461438439258751484249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12796307625626172500989499 19194461438439258751484249)
  ·
    refine ⟨14395846078829444063613187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19194461438439258751484249 14395846078829444063613187)
    ·
      refine ⟨21593769118244166095419781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14395846078829444063613187 21593769118244166095419781)
      ·
        refine ⟨4048831709670781142891209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21593769118244166095419781 4048831709670781142891209)
        ·
          refine ⟨3036623782253085857168407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4048831709670781142891209 3036623782253085857168407)
          ·
            refine ⟨4554935673379628785752611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3036623782253085857168407 4554935673379628785752611)
            ·
              refine ⟨6832403510069443178628917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4554935673379628785752611 6832403510069443178628917)
              ·
                refine ⟨640537829069010297996461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6832403510069443178628917 640537829069010297996461)
                ·
                  refine ⟨240201685900878861748673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 640537829069010297996461 240201685900878861748673)
                  ·
                    rfl

theorem cell20_526265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_526265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526265 prefixEnd_526265 := by exact prefixLift 526265
  have htrace : WordTrace (prefixWord ++ tailWord_526265) baseStart_526265 baseEnd_526265 := by
    simpa [prefixWord, tailWord_526265, baseEnd_526265] using wordTrace_append hprefix tailTrace_526265
  have hstable : (prefixWord ++ tailWord_526265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526265).length < 2 ^ (prefixWord ++ tailWord_526265).sum := by decide
  have hdescent : baseEnd_526265 < baseStart_526265 := by decide
  rcases family_descends (prefixWord ++ tailWord_526265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526268 : List Nat := [2, 2, 2, 5, 1, 1, 1, 2, 4]
def baseStart_526268 : Nat := 118140960795 + 526268 * 2 ^ 59
def prefixEnd_526268 : Nat := 4983230072969 + 3 ^ 40 * 526268 * 2
def baseEnd_526268 : Nat := 240203055182624184648661

theorem tailTrace_526268 : CollatzResearch.WordTrace tailWord_526268 prefixEnd_526268 240203055182624184648661 := by
  unfold tailWord_526268
  simp only [CollatzResearch.WordTrace]
  refine ⟨9597285428714195131921729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12796380571618926842562305 9597285428714195131921729)
  ·
    refine ⟨7197964071535646348941297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9597285428714195131921729 7197964071535646348941297)
    ·
      refine ⟨5398473053651734761705973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7197964071535646348941297 5398473053651734761705973)
      ·
        refine ⟨506106848779850133909935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5398473053651734761705973 506106848779850133909935)
        ·
          refine ⟨759160273169775200864903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506106848779850133909935 759160273169775200864903)
          ·
            refine ⟨1138740409754662801297355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759160273169775200864903 1138740409754662801297355)
            ·
              refine ⟨1708110614631994201946033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138740409754662801297355 1708110614631994201946033)
              ·
                refine ⟨1281082960973995651459525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1708110614631994201946033 1281082960973995651459525)
                ·
                  refine ⟨240203055182624184648661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1281082960973995651459525 240203055182624184648661)
                  ·
                    rfl

theorem cell20_526268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_526268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526268 prefixEnd_526268 := by exact prefixLift 526268
  have htrace : WordTrace (prefixWord ++ tailWord_526268) baseStart_526268 baseEnd_526268 := by
    simpa [prefixWord, tailWord_526268, baseEnd_526268] using wordTrace_append hprefix tailTrace_526268
  have hstable : (prefixWord ++ tailWord_526268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526268).length < 2 ^ (prefixWord ++ tailWord_526268).sum := by decide
  have hdescent : baseEnd_526268 < baseStart_526268 := by decide
  rcases family_descends (prefixWord ++ tailWord_526268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526272 : List Nat := [2, 1, 1, 2, 3, 2, 3, 2, 4]
def baseStart_526272 : Nat := 118140960795 + 526272 * 2 ^ 59
def prefixEnd_526272 : Nat := 4983230072969 + 3 ^ 40 * 526272 * 2
def baseEnd_526272 : Nat := 240204880891617948515311

theorem tailTrace_526272 : CollatzResearch.WordTrace tailWord_526272 prefixEnd_526272 240204880891617948515311 := by
  unfold tailWord_526272
  simp only [CollatzResearch.WordTrace]
  refine ⟨9597358374706949473494535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12796477832942599297992713 9597358374706949473494535)
  ·
    refine ⟨14396037562060424210241803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9597358374706949473494535 14396037562060424210241803)
    ·
      refine ⟨21594056343090636315362705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14396037562060424210241803 21594056343090636315362705)
      ·
        refine ⟨16195542257317977236522029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21594056343090636315362705 16195542257317977236522029)
        ·
          refine ⟨6073328346494241463695761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16195542257317977236522029 6073328346494241463695761)
          ·
            refine ⟨4554996259870681097771821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6073328346494241463695761 4554996259870681097771821)
            ·
              refine ⟨1708123597451505411664433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4554996259870681097771821 1708123597451505411664433)
              ·
                refine ⟨1281092698088629058748325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1708123597451505411664433 1281092698088629058748325)
                ·
                  refine ⟨240204880891617948515311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1281092698088629058748325 240204880891617948515311)
                  ·
                    rfl

theorem cell20_526272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_526272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526272 prefixEnd_526272 := by exact prefixLift 526272
  have htrace : WordTrace (prefixWord ++ tailWord_526272) baseStart_526272 baseEnd_526272 := by
    simpa [prefixWord, tailWord_526272, baseEnd_526272] using wordTrace_append hprefix tailTrace_526272
  have hstable : (prefixWord ++ tailWord_526272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526272).length < 2 ^ (prefixWord ++ tailWord_526272).sum := by decide
  have hdescent : baseEnd_526272 < baseStart_526272 := by decide
  rcases family_descends (prefixWord ++ tailWord_526272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526303 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 5]
def baseStart_526303 : Nat := 118140960795 + 526303 * 2 ^ 59
def prefixEnd_526303 : Nat := 4983230072969 + 3 ^ 40 * 526303 * 2
def baseEnd_526303 : Nat := 240219030136319618481851

theorem tailTrace_526303 : CollatzResearch.WordTrace tailWord_526303 prefixEnd_526303 240219030136319618481851 := by
  unfold tailWord_526303
  simp only [CollatzResearch.WordTrace]
  refine ⟨19195847412301591241367563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12797231608201060827578375 19195847412301591241367563)
  ·
    refine ⟨28793771118452386862051345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19195847412301591241367563 28793771118452386862051345)
    ·
      refine ⟨21595328338839290146538509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28793771118452386862051345 21595328338839290146538509)
      ·
        refine ⟨8098248127064733804951941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21595328338839290146538509 8098248127064733804951941)
        ·
          refine ⟨1518421523824637588428489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8098248127064733804951941 1518421523824637588428489)
          ·
            refine ⟨1138816142868478191321367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1518421523824637588428489 1138816142868478191321367)
            ·
              refine ⟨1708224214302717286982051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138816142868478191321367 1708224214302717286982051)
              ·
                refine ⟨2562336321454075930473077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1708224214302717286982051 2562336321454075930473077)
                ·
                  refine ⟨240219030136319618481851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2562336321454075930473077 240219030136319618481851)
                  ·
                    rfl

theorem cell20_526303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 5].length) (baseStart_526303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526303 prefixEnd_526303 := by exact prefixLift 526303
  have htrace : WordTrace (prefixWord ++ tailWord_526303) baseStart_526303 baseEnd_526303 := by
    simpa [prefixWord, tailWord_526303, baseEnd_526303] using wordTrace_append hprefix tailTrace_526303
  have hstable : (prefixWord ++ tailWord_526303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526303).length < 2 ^ (prefixWord ++ tailWord_526303).sum := by decide
  have hdescent : baseEnd_526303 < baseStart_526303 := by decide
  rcases family_descends (prefixWord ++ tailWord_526303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526340 : List Nat := [2, 3, 2, 4, 1, 2, 1, 3, 2]
def baseStart_526340 : Nat := 118140960795 + 526340 * 2 ^ 59
def prefixEnd_526340 : Nat := 4983230072969 + 3 ^ 40 * 526340 * 2
def baseEnd_526340 : Nat := 240235917944511934248367

theorem tailTrace_526340 : CollatzResearch.WordTrace tailWord_526340 prefixEnd_526340 240235917944511934248367 := by
  unfold tailWord_526340
  simp only [CollatzResearch.WordTrace]
  refine ⟨9598598456583773280232237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12798131275445031040309649 9598598456583773280232237)
  ·
    refine ⟨3599474421218914980087089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9598598456583773280232237 3599474421218914980087089)
    ·
      refine ⟨2699605815914186235065317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3599474421218914980087089 2699605815914186235065317)
      ·
        refine ⟨506176090483909919074747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2699605815914186235065317 506176090483909919074747)
        ·
          refine ⟨759264135725864878612121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506176090483909919074747 759264135725864878612121)
          ·
            refine ⟨569448101794398658959091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 759264135725864878612121 569448101794398658959091)
            ·
              refine ⟨854172152691597988438637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569448101794398658959091 854172152691597988438637)
              ·
                refine ⟨320314557259349245664489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 854172152691597988438637 320314557259349245664489)
                ·
                  refine ⟨240235917944511934248367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320314557259349245664489 240235917944511934248367)
                  ·
                    rfl

theorem cell20_526340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_526340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526340 prefixEnd_526340 := by exact prefixLift 526340
  have htrace : WordTrace (prefixWord ++ tailWord_526340) baseStart_526340 baseEnd_526340 := by
    simpa [prefixWord, tailWord_526340, baseEnd_526340] using wordTrace_append hprefix tailTrace_526340
  have hstable : (prefixWord ++ tailWord_526340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526340).length < 2 ^ (prefixWord ++ tailWord_526340).sum := by decide
  have hdescent : baseEnd_526340 < baseStart_526340 := by decide
  rcases family_descends (prefixWord ++ tailWord_526340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526365 : List Nat := [1, 4, 2, 2, 2, 1, 3, 1, 4]
def baseStart_526365 : Nat := 118140960795 + 526365 * 2 ^ 59
def prefixEnd_526365 : Nat := 4983230072969 + 3 ^ 40 * 526365 * 2
def baseEnd_526365 : Nat := 240247328625722958414931

theorem tailTrace_526365 : CollatzResearch.WordTrace tailWord_526365 prefixEnd_526365 240247328625722958414931 := by
  unfold tailWord_526365
  simp only [CollatzResearch.WordTrace]
  refine ⟨19198108738076975830124549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12798739158717983886749699 19198108738076975830124549)
  ·
    refine ⟨3599645388389432968148353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19198108738076975830124549 3599645388389432968148353)
    ·
      refine ⟨2699734041292074726111265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3599645388389432968148353 2699734041292074726111265)
      ·
        refine ⟨2024800530969056044583449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2699734041292074726111265 2024800530969056044583449)
        ·
          refine ⟨1518600398226792033437587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2024800530969056044583449 1518600398226792033437587)
          ·
            refine ⟨2277900597340188050156381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1518600398226792033437587 2277900597340188050156381)
            ·
              refine ⟨854212724002570518808643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2277900597340188050156381 854212724002570518808643)
              ·
                refine ⟨1281319086003855778212965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854212724002570518808643 1281319086003855778212965)
                ·
                  refine ⟨240247328625722958414931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1281319086003855778212965 240247328625722958414931)
                  ·
                    rfl

theorem cell20_526365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_526365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526365 prefixEnd_526365 := by exact prefixLift 526365
  have htrace : WordTrace (prefixWord ++ tailWord_526365) baseStart_526365 baseEnd_526365 := by
    simpa [prefixWord, tailWord_526365, baseEnd_526365] using wordTrace_append hprefix tailTrace_526365
  have hstable : (prefixWord ++ tailWord_526365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526365).length < 2 ^ (prefixWord ++ tailWord_526365).sum := by decide
  have hdescent : baseEnd_526365 < baseStart_526365 := by decide
  rcases family_descends (prefixWord ++ tailWord_526365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526375 : List Nat := [1, 1, 7, 1, 2, 1, 1, 3, 3]
def baseStart_526375 : Nat := 118140960795 + 526375 * 2 ^ 59
def prefixEnd_526375 : Nat := 4983230072969 + 3 ^ 40 * 526375 * 2
def baseEnd_526375 : Nat := 240251892898207368081557

theorem tailTrace_526375 : CollatzResearch.WordTrace tailWord_526375 prefixEnd_526375 240251892898207368081557 := by
  unfold tailWord_526375
  simp only [CollatzResearch.WordTrace]
  refine ⟨19198473468040747537988579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12798982312027165025325719 19198473468040747537988579)
  ·
    refine ⟨28797710202061121306982869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19198473468040747537988579 28797710202061121306982869)
    ·
      refine ⟨674946332860807530632411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 28797710202061121306982869 674946332860807530632411)
      ·
        refine ⟨1012419499291211295948617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674946332860807530632411 1012419499291211295948617)
        ·
          refine ⟨759314624468408471961463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1012419499291211295948617 759314624468408471961463)
          ·
            refine ⟨1138971936702612707942195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759314624468408471961463 1138971936702612707942195)
            ·
              refine ⟨1708457905053919061913293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138971936702612707942195 1708457905053919061913293)
              ·
                refine ⟨640671714395219648217485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1708457905053919061913293 640671714395219648217485)
                ·
                  refine ⟨240251892898207368081557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 640671714395219648217485 240251892898207368081557)
                  ·
                    rfl

theorem cell20_526375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 3].length) (baseStart_526375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526375 prefixEnd_526375 := by exact prefixLift 526375
  have htrace : WordTrace (prefixWord ++ tailWord_526375) baseStart_526375 baseEnd_526375 := by
    simpa [prefixWord, tailWord_526375, baseEnd_526375] using wordTrace_append hprefix tailTrace_526375
  have hstable : (prefixWord ++ tailWord_526375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526375).length < 2 ^ (prefixWord ++ tailWord_526375).sum := by decide
  have hdescent : baseEnd_526375 < baseStart_526375 := by decide
  rcases family_descends (prefixWord ++ tailWord_526375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526448 : List Nat := [2, 1, 1, 1, 5, 3, 3, 4]
def baseStart_526448 : Nat := 118140960795 + 526448 * 2 ^ 59
def prefixEnd_526448 : Nat := 4983230072969 + 3 ^ 40 * 526448 * 2
def baseEnd_526448 : Nat := 80095070695781186215975

theorem tailTrace_526448 : CollatzResearch.WordTrace tailWord_526448 prefixEnd_526448 80095070695781186215975 := by
  unfold tailWord_526448
  simp only [CollatzResearch.WordTrace]
  refine ⟨9600567998388140502697999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12800757331184187336930665 9600567998388140502697999)
  ·
    refine ⟨14400851997582210754046999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9600567998388140502697999 14400851997582210754046999)
    ·
      refine ⟨21601277996373316131070499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14400851997582210754046999 21601277996373316131070499)
      ·
        refine ⟨32401916994559974196605749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21601277996373316131070499 32401916994559974196605749)
        ·
          refine ⟨3037679718239997580931789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32401916994559974196605749 3037679718239997580931789)
          ·
            refine ⟨1139129894339999092849421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3037679718239997580931789 1139129894339999092849421)
            ·
              refine ⟨427173710377499659818533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1139129894339999092849421 427173710377499659818533)
              ·
                refine ⟨80095070695781186215975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 427173710377499659818533 80095070695781186215975)
                ·
                  rfl

theorem cell20_526448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 4].length) (baseStart_526448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526448 prefixEnd_526448 := by exact prefixLift 526448
  have htrace : WordTrace (prefixWord ++ tailWord_526448) baseStart_526448 baseEnd_526448 := by
    simpa [prefixWord, tailWord_526448, baseEnd_526448] using wordTrace_append hprefix tailTrace_526448
  have hstable : (prefixWord ++ tailWord_526448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526448).length < 2 ^ (prefixWord ++ tailWord_526448).sum := by decide
  have hdescent : baseEnd_526448 < baseStart_526448 := by decide
  rcases family_descends (prefixWord ++ tailWord_526448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526469 : List Nat := [1, 3, 1, 1, 5, 2, 7]
def baseStart_526469 : Nat := 118140960795 + 526469 * 2 ^ 59
def prefixEnd_526469 : Nat := 4983230072969 + 3 ^ 40 * 526469 * 2
def baseEnd_526469 : Nat := 26699421895506757660871

theorem tailTrace_526469 : CollatzResearch.WordTrace tailWord_526469 prefixEnd_526469 26699421895506757660871 := by
  unfold tailWord_526469
  simp only [CollatzResearch.WordTrace]
  refine ⟨19201901929700201591910461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12801267953133467727940307 19201901929700201591910461)
  ·
    refine ⟨7200713223637575596966423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19201901929700201591910461 7200713223637575596966423)
    ·
      refine ⟨10801069835456363395449635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7200713223637575596966423 10801069835456363395449635)
      ·
        refine ⟨16201604753184545093174453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10801069835456363395449635 16201604753184545093174453)
        ·
          refine ⟨1518900445611051102485105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16201604753184545093174453 1518900445611051102485105)
          ·
            refine ⟨1139175334208288326863829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1518900445611051102485105 1139175334208288326863829)
            ·
              refine ⟨26699421895506757660871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1139175334208288326863829 26699421895506757660871)
              ·
                rfl

theorem cell20_526469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 7].length) (baseStart_526469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526469 prefixEnd_526469 := by exact prefixLift 526469
  have htrace : WordTrace (prefixWord ++ tailWord_526469) baseStart_526469 baseEnd_526469 := by
    simpa [prefixWord, tailWord_526469, baseEnd_526469] using wordTrace_append hprefix tailTrace_526469
  have hstable : (prefixWord ++ tailWord_526469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526469).length < 2 ^ (prefixWord ++ tailWord_526469).sum := by decide
  have hdescent : baseEnd_526469 < baseStart_526469 := by decide
  rcases family_descends (prefixWord ++ tailWord_526469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526472 : List Nat := [2, 1, 3, 4, 1, 1, 3, 2, 3]
def baseStart_526472 : Nat := 118140960795 + 526472 * 2 ^ 59
def prefixEnd_526472 : Nat := 4983230072969 + 3 ^ 40 * 526472 * 2
def baseEnd_526472 : Nat := 240296166341306141847827

theorem tailTrace_526472 : CollatzResearch.WordTrace tailWord_526472 prefixEnd_526472 240296166341306141847827 := by
  unfold tailWord_526472
  simp only [CollatzResearch.WordTrace]
  refine ⟨9601005674344666552134835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12801340899126222069513113 9601005674344666552134835)
  ·
    refine ⟨14401508511516999828202253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9601005674344666552134835 14401508511516999828202253)
    ·
      refine ⟨5400565691818874935575845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14401508511516999828202253 5400565691818874935575845)
      ·
        refine ⟨1012606067216039050420471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5400565691818874935575845 1012606067216039050420471)
        ·
          refine ⟨1518909100824058575630707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1012606067216039050420471 1518909100824058575630707)
          ·
            refine ⟨2278363651236087863446061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1518909100824058575630707 2278363651236087863446061)
            ·
              refine ⟨854386369213532948792273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2278363651236087863446061 854386369213532948792273)
              ·
                refine ⟨640789776910149711594205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 854386369213532948792273 640789776910149711594205)
                ·
                  refine ⟨240296166341306141847827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 640789776910149711594205 240296166341306141847827)
                  ·
                    rfl

theorem cell20_526472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_526472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526472 prefixEnd_526472 := by exact prefixLift 526472
  have htrace : WordTrace (prefixWord ++ tailWord_526472) baseStart_526472 baseEnd_526472 := by
    simpa [prefixWord, tailWord_526472, baseEnd_526472] using wordTrace_append hprefix tailTrace_526472
  have hstable : (prefixWord ++ tailWord_526472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526472).length < 2 ^ (prefixWord ++ tailWord_526472).sum := by decide
  have hdescent : baseEnd_526472 < baseStart_526472 := by decide
  rcases family_descends (prefixWord ++ tailWord_526472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526513 : List Nat := [1, 2, 2, 5, 2, 2, 1, 3, 2]
def baseStart_526513 : Nat := 118140960795 + 526513 * 2 ^ 59
def prefixEnd_526513 : Nat := 4983230072969 + 3 ^ 40 * 526513 * 2
def baseEnd_526513 : Nat := 240314879858492221480993

theorem tailTrace_526513 : CollatzResearch.WordTrace tailWord_526513 prefixEnd_526513 240314879858492221480993 := by
  unfold tailWord_526513
  simp only [CollatzResearch.WordTrace]
  refine ⟨19203506741540797106512193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12802337827693864737674795 19203506741540797106512193)
  ·
    refine ⟨14402630056155597829884145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19203506741540797106512193 14402630056155597829884145)
    ·
      refine ⟨10801972542116698372413109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14402630056155597829884145 10801972542116698372413109)
      ·
        refine ⟨1012684925823440472413729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10801972542116698372413109 1012684925823440472413729)
        ·
          refine ⟨759513694367580354310297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1012684925823440472413729 759513694367580354310297)
          ·
            refine ⟨569635270775685265732723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 759513694367580354310297 569635270775685265732723)
            ·
              refine ⟨854452906163527898599085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569635270775685265732723 854452906163527898599085)
              ·
                refine ⟨320419839811322961974657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 854452906163527898599085 320419839811322961974657)
                ·
                  refine ⟨240314879858492221480993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320419839811322961974657 240314879858492221480993)
                  ·
                    rfl

theorem cell20_526513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 2].length) (baseStart_526513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526513 prefixEnd_526513 := by exact prefixLift 526513
  have htrace : WordTrace (prefixWord ++ tailWord_526513) baseStart_526513 baseEnd_526513 := by
    simpa [prefixWord, tailWord_526513, baseEnd_526513] using wordTrace_append hprefix tailTrace_526513
  have hstable : (prefixWord ++ tailWord_526513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526513).length < 2 ^ (prefixWord ++ tailWord_526513).sum := by decide
  have hdescent : baseEnd_526513 < baseStart_526513 := by decide
  rcases family_descends (prefixWord ++ tailWord_526513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526514 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_526514 : Nat := 118140960795 + 526514 * 2 ^ 59
def prefixEnd_526514 : Nat := 4983230072969 + 3 ^ 40 * 526514 * 2
def baseEnd_526514 : Nat := 240315336285740662447655

theorem tailTrace_526514 : CollatzResearch.WordTrace tailWord_526514 prefixEnd_526514 240315336285740662447655 := by
  unfold tailWord_526514
  simp only [CollatzResearch.WordTrace]
  refine ⟨4800885803634293569324649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12802362143024782851532397 4800885803634293569324649)
  ·
    refine ⟨3600664352725720176993487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4800885803634293569324649 3600664352725720176993487)
    ·
      refine ⟨5400996529088580265490231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3600664352725720176993487 5400996529088580265490231)
      ·
        refine ⟨8101494793632870398235347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5400996529088580265490231 8101494793632870398235347)
        ·
          refine ⟨12152242190449305597353021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8101494793632870398235347 12152242190449305597353021)
          ·
            refine ⟨4557090821418489599007383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12152242190449305597353021 4557090821418489599007383)
            ·
              refine ⟨6835636232127734398511075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4557090821418489599007383 6835636232127734398511075)
              ·
                refine ⟨10253454348191601597766613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6835636232127734398511075 10253454348191601597766613)
                ·
                  refine ⟨240315336285740662447655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10253454348191601597766613 240315336285740662447655)
                  ·
                    rfl

theorem cell20_526514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_526514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526514 prefixEnd_526514 := by exact prefixLift 526514
  have htrace : WordTrace (prefixWord ++ tailWord_526514) baseStart_526514 baseEnd_526514 := by
    simpa [prefixWord, tailWord_526514, baseEnd_526514] using wordTrace_append hprefix tailTrace_526514
  have hstable : (prefixWord ++ tailWord_526514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526514).length < 2 ^ (prefixWord ++ tailWord_526514).sum := by decide
  have hdescent : baseEnd_526514 < baseStart_526514 := by decide
  rcases family_descends (prefixWord ++ tailWord_526514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526524 : List Nat := [2, 2, 2, 3, 3, 2, 6]
def baseStart_526524 : Nat := 118140960795 + 526524 * 2 ^ 59
def prefixEnd_526524 : Nat := 4983230072969 + 3 ^ 40 * 526524 * 2
def baseEnd_526524 : Nat := 26702211173136119123809

theorem tailTrace_526524 : CollatzResearch.WordTrace tailWord_526524 prefixEnd_526524 26702211173136119123809 := by
  unfold tailWord_526524
  simp only [CollatzResearch.WordTrace]
  refine ⟨9601953972250472992581313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12802605296333963990108417 9601953972250472992581313)
  ·
    refine ⟨7201465479187854744435985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9601953972250472992581313 7201465479187854744435985)
    ·
      refine ⟨5401099109390891058326989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7201465479187854744435985 5401099109390891058326989)
      ·
        refine ⟨2025412166021584146872621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5401099109390891058326989 2025412166021584146872621)
        ·
          refine ⟨759529562258094055077233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2025412166021584146872621 759529562258094055077233)
          ·
            refine ⟨569647171693570541307925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 759529562258094055077233 569647171693570541307925)
            ·
              refine ⟨26702211173136119123809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 569647171693570541307925 26702211173136119123809)
              ·
                rfl

theorem cell20_526524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 6].length) (baseStart_526524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526524 prefixEnd_526524 := by exact prefixLift 526524
  have htrace : WordTrace (prefixWord ++ tailWord_526524) baseStart_526524 baseEnd_526524 := by
    simpa [prefixWord, tailWord_526524, baseEnd_526524] using wordTrace_append hprefix tailTrace_526524
  have hstable : (prefixWord ++ tailWord_526524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526524).length < 2 ^ (prefixWord ++ tailWord_526524).sum := by decide
  have hdescent : baseEnd_526524 < baseStart_526524 := by decide
  rcases family_descends (prefixWord ++ tailWord_526524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526559 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 6]
def baseStart_526559 : Nat := 118140960795 + 526559 * 2 ^ 59
def prefixEnd_526559 : Nat := 4983230072969 + 3 ^ 40 * 526559 * 2
def baseEnd_526559 : Nat := 240335875511920505947471

theorem tailTrace_526559 : CollatzResearch.WordTrace tailWord_526559 prefixEnd_526559 240335875511920505947471 := by
  unfold tailWord_526559
  simp only [CollatzResearch.WordTrace]
  refine ⟨19205184499374146962686731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12803456332916097975124487 19205184499374146962686731)
  ·
    refine ⟨28807776749061220444030097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19205184499374146962686731 28807776749061220444030097)
    ·
      refine ⟨21605832561795915333022573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28807776749061220444030097 21605832561795915333022573)
      ·
        refine ⟨8102187210673468249883465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21605832561795915333022573 8102187210673468249883465)
        ·
          refine ⟨6076640408005101187412599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8102187210673468249883465 6076640408005101187412599)
          ·
            refine ⟨9114960612007651781118899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6076640408005101187412599 9114960612007651781118899)
            ·
              refine ⟨13672440918011477671678349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9114960612007651781118899 13672440918011477671678349)
              ·
                refine ⟨5127165344254304126879381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13672440918011477671678349 5127165344254304126879381)
                ·
                  refine ⟨240335875511920505947471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5127165344254304126879381 240335875511920505947471)
                  ·
                    rfl

theorem cell20_526559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_526559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526559 prefixEnd_526559 := by exact prefixLift 526559
  have htrace : WordTrace (prefixWord ++ tailWord_526559) baseStart_526559 baseEnd_526559 := by
    simpa [prefixWord, tailWord_526559, baseEnd_526559] using wordTrace_append hprefix tailTrace_526559
  have hstable : (prefixWord ++ tailWord_526559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526559).length < 2 ^ (prefixWord ++ tailWord_526559).sum := by decide
  have hdescent : baseEnd_526559 < baseStart_526559 := by decide
  rcases family_descends (prefixWord ++ tailWord_526559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526593 : List Nat := [1, 2, 4, 1, 1, 2, 3, 4, 2]
def baseStart_526593 : Nat := 118140960795 + 526593 * 2 ^ 59
def prefixEnd_526593 : Nat := 4983230072969 + 3 ^ 40 * 526593 * 2
def baseEnd_526593 : Nat := 240351394038367498813999

theorem tailTrace_526593 : CollatzResearch.WordTrace tailWord_526593 prefixEnd_526593 240351394038367498813999 := by
  unfold tailWord_526593
  simp only [CollatzResearch.WordTrace]
  refine ⟨19206424581250970769424433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12804283054167313846282955 19206424581250970769424433)
  ·
    refine ⟨14404818435938228077068325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19206424581250970769424433 14404818435938228077068325)
    ·
      refine ⟨2700903456738417764450311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14404818435938228077068325 2700903456738417764450311)
      ·
        refine ⟨4051355185107626646675467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2700903456738417764450311 4051355185107626646675467)
        ·
          refine ⟨6077032777661439970013201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4051355185107626646675467 6077032777661439970013201)
          ·
            refine ⟨4557774583246079977509901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6077032777661439970013201 4557774583246079977509901)
            ·
              refine ⟨1709165468717279991566213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4557774583246079977509901 1709165468717279991566213)
              ·
                refine ⟨320468525384489998418665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1709165468717279991566213 320468525384489998418665)
                ·
                  refine ⟨240351394038367498813999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320468525384489998418665 240351394038367498813999)
                  ·
                    rfl

theorem cell20_526593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 2].length) (baseStart_526593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526593 prefixEnd_526593 := by exact prefixLift 526593
  have htrace : WordTrace (prefixWord ++ tailWord_526593) baseStart_526593 baseEnd_526593 := by
    simpa [prefixWord, tailWord_526593, baseEnd_526593] using wordTrace_append hprefix tailTrace_526593
  have hstable : (prefixWord ++ tailWord_526593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526593).length < 2 ^ (prefixWord ++ tailWord_526593).sum := by decide
  have hdescent : baseEnd_526593 < baseStart_526593 := by decide
  rcases family_descends (prefixWord ++ tailWord_526593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526600 : List Nat := [2, 1, 3, 2, 3, 3, 1, 5]
def baseStart_526600 : Nat := 118140960795 + 526600 * 2 ^ 59
def prefixEnd_526600 : Nat := 4983230072969 + 3 ^ 40 * 526600 * 2
def baseEnd_526600 : Nat := 80118196343035528526879

theorem tailTrace_526600 : CollatzResearch.WordTrace tailWord_526600 prefixEnd_526600 80118196343035528526879 := by
  unfold tailWord_526600
  simp only [CollatzResearch.WordTrace]
  refine ⟨9603339946112805482464627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12804453261483740643286169 9603339946112805482464627)
  ·
    refine ⟨14405009919169208223696941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9603339946112805482464627 14405009919169208223696941)
    ·
      refine ⟨5401878719688453083886353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14405009919169208223696941 5401878719688453083886353)
      ·
        refine ⟨4051409039766339812914765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5401878719688453083886353 4051409039766339812914765)
        ·
          refine ⟨1519278389912377429843037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4051409039766339812914765 1519278389912377429843037)
          ·
            refine ⟨569729396217141536191139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1519278389912377429843037 569729396217141536191139)
            ·
              refine ⟨854594094325712304286709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569729396217141536191139 854594094325712304286709)
              ·
                refine ⟨80118196343035528526879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 854594094325712304286709 80118196343035528526879)
                ·
                  rfl

theorem cell20_526600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 5].length) (baseStart_526600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526600 prefixEnd_526600 := by exact prefixLift 526600
  have htrace : WordTrace (prefixWord ++ tailWord_526600) baseStart_526600 baseEnd_526600 := by
    simpa [prefixWord, tailWord_526600, baseEnd_526600] using wordTrace_append hprefix tailTrace_526600
  have hstable : (prefixWord ++ tailWord_526600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526600).length < 2 ^ (prefixWord ++ tailWord_526600).sum := by decide
  have hdescent : baseEnd_526600 < baseStart_526600 := by decide
  rcases family_descends (prefixWord ++ tailWord_526600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526641 : List Nat := [1, 2, 2, 3, 5, 1, 1, 2, 3]
def baseStart_526641 : Nat := 118140960795 + 526641 * 2 ^ 59
def prefixEnd_526641 : Nat := 4983230072969 + 3 ^ 40 * 526641 * 2
def baseEnd_526641 : Nat := 240373302546292665213803

theorem tailTrace_526641 : CollatzResearch.WordTrace tailWord_526641 prefixEnd_526641 240373302546292665213803 := by
  unfold tailWord_526641
  simp only [CollatzResearch.WordTrace]
  refine ⟨19208175285077074967171777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12805450190051383311447851 19208175285077074967171777)
  ·
    refine ⟨14406131463807806225378833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19208175285077074967171777 14406131463807806225378833)
    ·
      refine ⟨10804598597855854669034125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14406131463807806225378833 10804598597855854669034125)
      ·
        refine ⟨4051724474195945500887797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10804598597855854669034125 4051724474195945500887797)
        ·
          refine ⟨379849169455869890708231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4051724474195945500887797 379849169455869890708231)
          ·
            refine ⟨569773754183804836062347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379849169455869890708231 569773754183804836062347)
            ·
              refine ⟨854660631275707254093521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569773754183804836062347 854660631275707254093521)
              ·
                refine ⟨640995473456780440570141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 854660631275707254093521 640995473456780440570141)
                ·
                  refine ⟨240373302546292665213803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 640995473456780440570141 240373302546292665213803)
                  ·
                    rfl

theorem cell20_526641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 3].length) (baseStart_526641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526641 prefixEnd_526641 := by exact prefixLift 526641
  have htrace : WordTrace (prefixWord ++ tailWord_526641) baseStart_526641 baseEnd_526641 := by
    simpa [prefixWord, tailWord_526641, baseEnd_526641] using wordTrace_append hprefix tailTrace_526641
  have hstable : (prefixWord ++ tailWord_526641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526641).length < 2 ^ (prefixWord ++ tailWord_526641).sum := by decide
  have hdescent : baseEnd_526641 < baseStart_526641 := by decide
  rcases family_descends (prefixWord ++ tailWord_526641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526652 : List Nat := [2, 2, 2, 2, 1, 2, 4, 1, 4]
def baseStart_526652 : Nat := 118140960795 + 526652 * 2 ^ 59
def prefixEnd_526652 : Nat := 4983230072969 + 3 ^ 40 * 526652 * 2
def baseEnd_526652 : Nat := 240378323246025515847091

theorem tailTrace_526652 : CollatzResearch.WordTrace tailWord_526652 prefixEnd_526652 240378323246025515847091 := by
  unfold tailWord_526652
  simp only [CollatzResearch.WordTrace]
  refine ⟨9604288244018611922911105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12805717658691482563881473 9604288244018611922911105)
  ·
    refine ⟨7203216183013958942183329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9604288244018611922911105 7203216183013958942183329)
    ·
      refine ⟨5402412137260469206637497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7203216183013958942183329 5402412137260469206637497)
      ·
        refine ⟨4051809102945351904978123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5402412137260469206637497 4051809102945351904978123)
        ·
          refine ⟨6077713654418027857467185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4051809102945351904978123 6077713654418027857467185)
          ·
            refine ⟨4558285240813520893100389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6077713654418027857467185 4558285240813520893100389)
            ·
              refine ⟨854678482652535167456323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4558285240813520893100389 854678482652535167456323)
              ·
                refine ⟨1282017723978802751184485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854678482652535167456323 1282017723978802751184485)
                ·
                  refine ⟨240378323246025515847091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1282017723978802751184485 240378323246025515847091)
                  ·
                    rfl

theorem cell20_526652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_526652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526652 prefixEnd_526652 := by exact prefixLift 526652
  have htrace : WordTrace (prefixWord ++ tailWord_526652) baseStart_526652 baseEnd_526652 := by
    simpa [prefixWord, tailWord_526652, baseEnd_526652] using wordTrace_append hprefix tailTrace_526652
  have hstable : (prefixWord ++ tailWord_526652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526652).length < 2 ^ (prefixWord ++ tailWord_526652).sum := by decide
  have hdescent : baseEnd_526652 < baseStart_526652 := by decide
  rcases family_descends (prefixWord ++ tailWord_526652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526676 : List Nat := [2, 4, 1, 1, 2, 2, 4, 4]
def baseStart_526676 : Nat := 118140960795 + 526676 * 2 ^ 59
def prefixEnd_526676 : Nat := 4983230072969 + 3 ^ 40 * 526676 * 2
def baseEnd_526676 : Nat := 80129759166662699682331

theorem tailTrace_526676 : CollatzResearch.WordTrace tailWord_526676 prefixEnd_526676 80129759166662699682331 := by
  unfold tailWord_526676
  simp only [CollatzResearch.WordTrace]
  refine ⟨9604725919975137972347941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12806301226633517296463921 9604725919975137972347941)
  ·
    refine ⟨1800886109995338369815239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9604725919975137972347941 1800886109995338369815239)
    ·
      refine ⟨2701329164993007554722859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1800886109995338369815239 2701329164993007554722859)
      ·
        refine ⟨4051993747489511332084289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2701329164993007554722859 4051993747489511332084289)
        ·
          refine ⟨3038995310617133499063217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4051993747489511332084289 3038995310617133499063217)
          ·
            refine ⟨2279246482962850124297413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3038995310617133499063217 2279246482962850124297413)
            ·
              refine ⟨427358715555534398305765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2279246482962850124297413 427358715555534398305765)
              ·
                refine ⟨80129759166662699682331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 427358715555534398305765 80129759166662699682331)
                ·
                  rfl

theorem cell20_526676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 4].length) (baseStart_526676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526676 prefixEnd_526676 := by exact prefixLift 526676
  have htrace : WordTrace (prefixWord ++ tailWord_526676) baseStart_526676 baseEnd_526676 := by
    simpa [prefixWord, tailWord_526676, baseEnd_526676] using wordTrace_append hprefix tailTrace_526676
  have hstable : (prefixWord ++ tailWord_526676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526676).length < 2 ^ (prefixWord ++ tailWord_526676).sum := by decide
  have hdescent : baseEnd_526676 < baseStart_526676 := by decide
  rcases family_descends (prefixWord ++ tailWord_526676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526704 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 5]
def baseStart_526704 : Nat := 118140960795 + 526704 * 2 ^ 59
def prefixEnd_526704 : Nat := 4983230072969 + 3 ^ 40 * 526704 * 2
def baseEnd_526704 : Nat := 240402057462944446113545

theorem tailTrace_526704 : CollatzResearch.WordTrace tailWord_526704 prefixEnd_526704 240402057462944446113545 := by
  unfold tailWord_526704
  simp only [CollatzResearch.WordTrace]
  refine ⟨9605236541924418363357583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12806982055899224484476777 9605236541924418363357583)
  ·
    refine ⟨14407854812886627545036375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9605236541924418363357583 14407854812886627545036375)
    ·
      refine ⟨21611782219329941317554563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14407854812886627545036375 21611782219329941317554563)
      ·
        refine ⟨32417673328994911976331845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21611782219329941317554563 32417673328994911976331845)
        ·
          refine ⟨6078313749186545995562221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32417673328994911976331845 6078313749186545995562221)
          ·
            refine ⟨2279367655944954748335833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6078313749186545995562221 2279367655944954748335833)
            ·
              refine ⟨1709525741958716061251875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2279367655944954748335833 1709525741958716061251875)
              ·
                refine ⟨2564288612938074091877813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1709525741958716061251875 2564288612938074091877813)
                ·
                  refine ⟨240402057462944446113545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2564288612938074091877813 240402057462944446113545)
                  ·
                    rfl

theorem cell20_526704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_526704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526704 prefixEnd_526704 := by exact prefixLift 526704
  have htrace : WordTrace (prefixWord ++ tailWord_526704) baseStart_526704 baseEnd_526704 := by
    simpa [prefixWord, tailWord_526704, baseEnd_526704] using wordTrace_append hprefix tailTrace_526704
  have hstable : (prefixWord ++ tailWord_526704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526704).length < 2 ^ (prefixWord ++ tailWord_526704).sum := by decide
  have hdescent : baseEnd_526704 < baseStart_526704 := by decide
  rcases family_descends (prefixWord ++ tailWord_526704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526711 : List Nat := [1, 1, 3, 1, 1, 2, 2, 5, 4]
def baseStart_526711 : Nat := 118140960795 + 526711 * 2 ^ 59
def prefixEnd_526711 : Nat := 4983230072969 + 3 ^ 40 * 526711 * 2
def baseEnd_526711 : Nat := 240405252453683532880183

theorem tailTrace_526711 : CollatzResearch.WordTrace tailWord_526711 prefixEnd_526711 240405252453683532880183 := by
  unfold tailWord_526711
  simp only [CollatzResearch.WordTrace]
  refine ⟨19210728394823476922219987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12807152263215651281479991 19210728394823476922219987)
  ·
    refine ⟨28816092592235215383329981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19210728394823476922219987 28816092592235215383329981)
    ·
      refine ⟨10806034722088205768748743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28816092592235215383329981 10806034722088205768748743)
      ·
        refine ⟨16209052083132308653123115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10806034722088205768748743 16209052083132308653123115)
        ·
          refine ⟨24313578124698462979684673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16209052083132308653123115 24313578124698462979684673)
          ·
            refine ⟨18235183593523847234763505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24313578124698462979684673 18235183593523847234763505)
            ·
              refine ⟨13676387695142885426072629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18235183593523847234763505 13676387695142885426072629)
              ·
                refine ⟨1282161346419645508694309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13676387695142885426072629 1282161346419645508694309)
                ·
                  refine ⟨240405252453683532880183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1282161346419645508694309 240405252453683532880183)
                  ·
                    rfl

theorem cell20_526711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 4].length) (baseStart_526711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526711 prefixEnd_526711 := by exact prefixLift 526711
  have htrace : WordTrace (prefixWord ++ tailWord_526711) baseStart_526711 baseEnd_526711 := by
    simpa [prefixWord, tailWord_526711, baseEnd_526711] using wordTrace_append hprefix tailTrace_526711
  have hstable : (prefixWord ++ tailWord_526711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526711).length < 2 ^ (prefixWord ++ tailWord_526711).sum := by decide
  have hdescent : baseEnd_526711 < baseStart_526711 := by decide
  rcases family_descends (prefixWord ++ tailWord_526711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526759 : List Nat := [1, 1, 6, 1, 1, 2, 1, 4, 3]
def baseStart_526759 : Nat := 118140960795 + 526759 * 2 ^ 59
def prefixEnd_526759 : Nat := 4983230072969 + 3 ^ 40 * 526759 * 2
def baseEnd_526759 : Nat := 240427160961608699279987

theorem tailTrace_526759 : CollatzResearch.WordTrace tailWord_526759 prefixEnd_526759 240427160961608699279987 := by
  unfold tailWord_526759
  simp only [CollatzResearch.WordTrace]
  refine ⟨19212479098649581119967331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12808319399099720746644887 19212479098649581119967331)
  ·
    refine ⟨28818718647974371679950997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19212479098649581119967331 28818718647974371679950997)
    ·
      refine ⟨1350877436623798672497703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28818718647974371679950997 1350877436623798672497703)
      ·
        refine ⟨2026316154935698008746555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1350877436623798672497703 2026316154935698008746555)
        ·
          refine ⟨3039474232403547013119833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2026316154935698008746555 3039474232403547013119833)
          ·
            refine ⟨2279605674302660259839875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3039474232403547013119833 2279605674302660259839875)
            ·
              refine ⟨3419408511453990389759813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2279605674302660259839875 3419408511453990389759813)
              ·
                refine ⟨641139095897623198079965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3419408511453990389759813 641139095897623198079965)
                ·
                  refine ⟨240427160961608699279987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 641139095897623198079965 240427160961608699279987)
                  ·
                    rfl

theorem cell20_526759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 3].length) (baseStart_526759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526759 prefixEnd_526759 := by exact prefixLift 526759
  have htrace : WordTrace (prefixWord ++ tailWord_526759) baseStart_526759 baseEnd_526759 := by
    simpa [prefixWord, tailWord_526759, baseEnd_526759] using wordTrace_append hprefix tailTrace_526759
  have hstable : (prefixWord ++ tailWord_526759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526759).length < 2 ^ (prefixWord ++ tailWord_526759).sum := by decide
  have hdescent : baseEnd_526759 < baseStart_526759 := by decide
  rcases family_descends (prefixWord ++ tailWord_526759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526821 : List Nat := [1, 3, 1, 5, 2, 1, 2, 1, 4]
def baseStart_526821 : Nat := 118140960795 + 526821 * 2 ^ 59
def prefixEnd_526821 : Nat := 4983230072969 + 3 ^ 40 * 526821 * 2
def baseEnd_526821 : Nat := 240455459451012039213067

theorem tailTrace_526821 : CollatzResearch.WordTrace tailWord_526821 prefixEnd_526821 240455459451012039213067 := by
  unfold tailWord_526821
  simp only [CollatzResearch.WordTrace]
  refine ⟨19214740424424965708724317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12809826949616643805816211 19214740424424965708724317)
  ·
    refine ⟨7205527659159362140771619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19214740424424965708724317 7205527659159362140771619)
    ·
      refine ⟨10808291488739043211157429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7205527659159362140771619 10808291488739043211157429)
      ·
        refine ⟨1013277327069285301046009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10808291488739043211157429 1013277327069285301046009)
        ·
          refine ⟨759957995301963975784507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1013277327069285301046009 759957995301963975784507)
          ·
            refine ⟨1139936992952945963676761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759957995301963975784507 1139936992952945963676761)
            ·
              refine ⟨854952744714709472757571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1139936992952945963676761 854952744714709472757571)
              ·
                refine ⟨1282429117072064209136357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854952744714709472757571 1282429117072064209136357)
                ·
                  refine ⟨240455459451012039213067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1282429117072064209136357 240455459451012039213067)
                  ·
                    rfl

theorem cell20_526821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_526821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526821 prefixEnd_526821 := by exact prefixLift 526821
  have htrace : WordTrace (prefixWord ++ tailWord_526821) baseStart_526821 baseEnd_526821 := by
    simpa [prefixWord, tailWord_526821, baseEnd_526821] using wordTrace_append hprefix tailTrace_526821
  have hstable : (prefixWord ++ tailWord_526821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526821).length < 2 ^ (prefixWord ++ tailWord_526821).sum := by decide
  have hdescent : baseEnd_526821 < baseStart_526821 := by decide
  rcases family_descends (prefixWord ++ tailWord_526821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526832 : List Nat := [2, 1, 1, 1, 3, 3, 2, 7]
def baseStart_526832 : Nat := 118140960795 + 526832 * 2 ^ 59
def prefixEnd_526832 : Nat := 4983230072969 + 3 ^ 40 * 526832 * 2
def baseEnd_526832 : Nat := 80153493383581629948785

theorem tailTrace_526832 : CollatzResearch.WordTrace tailWord_526832 prefixEnd_526832 80153493383581629948785 := by
  unfold tailWord_526832
  simp only [CollatzResearch.WordTrace]
  refine ⟨9607570813692557293687375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12810094418256743058249833 9607570813692557293687375)
  ·
    refine ⟨14411356220538835940531063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9607570813692557293687375 14411356220538835940531063)
    ·
      refine ⟨21617034330808253910796595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14411356220538835940531063 21617034330808253910796595)
      ·
        refine ⟨32425551496212380866194893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21617034330808253910796595 32425551496212380866194893)
        ·
          refine ⟨12159581811079642824823085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32425551496212380866194893 12159581811079642824823085)
          ·
            refine ⟨4559843179154866059308657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12159581811079642824823085 4559843179154866059308657)
            ·
              refine ⟨3419882384366149544481493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4559843179154866059308657 3419882384366149544481493)
              ·
                refine ⟨80153493383581629948785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3419882384366149544481493 80153493383581629948785)
                ·
                  rfl

theorem cell20_526832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_526832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526832 prefixEnd_526832 := by exact prefixLift 526832
  have htrace : WordTrace (prefixWord ++ tailWord_526832) baseStart_526832 baseEnd_526832 := by
    simpa [prefixWord, tailWord_526832, baseEnd_526832] using wordTrace_append hprefix tailTrace_526832
  have hstable : (prefixWord ++ tailWord_526832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526832).length < 2 ^ (prefixWord ++ tailWord_526832).sum := by decide
  have hdescent : baseEnd_526832 < baseStart_526832 := by decide
  rcases family_descends (prefixWord ++ tailWord_526832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526835 : List Nat := [1, 1, 1, 2, 2, 2, 7, 1, 3]
def baseStart_526835 : Nat := 118140960795 + 526835 * 2 ^ 59
def prefixEnd_526835 : Nat := 4983230072969 + 3 ^ 40 * 526835 * 2
def baseEnd_526835 : Nat := 240461849432490212746343

theorem tailTrace_526835 : CollatzResearch.WordTrace tailWord_526835 prefixEnd_526835 240461849432490212746343 := by
  unfold tailWord_526835
  simp only [CollatzResearch.WordTrace]
  refine ⟨19215251046374246099733959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12810167364249497399822639 19215251046374246099733959)
  ·
    refine ⟨28822876569561369149600939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19215251046374246099733959 28822876569561369149600939)
    ·
      refine ⟨43234314854342053724401409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28822876569561369149600939 43234314854342053724401409)
      ·
        refine ⟨32425736140756540293301057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43234314854342053724401409 32425736140756540293301057)
        ·
          refine ⟨24319302105567405219975793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32425736140756540293301057 24319302105567405219975793)
          ·
            refine ⟨18239476579175553914981845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24319302105567405219975793 18239476579175553914981845)
            ·
              refine ⟨427487732324427044882387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 18239476579175553914981845 427487732324427044882387)
              ·
                refine ⟨641231598486640567323581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427487732324427044882387 641231598486640567323581)
                ·
                  refine ⟨240461849432490212746343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 641231598486640567323581 240461849432490212746343)
                  ·
                    rfl

theorem cell20_526835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 3].length) (baseStart_526835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526835 prefixEnd_526835 := by exact prefixLift 526835
  have htrace : WordTrace (prefixWord ++ tailWord_526835) baseStart_526835 baseEnd_526835 := by
    simpa [prefixWord, tailWord_526835, baseEnd_526835] using wordTrace_append hprefix tailTrace_526835
  have hstable : (prefixWord ++ tailWord_526835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526835).length < 2 ^ (prefixWord ++ tailWord_526835).sum := by decide
  have hdescent : baseEnd_526835 < baseStart_526835 := by decide
  rcases family_descends (prefixWord ++ tailWord_526835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526849 : List Nat := [1, 2, 4, 1, 3, 2, 1, 6]
def baseStart_526849 : Nat := 118140960795 + 526849 * 2 ^ 59
def prefixEnd_526849 : Nat := 4983230072969 + 3 ^ 40 * 526849 * 2
def baseEnd_526849 : Nat := 80156079804656128759873

theorem tailTrace_526849 : CollatzResearch.WordTrace tailWord_526849 prefixEnd_526849 80156079804656128759873 := by
  unfold tailWord_526849
  simp only [CollatzResearch.WordTrace]
  refine ⟨19215761668323526490743601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12810507778882350993829067 19215761668323526490743601)
  ·
    refine ⟨14411821251242644868057701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19215761668323526490743601 14411821251242644868057701)
    ·
      refine ⟨2702216484607995912760819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14411821251242644868057701 2702216484607995912760819)
      ·
        refine ⟨4053324726911993869141229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2702216484607995912760819 4053324726911993869141229)
        ·
          refine ⟨1519996772591997700927961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4053324726911993869141229 1519996772591997700927961)
          ·
            refine ⟨1139997579443998275695971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1519996772591997700927961 1139997579443998275695971)
            ·
              refine ⟨1709996369165997413543957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1139997579443998275695971 1709996369165997413543957)
              ·
                refine ⟨80156079804656128759873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1709996369165997413543957 80156079804656128759873)
                ·
                  rfl

theorem cell20_526849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 6].length) (baseStart_526849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526849 prefixEnd_526849 := by exact prefixLift 526849
  have htrace : WordTrace (prefixWord ++ tailWord_526849) baseStart_526849 baseEnd_526849 := by
    simpa [prefixWord, tailWord_526849, baseEnd_526849] using wordTrace_append hprefix tailTrace_526849
  have hstable : (prefixWord ++ tailWord_526849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526849).length < 2 ^ (prefixWord ++ tailWord_526849).sum := by decide
  have hdescent : baseEnd_526849 < baseStart_526849 := by decide
  rcases family_descends (prefixWord ++ tailWord_526849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526855 : List Nat := [1, 1, 4, 3, 4, 1, 1, 3, 2]
def baseStart_526855 : Nat := 118140960795 + 526855 * 2 ^ 59
def prefixEnd_526855 : Nat := 4983230072969 + 3 ^ 40 * 526855 * 2
def baseEnd_526855 : Nat := 240470977977459032079595

theorem tailTrace_526855 : CollatzResearch.WordTrace tailWord_526855 prefixEnd_526855 240470977977459032079595 := by
  unfold tailWord_526855
  simp only [CollatzResearch.WordTrace]
  refine ⟨19215980506301789515462019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12810653670867859676974679 19215980506301789515462019)
  ·
    refine ⟨28823970759452684273193029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19215980506301789515462019 28823970759452684273193029)
    ·
      refine ⟨5404494517397378301223693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28823970759452684273193029 5404494517397378301223693)
      ·
        refine ⟨2026685444024016862958885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5404494517397378301223693 2026685444024016862958885)
        ·
          refine ⟨380003520754503161804791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2026685444024016862958885 380003520754503161804791)
          ·
            refine ⟨570005281131754742707187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380003520754503161804791 570005281131754742707187)
            ·
              refine ⟨855007921697632114060781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570005281131754742707187 855007921697632114060781)
              ·
                refine ⟨320627970636612042772793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 855007921697632114060781 320627970636612042772793)
                ·
                  refine ⟨240470977977459032079595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320627970636612042772793 240470977977459032079595)
                  ·
                    rfl

theorem cell20_526855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 2].length) (baseStart_526855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526855 prefixEnd_526855 := by exact prefixLift 526855
  have htrace : WordTrace (prefixWord ++ tailWord_526855) baseStart_526855 baseEnd_526855 := by
    simpa [prefixWord, tailWord_526855, baseEnd_526855] using wordTrace_append hprefix tailTrace_526855
  have hstable : (prefixWord ++ tailWord_526855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526855).length < 2 ^ (prefixWord ++ tailWord_526855).sum := by decide
  have hdescent : baseEnd_526855 < baseStart_526855 := by decide
  rcases family_descends (prefixWord ++ tailWord_526855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526859 : List Nat := [1, 1, 1, 1, 7, 1, 3, 3, 2]
def baseStart_526859 : Nat := 118140960795 + 526859 * 2 ^ 59
def prefixEnd_526859 : Nat := 4983230072969 + 3 ^ 40 * 526859 * 2
def baseEnd_526859 : Nat := 240472803686452795946245

theorem tailTrace_526859 : CollatzResearch.WordTrace tailWord_526859 prefixEnd_526859 240472803686452795946245 := by
  unfold tailWord_526859
  simp only [CollatzResearch.WordTrace]
  refine ⟨19216126398287298198607631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12810750932191532132405087 19216126398287298198607631)
  ·
    refine ⟨28824189597430947297911447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19216126398287298198607631 28824189597430947297911447)
    ·
      refine ⟨43236284396146420946867171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28824189597430947297911447 43236284396146420946867171)
      ·
        refine ⟨64854426594219631420300757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43236284396146420946867171 64854426594219631420300757)
        ·
          refine ⟨1520025623302022611413299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 64854426594219631420300757 1520025623302022611413299)
          ·
            refine ⟨2280038434953033917119949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1520025623302022611413299 2280038434953033917119949)
            ·
              refine ⟨855014413107387718919981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2280038434953033917119949 855014413107387718919981)
              ·
                refine ⟨320630404915270394594993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 855014413107387718919981 320630404915270394594993)
                ·
                  refine ⟨240472803686452795946245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320630404915270394594993 240472803686452795946245)
                  ·
                    rfl

theorem cell20_526859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 2].length) (baseStart_526859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526859 prefixEnd_526859 := by exact prefixLift 526859
  have htrace : WordTrace (prefixWord ++ tailWord_526859) baseStart_526859 baseEnd_526859 := by
    simpa [prefixWord, tailWord_526859, baseEnd_526859] using wordTrace_append hprefix tailTrace_526859
  have hstable : (prefixWord ++ tailWord_526859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526859).length < 2 ^ (prefixWord ++ tailWord_526859).sum := by decide
  have hdescent : baseEnd_526859 < baseStart_526859 := by decide
  rcases family_descends (prefixWord ++ tailWord_526859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526876 : List Nat := [2, 2, 3, 1, 2, 3, 3, 2, 2]
def baseStart_526876 : Nat := 118140960795 + 526876 * 2 ^ 59
def prefixEnd_526876 : Nat := 4983230072969 + 3 ^ 40 * 526876 * 2
def baseEnd_526876 : Nat := 240480562949676292379509

theorem tailTrace_526876 : CollatzResearch.WordTrace tailWord_526876 prefixEnd_526876 240480562949676292379509 := by
  unfold tailWord_526876
  simp only [CollatzResearch.WordTrace]
  refine ⟨9608373219612855050988241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12811164292817140067984321 9608373219612855050988241)
  ·
    refine ⟨7206279914709641288241181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9608373219612855050988241 7206279914709641288241181)
    ·
      refine ⟨2702354968016115483090443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7206279914709641288241181 2702354968016115483090443)
      ·
        refine ⟨4053532452024173224635665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2702354968016115483090443 4053532452024173224635665)
        ·
          refine ⟨3040149339018129918476749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4053532452024173224635665 3040149339018129918476749)
          ·
            refine ⟨1140056002131798719428781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3040149339018129918476749 1140056002131798719428781)
            ·
              refine ⟨427521000799424519785793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1140056002131798719428781 427521000799424519785793)
              ·
                refine ⟨320640750599568389839345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427521000799424519785793 320640750599568389839345)
                ·
                  refine ⟨240480562949676292379509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320640750599568389839345 240480562949676292379509)
                  ·
                    rfl

theorem cell20_526876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_526876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526876 prefixEnd_526876 := by exact prefixLift 526876
  have htrace : WordTrace (prefixWord ++ tailWord_526876) baseStart_526876 baseEnd_526876 := by
    simpa [prefixWord, tailWord_526876, baseEnd_526876] using wordTrace_append hprefix tailTrace_526876
  have hstable : (prefixWord ++ tailWord_526876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526876).length < 2 ^ (prefixWord ++ tailWord_526876).sum := by decide
  have hdescent : baseEnd_526876 < baseStart_526876 := by decide
  rcases family_descends (prefixWord ++ tailWord_526876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526890 : List Nat := [3, 1, 4, 1, 1, 2, 4, 1, 3]
def baseStart_526890 : Nat := 118140960795 + 526890 * 2 ^ 59
def prefixEnd_526890 : Nat := 4983230072969 + 3 ^ 40 * 526890 * 2
def baseEnd_526890 : Nat := 240486952931154465912785

theorem tailTrace_526890 : CollatzResearch.WordTrace tailWord_526890 prefixEnd_526890 240486952931154465912785 := by
  unfold tailWord_526890
  simp only [CollatzResearch.WordTrace]
  refine ⟨4804314265293747623246531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12811504707449993661990749 4804314265293747623246531)
  ·
    refine ⟨7206471397940621434869797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4804314265293747623246531 7206471397940621434869797)
    ·
      refine ⟨1351213387113866519038087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7206471397940621434869797 1351213387113866519038087)
      ·
        refine ⟨2026820080670799778557131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1351213387113866519038087 2026820080670799778557131)
        ·
          refine ⟨3040230121006199667835697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2026820080670799778557131 3040230121006199667835697)
          ·
            refine ⟨2280172590754649750876773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3040230121006199667835697 2280172590754649750876773)
            ·
              refine ⟨427532360766496828289395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2280172590754649750876773 427532360766496828289395)
              ·
                refine ⟨641298541149745242434093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427532360766496828289395 641298541149745242434093)
                ·
                  refine ⟨240486952931154465912785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 641298541149745242434093 240486952931154465912785)
                  ·
                    rfl

theorem cell20_526890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_526890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526890 prefixEnd_526890 := by exact prefixLift 526890
  have htrace : WordTrace (prefixWord ++ tailWord_526890) baseStart_526890 baseEnd_526890 := by
    simpa [prefixWord, tailWord_526890, baseEnd_526890] using wordTrace_append hprefix tailTrace_526890
  have hstable : (prefixWord ++ tailWord_526890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526890).length < 2 ^ (prefixWord ++ tailWord_526890).sum := by decide
  have hdescent : baseEnd_526890 < baseStart_526890 := by decide
  rcases family_descends (prefixWord ++ tailWord_526890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526901 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 6]
def baseStart_526901 : Nat := 118140960795 + 526901 * 2 ^ 59
def prefixEnd_526901 : Nat := 4983230072969 + 3 ^ 40 * 526901 * 2
def baseEnd_526901 : Nat := 240491973630887316546073

theorem tailTrace_526901 : CollatzResearch.WordTrace tailWord_526901 prefixEnd_526901 240491973630887316546073 := by
  unfold tailWord_526901
  simp only [CollatzResearch.WordTrace]
  refine ⟨19217658264135139371636557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12811772176090092914424371 19217658264135139371636557)
  ·
    refine ⟨7206621849050677264363709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19217658264135139371636557 7206621849050677264363709)
    ·
      refine ⟨2702483193394003974136391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7206621849050677264363709 2702483193394003974136391)
      ·
        refine ⟨4053724790091005961204587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2702483193394003974136391 4053724790091005961204587)
        ·
          refine ⟨6080587185136508941806881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4053724790091005961204587 6080587185136508941806881)
          ·
            refine ⟨4560440388852381706355161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6080587185136508941806881 4560440388852381706355161)
            ·
              refine ⟨3420330291639286279766371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4560440388852381706355161 3420330291639286279766371)
              ·
                refine ⟨5130495437458929419649557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3420330291639286279766371 5130495437458929419649557)
                ·
                  refine ⟨240491973630887316546073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5130495437458929419649557 240491973630887316546073)
                  ·
                    rfl

theorem cell20_526901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_526901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526901 prefixEnd_526901 := by exact prefixLift 526901
  have htrace : WordTrace (prefixWord ++ tailWord_526901) baseStart_526901 baseEnd_526901 := by
    simpa [prefixWord, tailWord_526901, baseEnd_526901] using wordTrace_append hprefix tailTrace_526901
  have hstable : (prefixWord ++ tailWord_526901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526901).length < 2 ^ (prefixWord ++ tailWord_526901).sum := by decide
  have hdescent : baseEnd_526901 < baseStart_526901 := by decide
  rcases family_descends (prefixWord ++ tailWord_526901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526915 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 7]
def baseStart_526915 : Nat := 118140960795 + 526915 * 2 ^ 59
def prefixEnd_526915 : Nat := 4983230072969 + 3 ^ 40 * 526915 * 2
def baseEnd_526915 : Nat := 240498363612365490079349

theorem tailTrace_526915 : CollatzResearch.WordTrace tailWord_526915 prefixEnd_526915 240498363612365490079349 := by
  unfold tailWord_526915
  simp only [CollatzResearch.WordTrace]
  refine ⟨19218168886084419762646199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12812112590722946508430799 19218168886084419762646199)
  ·
    refine ⟨28827253329126629643969299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19218168886084419762646199 28827253329126629643969299)
    ·
      refine ⟨43240879993689944465953949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28827253329126629643969299 43240879993689944465953949)
      ·
        refine ⟨16215329997633729174732731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43240879993689944465953949 16215329997633729174732731)
        ·
          refine ⟨24322994996450593762099097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16215329997633729174732731 24322994996450593762099097)
          ·
            refine ⟨18242246247337945321574323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24322994996450593762099097 18242246247337945321574323)
            ·
              refine ⟨27363369371006917982361485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18242246247337945321574323 27363369371006917982361485)
              ·
                refine ⟨10261263514127594243385557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27363369371006917982361485 10261263514127594243385557)
                ·
                  refine ⟨240498363612365490079349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10261263514127594243385557 240498363612365490079349)
                  ·
                    rfl

theorem cell20_526915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_526915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526915 prefixEnd_526915 := by exact prefixLift 526915
  have htrace : WordTrace (prefixWord ++ tailWord_526915) baseStart_526915 baseEnd_526915 := by
    simpa [prefixWord, tailWord_526915, baseEnd_526915] using wordTrace_append hprefix tailTrace_526915
  have hstable : (prefixWord ++ tailWord_526915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526915).length < 2 ^ (prefixWord ++ tailWord_526915).sum := by decide
  have hdescent : baseEnd_526915 < baseStart_526915 := by decide
  rcases family_descends (prefixWord ++ tailWord_526915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526925 : List Nat := [1, 6, 1, 1, 2, 9]
def baseStart_526925 : Nat := 118140960795 + 526925 * 2 ^ 59
def prefixEnd_526925 : Nat := 4983230072969 + 3 ^ 40 * 526925 * 2
def baseEnd_526925 : Nat := 8907515847587033323925

theorem tailTrace_526925 : CollatzResearch.WordTrace tailWord_526925 prefixEnd_526925 8907515847587033323925 := by
  unfold tailWord_526925
  simp only [CollatzResearch.WordTrace]
  refine ⟨19218533616048191470510229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12812355744032127647006819 19218533616048191470510229)
  ·
    refine ⟨900868763252258975180167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19218533616048191470510229 900868763252258975180167)
    ·
      refine ⟨1351303144878388462770251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 900868763252258975180167 1351303144878388462770251)
      ·
        refine ⟨2026954717317582694155377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1351303144878388462770251 2026954717317582694155377)
        ·
          refine ⟨1520216037988187020616533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2026954717317582694155377 1520216037988187020616533)
          ·
            refine ⟨8907515847587033323925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1520216037988187020616533 8907515847587033323925)
            ·
              rfl

theorem cell20_526925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 9].length) (baseStart_526925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526925 prefixEnd_526925 := by exact prefixLift 526925
  have htrace : WordTrace (prefixWord ++ tailWord_526925) baseStart_526925 baseEnd_526925 := by
    simpa [prefixWord, tailWord_526925, baseEnd_526925] using wordTrace_append hprefix tailTrace_526925
  have hstable : (prefixWord ++ tailWord_526925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526925).length < 2 ^ (prefixWord ++ tailWord_526925).sum := by decide
  have hdescent : baseEnd_526925 < baseStart_526925 := by decide
  rcases family_descends (prefixWord ++ tailWord_526925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526953 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 7]
def baseStart_526953 : Nat := 118140960795 + 526953 * 2 ^ 59
def prefixEnd_526953 : Nat := 4983230072969 + 3 ^ 40 * 526953 * 2
def baseEnd_526953 : Nat := 240515707847806246812527

theorem tailTrace_526953 : CollatzResearch.WordTrace tailWord_526953 prefixEnd_526953 240515707847806246812527 := by
  unfold tailWord_526953
  simp only [CollatzResearch.WordTrace]
  refine ⟨19219554859946752252529513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12813036573297834835019675 19219554859946752252529513)
  ·
    refine ⟨14414666144960064189397135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19219554859946752252529513 14414666144960064189397135)
    ·
      refine ⟨21621999217440096284095703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14414666144960064189397135 21621999217440096284095703)
      ·
        refine ⟨32432998826160144426143555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21621999217440096284095703 32432998826160144426143555)
        ·
          refine ⟨48649498239240216639215333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32432998826160144426143555 48649498239240216639215333)
          ·
            refine ⟨9121780919857540619852875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48649498239240216639215333 9121780919857540619852875)
            ·
              refine ⟨13682671379786310929779313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9121780919857540619852875 13682671379786310929779313)
              ·
                refine ⟨10262003534839733197334485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13682671379786310929779313 10262003534839733197334485)
                ·
                  refine ⟨240515707847806246812527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10262003534839733197334485 240515707847806246812527)
                  ·
                    rfl

theorem cell20_526953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_526953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526953 prefixEnd_526953 := by exact prefixLift 526953
  have htrace : WordTrace (prefixWord ++ tailWord_526953) baseStart_526953 baseEnd_526953 := by
    simpa [prefixWord, tailWord_526953, baseEnd_526953] using wordTrace_append hprefix tailTrace_526953
  have hstable : (prefixWord ++ tailWord_526953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526953).length < 2 ^ (prefixWord ++ tailWord_526953).sum := by decide
  have hdescent : baseEnd_526953 < baseStart_526953 := by decide
  rcases family_descends (prefixWord ++ tailWord_526953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526977 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 6]
def baseStart_526977 : Nat := 118140960795 + 526977 * 2 ^ 59
def prefixEnd_526977 : Nat := 4983230072969 + 3 ^ 40 * 526977 * 2
def baseEnd_526977 : Nat := 240526662101768830012429

theorem tailTrace_526977 : CollatzResearch.WordTrace tailWord_526977 prefixEnd_526977 240526662101768830012429 := by
  unfold tailWord_526977
  simp only [CollatzResearch.WordTrace]
  refine ⟨19220430211859804351403185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12813620141239869567602123 19220430211859804351403185)
  ·
    refine ⟨14415322658894853263552389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19220430211859804351403185 14415322658894853263552389)
    ·
      refine ⟨2702872998542784986916073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14415322658894853263552389 2702872998542784986916073)
      ·
        refine ⟨2027154748907088740187055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2702872998542784986916073 2027154748907088740187055)
        ·
          refine ⟨3040732123360633110280583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2027154748907088740187055 3040732123360633110280583)
          ·
            refine ⟨4561098185040949665420875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3040732123360633110280583 4561098185040949665420875)
            ·
              refine ⟨6841647277561424498131313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4561098185040949665420875 6841647277561424498131313)
              ·
                refine ⟨5131235458171068373598485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6841647277561424498131313 5131235458171068373598485)
                ·
                  refine ⟨240526662101768830012429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5131235458171068373598485 240526662101768830012429)
                  ·
                    rfl

theorem cell20_526977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_526977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526977 prefixEnd_526977 := by exact prefixLift 526977
  have htrace : WordTrace (prefixWord ++ tailWord_526977) baseStart_526977 baseEnd_526977 := by
    simpa [prefixWord, tailWord_526977, baseEnd_526977] using wordTrace_append hprefix tailTrace_526977
  have hstable : (prefixWord ++ tailWord_526977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526977).length < 2 ^ (prefixWord ++ tailWord_526977).sum := by decide
  have hdescent : baseEnd_526977 < baseStart_526977 := by decide
  rcases family_descends (prefixWord ++ tailWord_526977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526991 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 5]
def baseStart_526991 : Nat := 118140960795 + 526991 * 2 ^ 59
def prefixEnd_526991 : Nat := 4983230072969 + 3 ^ 40 * 526991 * 2
def baseEnd_526991 : Nat := 240533052083247003545705

theorem tailTrace_526991 : CollatzResearch.WordTrace tailWord_526991 prefixEnd_526991 240533052083247003545705 := by
  unfold tailWord_526991
  simp only [CollatzResearch.WordTrace]
  refine ⟨19220940833809084742412827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12813960555872723161608551 19220940833809084742412827)
  ·
    refine ⟨28831411250713627113619241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19220940833809084742412827 28831411250713627113619241)
    ·
      refine ⟨21623558438035220335214431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28831411250713627113619241 21623558438035220335214431)
      ·
        refine ⟨32435337657052830502821647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21623558438035220335214431 32435337657052830502821647)
        ·
          refine ⟨48653006485579245754232471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32435337657052830502821647 48653006485579245754232471)
          ·
            refine ⟨72979509728368868631348707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48653006485579245754232471 72979509728368868631348707)
            ·
              refine ⟨109469264592553302947023061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72979509728368868631348707 109469264592553302947023061)
              ·
                refine ⟨2565685888887968037820853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 109469264592553302947023061 2565685888887968037820853)
                ·
                  refine ⟨240533052083247003545705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2565685888887968037820853 240533052083247003545705)
                  ·
                    rfl

theorem cell20_526991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_526991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526991 prefixEnd_526991 := by exact prefixLift 526991
  have htrace : WordTrace (prefixWord ++ tailWord_526991) baseStart_526991 baseEnd_526991 := by
    simpa [prefixWord, tailWord_526991, baseEnd_526991] using wordTrace_append hprefix tailTrace_526991
  have hstable : (prefixWord ++ tailWord_526991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526991).length < 2 ^ (prefixWord ++ tailWord_526991).sum := by decide
  have hdescent : baseEnd_526991 < baseStart_526991 := by decide
  rcases family_descends (prefixWord ++ tailWord_526991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_526994 : List Nat := [3, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_526994 : Nat := 118140960795 + 526994 * 2 ^ 59
def prefixEnd_526994 : Nat := 4983230072969 + 3 ^ 40 * 526994 * 2
def baseEnd_526994 : Nat := 240534421364992326445693

theorem tailTrace_526994 : CollatzResearch.WordTrace tailWord_526994 prefixEnd_526994 240534421364992326445693 := by
  unfold tailWord_526994
  simp only [CollatzResearch.WordTrace]
  refine ⟨4805262563199554063693009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12814033501865477503181357 4805262563199554063693009)
  ·
    refine ⟨3603946922399665547769757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4805262563199554063693009 3603946922399665547769757)
    ·
      refine ⟨1351480095899874580413659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3603946922399665547769757 1351480095899874580413659)
      ·
        refine ⟨2027220143849811870620489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1351480095899874580413659 2027220143849811870620489)
        ·
          refine ⟨1520415107887358902965367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2027220143849811870620489 1520415107887358902965367)
          ·
            refine ⟨2280622661831038354448051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1520415107887358902965367 2280622661831038354448051)
            ·
              refine ⟨3420933992746557531672077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2280622661831038354448051 3420933992746557531672077)
              ·
                refine ⟨1282850247279959074377029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3420933992746557531672077 1282850247279959074377029)
                ·
                  refine ⟨240534421364992326445693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1282850247279959074377029 240534421364992326445693)
                  ·
                    rfl

theorem cell20_526994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_526994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_526994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_526994 prefixEnd_526994 := by exact prefixLift 526994
  have htrace : WordTrace (prefixWord ++ tailWord_526994) baseStart_526994 baseEnd_526994 := by
    simpa [prefixWord, tailWord_526994, baseEnd_526994] using wordTrace_append hprefix tailTrace_526994
  have hstable : (prefixWord ++ tailWord_526994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_526994).length < 2 ^ (prefixWord ++ tailWord_526994).sum := by decide
  have hdescent : baseEnd_526994 < baseStart_526994 := by decide
  rcases family_descends (prefixWord ++ tailWord_526994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527004 : List Nat := [2, 2, 3, 2, 2, 2, 3, 1, 3]
def baseStart_527004 : Nat := 118140960795 + 527004 * 2 ^ 59
def prefixEnd_527004 : Nat := 4983230072969 + 3 ^ 40 * 527004 * 2
def baseEnd_527004 : Nat := 240538985637476736112319

theorem tailTrace_527004 : CollatzResearch.WordTrace tailWord_527004 prefixEnd_527004 240538985637476736112319 := by
  unfold tailWord_527004
  simp only [CollatzResearch.WordTrace]
  refine ⟨9610707491380993981318033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12814276655174658641757377 9610707491380993981318033)
  ·
    refine ⟨7208030618535745485988525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9610707491380993981318033 7208030618535745485988525)
    ·
      refine ⟨2703011481950904557245697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7208030618535745485988525 2703011481950904557245697)
      ·
        refine ⟨2027258611463178417934273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2703011481950904557245697 2027258611463178417934273)
        ·
          refine ⟨1520443958597383813450705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2027258611463178417934273 1520443958597383813450705)
          ·
            refine ⟨1140332968948037860088029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1520443958597383813450705 1140332968948037860088029)
            ·
              refine ⟨427624863355514197533011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1140332968948037860088029 427624863355514197533011)
              ·
                refine ⟨641437295033271296299517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427624863355514197533011 641437295033271296299517)
                ·
                  refine ⟨240538985637476736112319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 641437295033271296299517 240538985637476736112319)
                  ·
                    rfl

theorem cell20_527004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_527004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527004 prefixEnd_527004 := by exact prefixLift 527004
  have htrace : WordTrace (prefixWord ++ tailWord_527004) baseStart_527004 baseEnd_527004 := by
    simpa [prefixWord, tailWord_527004, baseEnd_527004] using wordTrace_append hprefix tailTrace_527004
  have hstable : (prefixWord ++ tailWord_527004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527004).length < 2 ^ (prefixWord ++ tailWord_527004).sum := by decide
  have hdescent : baseEnd_527004 < baseStart_527004 := by decide
  rcases family_descends (prefixWord ++ tailWord_527004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527063 : List Nat := [1, 1, 3, 2, 1, 4, 4, 1, 3]
def baseStart_527063 : Nat := 118140960795 + 527063 * 2 ^ 59
def prefixEnd_527063 : Nat := 4983230072969 + 3 ^ 40 * 527063 * 2
def baseEnd_527063 : Nat := 240565914845134753145411

theorem tailTrace_527063 : CollatzResearch.WordTrace tailWord_527063 prefixEnd_527063 240565914845134753145411 := by
  unfold tailWord_527063
  simp only [CollatzResearch.WordTrace]
  refine ⟨19223566889548241039033843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12815711259698827359355895 19223566889548241039033843)
  ·
    refine ⟨28835350334322361558550765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19223566889548241039033843 28835350334322361558550765)
    ·
      refine ⟨10813256375370885584456537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28835350334322361558550765 10813256375370885584456537)
      ·
        refine ⟨8109942281528164188342403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10813256375370885584456537 8109942281528164188342403)
        ·
          refine ⟨12164913422292246282513605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8109942281528164188342403 12164913422292246282513605)
          ·
            refine ⟨2280921266679796177971301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12164913422292246282513605 2280921266679796177971301)
            ·
              refine ⟨427672737502461783369619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2280921266679796177971301 427672737502461783369619)
              ·
                refine ⟨641509106253692675054429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427672737502461783369619 641509106253692675054429)
                ·
                  refine ⟨240565914845134753145411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 641509106253692675054429 240565914845134753145411)
                  ·
                    rfl

theorem cell20_527063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 3].length) (baseStart_527063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527063 prefixEnd_527063 := by exact prefixLift 527063
  have htrace : WordTrace (prefixWord ++ tailWord_527063) baseStart_527063 baseEnd_527063 := by
    simpa [prefixWord, tailWord_527063, baseEnd_527063] using wordTrace_append hprefix tailTrace_527063
  have hstable : (prefixWord ++ tailWord_527063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527063).length < 2 ^ (prefixWord ++ tailWord_527063).sum := by decide
  have hdescent : baseEnd_527063 < baseStart_527063 := by decide
  rcases family_descends (prefixWord ++ tailWord_527063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527167 : List Nat := [1, 1, 2, 2, 5, 1, 1, 3, 4]
def baseStart_527167 : Nat := 118140960795 + 527167 * 2 ^ 59
def prefixEnd_527167 : Nat := 4983230072969 + 3 ^ 40 * 527167 * 2
def baseEnd_527167 : Nat := 240613383278972613678319

theorem tailTrace_527167 : CollatzResearch.WordTrace tailWord_527167 prefixEnd_527167 240613383278972613678319 := by
  unfold tailWord_527167
  simp only [CollatzResearch.WordTrace]
  refine ⟨19227360081171466800819755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12818240054114311200546503 19227360081171466800819755)
  ·
    refine ⟨28841040121757200201229633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19227360081171466800819755 28841040121757200201229633)
    ·
      refine ⟨21630780091317900150922225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28841040121757200201229633 21630780091317900150922225)
      ·
        refine ⟨16223085068488425113191669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21630780091317900150922225 16223085068488425113191669)
        ·
          refine ⟨1520914225170789854361719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16223085068488425113191669 1520914225170789854361719)
          ·
            refine ⟨2281371337756184781542579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1520914225170789854361719 2281371337756184781542579)
            ·
              refine ⟨3422057006634277172313869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2281371337756184781542579 3422057006634277172313869)
              ·
                refine ⟨1283271377487853939617701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3422057006634277172313869 1283271377487853939617701)
                ·
                  refine ⟨240613383278972613678319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1283271377487853939617701 240613383278972613678319)
                  ·
                    rfl

theorem cell20_527167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 4].length) (baseStart_527167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527167 prefixEnd_527167 := by exact prefixLift 527167
  have htrace : WordTrace (prefixWord ++ tailWord_527167) baseStart_527167 baseEnd_527167 := by
    simpa [prefixWord, tailWord_527167, baseEnd_527167] using wordTrace_append hprefix tailTrace_527167
  have hstable : (prefixWord ++ tailWord_527167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527167).length < 2 ^ (prefixWord ++ tailWord_527167).sum := by decide
  have hdescent : baseEnd_527167 < baseStart_527167 := by decide
  rcases family_descends (prefixWord ++ tailWord_527167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527177 : List Nat := [1, 2, 1, 1, 2, 6, 3, 1, 3]
def baseStart_527177 : Nat := 118140960795 + 527177 * 2 ^ 59
def prefixEnd_527177 : Nat := 4983230072969 + 3 ^ 40 * 527177 * 2
def baseEnd_527177 : Nat := 240617947551457023344945

theorem tailTrace_527177 : CollatzResearch.WordTrace tailWord_527177 prefixEnd_527177 240617947551457023344945 := by
  unfold tailWord_527177
  simp only [CollatzResearch.WordTrace]
  refine ⟨19227724811135238508683785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12818483207423492339122523 19227724811135238508683785)
  ·
    refine ⟨14420793608351428881512839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19227724811135238508683785 14420793608351428881512839)
    ·
      refine ⟨21631190412527143322269259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14420793608351428881512839 21631190412527143322269259)
      ·
        refine ⟨32446785618790714983403889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21631190412527143322269259 32446785618790714983403889)
        ·
          refine ⟨24335089214093036237552917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32446785618790714983403889 24335089214093036237552917)
          ·
            refine ⟨1140707306910611073635293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24335089214093036237552917 1140707306910611073635293)
            ·
              refine ⟨427765240091479152613235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1140707306910611073635293 427765240091479152613235)
              ·
                refine ⟨641647860137218728919853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427765240091479152613235 641647860137218728919853)
                ·
                  refine ⟨240617947551457023344945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 641647860137218728919853 240617947551457023344945)
                  ·
                    rfl

theorem cell20_527177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 3].length) (baseStart_527177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527177 prefixEnd_527177 := by exact prefixLift 527177
  have htrace : WordTrace (prefixWord ++ tailWord_527177) baseStart_527177 baseEnd_527177 := by
    simpa [prefixWord, tailWord_527177, baseEnd_527177] using wordTrace_append hprefix tailTrace_527177
  have hstable : (prefixWord ++ tailWord_527177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527177).length < 2 ^ (prefixWord ++ tailWord_527177).sum := by decide
  have hdescent : baseEnd_527177 < baseStart_527177 := by decide
  rcases family_descends (prefixWord ++ tailWord_527177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527191 : List Nat := [1, 1, 3, 2, 4, 1, 4, 4]
def baseStart_527191 : Nat := 118140960795 + 527191 * 2 ^ 59
def prefixEnd_527191 : Nat := 4983230072969 + 3 ^ 40 * 527191 * 2
def baseEnd_527191 : Nat := 80208112510978398959407

theorem tailTrace_527191 : CollatzResearch.WordTrace tailWord_527191 prefixEnd_527191 80208112510978398959407 := by
  unfold tailWord_527191
  simp only [CollatzResearch.WordTrace]
  refine ⟨19228235433084518899693427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12818823622056345933128951 19228235433084518899693427)
  ·
    refine ⟨28842353149626778349540141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19228235433084518899693427 28842353149626778349540141)
    ·
      refine ⟨10815882431110041881077553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28842353149626778349540141 10815882431110041881077553)
      ·
        refine ⟨8111911823332531410808165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10815882431110041881077553 8111911823332531410808165)
        ·
          refine ⟨1520983466874849639526531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8111911823332531410808165 1520983466874849639526531)
          ·
            refine ⟨2281475200312274459289797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1520983466874849639526531 2281475200312274459289797)
            ·
              refine ⟨427776600058551461116837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2281475200312274459289797 427776600058551461116837)
              ·
                refine ⟨80208112510978398959407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 427776600058551461116837 80208112510978398959407)
                ·
                  rfl

theorem cell20_527191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 4].length) (baseStart_527191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527191 prefixEnd_527191 := by exact prefixLift 527191
  have htrace : WordTrace (prefixWord ++ tailWord_527191) baseStart_527191 baseEnd_527191 := by
    simpa [prefixWord, tailWord_527191, baseEnd_527191] using wordTrace_append hprefix tailTrace_527191
  have hstable : (prefixWord ++ tailWord_527191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527191).length < 2 ^ (prefixWord ++ tailWord_527191).sum := by decide
  have hdescent : baseEnd_527191 < baseStart_527191 := by decide
  rcases family_descends (prefixWord ++ tailWord_527191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527219 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 5]
def baseStart_527219 : Nat := 118140960795 + 527219 * 2 ^ 59
def prefixEnd_527219 : Nat := 4983230072969 + 3 ^ 40 * 527219 * 2
def baseEnd_527219 : Nat := 240637117495891543944773

theorem tailTrace_527219 : CollatzResearch.WordTrace tailWord_527219 prefixEnd_527219 240637117495891543944773 := by
  unfold tailWord_527219
  simp only [CollatzResearch.WordTrace]
  refine ⟨19229256676983079681712711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12819504451322053121141807 19229256676983079681712711)
  ·
    refine ⟨28843885015474619522569067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19229256676983079681712711 28843885015474619522569067)
    ·
      refine ⟨43265827523211929283853601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28843885015474619522569067 43265827523211929283853601)
      ·
        refine ⟨32449370642408946962890201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43265827523211929283853601 32449370642408946962890201)
        ·
          refine ⟨24337027981806710222167651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32449370642408946962890201 24337027981806710222167651)
          ·
            refine ⟨36505541972710065333251477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24337027981806710222167651 36505541972710065333251477)
            ·
              refine ⟨1711197279970784312496163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36505541972710065333251477 1711197279970784312496163)
              ·
                refine ⟨2566795919956176468744245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1711197279970784312496163 2566795919956176468744245)
                ·
                  refine ⟨240637117495891543944773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2566795919956176468744245 240637117495891543944773)
                  ·
                    rfl

theorem cell20_527219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 5].length) (baseStart_527219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527219 prefixEnd_527219 := by exact prefixLift 527219
  have htrace : WordTrace (prefixWord ++ tailWord_527219) baseStart_527219 baseEnd_527219 := by
    simpa [prefixWord, tailWord_527219, baseEnd_527219] using wordTrace_append hprefix tailTrace_527219
  have hstable : (prefixWord ++ tailWord_527219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527219).length < 2 ^ (prefixWord ++ tailWord_527219).sum := by decide
  have hdescent : baseEnd_527219 < baseStart_527219 := by decide
  rcases family_descends (prefixWord ++ tailWord_527219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527284 : List Nat := [2, 5, 2, 1, 1, 1, 3, 5]
def baseStart_527284 : Nat := 118140960795 + 527284 * 2 ^ 59
def prefixEnd_527284 : Nat := 4983230072969 + 3 ^ 40 * 527284 * 2
def baseEnd_527284 : Nat := 80222261755680068925947

theorem tailTrace_527284 : CollatzResearch.WordTrace tailWord_527284 prefixEnd_527284 80222261755680068925947 := by
  unfold tailWord_527284
  simp only [CollatzResearch.WordTrace]
  refine ⟨9615813710873797891414453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12821084947831730521885937 9615813710873797891414453)
  ·
    refine ⟨901482535394418552320105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9615813710873797891414453 901482535394418552320105)
    ·
      refine ⟨676111901545813914240079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 901482535394418552320105 676111901545813914240079)
      ·
        refine ⟨1014167852318720871360119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676111901545813914240079 1014167852318720871360119)
        ·
          refine ⟨1521251778478081307040179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014167852318720871360119 1521251778478081307040179)
          ·
            refine ⟨2281877667717121960560269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1521251778478081307040179 2281877667717121960560269)
            ·
              refine ⟨855704125393920735210101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2281877667717121960560269 855704125393920735210101)
              ·
                refine ⟨80222261755680068925947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 855704125393920735210101 80222261755680068925947)
                ·
                  rfl

theorem cell20_527284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_527284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527284 prefixEnd_527284 := by exact prefixLift 527284
  have htrace : WordTrace (prefixWord ++ tailWord_527284) baseStart_527284 baseEnd_527284 := by
    simpa [prefixWord, tailWord_527284, baseEnd_527284] using wordTrace_append hprefix tailTrace_527284
  have hstable : (prefixWord ++ tailWord_527284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527284).length < 2 ^ (prefixWord ++ tailWord_527284).sum := by decide
  have hdescent : baseEnd_527284 < baseStart_527284 := by decide
  rcases family_descends (prefixWord ++ tailWord_527284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527288 : List Nat := [2, 1, 2, 1, 2, 4, 3, 5]
def baseStart_527288 : Nat := 118140960795 + 527288 * 2 ^ 59
def prefixEnd_527288 : Nat := 4983230072969 + 3 ^ 40 * 527288 * 2
def baseEnd_527288 : Nat := 80222870325344656881497

theorem tailTrace_527288 : CollatzResearch.WordTrace tailWord_527288 prefixEnd_527288 80222870325344656881497 := by
  unfold tailWord_527288
  simp only [CollatzResearch.WordTrace]
  refine ⟨9615886656866552232987259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12821182209155402977316345 9615886656866552232987259)
  ·
    refine ⟨14423829985299828349480889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9615886656866552232987259 14423829985299828349480889)
    ·
      refine ⟨10817872488974871262110667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14423829985299828349480889 10817872488974871262110667)
      ·
        refine ⟨16226808733462306893166001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10817872488974871262110667 16226808733462306893166001)
        ·
          refine ⟨12170106550096730169874501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16226808733462306893166001 12170106550096730169874501)
          ·
            refine ⟨2281894978143136906851469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12170106550096730169874501 2281894978143136906851469)
            ·
              refine ⟨855710616803676340069301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2281894978143136906851469 855710616803676340069301)
              ·
                refine ⟨80222870325344656881497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 855710616803676340069301 80222870325344656881497)
                ·
                  rfl

theorem cell20_527288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_527288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527288 prefixEnd_527288 := by exact prefixLift 527288
  have htrace : WordTrace (prefixWord ++ tailWord_527288) baseStart_527288 baseEnd_527288 := by
    simpa [prefixWord, tailWord_527288, baseEnd_527288] using wordTrace_append hprefix tailTrace_527288
  have hstable : (prefixWord ++ tailWord_527288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527288).length < 2 ^ (prefixWord ++ tailWord_527288).sum := by decide
  have hdescent : baseEnd_527288 < baseStart_527288 := by decide
  rcases family_descends (prefixWord ++ tailWord_527288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527336 : List Nat := [2, 1, 4, 1, 1, 1, 4, 4, 2]
def baseStart_527336 : Nat := 118140960795 + 527336 * 2 ^ 59
def prefixEnd_527336 : Nat := 4983230072969 + 3 ^ 40 * 527336 * 2
def baseEnd_527336 : Nat := 240690519483959137044295

theorem tailTrace_527336 : CollatzResearch.WordTrace tailWord_527336 prefixEnd_527336 240690519483959137044295 := by
  unfold tailWord_527336
  simp only [CollatzResearch.WordTrace]
  refine ⟨9616762008779604331860931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12822349345039472442481241 9616762008779604331860931)
  ·
    refine ⟨14425143013169406497791397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9616762008779604331860931 14425143013169406497791397)
    ·
      refine ⟨2704714314969263718335887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14425143013169406497791397 2704714314969263718335887)
      ·
        refine ⟨4057071472453895577503831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2704714314969263718335887 4057071472453895577503831)
        ·
          refine ⟨6085607208680843366255747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4057071472453895577503831 6085607208680843366255747)
          ·
            refine ⟨9128410813021265049383621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6085607208680843366255747 9128410813021265049383621)
            ·
              refine ⟨1711577027441487196759429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9128410813021265049383621 1711577027441487196759429)
              ·
                refine ⟨320920692645278849392393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1711577027441487196759429 320920692645278849392393)
                ·
                  refine ⟨240690519483959137044295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320920692645278849392393 240690519483959137044295)
                  ·
                    rfl

theorem cell20_527336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 2].length) (baseStart_527336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527336 prefixEnd_527336 := by exact prefixLift 527336
  have htrace : WordTrace (prefixWord ++ tailWord_527336) baseStart_527336 baseEnd_527336 := by
    simpa [prefixWord, tailWord_527336, baseEnd_527336] using wordTrace_append hprefix tailTrace_527336
  have hstable : (prefixWord ++ tailWord_527336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527336).length < 2 ^ (prefixWord ++ tailWord_527336).sum := by decide
  have hdescent : baseEnd_527336 < baseStart_527336 := by decide
  rcases family_descends (prefixWord ++ tailWord_527336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527371 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 5]
def baseStart_527371 : Nat := 118140960795 + 527371 * 2 ^ 59
def prefixEnd_527371 : Nat := 4983230072969 + 3 ^ 40 * 527371 * 2
def baseEnd_527371 : Nat := 240706494437654570877485

theorem tailTrace_527371 : CollatzResearch.WordTrace tailWord_527371 prefixEnd_527371 240706494437654570877485 := by
  unfold tailWord_527371
  simp only [CollatzResearch.WordTrace]
  refine ⟨19234800572432409641245967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12823200381621606427497311 19234800572432409641245967)
  ·
    refine ⟨28852200858648614461868951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19234800572432409641245967 28852200858648614461868951)
    ·
      refine ⟨43278301287972921692803427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28852200858648614461868951 43278301287972921692803427)
      ·
        refine ⟨64917451931959382539205141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43278301287972921692803427 64917451931959382539205141)
        ·
          refine ⟨3043005559310596056525241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64917451931959382539205141 3043005559310596056525241)
          ·
            refine ⟨2282254169482947042393931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3043005559310596056525241 2282254169482947042393931)
            ·
              refine ⟨3423381254224420563590897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2282254169482947042393931 3423381254224420563590897)
              ·
                refine ⟨2567535940668315422693173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3423381254224420563590897 2567535940668315422693173)
                ·
                  refine ⟨240706494437654570877485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2567535940668315422693173 240706494437654570877485)
                  ·
                    rfl

theorem cell20_527371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_527371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527371 prefixEnd_527371 := by exact prefixLift 527371
  have htrace : WordTrace (prefixWord ++ tailWord_527371) baseStart_527371 baseEnd_527371 := by
    simpa [prefixWord, tailWord_527371, baseEnd_527371] using wordTrace_append hprefix tailTrace_527371
  have hstable : (prefixWord ++ tailWord_527371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527371).length < 2 ^ (prefixWord ++ tailWord_527371).sum := by decide
  have hdescent : baseEnd_527371 < baseStart_527371 := by decide
  rcases family_descends (prefixWord ++ tailWord_527371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527385 : List Nat := [1, 2, 1, 2, 1, 1, 12]
def baseStart_527385 : Nat := 118140960795 + 527385 * 2 ^ 59
def prefixEnd_527385 : Nat := 4983230072969 + 3 ^ 40 * 527385 * 2
def baseEnd_527385 : Nat := 26745876046570304934529

theorem tailTrace_527385 : CollatzResearch.WordTrace tailWord_527385 prefixEnd_527385 26745876046570304934529 := by
  unfold tailWord_527385
  simp only [CollatzResearch.WordTrace]
  refine ⟨19235311194381690032255609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12823540796254460021503739 19235311194381690032255609)
  ·
    refine ⟨14426483395786267524191707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19235311194381690032255609 14426483395786267524191707)
    ·
      refine ⟨21639725093679401286287561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14426483395786267524191707 21639725093679401286287561)
      ·
        refine ⟨16229793820259550964715671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21639725093679401286287561 16229793820259550964715671)
        ·
          refine ⟨24344690730389326447073507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16229793820259550964715671 24344690730389326447073507)
          ·
            refine ⟨36517036095583989670610261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24344690730389326447073507 36517036095583989670610261)
            ·
              refine ⟨26745876046570304934529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 36517036095583989670610261 26745876046570304934529)
              ·
                rfl

theorem cell20_527385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 12].length) (baseStart_527385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527385 prefixEnd_527385 := by exact prefixLift 527385
  have htrace : WordTrace (prefixWord ++ tailWord_527385) baseStart_527385 baseEnd_527385 := by
    simpa [prefixWord, tailWord_527385, baseEnd_527385] using wordTrace_append hprefix tailTrace_527385
  have hstable : (prefixWord ++ tailWord_527385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527385).length < 2 ^ (prefixWord ++ tailWord_527385).sum := by decide
  have hdescent : baseEnd_527385 < baseStart_527385 := by decide
  rcases family_descends (prefixWord ++ tailWord_527385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527391 : List Nat := [1, 1, 2, 4, 1, 4, 3, 2, 2]
def baseStart_527391 : Nat := 118140960795 + 527391 * 2 ^ 59
def prefixEnd_527391 : Nat := 4983230072969 + 3 ^ 40 * 527391 * 2
def baseEnd_527391 : Nat := 240715622982623390210737

theorem tailTrace_527391 : CollatzResearch.WordTrace tailWord_527391 prefixEnd_527391 240715622982623390210737 := by
  unfold tailWord_527391
  simp only [CollatzResearch.WordTrace]
  refine ⟨19235530032359953056974027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12823686688239968704649351 19235530032359953056974027)
  ·
    refine ⟨28853295048539929585461041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19235530032359953056974027 28853295048539929585461041)
    ·
      refine ⟨21639971286404947189095781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28853295048539929585461041 21639971286404947189095781)
      ·
        refine ⟨4057494616200927597955459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21639971286404947189095781 4057494616200927597955459)
        ·
          refine ⟨6086241924301391396933189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4057494616200927597955459 6086241924301391396933189)
          ·
            refine ⟨1141170360806510886924973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6086241924301391396933189 1141170360806510886924973)
            ·
              refine ⟨427938885302441582596865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1141170360806510886924973 427938885302441582596865)
              ·
                refine ⟨320954163976831186947649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427938885302441582596865 320954163976831186947649)
                ·
                  refine ⟨240715622982623390210737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320954163976831186947649 240715622982623390210737)
                  ·
                    rfl

theorem cell20_527391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 2].length) (baseStart_527391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527391 prefixEnd_527391 := by exact prefixLift 527391
  have htrace : WordTrace (prefixWord ++ tailWord_527391) baseStart_527391 baseEnd_527391 := by
    simpa [prefixWord, tailWord_527391, baseEnd_527391] using wordTrace_append hprefix tailTrace_527391
  have hstable : (prefixWord ++ tailWord_527391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527391).length < 2 ^ (prefixWord ++ tailWord_527391).sum := by decide
  have hdescent : baseEnd_527391 < baseStart_527391 := by decide
  rcases family_descends (prefixWord ++ tailWord_527391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527395 : List Nat := [1, 1, 1, 4, 3, 2, 3, 1, 4]
def baseStart_527395 : Nat := 118140960795 + 527395 * 2 ^ 59
def prefixEnd_527395 : Nat := 4983230072969 + 3 ^ 40 * 527395 * 2
def baseEnd_527395 : Nat := 240717448691617154077387

theorem tailTrace_527395 : CollatzResearch.WordTrace tailWord_527395 prefixEnd_527395 240717448691617154077387 := by
  unfold tailWord_527395
  simp only [CollatzResearch.WordTrace]
  refine ⟨19235675924345461740119639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12823783949563641160079759 19235675924345461740119639)
  ·
    refine ⟨28853513886518192610179459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19235675924345461740119639 28853513886518192610179459)
    ·
      refine ⟨43280270829777288915269189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28853513886518192610179459 43280270829777288915269189)
      ·
        refine ⟨8115050780583241671612973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43280270829777288915269189 8115050780583241671612973)
        ·
          refine ⟨3043144042718715626854865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8115050780583241671612973 3043144042718715626854865)
          ·
            refine ⟨2282358032039036720141149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3043144042718715626854865 2282358032039036720141149)
            ·
              refine ⟨855884262014638770052931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2282358032039036720141149 855884262014638770052931)
              ·
                refine ⟨1283826393021958155079397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 855884262014638770052931 1283826393021958155079397)
                ·
                  refine ⟨240717448691617154077387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1283826393021958155079397 240717448691617154077387)
                  ·
                    rfl

theorem cell20_527395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 4].length) (baseStart_527395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527395 prefixEnd_527395 := by exact prefixLift 527395
  have htrace : WordTrace (prefixWord ++ tailWord_527395) baseStart_527395 baseEnd_527395 := by
    simpa [prefixWord, tailWord_527395, baseEnd_527395] using wordTrace_append hprefix tailTrace_527395
  have hstable : (prefixWord ++ tailWord_527395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527395).length < 2 ^ (prefixWord ++ tailWord_527395).sum := by decide
  have hdescent : baseEnd_527395 < baseStart_527395 := by decide
  rcases family_descends (prefixWord ++ tailWord_527395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527453 : List Nat := [1, 4, 4, 1, 3, 1, 1, 5]
def baseStart_527453 : Nat := 118140960795 + 527453 * 2 ^ 59
def prefixEnd_527453 : Nat := 4983230072969 + 3 ^ 40 * 527453 * 2
def baseEnd_527453 : Nat := 80247973824008910047939

theorem tailTrace_527453 : CollatzResearch.WordTrace tailWord_527453 prefixEnd_527453 80247973824008910047939 := by
  unfold tailWord_527453
  simp only [CollatzResearch.WordTrace]
  refine ⟨19237791358135337645731013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12825194238756891763820675 19237791358135337645731013)
  ·
    refine ⟨3607085879650375808574565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19237791358135337645731013 3607085879650375808574565)
    ·
      refine ⟨676328602434445464107731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3607085879650375808574565 676328602434445464107731)
      ·
        refine ⟨1014492903651668196161597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676328602434445464107731 1014492903651668196161597)
        ·
          refine ⟨380434838869375573560599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1014492903651668196161597 380434838869375573560599)
          ·
            refine ⟨570652258304063360340899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380434838869375573560599 570652258304063360340899)
            ·
              refine ⟨855978387456095040511349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570652258304063360340899 855978387456095040511349)
              ·
                refine ⟨80247973824008910047939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 855978387456095040511349 80247973824008910047939)
                ·
                  rfl

theorem cell20_527453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 5].length) (baseStart_527453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527453 prefixEnd_527453 := by exact prefixLift 527453
  have htrace : WordTrace (prefixWord ++ tailWord_527453) baseStart_527453 baseEnd_527453 := by
    simpa [prefixWord, tailWord_527453, baseEnd_527453] using wordTrace_append hprefix tailTrace_527453
  have hstable : (prefixWord ++ tailWord_527453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527453).length < 2 ^ (prefixWord ++ tailWord_527453).sum := by decide
  have hdescent : baseEnd_527453 < baseStart_527453 := by decide
  rcases family_descends (prefixWord ++ tailWord_527453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527485 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 5]
def baseStart_527485 : Nat := 118140960795 + 527485 * 2 ^ 59
def prefixEnd_527485 : Nat := 4983230072969 + 3 ^ 40 * 527485 * 2
def baseEnd_527485 : Nat := 240758527143976841077019

theorem tailTrace_527485 : CollatzResearch.WordTrace tailWord_527485 prefixEnd_527485 240758527143976841077019 := by
  unfold tailWord_527485
  simp only [CollatzResearch.WordTrace]
  refine ⟨19238958494019407110895909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12825972329346271407263939 19238958494019407110895909)
  ·
    refine ⟨3607304717628638833292983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19238958494019407110895909 3607304717628638833292983)
    ·
      refine ⟨5410957076442958249939475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3607304717628638833292983 5410957076442958249939475)
      ·
        refine ⟨8116435614664437374909213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5410957076442958249939475 8116435614664437374909213)
        ·
          refine ⟨3043663355499164015590955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8116435614664437374909213 3043663355499164015590955)
          ·
            refine ⟨4565495033248746023386433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3043663355499164015590955 4565495033248746023386433)
            ·
              refine ⟨3424121274936559517539825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4565495033248746023386433 3424121274936559517539825)
              ·
                refine ⟨2568090956202419638154869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3424121274936559517539825 2568090956202419638154869)
                ·
                  refine ⟨240758527143976841077019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2568090956202419638154869 240758527143976841077019)
                  ·
                    rfl

theorem cell20_527485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_527485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527485 prefixEnd_527485 := by exact prefixLift 527485
  have htrace : WordTrace (prefixWord ++ tailWord_527485) baseStart_527485 baseEnd_527485 := by
    simpa [prefixWord, tailWord_527485, baseEnd_527485] using wordTrace_append hprefix tailTrace_527485
  have hstable : (prefixWord ++ tailWord_527485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527485).length < 2 ^ (prefixWord ++ tailWord_527485).sum := by decide
  have hdescent : baseEnd_527485 < baseStart_527485 := by decide
  rcases family_descends (prefixWord ++ tailWord_527485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527502 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_527502 : Nat := 118140960795 + 527502 * 2 ^ 59
def prefixEnd_527502 : Nat := 4983230072969 + 3 ^ 40 * 527502 * 2
def baseEnd_527502 : Nat := 240766286407200337510283

theorem tailTrace_527502 : CollatzResearch.WordTrace tailWord_527502 prefixEnd_527502 240766286407200337510283 := by
  unfold tailWord_527502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2404947316869727376783095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12826385689971879342843173 2404947316869727376783095)
  ·
    refine ⟨3607420975304591065174643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2404947316869727376783095 3607420975304591065174643)
    ·
      refine ⟨5411131462956886597761965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3607420975304591065174643 5411131462956886597761965)
      ·
        refine ⟨2029174298608832474160737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5411131462956886597761965 2029174298608832474160737)
        ·
          refine ⟨1521880723956624355620553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2029174298608832474160737 1521880723956624355620553)
          ·
            refine ⟨1141410542967468266715415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1521880723956624355620553 1141410542967468266715415)
            ·
              refine ⟨1712115814451202400073123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141410542967468266715415 1712115814451202400073123)
              ·
                refine ⟨2568173721676803600109685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1712115814451202400073123 2568173721676803600109685)
                ·
                  refine ⟨240766286407200337510283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2568173721676803600109685 240766286407200337510283)
                  ·
                    rfl

theorem cell20_527502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_527502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527502 prefixEnd_527502 := by exact prefixLift 527502
  have htrace : WordTrace (prefixWord ++ tailWord_527502) baseStart_527502 baseEnd_527502 := by
    simpa [prefixWord, tailWord_527502, baseEnd_527502] using wordTrace_append hprefix tailTrace_527502
  have hstable : (prefixWord ++ tailWord_527502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527502).length < 2 ^ (prefixWord ++ tailWord_527502).sum := by decide
  have hdescent : baseEnd_527502 < baseStart_527502 := by decide
  rcases family_descends (prefixWord ++ tailWord_527502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527523 : List Nat := [1, 1, 1, 4, 1, 1, 1, 7, 3]
def baseStart_527523 : Nat := 118140960795 + 527523 * 2 ^ 59
def prefixEnd_527523 : Nat := 4983230072969 + 3 ^ 40 * 527523 * 2
def baseEnd_527523 : Nat := 240775871379417597810197

theorem tailTrace_527523 : CollatzResearch.WordTrace tailWord_527523 prefixEnd_527523 240775871379417597810197 := by
  unfold tailWord_527523
  simp only [CollatzResearch.WordTrace]
  refine ⟨19240344467881739600779223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12826896311921159733852815 19240344467881739600779223)
  ·
    refine ⟨28860516701822609401168835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19240344467881739600779223 28860516701822609401168835)
    ·
      refine ⟨43290775052733914101753253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28860516701822609401168835 43290775052733914101753253)
      ·
        refine ⟨8117020322387608894078735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43290775052733914101753253 8117020322387608894078735)
        ·
          refine ⟨12175530483581413341118103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8117020322387608894078735 12175530483581413341118103)
          ·
            refine ⟨18263295725372120011677155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12175530483581413341118103 18263295725372120011677155)
            ·
              refine ⟨27394943588058180017515733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18263295725372120011677155 27394943588058180017515733)
              ·
                refine ⟨642068990345113594160525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 27394943588058180017515733 642068990345113594160525)
                ·
                  refine ⟨240775871379417597810197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 642068990345113594160525 240775871379417597810197)
                  ·
                    rfl

theorem cell20_527523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 3].length) (baseStart_527523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527523 prefixEnd_527523 := by exact prefixLift 527523
  have htrace : WordTrace (prefixWord ++ tailWord_527523) baseStart_527523 baseEnd_527523 := by
    simpa [prefixWord, tailWord_527523, baseEnd_527523] using wordTrace_append hprefix tailTrace_527523
  have hstable : (prefixWord ++ tailWord_527523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527523).length < 2 ^ (prefixWord ++ tailWord_527523).sum := by decide
  have hdescent : baseEnd_527523 < baseStart_527523 := by decide
  rcases family_descends (prefixWord ++ tailWord_527523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527533 : List Nat := [1, 5, 2, 1, 3, 1, 1, 6]
def baseStart_527533 : Nat := 118140960795 + 527533 * 2 ^ 59
def prefixEnd_527533 : Nat := 4983230072969 + 3 ^ 40 * 527533 * 2
def baseEnd_527533 : Nat := 80260145217300669158941

theorem tailTrace_527533 : CollatzResearch.WordTrace tailWord_527533 prefixEnd_527533 80260145217300669158941 := by
  unfold tailWord_527533
  simp only [CollatzResearch.WordTrace]
  refine ⟨19240709197845511308643253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12827139465230340872428835 19240709197845511308643253)
  ·
    refine ⟨1803816487298016685185305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19240709197845511308643253 1803816487298016685185305)
    ·
      refine ⟨1352862365473512513888979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1803816487298016685185305 1352862365473512513888979)
      ·
        refine ⟨2029293548210268770833469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1352862365473512513888979 2029293548210268770833469)
        ·
          refine ⟨760985080578850789062551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2029293548210268770833469 760985080578850789062551)
          ·
            refine ⟨1141477620868276183593827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760985080578850789062551 1141477620868276183593827)
            ·
              refine ⟨1712216431302414275390741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141477620868276183593827 1712216431302414275390741)
              ·
                refine ⟨80260145217300669158941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1712216431302414275390741 80260145217300669158941)
                ·
                  rfl

theorem cell20_527533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 6].length) (baseStart_527533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527533 prefixEnd_527533 := by exact prefixLift 527533
  have htrace : WordTrace (prefixWord ++ tailWord_527533) baseStart_527533 baseEnd_527533 := by
    simpa [prefixWord, tailWord_527533, baseEnd_527533] using wordTrace_append hprefix tailTrace_527533
  have hstable : (prefixWord ++ tailWord_527533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527533).length < 2 ^ (prefixWord ++ tailWord_527533).sum := by decide
  have hdescent : baseEnd_527533 < baseStart_527533 := by decide
  rcases family_descends (prefixWord ++ tailWord_527533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527547 : List Nat := [1, 1, 1, 1, 1, 2, 4, 7, 2]
def baseStart_527547 : Nat := 118140960795 + 527547 * 2 ^ 59
def prefixEnd_527547 : Nat := 4983230072969 + 3 ^ 40 * 527547 * 2
def baseEnd_527547 : Nat := 240786825633380181010099

theorem tailTrace_527547 : CollatzResearch.WordTrace tailWord_527547 prefixEnd_527547 240786825633380181010099 := by
  unfold tailWord_527547
  simp only [CollatzResearch.WordTrace]
  refine ⟨19241219819794791699652895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12827479879863194466435263 19241219819794791699652895)
  ·
    refine ⟨28861829729692187549479343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19241219819794791699652895 28861829729692187549479343)
    ·
      refine ⟨43292744594538281324219015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28861829729692187549479343 43292744594538281324219015)
      ·
        refine ⟨64939116891807421986328523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43292744594538281324219015 64939116891807421986328523)
        ·
          refine ⟨97408675337711132979492785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64939116891807421986328523 97408675337711132979492785)
          ·
            refine ⟨73056506503283349734619589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97408675337711132979492785 73056506503283349734619589)
            ·
              refine ⟨13698094969365628075241173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73056506503283349734619589 13698094969365628075241173)
              ·
                refine ⟨321049100844506908013465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13698094969365628075241173 321049100844506908013465)
                ·
                  refine ⟨240786825633380181010099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321049100844506908013465 240786825633380181010099)
                  ·
                    rfl

theorem cell20_527547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 2].length) (baseStart_527547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527547 prefixEnd_527547 := by exact prefixLift 527547
  have htrace : WordTrace (prefixWord ++ tailWord_527547) baseStart_527547 baseEnd_527547 := by
    simpa [prefixWord, tailWord_527547, baseEnd_527547] using wordTrace_append hprefix tailTrace_527547
  have hstable : (prefixWord ++ tailWord_527547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527547).length < 2 ^ (prefixWord ++ tailWord_527547).sum := by decide
  have hdescent : baseEnd_527547 < baseStart_527547 := by decide
  rcases family_descends (prefixWord ++ tailWord_527547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527574 : List Nat := [5, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_527574 : Nat := 118140960795 + 527574 * 2 ^ 59
def prefixEnd_527574 : Nat := 4983230072969 + 3 ^ 40 * 527574 * 2
def baseEnd_527574 : Nat := 240799149169088087109989

theorem tailTrace_527574 : CollatzResearch.WordTrace tailWord_527574 prefixEnd_527574 240799149169088087109989 := by
  unfold tailWord_527574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1202637786918560956930361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12828136393797983540590517 1202637786918560956930361)
  ·
    refine ⟨901978340188920717697771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1202637786918560956930361 901978340188920717697771)
    ·
      refine ⟨1352967510283381076546657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 901978340188920717697771 1352967510283381076546657)
      ·
        refine ⟨1014725632712535807409993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1352967510283381076546657 1014725632712535807409993)
        ·
          refine ⟨761044224534401855557495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1014725632712535807409993 761044224534401855557495)
          ·
            refine ⟨1141566336801602783336243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761044224534401855557495 1141566336801602783336243)
            ·
              refine ⟨1712349505202404175004365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141566336801602783336243 1712349505202404175004365)
              ·
                refine ⟨642131064450901565626637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1712349505202404175004365 642131064450901565626637)
                ·
                  refine ⟨240799149169088087109989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 642131064450901565626637 240799149169088087109989)
                  ·
                    rfl

theorem cell20_527574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_527574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527574 prefixEnd_527574 := by exact prefixLift 527574
  have htrace : WordTrace (prefixWord ++ tailWord_527574) baseStart_527574 baseEnd_527574 := by
    simpa [prefixWord, tailWord_527574, baseEnd_527574] using wordTrace_append hprefix tailTrace_527574
  have hstable : (prefixWord ++ tailWord_527574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527574).length < 2 ^ (prefixWord ++ tailWord_527574).sum := by decide
  have hdescent : baseEnd_527574 < baseStart_527574 := by decide
  rcases family_descends (prefixWord ++ tailWord_527574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527575 : List Nat := [1, 1, 3, 2, 1, 2, 3, 7]
def baseStart_527575 : Nat := 118140960795 + 527575 * 2 ^ 59
def prefixEnd_527575 : Nat := 4983230072969 + 3 ^ 40 * 527575 * 2
def baseEnd_527575 : Nat := 80266535198778842692217

theorem tailTrace_527575 : CollatzResearch.WordTrace tailWord_527575 prefixEnd_527575 80266535198778842692217 := by
  unfold tailWord_527575
  simp only [CollatzResearch.WordTrace]
  refine ⟨19242241063693352481672179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12828160709128901654448119 19242241063693352481672179)
  ·
    refine ⟨28863361595540028722508269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19242241063693352481672179 28863361595540028722508269)
    ·
      refine ⟨10823760598327510770940601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28863361595540028722508269 10823760598327510770940601)
      ·
        refine ⟨8117820448745633078205451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10823760598327510770940601 8117820448745633078205451)
        ·
          refine ⟨12176730673118449617308177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8117820448745633078205451 12176730673118449617308177)
          ·
            refine ⟨9132548004838837212981133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12176730673118449617308177 9132548004838837212981133)
            ·
              refine ⟨3424705501814563954867925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9132548004838837212981133 3424705501814563954867925)
              ·
                refine ⟨80266535198778842692217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3424705501814563954867925 80266535198778842692217)
                ·
                  rfl

theorem cell20_527575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 7].length) (baseStart_527575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527575 prefixEnd_527575 := by exact prefixLift 527575
  have htrace : WordTrace (prefixWord ++ tailWord_527575) baseStart_527575 baseEnd_527575 := by
    simpa [prefixWord, tailWord_527575, baseEnd_527575] using wordTrace_append hprefix tailTrace_527575
  have hstable : (prefixWord ++ tailWord_527575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527575).length < 2 ^ (prefixWord ++ tailWord_527575).sum := by decide
  have hdescent : baseEnd_527575 < baseStart_527575 := by decide
  rcases family_descends (prefixWord ++ tailWord_527575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527619 : List Nat := [1, 1, 1, 3, 2, 6, 2, 2, 2]
def baseStart_527619 : Nat := 118140960795 + 527619 * 2 ^ 59
def prefixEnd_527619 : Nat := 4983230072969 + 3 ^ 40 * 527619 * 2
def baseEnd_527619 : Nat := 240819688395267930609805

theorem tailTrace_527619 : CollatzResearch.WordTrace tailWord_527619 prefixEnd_527619 240819688395267930609805 := by
  unfold tailWord_527619
  simp only [CollatzResearch.WordTrace]
  refine ⟨19243845875533947996273911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12829230583689298664182607 19243845875533947996273911)
  ·
    refine ⟨28865768813300921994410867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19243845875533947996273911 28865768813300921994410867)
    ·
      refine ⟨43298653219951382991616301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28865768813300921994410867 43298653219951382991616301)
      ·
        refine ⟨16236994957481768621856113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43298653219951382991616301 16236994957481768621856113)
        ·
          refine ⟨12177746218111326466392085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16236994957481768621856113 12177746218111326466392085)
          ·
            refine ⟨570831853973968428112129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12177746218111326466392085 570831853973968428112129)
            ·
              refine ⟨428123890480476321084097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570831853973968428112129 428123890480476321084097)
              ·
                refine ⟨321092917860357240813073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428123890480476321084097 321092917860357240813073)
                ·
                  refine ⟨240819688395267930609805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321092917860357240813073 240819688395267930609805)
                  ·
                    rfl

theorem cell20_527619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 2].length) (baseStart_527619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527619 prefixEnd_527619 := by exact prefixLift 527619
  have htrace : WordTrace (prefixWord ++ tailWord_527619) baseStart_527619 baseEnd_527619 := by
    simpa [prefixWord, tailWord_527619, baseEnd_527619] using wordTrace_append hprefix tailTrace_527619
  have hstable : (prefixWord ++ tailWord_527619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527619).length < 2 ^ (prefixWord ++ tailWord_527619).sum := by decide
  have hdescent : baseEnd_527619 < baseStart_527619 := by decide
  rcases family_descends (prefixWord ++ tailWord_527619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527630 : List Nat := [4, 1, 1, 2, 1, 3, 3, 5]
def baseStart_527630 : Nat := 118140960795 + 527630 * 2 ^ 59
def prefixEnd_527630 : Nat := 4983230072969 + 3 ^ 40 * 527630 * 2
def baseEnd_527630 : Nat := 80274903031666927081031

theorem tailTrace_527630 : CollatzResearch.WordTrace tailWord_527630 prefixEnd_527630 80274903031666927081031 := by
  unfold tailWord_527630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2405530884811762109365543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12829498052329397916616229 2405530884811762109365543)
  ·
    refine ⟨3608296327217643164048315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2405530884811762109365543 3608296327217643164048315)
    ·
      refine ⟨5412444490826464746072473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3608296327217643164048315 5412444490826464746072473)
      ·
        refine ⟨4059333368119848559554355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5412444490826464746072473 4059333368119848559554355)
        ·
          refine ⟨6089000052179772839331533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4059333368119848559554355 6089000052179772839331533)
          ·
            refine ⟨2283375019567414814749325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6089000052179772839331533 2283375019567414814749325)
            ·
              refine ⟨856265632337780555530997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2283375019567414814749325 856265632337780555530997)
              ·
                refine ⟨80274903031666927081031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 856265632337780555530997 80274903031666927081031)
                ·
                  rfl

theorem cell20_527630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_527630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527630 prefixEnd_527630 := by exact prefixLift 527630
  have htrace : WordTrace (prefixWord ++ tailWord_527630) baseStart_527630 baseEnd_527630 := by
    simpa [prefixWord, tailWord_527630, baseEnd_527630] using wordTrace_append hprefix tailTrace_527630
  have hstable : (prefixWord ++ tailWord_527630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527630).length < 2 ^ (prefixWord ++ tailWord_527630).sum := by decide
  have hdescent : baseEnd_527630 < baseStart_527630 := by decide
  rcases family_descends (prefixWord ++ tailWord_527630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527644 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 6]
def baseStart_527644 : Nat := 118140960795 + 527644 * 2 ^ 59
def prefixEnd_527644 : Nat := 4983230072969 + 3 ^ 40 * 527644 * 2
def baseEnd_527644 : Nat := 240831099076478954776369

theorem tailTrace_527644 : CollatzResearch.WordTrace tailWord_527644 prefixEnd_527644 240831099076478954776369 := by
  unfold tailWord_527644
  simp only [CollatzResearch.WordTrace]
  refine ⟨9622378850221688632966993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12829838466962251510622657 9622378850221688632966993)
  ·
    refine ⟨7216784137666266474725245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9622378850221688632966993 7216784137666266474725245)
    ·
      refine ⟨2706294051624849928021967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7216784137666266474725245 2706294051624849928021967)
      ·
        refine ⟨4059441077437274892032951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2706294051624849928021967 4059441077437274892032951)
        ·
          refine ⟨6089161616155912338049427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4059441077437274892032951 6089161616155912338049427)
          ·
            refine ⟨9133742424233868507074141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6089161616155912338049427 9133742424233868507074141)
            ·
              refine ⟨3425153409087700690152803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9133742424233868507074141 3425153409087700690152803)
              ·
                refine ⟨5137730113631551035229205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3425153409087700690152803 5137730113631551035229205)
                ·
                  refine ⟨240831099076478954776369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5137730113631551035229205 240831099076478954776369)
                  ·
                    rfl

theorem cell20_527644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_527644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527644 prefixEnd_527644 := by exact prefixLift 527644
  have htrace : WordTrace (prefixWord ++ tailWord_527644) baseStart_527644 baseEnd_527644 := by
    simpa [prefixWord, tailWord_527644, baseEnd_527644] using wordTrace_append hprefix tailTrace_527644
  have hstable : (prefixWord ++ tailWord_527644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527644).length < 2 ^ (prefixWord ++ tailWord_527644).sum := by decide
  have hdescent : baseEnd_527644 < baseStart_527644 := by decide
  rcases family_descends (prefixWord ++ tailWord_527644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527647 : List Nat := [1, 1, 2, 4, 4, 1, 3, 4]
def baseStart_527647 : Nat := 118140960795 + 527647 * 2 ^ 59
def prefixEnd_527647 : Nat := 4983230072969 + 3 ^ 40 * 527647 * 2
def baseEnd_527647 : Nat := 80277489452741425892119

theorem tailTrace_527647 : CollatzResearch.WordTrace tailWord_527647 prefixEnd_527647 80277489452741425892119 := by
  unfold tailWord_527647
  simp only [CollatzResearch.WordTrace]
  refine ⟨19244867119432508778293195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12829911412955005852195463 19244867119432508778293195)
  ·
    refine ⟨28867300679148763167439793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19244867119432508778293195 28867300679148763167439793)
    ·
      refine ⟨21650475509361572375579845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28867300679148763167439793 21650475509361572375579845)
      ·
        refine ⟨4059464158005294820421221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21650475509361572375579845 4059464158005294820421221)
        ·
          refine ⟨761149529625992778828979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4059464158005294820421221 761149529625992778828979)
          ·
            refine ⟨1141724294438989168243469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761149529625992778828979 1141724294438989168243469)
            ·
              refine ⟨428146610414620938091301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1141724294438989168243469 428146610414620938091301)
              ·
                refine ⟨80277489452741425892119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 428146610414620938091301 80277489452741425892119)
                ·
                  rfl

theorem cell20_527647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 4].length) (baseStart_527647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527647 prefixEnd_527647 := by exact prefixLift 527647
  have htrace : WordTrace (prefixWord ++ tailWord_527647) baseStart_527647 baseEnd_527647 := by
    simpa [prefixWord, tailWord_527647, baseEnd_527647] using wordTrace_append hprefix tailTrace_527647
  have hstable : (prefixWord ++ tailWord_527647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527647).length < 2 ^ (prefixWord ++ tailWord_527647).sum := by decide
  have hdescent : baseEnd_527647 < baseStart_527647 := by decide
  rcases family_descends (prefixWord ++ tailWord_527647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527668 : List Nat := [2, 5, 1, 1, 1, 1, 9]
def baseStart_527668 : Nat := 118140960795 + 527668 * 2 ^ 59
def prefixEnd_527668 : Nat := 4983230072969 + 3 ^ 40 * 527668 * 2
def baseEnd_527668 : Nat := 26760228147826837552919

theorem tailTrace_527668 : CollatzResearch.WordTrace tailWord_527668 prefixEnd_527668 26760228147826837552919 := by
  unfold tailWord_527668
  simp only [CollatzResearch.WordTrace]
  refine ⟨9622816526178214682403829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12830422034904286243205105 9622816526178214682403829)
  ·
    refine ⟨902139049329207626475359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9622816526178214682403829 902139049329207626475359)
    ·
      refine ⟨1353208573993811439713039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 902139049329207626475359 1353208573993811439713039)
      ·
        refine ⟨2029812860990717159569559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1353208573993811439713039 2029812860990717159569559)
        ·
          refine ⟨3044719291486075739354339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2029812860990717159569559 3044719291486075739354339)
          ·
            refine ⟨4567078937229113609031509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3044719291486075739354339 4567078937229113609031509)
            ·
              refine ⟨26760228147826837552919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4567078937229113609031509 26760228147826837552919)
              ·
                rfl

theorem cell20_527668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 9].length) (baseStart_527668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527668 prefixEnd_527668 := by exact prefixLift 527668
  have htrace : WordTrace (prefixWord ++ tailWord_527668) baseStart_527668 baseEnd_527668 := by
    simpa [prefixWord, tailWord_527668, baseEnd_527668] using wordTrace_append hprefix tailTrace_527668
  have hstable : (prefixWord ++ tailWord_527668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527668).length < 2 ^ (prefixWord ++ tailWord_527668).sum := by decide
  have hdescent : baseEnd_527668 < baseStart_527668 := by decide
  rcases family_descends (prefixWord ++ tailWord_527668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527678 : List Nat := [4, 2, 1, 2, 1, 1, 1, 6, 2]
def baseStart_527678 : Nat := 118140960795 + 527678 * 2 ^ 59
def prefixEnd_527678 : Nat := 4983230072969 + 3 ^ 40 * 527678 * 2
def baseEnd_527678 : Nat := 240846617602925947642897

theorem tailTrace_527678 : CollatzResearch.WordTrace tailWord_527678 prefixEnd_527678 240846617602925947642897 := by
  unfold tailWord_527678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2405749722790025134083961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12830665188213467381781125 2405749722790025134083961)
  ·
    refine ⟨1804312292092518850562971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2405749722790025134083961 1804312292092518850562971)
    ·
      refine ⟨2706468438138778275844457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1804312292092518850562971 2706468438138778275844457)
      ·
        refine ⟨2029851328604083706883343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2706468438138778275844457 2029851328604083706883343)
        ·
          refine ⟨3044776992906125560325015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2029851328604083706883343 3044776992906125560325015)
          ·
            refine ⟨4567165489359188340487523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3044776992906125560325015 4567165489359188340487523)
            ·
              refine ⟨6850748234038782510731285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4567165489359188340487523 6850748234038782510731285)
              ·
                refine ⟨321128823470567930190529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6850748234038782510731285 321128823470567930190529)
                ·
                  refine ⟨240846617602925947642897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321128823470567930190529 240846617602925947642897)
                  ·
                    rfl

theorem cell20_527678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_527678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527678 prefixEnd_527678 := by exact prefixLift 527678
  have htrace : WordTrace (prefixWord ++ tailWord_527678) baseStart_527678 baseEnd_527678 := by
    simpa [prefixWord, tailWord_527678, baseEnd_527678] using wordTrace_append hprefix tailTrace_527678
  have hstable : (prefixWord ++ tailWord_527678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527678).length < 2 ^ (prefixWord ++ tailWord_527678).sum := by decide
  have hdescent : baseEnd_527678 < baseStart_527678 := by decide
  rcases family_descends (prefixWord ++ tailWord_527678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527706 : List Nat := [3, 1, 1, 2, 1, 2, 6, 4]
def baseStart_527706 : Nat := 118140960795 + 527706 * 2 ^ 59
def prefixEnd_527706 : Nat := 4983230072969 + 3 ^ 40 * 527706 * 2
def baseEnd_527706 : Nat := 80286465855294098236483

theorem tailTrace_527706 : CollatzResearch.WordTrace tailWord_527706 prefixEnd_527706 80286465855294098236483 := by
  unfold tailWord_527706
  simp only [CollatzResearch.WordTrace]
  refine ⟨4811754756554690463672743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12831346017479174569793981 4811754756554690463672743)
  ·
    refine ⟨7217632134832035695509115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4811754756554690463672743 7217632134832035695509115)
    ·
      refine ⟨10826448202248053543263673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7217632134832035695509115 10826448202248053543263673)
      ·
        refine ⟨8119836151686040157447755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10826448202248053543263673 8119836151686040157447755)
        ·
          refine ⟨12179754227529060236171633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8119836151686040157447755 12179754227529060236171633)
          ·
            refine ⟨9134815670646795177128725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12179754227529060236171633 9134815670646795177128725)
            ·
              refine ⟨428194484561568523927909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9134815670646795177128725 428194484561568523927909)
              ·
                refine ⟨80286465855294098236483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 428194484561568523927909 80286465855294098236483)
                ·
                  rfl

theorem cell20_527706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_527706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527706 prefixEnd_527706 := by exact prefixLift 527706
  have htrace : WordTrace (prefixWord ++ tailWord_527706) baseStart_527706 baseEnd_527706 := by
    simpa [prefixWord, tailWord_527706, baseEnd_527706] using wordTrace_append hprefix tailTrace_527706
  have hstable : (prefixWord ++ tailWord_527706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527706).length < 2 ^ (prefixWord ++ tailWord_527706).sum := by decide
  have hdescent : baseEnd_527706 < baseStart_527706 := by decide
  rcases family_descends (prefixWord ++ tailWord_527706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527716 : List Nat := [2, 3, 1, 1, 3, 2, 3, 3, 2]
def baseStart_527716 : Nat := 118140960795 + 527716 * 2 ^ 59
def prefixEnd_527716 : Nat := 4983230072969 + 3 ^ 40 * 527716 * 2
def baseEnd_527716 : Nat := 240863961838366704376075

theorem tailTrace_527716 : CollatzResearch.WordTrace tailWord_527716 prefixEnd_527716 240863961838366704376075 := by
  unfold tailWord_527716
  simp only [CollatzResearch.WordTrace]
  refine ⟨9623691878091266781277501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12831589170788355708370001 9623691878091266781277501)
  ·
    refine ⟨3608884454284225042979063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9623691878091266781277501 3608884454284225042979063)
    ·
      refine ⟨5413326681426337564468595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3608884454284225042979063 5413326681426337564468595)
      ·
        refine ⟨8119990022139506346702893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5413326681426337564468595 8119990022139506346702893)
        ·
          refine ⟨3044996258302314880013585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8119990022139506346702893 3044996258302314880013585)
          ·
            refine ⟨2283747193726736160010189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3044996258302314880013585 2283747193726736160010189)
            ·
              refine ⟨856405197647526060003821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2283747193726736160010189 856405197647526060003821)
              ·
                refine ⟨321151949117822272501433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 856405197647526060003821 321151949117822272501433)
                ·
                  refine ⟨240863961838366704376075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321151949117822272501433 240863961838366704376075)
                  ·
                    rfl

theorem cell20_527716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_527716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527716 prefixEnd_527716 := by exact prefixLift 527716
  have htrace : WordTrace (prefixWord ++ tailWord_527716) baseStart_527716 baseEnd_527716 := by
    simpa [prefixWord, tailWord_527716, baseEnd_527716] using wordTrace_append hprefix tailTrace_527716
  have hstable : (prefixWord ++ tailWord_527716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527716).length < 2 ^ (prefixWord ++ tailWord_527716).sum := by decide
  have hdescent : baseEnd_527716 < baseStart_527716 := by decide
  rcases family_descends (prefixWord ++ tailWord_527716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527733 : List Nat := [1, 3, 4, 1, 4, 1, 1, 1, 4]
def baseStart_527733 : Nat := 118140960795 + 527733 * 2 ^ 59
def prefixEnd_527733 : Nat := 4983230072969 + 3 ^ 40 * 527733 * 2
def baseEnd_527733 : Nat := 240871721101590200809339

theorem tailTrace_527733 : CollatzResearch.WordTrace tailWord_527733 prefixEnd_527733 240871721101590200809339 := by
  unfold tailWord_527733
  simp only [CollatzResearch.WordTrace]
  refine ⟨19248003797120945465923853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12832002531413963643949235 19248003797120945465923853)
  ·
    refine ⟨7218001423920354549721445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19248003797120945465923853 7218001423920354549721445)
    ·
      refine ⟨1353375266985066478072771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7218001423920354549721445 1353375266985066478072771)
      ·
        refine ⟨2030062900477599717109157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1353375266985066478072771 2030062900477599717109157)
        ·
          refine ⟨380636793839549946957967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2030062900477599717109157 380636793839549946957967)
          ·
            refine ⟨570955190759324920436951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380636793839549946957967 570955190759324920436951)
            ·
              refine ⟨856432786138987380655427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570955190759324920436951 856432786138987380655427)
              ·
                refine ⟨1284649179208481070983141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 856432786138987380655427 1284649179208481070983141)
                ·
                  refine ⟨240871721101590200809339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1284649179208481070983141 240871721101590200809339)
                  ·
                    rfl

theorem cell20_527733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_527733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527733 prefixEnd_527733 := by exact prefixLift 527733
  have htrace : WordTrace (prefixWord ++ tailWord_527733) baseStart_527733 baseEnd_527733 := by
    simpa [prefixWord, tailWord_527733, baseEnd_527733] using wordTrace_append hprefix tailTrace_527733
  have hstable : (prefixWord ++ tailWord_527733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527733).length < 2 ^ (prefixWord ++ tailWord_527733).sum := by decide
  have hdescent : baseEnd_527733 < baseStart_527733 := by decide
  rcases family_descends (prefixWord ++ tailWord_527733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527737 : List Nat := [1, 2, 1, 3, 2, 1, 2, 6, 2]
def baseStart_527737 : Nat := 118140960795 + 527737 * 2 ^ 59
def prefixEnd_527737 : Nat := 4983230072969 + 3 ^ 40 * 527737 * 2
def baseEnd_527737 : Nat := 240873546810583964675989

theorem tailTrace_527737 : CollatzResearch.WordTrace tailWord_527737 prefixEnd_527737 240873546810583964675989 := by
  unfold tailWord_527737
  simp only [CollatzResearch.WordTrace]
  refine ⟨19248149689106454149069465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12832099792737636099379643 19248149689106454149069465)
  ·
    refine ⟨14436112266829840611802099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19248149689106454149069465 14436112266829840611802099)
    ·
      refine ⟨21654168400244760917703149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14436112266829840611802099 21654168400244760917703149)
      ·
        refine ⟨8120313150091785344138681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21654168400244760917703149 8120313150091785344138681)
        ·
          refine ⟨6090234862568839008104011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8120313150091785344138681 6090234862568839008104011)
          ·
            refine ⟨9135352293853258512156017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6090234862568839008104011 9135352293853258512156017)
            ·
              refine ⟨6851514220389943884117013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9135352293853258512156017 6851514220389943884117013)
              ·
                refine ⟨321164729080778619567985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6851514220389943884117013 321164729080778619567985)
                ·
                  refine ⟨240873546810583964675989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321164729080778619567985 240873546810583964675989)
                  ·
                    rfl

theorem cell20_527737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 2].length) (baseStart_527737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527737 prefixEnd_527737 := by exact prefixLift 527737
  have htrace : WordTrace (prefixWord ++ tailWord_527737) baseStart_527737 baseEnd_527737 := by
    simpa [prefixWord, tailWord_527737, baseEnd_527737] using wordTrace_append hprefix tailTrace_527737
  have hstable : (prefixWord ++ tailWord_527737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527737).length < 2 ^ (prefixWord ++ tailWord_527737).sum := by decide
  have hdescent : baseEnd_527737 < baseStart_527737 := by decide
  rcases family_descends (prefixWord ++ tailWord_527737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527747 : List Nat := [1, 1, 1, 3, 5, 3, 2, 1, 3]
def baseStart_527747 : Nat := 118140960795 + 527747 * 2 ^ 59
def prefixEnd_527747 : Nat := 4983230072969 + 3 ^ 40 * 527747 * 2
def baseEnd_527747 : Nat := 240878111083068374342615

theorem tailTrace_527747 : CollatzResearch.WordTrace tailWord_527747 prefixEnd_527747 240878111083068374342615 := by
  unfold tailWord_527747
  simp only [CollatzResearch.WordTrace]
  refine ⟨19248514419070225856933495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12832342946046817237955663 19248514419070225856933495)
  ·
    refine ⟨28872771628605338785400243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19248514419070225856933495 28872771628605338785400243)
    ·
      refine ⟨43309157442908008178100365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28872771628605338785400243 43309157442908008178100365)
      ·
        refine ⟨16240934041090503066787637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43309157442908008178100365 16240934041090503066787637)
        ·
          refine ⟨1522587566352234662511341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16240934041090503066787637 1522587566352234662511341)
          ·
            refine ⟨570970337382087998441753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1522587566352234662511341 570970337382087998441753)
            ·
              refine ⟨428227753036565998831315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570970337382087998441753 428227753036565998831315)
              ·
                refine ⟨642341629554848998246973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428227753036565998831315 642341629554848998246973)
                ·
                  refine ⟨240878111083068374342615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 642341629554848998246973 240878111083068374342615)
                  ·
                    rfl

theorem cell20_527747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 3].length) (baseStart_527747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527747 prefixEnd_527747 := by exact prefixLift 527747
  have htrace : WordTrace (prefixWord ++ tailWord_527747) baseStart_527747 baseEnd_527747 := by
    simpa [prefixWord, tailWord_527747, baseEnd_527747] using wordTrace_append hprefix tailTrace_527747
  have hstable : (prefixWord ++ tailWord_527747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527747).length < 2 ^ (prefixWord ++ tailWord_527747).sum := by decide
  have hdescent : baseEnd_527747 < baseStart_527747 := by decide
  rcases family_descends (prefixWord ++ tailWord_527747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527765 : List Nat := [1, 3, 2, 1, 1, 2, 4, 6]
def baseStart_527765 : Nat := 118140960795 + 527765 * 2 ^ 59
def prefixEnd_527765 : Nat := 4983230072969 + 3 ^ 40 * 527765 * 2
def baseEnd_527765 : Nat := 80295442257846770580847

theorem tailTrace_527765 : CollatzResearch.WordTrace tailWord_527765 prefixEnd_527765 80295442257846770580847 := by
  unfold tailWord_527765
  simp only [CollatzResearch.WordTrace]
  refine ⟨19249170933005014931088749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12832780622003343287392499 19249170933005014931088749)
  ·
    refine ⟨7218439099876880599158281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19249170933005014931088749 7218439099876880599158281)
    ·
      refine ⟨5413829324907660449368711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7218439099876880599158281 5413829324907660449368711)
      ·
        refine ⟨8120743987361490674053067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5413829324907660449368711 8120743987361490674053067)
        ·
          refine ⟨12181115981042236011079601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8120743987361490674053067 12181115981042236011079601)
          ·
            refine ⟨9135836985781677008309701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12181115981042236011079601 9135836985781677008309701)
            ·
              refine ⟨1712969434834064439058069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9135836985781677008309701 1712969434834064439058069)
              ·
                refine ⟨80295442257846770580847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1712969434834064439058069 80295442257846770580847)
                ·
                  rfl

theorem cell20_527765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 6].length) (baseStart_527765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527765 prefixEnd_527765 := by exact prefixLift 527765
  have htrace : WordTrace (prefixWord ++ tailWord_527765) baseStart_527765 baseEnd_527765 := by
    simpa [prefixWord, tailWord_527765, baseEnd_527765] using wordTrace_append hprefix tailTrace_527765
  have hstable : (prefixWord ++ tailWord_527765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527765).length < 2 ^ (prefixWord ++ tailWord_527765).sum := by decide
  have hdescent : baseEnd_527765 < baseStart_527765 := by decide
  rcases family_descends (prefixWord ++ tailWord_527765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527841 : List Nat := [1, 2, 3, 1, 2, 4, 7]
def baseStart_527841 : Nat := 118140960795 + 527841 * 2 ^ 59
def prefixEnd_527841 : Nat := 4983230072969 + 3 ^ 40 * 527841 * 2
def baseEnd_527841 : Nat := 26769001693824647245433

theorem tailTrace_527841 : CollatzResearch.WordTrace tailWord_527841 prefixEnd_527841 26769001693824647245433 := by
  unfold tailWord_527841
  simp only [CollatzResearch.WordTrace]
  refine ⟨19251942880729679910855377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12834628587153119940570251 19251942880729679910855377)
  ·
    refine ⟨14438957160547259933141533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19251942880729679910855377 14438957160547259933141533)
    ·
      refine ⟨5414608935205222474928075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14438957160547259933141533 5414608935205222474928075)
      ·
        refine ⟨8121913402807833712392113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5414608935205222474928075 8121913402807833712392113)
        ·
          refine ⟨6091435052105875284294085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8121913402807833712392113 6091435052105875284294085)
          ·
            refine ⟨1142144072269851615805141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6091435052105875284294085 1142144072269851615805141)
            ·
              refine ⟨26769001693824647245433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1142144072269851615805141 26769001693824647245433)
              ·
                rfl

theorem cell20_527841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 7].length) (baseStart_527841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527841 prefixEnd_527841 := by exact prefixLift 527841
  have htrace : WordTrace (prefixWord ++ tailWord_527841) baseStart_527841 baseEnd_527841 := by
    simpa [prefixWord, tailWord_527841, baseEnd_527841] using wordTrace_append hprefix tailTrace_527841
  have hstable : (prefixWord ++ tailWord_527841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527841).length < 2 ^ (prefixWord ++ tailWord_527841).sum := by decide
  have hdescent : baseEnd_527841 < baseStart_527841 := by decide
  rcases family_descends (prefixWord ++ tailWord_527841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527892 : List Nat := [2, 4, 3, 1, 3, 1, 6]
def baseStart_527892 : Nat := 118140960795 + 527892 * 2 ^ 59
def prefixEnd_527892 : Nat := 4983230072969 + 3 ^ 40 * 527892 * 2
def baseEnd_527892 : Nat := 26771588114899146056521

theorem tailTrace_527892 : CollatzResearch.WordTrace tailWord_527892 prefixEnd_527892 26771588114899146056521 := by
  unfold tailWord_527892
  simp only [CollatzResearch.WordTrace]
  refine ⟨9626901501772457810480965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12835868669029943747307953 9626901501772457810480965)
  ·
    refine ⟨1805044031582335839465181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9626901501772457810480965 1805044031582335839465181)
    ·
      refine ⟨676891511843375939799443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1805044031582335839465181 676891511843375939799443)
      ·
        refine ⟨1015337267765063909699165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676891511843375939799443 1015337267765063909699165)
        ·
          refine ⟨380751475411898966137187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1015337267765063909699165 380751475411898966137187)
          ·
            refine ⟨571127213117848449205781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380751475411898966137187 571127213117848449205781)
            ·
              refine ⟨26771588114899146056521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 571127213117848449205781 26771588114899146056521)
              ·
                rfl

theorem cell20_527892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 6].length) (baseStart_527892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527892 prefixEnd_527892 := by exact prefixLift 527892
  have htrace : WordTrace (prefixWord ++ tailWord_527892) baseStart_527892 baseEnd_527892 := by
    simpa [prefixWord, tailWord_527892, baseEnd_527892] using wordTrace_append hprefix tailTrace_527892
  have hstable : (prefixWord ++ tailWord_527892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527892).length < 2 ^ (prefixWord ++ tailWord_527892).sum := by decide
  have hdescent : baseEnd_527892 < baseStart_527892 := by decide
  rcases family_descends (prefixWord ++ tailWord_527892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527896 : List Nat := [2, 1, 2, 3, 4, 2, 6]
def baseStart_527896 : Nat := 118140960795 + 527896 * 2 ^ 59
def prefixEnd_527896 : Nat := 4983230072969 + 3 ^ 40 * 527896 * 2
def baseEnd_527896 : Nat := 26771790971454008708371

theorem tailTrace_527896 : CollatzResearch.WordTrace tailWord_527896 prefixEnd_527896 26771790971454008708371 := by
  unfold tailWord_527896
  simp only [CollatzResearch.WordTrace]
  refine ⟨9626974447765212152053771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12835965930353616202738361 9626974447765212152053771)
  ·
    refine ⟨14440461671647818228080657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9626974447765212152053771 14440461671647818228080657)
    ·
      refine ⟨10830346253735863671060493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14440461671647818228080657 10830346253735863671060493)
      ·
        refine ⟨4061379845150948876647685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10830346253735863671060493 4061379845150948876647685)
        ·
          refine ⟨761508720965802914371441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4061379845150948876647685 761508720965802914371441)
          ·
            refine ⟨571131540724352185778581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 761508720965802914371441 571131540724352185778581)
            ·
              refine ⟨26771790971454008708371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 571131540724352185778581 26771790971454008708371)
              ·
                rfl

theorem cell20_527896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 6].length) (baseStart_527896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527896 prefixEnd_527896 := by exact prefixLift 527896
  have htrace : WordTrace (prefixWord ++ tailWord_527896) baseStart_527896 baseEnd_527896 := by
    simpa [prefixWord, tailWord_527896, baseEnd_527896] using wordTrace_append hprefix tailTrace_527896
  have hstable : (prefixWord ++ tailWord_527896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527896).length < 2 ^ (prefixWord ++ tailWord_527896).sum := by decide
  have hdescent : baseEnd_527896 < baseStart_527896 := by decide
  rcases family_descends (prefixWord ++ tailWord_527896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527962 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_527962 : Nat := 118140960795 + 527962 * 2 ^ 59
def prefixEnd_527962 : Nat := 4983230072969 + 3 ^ 40 * 527962 * 2
def baseEnd_527962 : Nat := 240976242941483182175069

theorem tailTrace_527962 : CollatzResearch.WordTrace tailWord_527962 prefixEnd_527962 240976242941483182175069 := by
  unfold tailWord_527962
  simp only [CollatzResearch.WordTrace]
  refine ⟨4814089028322829394002535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12837570742194211717340093 4814089028322829394002535)
  ·
    refine ⟨7221133542484244091003803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4814089028322829394002535 7221133542484244091003803)
    ·
      refine ⟨10831700313726366136505705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7221133542484244091003803 10831700313726366136505705)
      ·
        refine ⟨8123775235294774602379279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10831700313726366136505705 8123775235294774602379279)
        ·
          refine ⟨12185662852942161903568919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8123775235294774602379279 12185662852942161903568919)
          ·
            refine ⟨18278494279413242855353379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12185662852942161903568919 18278494279413242855353379)
            ·
              refine ⟨27417741419119864283030069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18278494279413242855353379 27417741419119864283030069)
              ·
                refine ⟨2570413258042487276534069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27417741419119864283030069 2570413258042487276534069)
                ·
                  refine ⟨240976242941483182175069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2570413258042487276534069 240976242941483182175069)
                  ·
                    rfl

theorem cell20_527962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_527962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527962 prefixEnd_527962 := by exact prefixLift 527962
  have htrace : WordTrace (prefixWord ++ tailWord_527962) baseStart_527962 baseEnd_527962 := by
    simpa [prefixWord, tailWord_527962, baseEnd_527962] using wordTrace_append hprefix tailTrace_527962
  have hstable : (prefixWord ++ tailWord_527962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527962).length < 2 ^ (prefixWord ++ tailWord_527962).sum := by decide
  have hdescent : baseEnd_527962 < baseStart_527962 := by decide
  rcases family_descends (prefixWord ++ tailWord_527962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527972 : List Nat := [2, 3, 1, 1, 2, 5, 1, 5]
def baseStart_527972 : Nat := 118140960795 + 527972 * 2 ^ 59
def prefixEnd_527972 : Nat := 4983230072969 + 3 ^ 40 * 527972 * 2
def baseEnd_527972 : Nat := 80326935737989197280565

theorem tailTrace_527972 : CollatzResearch.WordTrace tailWord_527972 prefixEnd_527972 80326935737989197280565 := by
  unfold tailWord_527972
  simp only [CollatzResearch.WordTrace]
  refine ⟨9628360421627544641937085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12837813895503392855916113 9628360421627544641937085)
  ·
    refine ⟨3610635158110329240726407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9628360421627544641937085 3610635158110329240726407)
    ·
      refine ⟨5415952737165493861089611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3610635158110329240726407 5415952737165493861089611)
      ·
        refine ⟨8123929105748240791634417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5415952737165493861089611 8123929105748240791634417)
        ·
          refine ⟨6092946829311180593725813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8123929105748240791634417 6092946829311180593725813)
          ·
            refine ⟨571213765247923180661795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6092946829311180593725813 571213765247923180661795)
            ·
              refine ⟨856820647871884770992693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571213765247923180661795 856820647871884770992693)
              ·
                refine ⟨80326935737989197280565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 856820647871884770992693 80326935737989197280565)
                ·
                  rfl

theorem cell20_527972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 5].length) (baseStart_527972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527972 prefixEnd_527972 := by exact prefixLift 527972
  have htrace : WordTrace (prefixWord ++ tailWord_527972) baseStart_527972 baseEnd_527972 := by
    simpa [prefixWord, tailWord_527972, baseEnd_527972] using wordTrace_append hprefix tailTrace_527972
  have hstable : (prefixWord ++ tailWord_527972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527972).length < 2 ^ (prefixWord ++ tailWord_527972).sum := by decide
  have hdescent : baseEnd_527972 < baseStart_527972 := by decide
  rcases family_descends (prefixWord ++ tailWord_527972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527986 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_527986 : Nat := 118140960795 + 527986 * 2 ^ 59
def prefixEnd_527986 : Nat := 4983230072969 + 3 ^ 40 * 527986 * 2
def baseEnd_527986 : Nat := 240987197195445765374971

theorem tailTrace_527986 : CollatzResearch.WordTrace tailWord_527986 prefixEnd_527986 240987197195445765374971 := by
  unfold tailWord_527986
  simp only [CollatzResearch.WordTrace]
  refine ⟨4814307866301092418720953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12838154310136246449922541 4814307866301092418720953)
  ·
    refine ⟨3610730899725819314040715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4814307866301092418720953 3610730899725819314040715)
    ·
      refine ⟨5416096349588728971061073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3610730899725819314040715 5416096349588728971061073)
      ·
        refine ⟨4062072262191546728295805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5416096349588728971061073 4062072262191546728295805)
        ·
          refine ⟨1523277098321830023110927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4062072262191546728295805 1523277098321830023110927)
          ·
            refine ⟨2284915647482745034666391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1523277098321830023110927 2284915647482745034666391)
            ·
              refine ⟨3427373471224117551999587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2284915647482745034666391 3427373471224117551999587)
              ·
                refine ⟨5141060206836176327999381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3427373471224117551999587 5141060206836176327999381)
                ·
                  refine ⟨240987197195445765374971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5141060206836176327999381 240987197195445765374971)
                  ·
                    rfl

theorem cell20_527986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_527986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527986 prefixEnd_527986 := by exact prefixLift 527986
  have htrace : WordTrace (prefixWord ++ tailWord_527986) baseStart_527986 baseEnd_527986 := by
    simpa [prefixWord, tailWord_527986, baseEnd_527986] using wordTrace_append hprefix tailTrace_527986
  have hstable : (prefixWord ++ tailWord_527986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527986).length < 2 ^ (prefixWord ++ tailWord_527986).sum := by decide
  have hdescent : baseEnd_527986 < baseStart_527986 := by decide
  rcases family_descends (prefixWord ++ tailWord_527986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_527989 : List Nat := [1, 3, 4, 2, 1, 2, 3, 4]
def baseStart_527989 : Nat := 118140960795 + 527989 * 2 ^ 59
def prefixEnd_527989 : Nat := 4983230072969 + 3 ^ 40 * 527989 * 2
def baseEnd_527989 : Nat := 80329522159063696091653

theorem tailTrace_527989 : CollatzResearch.WordTrace tailWord_527989 prefixEnd_527989 80329522159063696091653 := by
  unfold tailWord_527989
  simp only [CollatzResearch.WordTrace]
  refine ⟨19257340884193501187243021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12838227256129000791495347 19257340884193501187243021)
  ·
    refine ⟨7221502831572562945216133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19257340884193501187243021 7221502831572562945216133)
    ·
      refine ⟨1354031780919855552228025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7221502831572562945216133 1354031780919855552228025)
      ·
        refine ⟨1015523835689891664171019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1354031780919855552228025 1015523835689891664171019)
        ·
          refine ⟨1523285753534837496256529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1015523835689891664171019 1523285753534837496256529)
          ·
            refine ⟨1142464315151128122192397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1523285753534837496256529 1142464315151128122192397)
            ·
              refine ⟨428424118181673045822149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1142464315151128122192397 428424118181673045822149)
              ·
                refine ⟨80329522159063696091653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 428424118181673045822149 80329522159063696091653)
                ·
                  rfl

theorem cell20_527989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 4].length) (baseStart_527989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_527989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_527989 prefixEnd_527989 := by exact prefixLift 527989
  have htrace : WordTrace (prefixWord ++ tailWord_527989) baseStart_527989 baseEnd_527989 := by
    simpa [prefixWord, tailWord_527989, baseEnd_527989] using wordTrace_append hprefix tailTrace_527989
  have hstable : (prefixWord ++ tailWord_527989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_527989).length < 2 ^ (prefixWord ++ tailWord_527989).sum := by decide
  have hdescent : baseEnd_527989 < baseStart_527989 := by decide
  rcases family_descends (prefixWord ++ tailWord_527989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528000 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 5]
def baseStart_528000 : Nat := 118140960795 + 528000 * 2 ^ 59
def prefixEnd_528000 : Nat := 4983230072969 + 3 ^ 40 * 528000 * 2
def baseEnd_528000 : Nat := 240993587176923938908247

theorem tailTrace_528000 : CollatzResearch.WordTrace tailWord_528000 prefixEnd_528000 240993587176923938908247 := by
  unfold tailWord_528000
  simp only [CollatzResearch.WordTrace]
  refine ⟨9628871043576825032946727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12838494724769100043928969 9628871043576825032946727)
  ·
    refine ⟨14443306565365237549420091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9628871043576825032946727 14443306565365237549420091)
    ·
      refine ⟨21664959848047856324130137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14443306565365237549420091 21664959848047856324130137)
      ·
        refine ⟨16248719886035892243097603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21664959848047856324130137 16248719886035892243097603)
        ·
          refine ⟨24373079829053838364646405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16248719886035892243097603 24373079829053838364646405)
          ·
            refine ⟨4569952467947594693371201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24373079829053838364646405 4569952467947594693371201)
            ·
              refine ⟨3427464350960696020028401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4569952467947594693371201 3427464350960696020028401)
              ·
                refine ⟨2570598263220522015021301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3427464350960696020028401 2570598263220522015021301)
                ·
                  refine ⟨240993587176923938908247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2570598263220522015021301 240993587176923938908247)
                  ·
                    rfl

theorem cell20_528000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_528000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528000 prefixEnd_528000 := by exact prefixLift 528000
  have htrace : WordTrace (prefixWord ++ tailWord_528000) baseStart_528000 baseEnd_528000 := by
    simpa [prefixWord, tailWord_528000, baseEnd_528000] using wordTrace_append hprefix tailTrace_528000
  have hstable : (prefixWord ++ tailWord_528000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528000).length < 2 ^ (prefixWord ++ tailWord_528000).sum := by decide
  have hdescent : baseEnd_528000 < baseStart_528000 := by decide
  rcases family_descends (prefixWord ++ tailWord_528000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528020 : List Nat := [2, 4, 2, 2, 2, 1, 2, 1, 4]
def baseStart_528020 : Nat := 118140960795 + 528020 * 2 ^ 59
def prefixEnd_528020 : Nat := 4983230072969 + 3 ^ 40 * 528020 * 2
def baseEnd_528020 : Nat := 241002715721892758241499

theorem tailTrace_528020 : CollatzResearch.WordTrace tailWord_528020 prefixEnd_528020 241002715721892758241499 := by
  unfold tailWord_528020
  simp only [CollatzResearch.WordTrace]
  refine ⟨9629235773540596740810757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12838981031387462321081009 9629235773540596740810757)
  ·
    refine ⟨1805481707538861888902017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9629235773540596740810757 1805481707538861888902017)
    ·
      refine ⟨1354111280654146416676513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1805481707538861888902017 1354111280654146416676513)
      ·
        refine ⟨1015583460490609812507385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1354111280654146416676513 1015583460490609812507385)
        ·
          refine ⟨761687595367957359380539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1015583460490609812507385 761687595367957359380539)
          ·
            refine ⟨1142531393051936039070809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761687595367957359380539 1142531393051936039070809)
            ·
              refine ⟨856898544788952029303107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1142531393051936039070809 856898544788952029303107)
              ·
                refine ⟨1285347817183428043954661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 856898544788952029303107 1285347817183428043954661)
                ·
                  refine ⟨241002715721892758241499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1285347817183428043954661 241002715721892758241499)
                  ·
                    rfl

theorem cell20_528020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_528020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528020 prefixEnd_528020 := by exact prefixLift 528020
  have htrace : WordTrace (prefixWord ++ tailWord_528020) baseStart_528020 baseEnd_528020 := by
    simpa [prefixWord, tailWord_528020, baseEnd_528020] using wordTrace_append hprefix tailTrace_528020
  have hstable : (prefixWord ++ tailWord_528020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528020).length < 2 ^ (prefixWord ++ tailWord_528020).sum := by decide
  have hdescent : baseEnd_528020 < baseStart_528020 := by decide
  rcases family_descends (prefixWord ++ tailWord_528020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528024 : List Nat := [2, 1, 2, 4, 1, 2, 1, 3, 4]
def baseStart_528024 : Nat := 118140960795 + 528024 * 2 ^ 59
def prefixEnd_528024 : Nat := 4983230072969 + 3 ^ 40 * 528024 * 2
def baseEnd_528024 : Nat := 241004541430886522108149

theorem tailTrace_528024 : CollatzResearch.WordTrace tailWord_528024 prefixEnd_528024 241004541430886522108149 := by
  unfold tailWord_528024
  simp only [CollatzResearch.WordTrace]
  refine ⟨9629308719533351082383563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12839078292711134776511417 9629308719533351082383563)
  ·
    refine ⟨14443963079300026623575345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9629308719533351082383563 14443963079300026623575345)
    ·
      refine ⟨10832972309475019967681509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14443963079300026623575345 10832972309475019967681509)
      ·
        refine ⟨2031182308026566243940283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10832972309475019967681509 2031182308026566243940283)
        ·
          refine ⟨3046773462039849365910425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2031182308026566243940283 3046773462039849365910425)
          ·
            refine ⟨2285080096529887024432819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3046773462039849365910425 2285080096529887024432819)
            ·
              refine ⟨3427620144794830536649229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2285080096529887024432819 3427620144794830536649229)
              ·
                refine ⟨1285357554298061451243461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3427620144794830536649229 1285357554298061451243461)
                ·
                  refine ⟨241004541430886522108149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1285357554298061451243461 241004541430886522108149)
                  ·
                    rfl

theorem cell20_528024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_528024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528024 prefixEnd_528024 := by exact prefixLift 528024
  have htrace : WordTrace (prefixWord ++ tailWord_528024) baseStart_528024 baseEnd_528024 := by
    simpa [prefixWord, tailWord_528024, baseEnd_528024] using wordTrace_append hprefix tailTrace_528024
  have hstable : (prefixWord ++ tailWord_528024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528024).length < 2 ^ (prefixWord ++ tailWord_528024).sum := by decide
  have hdescent : baseEnd_528024 < baseStart_528024 := by decide
  rcases family_descends (prefixWord ++ tailWord_528024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528040 : List Nat := [2, 1, 7, 1, 2, 1, 2, 4]
def baseStart_528040 : Nat := 118140960795 + 528040 * 2 ^ 59
def prefixEnd_528040 : Nat := 4983230072969 + 3 ^ 40 * 528040 * 2
def baseEnd_528040 : Nat := 80337281422287192524917

theorem tailTrace_528040 : CollatzResearch.WordTrace tailWord_528040 prefixEnd_528040 80337281422287192524917 := by
  unfold tailWord_528040
  simp only [CollatzResearch.WordTrace]
  refine ⟨9629600503504368448674787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12839467338005824598233049 9629600503504368448674787)
  ·
    refine ⟨14444400755256552673012181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9629600503504368448674787 14444400755256552673012181)
    ·
      refine ⟨338540642701325453273723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 14444400755256552673012181 338540642701325453273723)
      ·
        refine ⟨507810964051988179910585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338540642701325453273723 507810964051988179910585)
        ·
          refine ⟨380858223038991134932939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507810964051988179910585 380858223038991134932939)
          ·
            refine ⟨571287334558486702399409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380858223038991134932939 571287334558486702399409)
            ·
              refine ⟨428465500918865026799557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571287334558486702399409 428465500918865026799557)
              ·
                refine ⟨80337281422287192524917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 428465500918865026799557 80337281422287192524917)
                ·
                  rfl

theorem cell20_528040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 4].length) (baseStart_528040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528040 prefixEnd_528040 := by exact prefixLift 528040
  have htrace : WordTrace (prefixWord ++ tailWord_528040) baseStart_528040 baseEnd_528040 := by
    simpa [prefixWord, tailWord_528040, baseEnd_528040] using wordTrace_append hprefix tailTrace_528040
  have hstable : (prefixWord ++ tailWord_528040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528040).length < 2 ^ (prefixWord ++ tailWord_528040).sum := by decide
  have hdescent : baseEnd_528040 < baseStart_528040 := by decide
  rcases family_descends (prefixWord ++ tailWord_528040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528054 : List Nat := [5, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_528054 : Nat := 118140960795 + 528054 * 2 ^ 59
def prefixEnd_528054 : Nat := 4983230072969 + 3 ^ 40 * 528054 * 2
def baseEnd_528054 : Nat := 241018234248339751108027

theorem tailTrace_528054 : CollatzResearch.WordTrace tailWord_528054 prefixEnd_528054 241018234248339751108027 := by
  unfold tailWord_528054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1203731976809876080522451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12839807752638678192239477 1203731976809876080522451)
  ·
    refine ⟨1805597965214814120783677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1203731976809876080522451 1805597965214814120783677)
    ·
      refine ⟨677099236955555295293879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1805597965214814120783677 677099236955555295293879)
      ·
        refine ⟨1015648855433332942940819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677099236955555295293879 1015648855433332942940819)
        ·
          refine ⟨1523473283149999414411229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1015648855433332942940819 1523473283149999414411229)
          ·
            refine ⟨571302481181249780404211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1523473283149999414411229 571302481181249780404211)
            ·
              refine ⟨856953721771874670606317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571302481181249780404211 856953721771874670606317)
              ·
                refine ⟨321357645664453001477369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 856953721771874670606317 321357645664453001477369)
                ·
                  refine ⟨241018234248339751108027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321357645664453001477369 241018234248339751108027)
                  ·
                    rfl

theorem cell20_528054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_528054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528054 prefixEnd_528054 := by exact prefixLift 528054
  have htrace : WordTrace (prefixWord ++ tailWord_528054) baseStart_528054 baseEnd_528054 := by
    simpa [prefixWord, tailWord_528054, baseEnd_528054] using wordTrace_append hprefix tailTrace_528054
  have hstable : (prefixWord ++ tailWord_528054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528054).length < 2 ^ (prefixWord ++ tailWord_528054).sum := by decide
  have hdescent : baseEnd_528054 < baseStart_528054 := by decide
  rcases family_descends (prefixWord ++ tailWord_528054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528058 : List Nat := [3, 1, 1, 1, 2, 6, 1, 3, 2]
def baseStart_528058 : Nat := 118140960795 + 528058 * 2 ^ 59
def prefixEnd_528058 : Nat := 4983230072969 + 3 ^ 40 * 528058 * 2
def baseEnd_528058 : Nat := 241020059957333514974677

theorem tailTrace_528058 : CollatzResearch.WordTrace tailWord_528058 prefixEnd_528058 241020059957333514974677 := by
  unfold tailWord_528058
  simp only [CollatzResearch.WordTrace]
  refine ⟨4814964380235881492876207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12839905013962350647669885 4814964380235881492876207)
  ·
    refine ⟨7222446570353822239314311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4814964380235881492876207 7222446570353822239314311)
    ·
      refine ⟨10833669855530733358971467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7222446570353822239314311 10833669855530733358971467)
      ·
        refine ⟨16250504783296100038457201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10833669855530733358971467 16250504783296100038457201)
        ·
          refine ⟨12187878587472075028842901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16250504783296100038457201 12187878587472075028842901)
          ·
            refine ⟨571306808787753516977011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12187878587472075028842901 571306808787753516977011)
            ·
              refine ⟨856960213181630275465517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571306808787753516977011 856960213181630275465517)
              ·
                refine ⟨321360079943111353299569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 856960213181630275465517 321360079943111353299569)
                ·
                  refine ⟨241020059957333514974677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321360079943111353299569 241020059957333514974677)
                  ·
                    rfl

theorem cell20_528058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_528058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528058 prefixEnd_528058 := by exact prefixLift 528058
  have htrace : WordTrace (prefixWord ++ tailWord_528058) baseStart_528058 baseEnd_528058 := by
    simpa [prefixWord, tailWord_528058, baseEnd_528058] using wordTrace_append hprefix tailTrace_528058
  have hstable : (prefixWord ++ tailWord_528058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528058).length < 2 ^ (prefixWord ++ tailWord_528058).sum := by decide
  have hdescent : baseEnd_528058 < baseStart_528058 := by decide
  rcases family_descends (prefixWord ++ tailWord_528058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528162 : List Nat := [3, 3, 1, 1, 2, 1, 5, 4]
def baseStart_528162 : Nat := 118140960795 + 528162 * 2 ^ 59
def prefixEnd_528162 : Nat := 4983230072969 + 3 ^ 40 * 528162 * 2
def baseEnd_528162 : Nat := 80355842797057125169195

theorem tailTrace_528162 : CollatzResearch.WordTrace tailWord_528162 prefixEnd_528162 80355842797057125169195 := by
  unfold tailWord_528162
  simp only [CollatzResearch.WordTrace]
  refine ⟨4815912678141687933322685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12842433808377834488860493 4815912678141687933322685)
  ·
    refine ⟨1805967254303132974996007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4815912678141687933322685 1805967254303132974996007)
    ·
      refine ⟨2708950881454699462494011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1805967254303132974996007 2708950881454699462494011)
      ·
        refine ⟨4063426322182049193741017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2708950881454699462494011 4063426322182049193741017)
        ·
          refine ⟨3047569741636536895305763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4063426322182049193741017 3047569741636536895305763)
          ·
            refine ⟨4571354612454805342958645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3047569741636536895305763 4571354612454805342958645)
            ·
              refine ⟨428564494917638000902373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4571354612454805342958645 428564494917638000902373)
              ·
                refine ⟨80355842797057125169195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 428564494917638000902373 80355842797057125169195)
                ·
                  rfl

theorem cell20_528162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_528162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528162 prefixEnd_528162 := by exact prefixLift 528162
  have htrace : WordTrace (prefixWord ++ tailWord_528162) baseStart_528162 baseEnd_528162 := by
    simpa [prefixWord, tailWord_528162, baseEnd_528162] using wordTrace_append hprefix tailTrace_528162
  have hstable : (prefixWord ++ tailWord_528162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528162).length < 2 ^ (prefixWord ++ tailWord_528162).sum := by decide
  have hdescent : baseEnd_528162 < baseStart_528162 := by decide
  rcases family_descends (prefixWord ++ tailWord_528162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528186 : List Nat := [3, 1, 1, 1, 5, 3, 1, 2, 3]
def baseStart_528186 : Nat := 118140960795 + 528186 * 2 ^ 59
def prefixEnd_528186 : Nat := 4983230072969 + 3 ^ 40 * 528186 * 2
def baseEnd_528186 : Nat := 241078482645133958707487

theorem tailTrace_528186 : CollatzResearch.WordTrace tailWord_528186 prefixEnd_528186 241078482645133958707487 := by
  unfold tailWord_528186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4816131516119950958041103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12843017376319869221442941 4816131516119950958041103)
  ·
    refine ⟨7224197274179926437061655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4816131516119950958041103 7224197274179926437061655)
    ·
      refine ⟨10836295911269889655592483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7224197274179926437061655 10836295911269889655592483)
      ·
        refine ⟨16254443866904834483388725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10836295911269889655592483 16254443866904834483388725)
        ·
          refine ⟨1523854112522328232817693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16254443866904834483388725 1523854112522328232817693)
          ·
            refine ⟨571445292195873087306635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1523854112522328232817693 571445292195873087306635)
            ·
              refine ⟨857167938293809630959953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571445292195873087306635 857167938293809630959953)
              ·
                refine ⟨642875953720357223219965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 857167938293809630959953 642875953720357223219965)
                ·
                  refine ⟨241078482645133958707487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 642875953720357223219965 241078482645133958707487)
                  ·
                    rfl

theorem cell20_528186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_528186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528186 prefixEnd_528186 := by exact prefixLift 528186
  have htrace : WordTrace (prefixWord ++ tailWord_528186) baseStart_528186 baseEnd_528186 := by
    simpa [prefixWord, tailWord_528186, baseEnd_528186] using wordTrace_append hprefix tailTrace_528186
  have hstable : (prefixWord ++ tailWord_528186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528186).length < 2 ^ (prefixWord ++ tailWord_528186).sum := by decide
  have hdescent : baseEnd_528186 < baseStart_528186 := by decide
  rcases family_descends (prefixWord ++ tailWord_528186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528227 : List Nat := [1, 1, 1, 5, 5, 1, 1, 3, 2]
def baseStart_528227 : Nat := 118140960795 + 528227 * 2 ^ 59
def prefixEnd_528227 : Nat := 4983230072969 + 3 ^ 40 * 528227 * 2
def baseEnd_528227 : Nat := 241097196162320038340653

theorem tailTrace_528227 : CollatzResearch.WordTrace tailWord_528227 prefixEnd_528227 241097196162320038340653 := by
  unfold tailWord_528227
  simp only [CollatzResearch.WordTrace]
  refine ⟨19266021457331267834406935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12844014304887511889604623 19266021457331267834406935)
  ·
    refine ⟨28899032185996901751610403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19266021457331267834406935 28899032185996901751610403)
    ·
      refine ⟨43348548278995352627415605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28899032185996901751610403 43348548278995352627415605)
      ·
        refine ⟨4063926401155814308820213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43348548278995352627415605 4063926401155814308820213)
        ·
          refine ⟨380993100108357591451895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4063926401155814308820213 380993100108357591451895)
          ·
            refine ⟨571489650162536387177843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380993100108357591451895 571489650162536387177843)
            ·
              refine ⟨857234475243804580766765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571489650162536387177843 857234475243804580766765)
              ·
                refine ⟨321462928216426717787537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 857234475243804580766765 321462928216426717787537)
                ·
                  refine ⟨241097196162320038340653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321462928216426717787537 241097196162320038340653)
                  ·
                    rfl

theorem cell20_528227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 2].length) (baseStart_528227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528227 prefixEnd_528227 := by exact prefixLift 528227
  have htrace : WordTrace (prefixWord ++ tailWord_528227) baseStart_528227 baseEnd_528227 := by
    simpa [prefixWord, tailWord_528227, baseEnd_528227] using wordTrace_append hprefix tailTrace_528227
  have hstable : (prefixWord ++ tailWord_528227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528227).length < 2 ^ (prefixWord ++ tailWord_528227).sum := by decide
  have hdescent : baseEnd_528227 < baseStart_528227 := by decide
  rcases family_descends (prefixWord ++ tailWord_528227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528238 : List Nat := [4, 1, 2, 3, 1, 3, 6]
def baseStart_528238 : Nat := 118140960795 + 528238 * 2 ^ 59
def prefixEnd_528238 : Nat := 4983230072969 + 3 ^ 40 * 528238 * 2
def baseEnd_528238 : Nat := 26789135206894765441549

theorem tailTrace_528238 : CollatzResearch.WordTrace tailWord_528238 prefixEnd_528238 26789135206894765441549 := by
  unfold tailWord_528238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2408302832536427089132171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12844281773527611142038245 2408302832536427089132171)
  ·
    refine ⟨3612454248804640633698257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2408302832536427089132171 3612454248804640633698257)
    ·
      refine ⟨2709340686603480475273693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3612454248804640633698257 2709340686603480475273693)
      ·
        refine ⟨1016002757476305178227635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2709340686603480475273693 1016002757476305178227635)
        ·
          refine ⟨1524004136214457767341453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1016002757476305178227635 1524004136214457767341453)
          ·
            refine ⟨571501551080421662753045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1524004136214457767341453 571501551080421662753045)
            ·
              refine ⟨26789135206894765441549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 571501551080421662753045 26789135206894765441549)
              ·
                rfl

theorem cell20_528238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 6].length) (baseStart_528238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528238 prefixEnd_528238 := by exact prefixLift 528238
  have htrace : WordTrace (prefixWord ++ tailWord_528238) baseStart_528238 baseEnd_528238 := by
    simpa [prefixWord, tailWord_528238, baseEnd_528238] using wordTrace_append hprefix tailTrace_528238
  have hstable : (prefixWord ++ tailWord_528238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528238).length < 2 ^ (prefixWord ++ tailWord_528238).sum := by decide
  have hdescent : baseEnd_528238 < baseStart_528238 := by decide
  rcases family_descends (prefixWord ++ tailWord_528238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528245 : List Nat := [1, 3, 4, 1, 1, 1, 2, 4, 3]
def baseStart_528245 : Nat := 118140960795 + 528245 * 2 ^ 59
def prefixEnd_528245 : Nat := 4983230072969 + 3 ^ 40 * 528245 * 2
def baseEnd_528245 : Nat := 241105411852791975740579

theorem tailTrace_528245 : CollatzResearch.WordTrace tailWord_528245 prefixEnd_528245 241105411852791975740579 := by
  unfold tailWord_528245
  simp only [CollatzResearch.WordTrace]
  refine ⟨19266677971266056908562189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12844451980844037939041459 19266677971266056908562189)
  ·
    refine ⟨7225004239224771340710821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19266677971266056908562189 7225004239224771340710821)
    ·
      refine ⟨1354688294854644626383279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7225004239224771340710821 1354688294854644626383279)
      ·
        refine ⟨2032032442281966939574919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1354688294854644626383279 2032032442281966939574919)
        ·
          refine ⟨3048048663422950409362379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2032032442281966939574919 3048048663422950409362379)
          ·
            refine ⟨4572072995134425614043569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3048048663422950409362379 4572072995134425614043569)
            ·
              refine ⟨3429054746350819210532677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4572072995134425614043569 3429054746350819210532677)
              ·
                refine ⟨642947764940778601974877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3429054746350819210532677 642947764940778601974877)
                ·
                  refine ⟨241105411852791975740579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 642947764940778601974877 241105411852791975740579)
                  ·
                    rfl

theorem cell20_528245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_528245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528245 prefixEnd_528245 := by exact prefixLift 528245
  have htrace : WordTrace (prefixWord ++ tailWord_528245) baseStart_528245 baseEnd_528245 := by
    simpa [prefixWord, tailWord_528245, baseEnd_528245] using wordTrace_append hprefix tailTrace_528245
  have hstable : (prefixWord ++ tailWord_528245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528245).length < 2 ^ (prefixWord ++ tailWord_528245).sum := by decide
  have hdescent : baseEnd_528245 < baseStart_528245 := by decide
  rcases family_descends (prefixWord ++ tailWord_528245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528259 : List Nat := [1, 1, 1, 3, 4, 3, 2, 5]
def baseStart_528259 : Nat := 118140960795 + 528259 * 2 ^ 59
def prefixEnd_528259 : Nat := 4983230072969 + 3 ^ 40 * 528259 * 2
def baseEnd_528259 : Nat := 80370600611423383091285

theorem tailTrace_528259 : CollatzResearch.WordTrace tailWord_528259 prefixEnd_528259 80370600611423383091285 := by
  unfold tailWord_528259
  simp only [CollatzResearch.WordTrace]
  refine ⟨19267188593215337299571831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12844792395476891533047887 19267188593215337299571831)
  ·
    refine ⟨28900782889823005949357747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19267188593215337299571831 28900782889823005949357747)
    ·
      refine ⟨43351174334734508924036621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28900782889823005949357747 43351174334734508924036621)
      ·
        refine ⟨16256690375525440846513733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43351174334734508924036621 16256690375525440846513733)
        ·
          refine ⟨3048129445411020158721325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16256690375525440846513733 3048129445411020158721325)
          ·
            refine ⟨1143048542029132559520497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3048129445411020158721325 1143048542029132559520497)
            ·
              refine ⟨857286406521849419640373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1143048542029132559520497 857286406521849419640373)
              ·
                refine ⟨80370600611423383091285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 857286406521849419640373 80370600611423383091285)
                ·
                  rfl

theorem cell20_528259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 5].length) (baseStart_528259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528259 prefixEnd_528259 := by exact prefixLift 528259
  have htrace : WordTrace (prefixWord ++ tailWord_528259) baseStart_528259 baseEnd_528259 := by
    simpa [prefixWord, tailWord_528259, baseEnd_528259] using wordTrace_append hprefix tailTrace_528259
  have hstable : (prefixWord ++ tailWord_528259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528259).length < 2 ^ (prefixWord ++ tailWord_528259).sum := by decide
  have hdescent : baseEnd_528259 < baseStart_528259 := by decide
  rcases family_descends (prefixWord ++ tailWord_528259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528273 : List Nat := [1, 2, 2, 1, 1, 1, 4, 4, 4]
def baseStart_528273 : Nat := 118140960795 + 528273 * 2 ^ 59
def prefixEnd_528273 : Nat := 4983230072969 + 3 ^ 40 * 528273 * 2
def baseEnd_528273 : Nat := 241118191815748322807131

theorem tailTrace_528273 : CollatzResearch.WordTrace tailWord_528273 prefixEnd_528273 241118191815748322807131 := by
  unfold tailWord_528273
  simp only [CollatzResearch.WordTrace]
  refine ⟨19267699215164617690581473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12845132810109745127054315 19267699215164617690581473)
  ·
    refine ⟨14450774411373463267936105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19267699215164617690581473 14450774411373463267936105)
    ·
      refine ⟨10838080808530097450952079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14450774411373463267936105 10838080808530097450952079)
      ·
        refine ⟨16257121212795146176428119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10838080808530097450952079 16257121212795146176428119)
        ·
          refine ⟨24385681819192719264642179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16257121212795146176428119 24385681819192719264642179)
          ·
            refine ⟨36578522728789078896963269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24385681819192719264642179 36578522728789078896963269)
            ·
              refine ⟨6858473011647952293180613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36578522728789078896963269 6858473011647952293180613)
              ·
                refine ⟨1285963689683991054971365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6858473011647952293180613 1285963689683991054971365)
                ·
                  refine ⟨241118191815748322807131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1285963689683991054971365 241118191815748322807131)
                  ·
                    rfl

theorem cell20_528273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_528273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528273 prefixEnd_528273 := by exact prefixLift 528273
  have htrace : WordTrace (prefixWord ++ tailWord_528273) baseStart_528273 baseEnd_528273 := by
    simpa [prefixWord, tailWord_528273, baseEnd_528273] using wordTrace_append hprefix tailTrace_528273
  have hstable : (prefixWord ++ tailWord_528273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528273).length < 2 ^ (prefixWord ++ tailWord_528273).sum := by decide
  have hdescent : baseEnd_528273 < baseStart_528273 := by decide
  rcases family_descends (prefixWord ++ tailWord_528273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528311 : List Nat := [1, 1, 3, 1, 3, 1, 1, 5, 4]
def baseStart_528311 : Nat := 118140960795 + 528311 * 2 ^ 59
def prefixEnd_528311 : Nat := 4983230072969 + 3 ^ 40 * 528311 * 2
def baseEnd_528311 : Nat := 241135536051189079540309

theorem tailTrace_528311 : CollatzResearch.WordTrace tailWord_528311 prefixEnd_528311 241135536051189079540309 := by
  unfold tailWord_528311
  simp only [CollatzResearch.WordTrace]
  refine ⟨19269085189026950180464787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12846056792684633453643191 19269085189026950180464787)
  ·
    refine ⟨28903627783540425270697181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19269085189026950180464787 28903627783540425270697181)
    ·
      refine ⟨10838860418827659476511443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28903627783540425270697181 10838860418827659476511443)
      ·
        refine ⟨16258290628241489214767165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10838860418827659476511443 16258290628241489214767165)
        ·
          refine ⟨6096858985590558455537687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16258290628241489214767165 6096858985590558455537687)
          ·
            refine ⟨9145288478385837683306531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6096858985590558455537687 9145288478385837683306531)
            ·
              refine ⟨13717932717578756524959797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9145288478385837683306531 13717932717578756524959797)
              ·
                refine ⟨1286056192273008424214981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13717932717578756524959797 1286056192273008424214981)
                ·
                  refine ⟨241135536051189079540309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1286056192273008424214981 241135536051189079540309)
                  ·
                    rfl

theorem cell20_528311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 4].length) (baseStart_528311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528311 prefixEnd_528311 := by exact prefixLift 528311
  have htrace : WordTrace (prefixWord ++ tailWord_528311) baseStart_528311 baseEnd_528311 := by
    simpa [prefixWord, tailWord_528311, baseEnd_528311] using wordTrace_append hprefix tailTrace_528311
  have hstable : (prefixWord ++ tailWord_528311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528311).length < 2 ^ (prefixWord ++ tailWord_528311).sum := by decide
  have hdescent : baseEnd_528311 < baseStart_528311 := by decide
  rcases family_descends (prefixWord ++ tailWord_528311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528328 : List Nat := [2, 1, 3, 1, 4, 2, 1, 2, 4]
def baseStart_528328 : Nat := 118140960795 + 528328 * 2 ^ 59
def prefixEnd_528328 : Nat := 4983230072969 + 3 ^ 40 * 528328 * 2
def baseEnd_528328 : Nat := 241143295314412575973573

theorem tailTrace_528328 : CollatzResearch.WordTrace tailWord_528328 prefixEnd_528328 241143295314412575973573 := by
  unfold tailWord_528328
  simp only [CollatzResearch.WordTrace]
  refine ⟨9634852614982681041916819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12846470153310241389222425 9634852614982681041916819)
  ·
    refine ⟨14452278922474021562875229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9634852614982681041916819 14452278922474021562875229)
    ·
      refine ⟨5419604595927758086078211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14452278922474021562875229 5419604595927758086078211)
      ·
        refine ⟨8129406893891637129117317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5419604595927758086078211 8129406893891637129117317)
        ·
          refine ⟨1524263792604681961709497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8129406893891637129117317 1524263792604681961709497)
          ·
            refine ⟨1143197844453511471282123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1524263792604681961709497 1143197844453511471282123)
            ·
              refine ⟨1714796766680267206923185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1143197844453511471282123 1714796766680267206923185)
              ·
                refine ⟨1286097575010200405192389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1714796766680267206923185 1286097575010200405192389)
                ·
                  refine ⟨241143295314412575973573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1286097575010200405192389 241143295314412575973573)
                  ·
                    rfl

theorem cell20_528328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_528328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528328 prefixEnd_528328 := by exact prefixLift 528328
  have htrace : WordTrace (prefixWord ++ tailWord_528328) baseStart_528328 baseEnd_528328 := by
    simpa [prefixWord, tailWord_528328, baseEnd_528328] using wordTrace_append hprefix tailTrace_528328
  have hstable : (prefixWord ++ tailWord_528328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528328).length < 2 ^ (prefixWord ++ tailWord_528328).sum := by decide
  have hdescent : baseEnd_528328 < baseStart_528328 := by decide
  rcases family_descends (prefixWord ++ tailWord_528328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528335 : List Nat := [1, 1, 2, 1, 1, 5, 5, 4]
def baseStart_528335 : Nat := 118140960795 + 528335 * 2 ^ 59
def prefixEnd_528335 : Nat := 4983230072969 + 3 ^ 40 * 528335 * 2
def baseEnd_528335 : Nat := 80382163435050554246737

theorem tailTrace_528335 : CollatzResearch.WordTrace tailWord_528335 prefixEnd_528335 80382163435050554246737 := by
  unfold tailWord_528335
  simp only [CollatzResearch.WordTrace]
  refine ⟨19269960540940002279338459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12846640360626668186225639 19269960540940002279338459)
  ·
    refine ⟨28904940811410003419007689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19269960540940002279338459 28904940811410003419007689)
    ·
      refine ⟨21678705608557502564255767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28904940811410003419007689 21678705608557502564255767)
      ·
        refine ⟨32518058412836253846383651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21678705608557502564255767 32518058412836253846383651)
        ·
          refine ⟨48777087619254380769575477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32518058412836253846383651 48777087619254380769575477)
          ·
            refine ⟨4572851964305098197147701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48777087619254380769575477 4572851964305098197147701)
            ·
              refine ⟨428704871653602955982597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4572851964305098197147701 428704871653602955982597)
              ·
                refine ⟨80382163435050554246737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 428704871653602955982597 80382163435050554246737)
                ·
                  rfl

theorem cell20_528335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 4].length) (baseStart_528335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528335 prefixEnd_528335 := by exact prefixLift 528335
  have htrace : WordTrace (prefixWord ++ tailWord_528335) baseStart_528335 baseEnd_528335 := by
    simpa [prefixWord, tailWord_528335, baseEnd_528335] using wordTrace_append hprefix tailTrace_528335
  have hstable : (prefixWord ++ tailWord_528335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528335).length < 2 ^ (prefixWord ++ tailWord_528335).sum := by decide
  have hdescent : baseEnd_528335 < baseStart_528335 := by decide
  rcases family_descends (prefixWord ++ tailWord_528335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528356 : List Nat := [2, 3, 1, 1, 1, 1, 11]
def baseStart_528356 : Nat := 118140960795 + 528356 * 2 ^ 59
def prefixEnd_528356 : Nat := 4983230072969 + 3 ^ 40 * 528356 * 2
def baseEnd_528356 : Nat := 26795119475263213671125

theorem tailTrace_528356 : CollatzResearch.WordTrace tailWord_528356 prefixEnd_528356 26795119475263213671125 := by
  unfold tailWord_528356
  simp only [CollatzResearch.WordTrace]
  refine ⟨9635363236931961432926461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12847150982575948577235281 9635363236931961432926461)
  ·
    refine ⟨3613261213849485537347423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9635363236931961432926461 3613261213849485537347423)
    ·
      refine ⟨5419891820774228306021135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3613261213849485537347423 5419891820774228306021135)
      ·
        refine ⟨8129837731161342459031703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5419891820774228306021135 8129837731161342459031703)
        ·
          refine ⟨12194756596742013688547555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8129837731161342459031703 12194756596742013688547555)
          ·
            refine ⟨18292134895113020532821333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12194756596742013688547555 18292134895113020532821333)
            ·
              refine ⟨26795119475263213671125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18292134895113020532821333 26795119475263213671125)
              ·
                rfl

theorem cell20_528356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 11].length) (baseStart_528356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528356 prefixEnd_528356 := by exact prefixLift 528356
  have htrace : WordTrace (prefixWord ++ tailWord_528356) baseStart_528356 baseEnd_528356 := by
    simpa [prefixWord, tailWord_528356, baseEnd_528356] using wordTrace_append hprefix tailTrace_528356
  have hstable : (prefixWord ++ tailWord_528356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528356).length < 2 ^ (prefixWord ++ tailWord_528356).sum := by decide
  have hdescent : baseEnd_528356 < baseStart_528356 := by decide
  rcases family_descends (prefixWord ++ tailWord_528356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528359 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 5]
def baseStart_528359 : Nat := 118140960795 + 528359 * 2 ^ 59
def prefixEnd_528359 : Nat := 4983230072969 + 3 ^ 40 * 528359 * 2
def baseEnd_528359 : Nat := 241157444559114245940113

theorem tailTrace_528359 : CollatzResearch.WordTrace tailWord_528359 prefixEnd_528359 241157444559114245940113 := by
  unfold tailWord_528359
  simp only [CollatzResearch.WordTrace]
  refine ⟨19270835892853054378212131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12847223928568702918808087 19270835892853054378212131)
  ·
    refine ⟨28906253839279581567318197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19270835892853054378212131 28906253839279581567318197)
    ·
      refine ⟨2709961297432460771936081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28906253839279581567318197 2709961297432460771936081)
      ·
        refine ⟨2032470973074345578952061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2709961297432460771936081 2032470973074345578952061)
        ·
          refine ⟨762176614902879592107023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2032470973074345578952061 762176614902879592107023)
          ·
            refine ⟨1143264922354319388160535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762176614902879592107023 1143264922354319388160535)
            ·
              refine ⟨1714897383531479082240803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1143264922354319388160535 1714897383531479082240803)
              ·
                refine ⟨2572346075297218623361205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1714897383531479082240803 2572346075297218623361205)
                ·
                  refine ⟨241157444559114245940113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2572346075297218623361205 241157444559114245940113)
                  ·
                    rfl

theorem cell20_528359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 5].length) (baseStart_528359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528359 prefixEnd_528359 := by exact prefixLift 528359
  have htrace : WordTrace (prefixWord ++ tailWord_528359) baseStart_528359 baseEnd_528359 := by
    simpa [prefixWord, tailWord_528359, baseEnd_528359] using wordTrace_append hprefix tailTrace_528359
  have hstable : (prefixWord ++ tailWord_528359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528359).length < 2 ^ (prefixWord ++ tailWord_528359).sum := by decide
  have hdescent : baseEnd_528359 < baseStart_528359 := by decide
  rcases family_descends (prefixWord ++ tailWord_528359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528366 : List Nat := [4, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_528366 : Nat := 118140960795 + 528366 * 2 ^ 59
def prefixEnd_528366 : Nat := 4983230072969 + 3 ^ 40 * 528366 * 2
def baseEnd_528366 : Nat := 241160639549853332706751

theorem tailTrace_528366 : CollatzResearch.WordTrace tailWord_528366 prefixEnd_528366 241160639549853332706751 := by
  unfold tailWord_528366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2408886400478461821714619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12847394135885129715811301 2408886400478461821714619)
  ·
    refine ⟨3613329600717692732571929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2408886400478461821714619 3613329600717692732571929)
    ·
      refine ⟨2709997200538269549428947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3613329600717692732571929 2709997200538269549428947)
      ·
        refine ⟨4064995800807404324143421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2709997200538269549428947 4064995800807404324143421)
        ·
          refine ⟨1524373425302776621553783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4064995800807404324143421 1524373425302776621553783)
          ·
            refine ⟨2286560137954164932330675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1524373425302776621553783 2286560137954164932330675)
            ·
              refine ⟨3429840206931247398496013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2286560137954164932330675 3429840206931247398496013)
              ·
                refine ⟨1286190077599217774436005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3429840206931247398496013 1286190077599217774436005)
                ·
                  refine ⟨241160639549853332706751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1286190077599217774436005 241160639549853332706751)
                  ·
                    rfl

theorem cell20_528366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_528366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528366 prefixEnd_528366 := by exact prefixLift 528366
  have htrace : WordTrace (prefixWord ++ tailWord_528366) baseStart_528366 baseEnd_528366 := by
    simpa [prefixWord, tailWord_528366, baseEnd_528366] using wordTrace_append hprefix tailTrace_528366
  have hstable : (prefixWord ++ tailWord_528366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528366).length < 2 ^ (prefixWord ++ tailWord_528366).sum := by decide
  have hdescent : baseEnd_528366 < baseStart_528366 := by decide
  rcases family_descends (prefixWord ++ tailWord_528366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528418 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_528418 : Nat := 118140960795 + 528418 * 2 ^ 59
def prefixEnd_528418 : Nat := 4983230072969 + 3 ^ 40 * 528418 * 2
def baseEnd_528418 : Nat := 241184373766772262973205

theorem tailTrace_528418 : CollatzResearch.WordTrace tailWord_528418 prefixEnd_528418 241184373766772262973205 := by
  unfold tailWord_528418
  simp only [CollatzResearch.WordTrace]
  refine ⟨4818246949909826863652477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12848658533092871636406605 4818246949909826863652477)
  ·
    refine ⟨1806842606216185073869679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4818246949909826863652477 1806842606216185073869679)
    ·
      refine ⟨2710263909324277610804519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1806842606216185073869679 2710263909324277610804519)
      ·
        refine ⟨4065395863986416416206779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2710263909324277610804519 4065395863986416416206779)
        ·
          refine ⟨6098093795979624624310169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4065395863986416416206779 6098093795979624624310169)
          ·
            refine ⟨4573570346984718468232627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6098093795979624624310169 4573570346984718468232627)
            ·
              refine ⟨6860355520477077702348941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4573570346984718468232627 6860355520477077702348941)
              ·
                refine ⟨2572633320178904138380853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6860355520477077702348941 2572633320178904138380853)
                ·
                  refine ⟨241184373766772262973205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2572633320178904138380853 241184373766772262973205)
                  ·
                    rfl

theorem cell20_528418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_528418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528418 prefixEnd_528418 := by exact prefixLift 528418
  have htrace : WordTrace (prefixWord ++ tailWord_528418) baseStart_528418 baseEnd_528418 := by
    simpa [prefixWord, tailWord_528418, baseEnd_528418] using wordTrace_append hprefix tailTrace_528418
  have hstable : (prefixWord ++ tailWord_528418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528418).length < 2 ^ (prefixWord ++ tailWord_528418).sum := by decide
  have hdescent : baseEnd_528418 < baseStart_528418 := by decide
  rcases family_descends (prefixWord ++ tailWord_528418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528432 : List Nat := [2, 1, 1, 1, 2, 5, 1, 7]
def baseStart_528432 : Nat := 118140960795 + 528432 * 2 ^ 59
def prefixEnd_528432 : Nat := 4983230072969 + 3 ^ 40 * 528432 * 2
def baseEnd_528432 : Nat := 80396921249416812168827

theorem tailTrace_528432 : CollatzResearch.WordTrace tailWord_528432 prefixEnd_528432 80396921249416812168827 := by
  unfold tailWord_528432
  simp only [CollatzResearch.WordTrace]
  refine ⟨9636749210794293922809775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12848998947725725230413033 9636749210794293922809775)
  ·
    refine ⟨14455123816191440884214663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9636749210794293922809775 14455123816191440884214663)
    ·
      refine ⟨21682685724287161326321995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14455123816191440884214663 21682685724287161326321995)
      ·
        refine ⟨32524028586430741989482993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21682685724287161326321995 32524028586430741989482993)
        ·
          refine ⟨24393021439823056492112245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32524028586430741989482993 24393021439823056492112245)
          ·
            refine ⟨2286845759983411546135523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24393021439823056492112245 2286845759983411546135523)
            ·
              refine ⟨3430268639975117319203285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2286845759983411546135523 3430268639975117319203285)
              ·
                refine ⟨80396921249416812168827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3430268639975117319203285 80396921249416812168827)
                ·
                  rfl

theorem cell20_528432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_528432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528432 prefixEnd_528432 := by exact prefixLift 528432
  have htrace : WordTrace (prefixWord ++ tailWord_528432) baseStart_528432 baseEnd_528432 := by
    simpa [prefixWord, tailWord_528432, baseEnd_528432] using wordTrace_append hprefix tailTrace_528432
  have hstable : (prefixWord ++ tailWord_528432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528432).length < 2 ^ (prefixWord ++ tailWord_528432).sum := by decide
  have hdescent : baseEnd_528432 < baseStart_528432 := by decide
  rcases family_descends (prefixWord ++ tailWord_528432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528435 : List Nat := [1, 1, 1, 2, 4, 1, 6, 1, 3]
def baseStart_528435 : Nat := 118140960795 + 528435 * 2 ^ 59
def prefixEnd_528435 : Nat := 4983230072969 + 3 ^ 40 * 528435 * 2
def baseEnd_528435 : Nat := 241192133029995759406469

theorem tailTrace_528435 : CollatzResearch.WordTrace tailWord_528435 prefixEnd_528435 241192133029995759406469 := by
  unfold tailWord_528435
  simp only [CollatzResearch.WordTrace]
  refine ⟨19273607840577719357978759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12849071893718479571985839 19273607840577719357978759)
  ·
    refine ⟨28910411760866579036968139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19273607840577719357978759 28910411760866579036968139)
    ·
      refine ⟨43365617641299868555452209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28910411760866579036968139 43365617641299868555452209)
      ·
        refine ⟨32524213230974901416589157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43365617641299868555452209 32524213230974901416589157)
        ·
          refine ⟨6098289980807794015610467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32524213230974901416589157 6098289980807794015610467)
          ·
            refine ⟨9147434971211691023415701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6098289980807794015610467 9147434971211691023415701)
            ·
              refine ⟨428786014275548016722611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9147434971211691023415701 428786014275548016722611)
              ·
                refine ⟨643179021413322025083917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428786014275548016722611 643179021413322025083917)
                ·
                  refine ⟨241192133029995759406469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 643179021413322025083917 241192133029995759406469)
                  ·
                    rfl

theorem cell20_528435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 3].length) (baseStart_528435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528435 prefixEnd_528435 := by exact prefixLift 528435
  have htrace : WordTrace (prefixWord ++ tailWord_528435) baseStart_528435 baseEnd_528435 := by
    simpa [prefixWord, tailWord_528435, baseEnd_528435] using wordTrace_append hprefix tailTrace_528435
  have hstable : (prefixWord ++ tailWord_528435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528435).length < 2 ^ (prefixWord ++ tailWord_528435).sum := by decide
  have hdescent : baseEnd_528435 < baseStart_528435 := by decide
  rcases family_descends (prefixWord ++ tailWord_528435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528449 : List Nat := [1, 2, 5, 1, 2, 1, 2, 6]
def baseStart_528449 : Nat := 118140960795 + 528449 * 2 ^ 59
def prefixEnd_528449 : Nat := 4983230072969 + 3 ^ 40 * 528449 * 2
def baseEnd_528449 : Nat := 80399507670491310979915

theorem tailTrace_528449 : CollatzResearch.WordTrace tailWord_528449 prefixEnd_528449 80399507670491310979915 := by
  unfold tailWord_528449
  simp only [CollatzResearch.WordTrace]
  refine ⟨19274118462526999748988401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12849412308351333165992267 19274118462526999748988401)
  ·
    refine ⟨14455588846895249811741301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19274118462526999748988401 14455588846895249811741301)
    ·
      refine ⟨1355211454396429669850747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14455588846895249811741301 1355211454396429669850747)
      ·
        refine ⟨2032817181594644504776121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1355211454396429669850747 2032817181594644504776121)
        ·
          refine ⟨1524612886195983378582091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2032817181594644504776121 1524612886195983378582091)
          ·
            refine ⟨2286919329293975067873137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1524612886195983378582091 2286919329293975067873137)
            ·
              refine ⟨1715189496970481300904853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2286919329293975067873137 1715189496970481300904853)
              ·
                refine ⟨80399507670491310979915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1715189496970481300904853 80399507670491310979915)
                ·
                  rfl

theorem cell20_528449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 6].length) (baseStart_528449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528449 prefixEnd_528449 := by exact prefixLift 528449
  have htrace : WordTrace (prefixWord ++ tailWord_528449) baseStart_528449 baseEnd_528449 := by
    simpa [prefixWord, tailWord_528449, baseEnd_528449] using wordTrace_append hprefix tailTrace_528449
  have hstable : (prefixWord ++ tailWord_528449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528449).length < 2 ^ (prefixWord ++ tailWord_528449).sum := by decide
  have hdescent : baseEnd_528449 < baseStart_528449 := by decide
  rcases family_descends (prefixWord ++ tailWord_528449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528476 : List Nat := [2, 2, 4, 1, 1, 2, 4, 2, 2]
def baseStart_528476 : Nat := 118140960795 + 528476 * 2 ^ 59
def prefixEnd_528476 : Nat := 4983230072969 + 3 ^ 40 * 528476 * 2
def baseEnd_528476 : Nat := 241210846547181839039635

theorem tailTrace_528476 : CollatzResearch.WordTrace tailWord_528476 prefixEnd_528476 241210846547181839039635 := by
  unfold tailWord_528476
  simp only [CollatzResearch.WordTrace]
  refine ⟨9637551616714591680110641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12850068822286122240147521 9637551616714591680110641)
  ·
    refine ⟨7228163712535943760082981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9637551616714591680110641 7228163712535943760082981)
    ·
      refine ⟨1355280696100489455015559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7228163712535943760082981 1355280696100489455015559)
      ·
        refine ⟨2032921044150734182523339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1355280696100489455015559 2032921044150734182523339)
        ·
          refine ⟨3049381566226101273785009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2032921044150734182523339 3049381566226101273785009)
          ·
            refine ⟨2287036174669575955338757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3049381566226101273785009 2287036174669575955338757)
            ·
              refine ⟨428819282750545491626017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2287036174669575955338757 428819282750545491626017)
              ·
                refine ⟨321614462062909118719513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428819282750545491626017 321614462062909118719513)
                ·
                  refine ⟨241210846547181839039635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321614462062909118719513 241210846547181839039635)
                  ·
                    rfl

theorem cell20_528476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_528476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528476 prefixEnd_528476 := by exact prefixLift 528476
  have htrace : WordTrace (prefixWord ++ tailWord_528476) baseStart_528476 baseEnd_528476 := by
    simpa [prefixWord, tailWord_528476, baseEnd_528476] using wordTrace_append hprefix tailTrace_528476
  have hstable : (prefixWord ++ tailWord_528476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528476).length < 2 ^ (prefixWord ++ tailWord_528476).sum := by decide
  have hdescent : baseEnd_528476 < baseStart_528476 := by decide
  rcases family_descends (prefixWord ++ tailWord_528476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528549 : List Nat := [1, 3, 1, 2, 1, 3, 5, 1, 3]
def baseStart_528549 : Nat := 118140960795 + 528549 * 2 ^ 59
def prefixEnd_528549 : Nat := 4983230072969 + 3 ^ 40 * 528549 * 2
def baseEnd_528549 : Nat := 241244165736318029606003

theorem tailTrace_528549 : CollatzResearch.WordTrace tailWord_528549 prefixEnd_528549 241244165736318029606003 := by
  unfold tailWord_528549
  simp only [CollatzResearch.WordTrace]
  refine ⟨19277765762164716827628701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12851843841443144551752467 19277765762164716827628701)
  ·
    refine ⟨7229162160811768810360763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19277765762164716827628701 7229162160811768810360763)
    ·
      refine ⟨10843743241217653215541145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7229162160811768810360763 10843743241217653215541145)
      ·
        refine ⟨8132807430913239911655859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10843743241217653215541145 8132807430913239911655859)
        ·
          refine ⟨12199211146369859867483789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8132807430913239911655859 12199211146369859867483789)
          ·
            refine ⟨4574704179888697450306421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12199211146369859867483789 4574704179888697450306421)
            ·
              refine ⟨428878516864565385966227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4574704179888697450306421 428878516864565385966227)
              ·
                refine ⟨643317775296848078949341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428878516864565385966227 643317775296848078949341)
                ·
                  refine ⟨241244165736318029606003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 643317775296848078949341 241244165736318029606003)
                  ·
                    rfl

theorem cell20_528549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_528549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528549 prefixEnd_528549 := by exact prefixLift 528549
  have htrace : WordTrace (prefixWord ++ tailWord_528549) baseStart_528549 baseEnd_528549 := by
    simpa [prefixWord, tailWord_528549, baseEnd_528549] using wordTrace_append hprefix tailTrace_528549
  have hstable : (prefixWord ++ tailWord_528549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528549).length < 2 ^ (prefixWord ++ tailWord_528549).sum := by decide
  have hdescent : baseEnd_528549 < baseStart_528549 := by decide
  rcases family_descends (prefixWord ++ tailWord_528549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528590 : List Nat := [4, 1, 1, 1, 4, 2, 3, 2, 2]
def baseStart_528590 : Nat := 118140960795 + 528590 * 2 ^ 59
def prefixEnd_528590 : Nat := 4983230072969 + 3 ^ 40 * 528590 * 2
def baseEnd_528590 : Nat := 241262879253504109239169

theorem tailTrace_528590 : CollatzResearch.WordTrace tailWord_528590 prefixEnd_528590 241262879253504109239169 := by
  unfold tailWord_528590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2409907644377022603733903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12852840770010787219914149 2409907644377022603733903)
  ·
    refine ⟨3614861466565533905600855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2409907644377022603733903 3614861466565533905600855)
    ·
      refine ⟨5422292199848300858401283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3614861466565533905600855 5422292199848300858401283)
      ·
        refine ⟨8133438299772451287601925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5422292199848300858401283 8133438299772451287601925)
        ·
          refine ⟨1525019681207334616425361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8133438299772451287601925 1525019681207334616425361)
          ·
            refine ⟨1143764760905500962319021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1525019681207334616425361 1143764760905500962319021)
            ·
              refine ⟨428911785339562860869633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1143764760905500962319021 428911785339562860869633)
              ·
                refine ⟨321683839004672145652225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428911785339562860869633 321683839004672145652225)
                ·
                  refine ⟨241262879253504109239169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321683839004672145652225 241262879253504109239169)
                  ·
                    rfl

theorem cell20_528590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_528590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528590 prefixEnd_528590 := by exact prefixLift 528590
  have htrace : WordTrace (prefixWord ++ tailWord_528590) baseStart_528590 baseEnd_528590 := by
    simpa [prefixWord, tailWord_528590, baseEnd_528590] using wordTrace_append hprefix tailTrace_528590
  have hstable : (prefixWord ++ tailWord_528590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528590).length < 2 ^ (prefixWord ++ tailWord_528590).sum := by decide
  have hdescent : baseEnd_528590 < baseStart_528590 := by decide
  rcases family_descends (prefixWord ++ tailWord_528590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528591 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 5]
def baseStart_528591 : Nat := 118140960795 + 528591 * 2 ^ 59
def prefixEnd_528591 : Nat := 4983230072969 + 3 ^ 40 * 528591 * 2
def baseEnd_528591 : Nat := 241263335680752550205831

theorem tailTrace_528591 : CollatzResearch.WordTrace tailWord_528591 prefixEnd_528591 241263335680752550205831 := by
  unfold tailWord_528591
  simp only [CollatzResearch.WordTrace]
  refine ⟨19279297628012558000657627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12852865085341705333771751 19279297628012558000657627)
  ·
    refine ⟨28918946442018837000986441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19279297628012558000657627 28918946442018837000986441)
    ·
      refine ⟨21689209831514127750739831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28918946442018837000986441 21689209831514127750739831)
      ·
        refine ⟨32533814747271191626109747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21689209831514127750739831 32533814747271191626109747)
        ·
          refine ⟨48800722120906787439164621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32533814747271191626109747 48800722120906787439164621)
          ·
            refine ⟨18300270795340045289686733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48800722120906787439164621 18300270795340045289686733)
            ·
              refine ⟨6862601548252516983632525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18300270795340045289686733 6862601548252516983632525)
              ·
                refine ⟨2573475580594693868862197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6862601548252516983632525 2573475580594693868862197)
                ·
                  refine ⟨241263335680752550205831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2573475580594693868862197 241263335680752550205831)
                  ·
                    rfl

theorem cell20_528591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_528591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528591 prefixEnd_528591 := by exact prefixLift 528591
  have htrace : WordTrace (prefixWord ++ tailWord_528591) baseStart_528591 baseEnd_528591 := by
    simpa [prefixWord, tailWord_528591, baseEnd_528591] using wordTrace_append hprefix tailTrace_528591
  have hstable : (prefixWord ++ tailWord_528591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528591).length < 2 ^ (prefixWord ++ tailWord_528591).sum := by decide
  have hdescent : baseEnd_528591 < baseStart_528591 := by decide
  rcases family_descends (prefixWord ++ tailWord_528591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528594 : List Nat := [3, 2, 2, 2, 1, 2, 3, 1, 4]
def baseStart_528594 : Nat := 118140960795 + 528594 * 2 ^ 59
def prefixEnd_528594 : Nat := 4983230072969 + 3 ^ 40 * 528594 * 2
def baseEnd_528594 : Nat := 241264704962497873105819

theorem tailTrace_528594 : CollatzResearch.WordTrace tailWord_528594 prefixEnd_528594 241264704962497873105819 := by
  unfold tailWord_528594
  simp only [CollatzResearch.WordTrace]
  refine ⟨4819851761750422378254209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12852938031334459675344557 4819851761750422378254209)
  ·
    refine ⟨3614888821312816783690657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4819851761750422378254209 3614888821312816783690657)
    ·
      refine ⟨2711166615984612587767993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3614888821312816783690657 2711166615984612587767993)
      ·
        refine ⟨2033374961988459440825995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2711166615984612587767993 2033374961988459440825995)
        ·
          refine ⟨3050062442982689161238993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2033374961988459440825995 3050062442982689161238993)
          ·
            refine ⟨2287546832237016870929245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3050062442982689161238993 2287546832237016870929245)
            ·
              refine ⟨857830062088881326598467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2287546832237016870929245 857830062088881326598467)
              ·
                refine ⟨1286745093133321989897701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857830062088881326598467 1286745093133321989897701)
                ·
                  refine ⟨241264704962497873105819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1286745093133321989897701 241264704962497873105819)
                  ·
                    rfl

theorem cell20_528594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_528594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528594 prefixEnd_528594 := by exact prefixLift 528594
  have htrace : WordTrace (prefixWord ++ tailWord_528594) baseStart_528594 baseEnd_528594 := by
    simpa [prefixWord, tailWord_528594, baseEnd_528594] using wordTrace_append hprefix tailTrace_528594
  have hstable : (prefixWord ++ tailWord_528594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528594).length < 2 ^ (prefixWord ++ tailWord_528594).sum := by decide
  have hdescent : baseEnd_528594 < baseStart_528594 := by decide
  rcases family_descends (prefixWord ++ tailWord_528594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528608 : List Nat := [2, 1, 1, 3, 1, 3, 3, 3, 3]
def baseStart_528608 : Nat := 118140960795 + 528608 * 2 ^ 59
def prefixEnd_528608 : Nat := 4983230072969 + 3 ^ 40 * 528608 * 2
def baseEnd_528608 : Nat := 241271094943976046639095

theorem tailTrace_528608 : CollatzResearch.WordTrace tailWord_528608 prefixEnd_528608 241271094943976046639095 := by
  unfold tailWord_528608
  simp only [CollatzResearch.WordTrace]
  refine ⟨9639958834475484952013239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12853278445967313269350985 9639958834475484952013239)
  ·
    refine ⟨14459938251713227428019859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9639958834475484952013239 14459938251713227428019859)
    ·
      refine ⟨21689907377569841142029789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14459938251713227428019859 21689907377569841142029789)
      ·
        refine ⟨8133715266588690428261171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21689907377569841142029789 8133715266588690428261171)
        ·
          refine ⟨12200572899883035642391757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8133715266588690428261171 12200572899883035642391757)
          ·
            refine ⟨4575214837456138365896909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12200572899883035642391757 4575214837456138365896909)
            ·
              refine ⟨1715705564046051887211341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4575214837456138365896909 1715705564046051887211341)
              ·
                refine ⟨643389586517269457704253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1715705564046051887211341 643389586517269457704253)
                ·
                  refine ⟨241271094943976046639095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 643389586517269457704253 241271094943976046639095)
                  ·
                    rfl

theorem cell20_528608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_528608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528608 prefixEnd_528608 := by exact prefixLift 528608
  have htrace : WordTrace (prefixWord ++ tailWord_528608) baseStart_528608 baseEnd_528608 := by
    simpa [prefixWord, tailWord_528608, baseEnd_528608] using wordTrace_append hprefix tailTrace_528608
  have hstable : (prefixWord ++ tailWord_528608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528608).length < 2 ^ (prefixWord ++ tailWord_528608).sum := by decide
  have hdescent : baseEnd_528608 < baseStart_528608 := by decide
  rcases family_descends (prefixWord ++ tailWord_528608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528642 : List Nat := [3, 4, 1, 1, 2, 2, 2, 2, 3]
def baseStart_528642 : Nat := 118140960795 + 528642 * 2 ^ 59
def prefixEnd_528642 : Nat := 4983230072969 + 3 ^ 40 * 528642 * 2
def baseEnd_528642 : Nat := 241286613470423039505623

theorem tailTrace_528642 : CollatzResearch.WordTrace tailWord_528642 prefixEnd_528642 241286613470423039505623 := by
  unfold tailWord_528642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4820289437706948427691045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12854105167218529140509453 4820289437706948427691045)
  ·
    refine ⟨903804269570052830192071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4820289437706948427691045 903804269570052830192071)
    ·
      refine ⟨1355706404355079245288107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 903804269570052830192071 1355706404355079245288107)
      ·
        refine ⟨2033559606532618867932161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1355706404355079245288107 2033559606532618867932161)
        ·
          refine ⟨1525169704899464150949121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2033559606532618867932161 1525169704899464150949121)
          ·
            refine ⟨1143877278674598113211841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1525169704899464150949121 1143877278674598113211841)
            ·
              refine ⟨857907959005948584908881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1143877278674598113211841 857907959005948584908881)
              ·
                refine ⟨643430969254461438681661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 857907959005948584908881 643430969254461438681661)
                ·
                  refine ⟨241286613470423039505623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 643430969254461438681661 241286613470423039505623)
                  ·
                    rfl

theorem cell20_528642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_528642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528642 prefixEnd_528642 := by exact prefixLift 528642
  have htrace : WordTrace (prefixWord ++ tailWord_528642) baseStart_528642 baseEnd_528642 := by
    simpa [prefixWord, tailWord_528642, baseEnd_528642] using wordTrace_append hprefix tailTrace_528642
  have hstable : (prefixWord ++ tailWord_528642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528642).length < 2 ^ (prefixWord ++ tailWord_528642).sum := by decide
  have hdescent : baseEnd_528642 < baseStart_528642 := by decide
  rcases family_descends (prefixWord ++ tailWord_528642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528649 : List Nat := [1, 2, 1, 1, 3, 4, 4, 2, 2]
def baseStart_528649 : Nat := 118140960795 + 528649 * 2 ^ 59
def prefixEnd_528649 : Nat := 4983230072969 + 3 ^ 40 * 528649 * 2
def baseEnd_528649 : Nat := 241289808461162126272261

theorem tailTrace_528649 : CollatzResearch.WordTrace tailWord_528649 prefixEnd_528649 241289808461162126272261 := by
  unfold tailWord_528649
  simp only [CollatzResearch.WordTrace]
  refine ⟨19281413061802433906269001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12854275374534955937512667 19281413061802433906269001)
  ·
    refine ⟨14461059796351825429701751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19281413061802433906269001 14461059796351825429701751)
    ·
      refine ⟨21691589694527738144552627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14461059796351825429701751 21691589694527738144552627)
      ·
        refine ⟨32537384541791607216828941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21691589694527738144552627 32537384541791607216828941)
        ·
          refine ⟨12201519203171852706310853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32537384541791607216828941 12201519203171852706310853)
          ·
            refine ⟨2287784850594722382433285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12201519203171852706310853 2287784850594722382433285)
            ·
              refine ⟨428959659486510446706241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2287784850594722382433285 428959659486510446706241)
              ·
                refine ⟨321719744614882835029681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428959659486510446706241 321719744614882835029681)
                ·
                  refine ⟨241289808461162126272261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321719744614882835029681 241289808461162126272261)
                  ·
                    rfl

theorem cell20_528649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 2].length) (baseStart_528649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528649 prefixEnd_528649 := by exact prefixLift 528649
  have htrace : WordTrace (prefixWord ++ tailWord_528649) baseStart_528649 baseEnd_528649 := by
    simpa [prefixWord, tailWord_528649, baseEnd_528649] using wordTrace_append hprefix tailTrace_528649
  have hstable : (prefixWord ++ tailWord_528649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528649).length < 2 ^ (prefixWord ++ tailWord_528649).sum := by decide
  have hdescent : baseEnd_528649 < baseStart_528649 := by decide
  rcases family_descends (prefixWord ++ tailWord_528649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528698 : List Nat := [3, 1, 1, 1, 4, 3, 7]
def baseStart_528698 : Nat := 118140960795 + 528698 * 2 ^ 59
def prefixEnd_528698 : Nat := 4983230072969 + 3 ^ 40 * 528698 * 2
def baseEnd_528698 : Nat := 26812463710703970404303

theorem tailTrace_528698 : CollatzResearch.WordTrace tailWord_528698 prefixEnd_528698 26812463710703970404303 := by
  unfold tailWord_528698
  simp only [CollatzResearch.WordTrace]
  refine ⟨4820800059656228818700687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12855466825749943516535165 4820800059656228818700687)
  ·
    refine ⟨7231200089484343228051031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4820800059656228818700687 7231200089484343228051031)
    ·
      refine ⟨10846800134226514842076547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7231200089484343228051031 10846800134226514842076547)
      ·
        refine ⟨16270200201339772263114821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10846800134226514842076547 16270200201339772263114821)
        ·
          refine ⟨3050662537751207299334029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16270200201339772263114821 3050662537751207299334029)
          ·
            refine ⟨1143998451656702737250261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3050662537751207299334029 1143998451656702737250261)
            ·
              refine ⟨26812463710703970404303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1143998451656702737250261 26812463710703970404303)
              ·
                rfl

theorem cell20_528698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 7].length) (baseStart_528698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528698 prefixEnd_528698 := by exact prefixLift 528698
  have htrace : WordTrace (prefixWord ++ tailWord_528698) baseStart_528698 baseEnd_528698 := by
    simpa [prefixWord, tailWord_528698, baseEnd_528698] using wordTrace_append hprefix tailTrace_528698
  have hstable : (prefixWord ++ tailWord_528698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528698).length < 2 ^ (prefixWord ++ tailWord_528698).sum := by decide
  have hdescent : baseEnd_528698 < baseStart_528698 := by decide
  rcases family_descends (prefixWord ++ tailWord_528698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528722 : List Nat := [3, 2, 2, 1, 1, 1, 2, 5, 3]
def baseStart_528722 : Nat := 118140960795 + 528722 * 2 ^ 59
def prefixEnd_528722 : Nat := 4983230072969 + 3 ^ 40 * 528722 * 2
def baseEnd_528722 : Nat := 241323127650298316838629

theorem tailTrace_528722 : CollatzResearch.WordTrace tailWord_528722 prefixEnd_528722 241323127650298316838629 := by
  unfold tailWord_528722
  simp only [CollatzResearch.WordTrace]
  refine ⟨4821018897634491843419105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12856050393691978249117613 4821018897634491843419105)
  ·
    refine ⟨3615764173225868882564329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4821018897634491843419105 3615764173225868882564329)
    ·
      refine ⟨2711823129919401661923247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3615764173225868882564329 2711823129919401661923247)
      ·
        refine ⟨4067734694879102492884871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2711823129919401661923247 4067734694879102492884871)
        ·
          refine ⟨6101602042318653739327307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4067734694879102492884871 6101602042318653739327307)
          ·
            refine ⟨9152403063477980608990961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6101602042318653739327307 9152403063477980608990961)
            ·
              refine ⟨6864302297608485456743221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9152403063477980608990961 6864302297608485456743221)
              ·
                refine ⟨643528340400795511569677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6864302297608485456743221 643528340400795511569677)
                ·
                  refine ⟨241323127650298316838629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 643528340400795511569677 241323127650298316838629)
                  ·
                    rfl

theorem cell20_528722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_528722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528722 prefixEnd_528722 := by exact prefixLift 528722
  have htrace : WordTrace (prefixWord ++ tailWord_528722) baseStart_528722 baseEnd_528722 := by
    simpa [prefixWord, tailWord_528722, baseEnd_528722] using wordTrace_append hprefix tailTrace_528722
  have hstable : (prefixWord ++ tailWord_528722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528722).length < 2 ^ (prefixWord ++ tailWord_528722).sum := by decide
  have hdescent : baseEnd_528722 < baseStart_528722 := by decide
  rcases family_descends (prefixWord ++ tailWord_528722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528732 : List Nat := [2, 2, 4, 3, 1, 1, 1, 6]
def baseStart_528732 : Nat := 118140960795 + 528732 * 2 ^ 59
def prefixEnd_528732 : Nat := 4983230072969 + 3 ^ 40 * 528732 * 2
def baseEnd_528732 : Nat := 80442563974260908835085

theorem tailTrace_528732 : CollatzResearch.WordTrace tailWord_528732 prefixEnd_528732 80442563974260908835085 := by
  unfold tailWord_528732
  simp only [CollatzResearch.WordTrace]
  refine ⟨9642220160250869540770225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12856293547001159387693633 9642220160250869540770225)
  ·
    refine ⟨7231665120188152155577669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9642220160250869540770225 7231665120188152155577669)
    ·
      refine ⟨1355937210035278529170813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7231665120188152155577669 1355937210035278529170813)
      ·
        refine ⟨508476453763229448439055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1355937210035278529170813 508476453763229448439055)
        ·
          refine ⟨762714680644844172658583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508476453763229448439055 762714680644844172658583)
          ·
            refine ⟨1144072020967266258987875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762714680644844172658583 1144072020967266258987875)
            ·
              refine ⟨1716108031450899388481813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1144072020967266258987875 1716108031450899388481813)
              ·
                refine ⟨80442563974260908835085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1716108031450899388481813 80442563974260908835085)
                ·
                  rfl

theorem cell20_528732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 6].length) (baseStart_528732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528732 prefixEnd_528732 := by exact prefixLift 528732
  have htrace : WordTrace (prefixWord ++ tailWord_528732) baseStart_528732 baseEnd_528732 := by
    simpa [prefixWord, tailWord_528732, baseEnd_528732] using wordTrace_append hprefix tailTrace_528732
  have hstable : (prefixWord ++ tailWord_528732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528732).length < 2 ^ (prefixWord ++ tailWord_528732).sum := by decide
  have hdescent : baseEnd_528732 < baseStart_528732 := by decide
  rcases family_descends (prefixWord ++ tailWord_528732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528734 : List Nat := [4, 4, 2, 1, 2, 1, 1, 3, 2]
def baseStart_528734 : Nat := 118140960795 + 528734 * 2 ^ 59
def prefixEnd_528734 : Nat := 4983230072969 + 3 ^ 40 * 528734 * 2
def baseEnd_528734 : Nat := 241328604777279608438581

theorem tailTrace_528734 : CollatzResearch.WordTrace tailWord_528734 prefixEnd_528734 241328604777279608438581 := by
  unfold tailWord_528734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2410564158311811677889157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12856342177662995615408837 2410564158311811677889157)
  ·
    refine ⟨451980779683464689604217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2410564158311811677889157 451980779683464689604217)
    ·
      refine ⟨338985584762598517203163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451980779683464689604217 338985584762598517203163)
      ·
        refine ⟨508478377143897775804745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338985584762598517203163 508478377143897775804745)
        ·
          refine ⟨381358782857923331853559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508478377143897775804745 381358782857923331853559)
          ·
            refine ⟨572038174286884997780339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381358782857923331853559 572038174286884997780339)
            ·
              refine ⟨858057261430327496670509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572038174286884997780339 858057261430327496670509)
              ·
                refine ⟨321771473036372811251441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 858057261430327496670509 321771473036372811251441)
                ·
                  refine ⟨241328604777279608438581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321771473036372811251441 241328604777279608438581)
                  ·
                    rfl

theorem cell20_528734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_528734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528734 prefixEnd_528734 := by exact prefixLift 528734
  have htrace : WordTrace (prefixWord ++ tailWord_528734) baseStart_528734 baseEnd_528734 := by
    simpa [prefixWord, tailWord_528734, baseEnd_528734] using wordTrace_append hprefix tailTrace_528734
  have hstable : (prefixWord ++ tailWord_528734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528734).length < 2 ^ (prefixWord ++ tailWord_528734).sum := by decide
  have hdescent : baseEnd_528734 < baseStart_528734 := by decide
  rcases family_descends (prefixWord ++ tailWord_528734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528763 : List Nat := [1, 1, 1, 1, 1, 8, 3, 2, 2]
def baseStart_528763 : Nat := 118140960795 + 528763 * 2 ^ 59
def prefixEnd_528763 : Nat := 4983230072969 + 3 ^ 40 * 528763 * 2
def baseEnd_528763 : Nat := 241341841167484396471795

theorem tailTrace_528763 : CollatzResearch.WordTrace tailWord_528763 prefixEnd_528763 241341841167484396471795 := by
  unfold tailWord_528763
  simp only [CollatzResearch.WordTrace]
  refine ⟨19285570983389431375918943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12857047322259620917279295 19285570983389431375918943)
  ·
    refine ⟨28928356475084147063878415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19285570983389431375918943 28928356475084147063878415)
    ·
      refine ⟨43392534712626220595817623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28928356475084147063878415 43392534712626220595817623)
      ·
        refine ⟨65088802068939330893726435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43392534712626220595817623 65088802068939330893726435)
        ·
          refine ⟨97633203103408996340589653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65088802068939330893726435 97633203103408996340589653)
          ·
            refine ⟨1144139098868074175866285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 97633203103408996340589653 1144139098868074175866285)
            ·
              refine ⟨429052162075527815949857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1144139098868074175866285 429052162075527815949857)
              ·
                refine ⟨321789121556645861962393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429052162075527815949857 321789121556645861962393)
                ·
                  refine ⟨241341841167484396471795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321789121556645861962393 241341841167484396471795)
                  ·
                    rfl

theorem cell20_528763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 2].length) (baseStart_528763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528763 prefixEnd_528763 := by exact prefixLift 528763
  have htrace : WordTrace (prefixWord ++ tailWord_528763) baseStart_528763 baseEnd_528763 := by
    simpa [prefixWord, tailWord_528763, baseEnd_528763] using wordTrace_append hprefix tailTrace_528763
  have hstable : (prefixWord ++ tailWord_528763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528763).length < 2 ^ (prefixWord ++ tailWord_528763).sum := by decide
  have hdescent : baseEnd_528763 < baseStart_528763 := by decide
  rcases family_descends (prefixWord ++ tailWord_528763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528777 : List Nat := [1, 2, 1, 1, 6, 1, 4, 1, 3]
def baseStart_528777 : Nat := 118140960795 + 528777 * 2 ^ 59
def prefixEnd_528777 : Nat := 4983230072969 + 3 ^ 40 * 528777 * 2
def baseEnd_528777 : Nat := 241348231148962570005071

theorem tailTrace_528777 : CollatzResearch.WordTrace tailWord_528777 prefixEnd_528777 241348231148962570005071 := by
  unfold tailWord_528777
  simp only [CollatzResearch.WordTrace]
  refine ⟨19286081605338711766928585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12857387736892474511285723 19286081605338711766928585)
  ·
    refine ⟨14464561204004033825196439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19286081605338711766928585 14464561204004033825196439)
    ·
      refine ⟨21696841806006050737794659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14464561204004033825196439 21696841806006050737794659)
      ·
        refine ⟨32545262709009076106691989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21696841806006050737794659 32545262709009076106691989)
        ·
          refine ⟨1525559189484800442501187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32545262709009076106691989 1525559189484800442501187)
          ·
            refine ⟨2288338784227200663751781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1525559189484800442501187 2288338784227200663751781)
            ·
              refine ⟨429063522042600124453459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2288338784227200663751781 429063522042600124453459)
              ·
                refine ⟨643595283063900186680189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429063522042600124453459 643595283063900186680189)
                ·
                  refine ⟨241348231148962570005071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 643595283063900186680189 241348231148962570005071)
                  ·
                    rfl

theorem cell20_528777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 3].length) (baseStart_528777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528777 prefixEnd_528777 := by exact prefixLift 528777
  have htrace : WordTrace (prefixWord ++ tailWord_528777) baseStart_528777 baseEnd_528777 := by
    simpa [prefixWord, tailWord_528777, baseEnd_528777] using wordTrace_append hprefix tailTrace_528777
  have hstable : (prefixWord ++ tailWord_528777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528777).length < 2 ^ (prefixWord ++ tailWord_528777).sum := by decide
  have hdescent : baseEnd_528777 < baseStart_528777 := by decide
  rcases family_descends (prefixWord ++ tailWord_528777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528826 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_528826 : Nat := 118140960795 + 528826 * 2 ^ 59
def prefixEnd_528826 : Nat := 4983230072969 + 3 ^ 40 * 528826 * 2
def baseEnd_528826 : Nat := 241370596084136177371537

theorem tailTrace_528826 : CollatzResearch.WordTrace tailWord_528826 prefixEnd_528826 241370596084136177371537 := by
  unfold tailWord_528826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4821967195540298283865583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12858579188107462090308221 4821967195540298283865583)
  ·
    refine ⟨7232950793310447425798375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4821967195540298283865583 7232950793310447425798375)
    ·
      refine ⟨10849426189965671138697563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7232950793310447425798375 10849426189965671138697563)
      ·
        refine ⟨16274139284948506708046345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10849426189965671138697563 16274139284948506708046345)
        ·
          refine ⟨12205604463711380031034759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16274139284948506708046345 12205604463711380031034759)
          ·
            refine ⟨18308406695567070046552139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12205604463711380031034759 18308406695567070046552139)
            ·
              refine ⟨27462610043350605069828209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18308406695567070046552139 27462610043350605069828209)
              ·
                refine ⟨20596957532512953802371157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27462610043350605069828209 20596957532512953802371157)
                ·
                  refine ⟨241370596084136177371537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20596957532512953802371157 241370596084136177371537)
                  ·
                    rfl

theorem cell20_528826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_528826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528826 prefixEnd_528826 := by exact prefixLift 528826
  have htrace : WordTrace (prefixWord ++ tailWord_528826) baseStart_528826 baseEnd_528826 := by
    simpa [prefixWord, tailWord_528826, baseEnd_528826] using wordTrace_append hprefix tailTrace_528826
  have hstable : (prefixWord ++ tailWord_528826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528826).length < 2 ^ (prefixWord ++ tailWord_528826).sum := by decide
  have hdescent : baseEnd_528826 < baseStart_528826 := by decide
  rcases family_descends (prefixWord ++ tailWord_528826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528829 : List Nat := [1, 4, 1, 2, 2, 4, 1, 5]
def baseStart_528829 : Nat := 118140960795 + 528829 * 2 ^ 59
def prefixEnd_528829 : Nat := 4983230072969 + 3 ^ 40 * 528829 * 2
def baseEnd_528829 : Nat := 80457321788627166757175

theorem tailTrace_528829 : CollatzResearch.WordTrace tailWord_528829 prefixEnd_528829 80457321788627166757175 := by
  unfold tailWord_528829
  simp only [CollatzResearch.WordTrace]
  refine ⟨19287978201150324647821541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12858652134100216431881027 19287978201150324647821541)
  ·
    refine ⟨3616495912715685871466539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19287978201150324647821541 3616495912715685871466539)
    ·
      refine ⟨5424743869073528807199809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3616495912715685871466539 5424743869073528807199809)
      ·
        refine ⟨4068557901805146605399857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5424743869073528807199809 4068557901805146605399857)
        ·
          refine ⟨3051418426353859954049893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4068557901805146605399857 3051418426353859954049893)
          ·
            refine ⟨572140954941348741384355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3051418426353859954049893 572140954941348741384355)
            ·
              refine ⟨858211432412023112076533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572140954941348741384355 858211432412023112076533)
              ·
                refine ⟨80457321788627166757175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 858211432412023112076533 80457321788627166757175)
                ·
                  rfl

theorem cell20_528829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 5].length) (baseStart_528829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528829 prefixEnd_528829 := by exact prefixLift 528829
  have htrace : WordTrace (prefixWord ++ tailWord_528829) baseStart_528829 baseEnd_528829 := by
    simpa [prefixWord, tailWord_528829, baseEnd_528829] using wordTrace_append hprefix tailTrace_528829
  have hstable : (prefixWord ++ tailWord_528829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528829).length < 2 ^ (prefixWord ++ tailWord_528829).sum := by decide
  have hdescent : baseEnd_528829 < baseStart_528829 := by decide
  rcases family_descends (prefixWord ++ tailWord_528829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528857 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 5]
def baseStart_528857 : Nat := 118140960795 + 528857 * 2 ^ 59
def prefixEnd_528857 : Nat := 4983230072969 + 3 ^ 40 * 528857 * 2
def baseEnd_528857 : Nat := 241384745328837847338077

theorem tailTrace_528857 : CollatzResearch.WordTrace tailWord_528857 prefixEnd_528857 241384745328837847338077 := by
  unfold tailWord_528857
  simp only [CollatzResearch.WordTrace]
  refine ⟨19288999445048885429840825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12859332963365923619893883 19288999445048885429840825)
  ·
    refine ⟨14466749583786664072380619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19288999445048885429840825 14466749583786664072380619)
    ·
      refine ⟨21700124375679996108570929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14466749583786664072380619 21700124375679996108570929)
      ·
        refine ⟨16275093281759997081428197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21700124375679996108570929 16275093281759997081428197)
        ·
          refine ⟨3051579990329999452767787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16275093281759997081428197 3051579990329999452767787)
          ·
            refine ⟨4577369985494999179151681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051579990329999452767787 4577369985494999179151681)
            ·
              refine ⟨3433027489121249384363761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4577369985494999179151681 3433027489121249384363761)
              ·
                refine ⟨2574770616840937038272821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3433027489121249384363761 2574770616840937038272821)
                ·
                  refine ⟨241384745328837847338077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2574770616840937038272821 241384745328837847338077)
                  ·
                    rfl

theorem cell20_528857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_528857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528857 prefixEnd_528857 := by exact prefixLift 528857
  have htrace : WordTrace (prefixWord ++ tailWord_528857) baseStart_528857 baseEnd_528857 := by
    simpa [prefixWord, tailWord_528857, baseEnd_528857] using wordTrace_append hprefix tailTrace_528857
  have hstable : (prefixWord ++ tailWord_528857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528857).length < 2 ^ (prefixWord ++ tailWord_528857).sum := by decide
  have hdescent : baseEnd_528857 < baseStart_528857 := by decide
  rcases family_descends (prefixWord ++ tailWord_528857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528864 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 6]
def baseStart_528864 : Nat := 118140960795 + 528864 * 2 ^ 59
def prefixEnd_528864 : Nat := 4983230072969 + 3 ^ 40 * 528864 * 2
def baseEnd_528864 : Nat := 241387940319576934104715

theorem tailTrace_528864 : CollatzResearch.WordTrace tailWord_528864 prefixEnd_528864 241387940319576934104715 := by
  unfold tailWord_528864
  simp only [CollatzResearch.WordTrace]
  refine ⟨9644627378011762812672823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12859503170682350416897097 9644627378011762812672823)
  ·
    refine ⟨14466941067017644219009235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9644627378011762812672823 14466941067017644219009235)
    ·
      refine ⟨21700411600526466328513853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14466941067017644219009235 21700411600526466328513853)
      ·
        refine ⟨8137654350197424873192695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21700411600526466328513853 8137654350197424873192695)
        ·
          refine ⟨12206481525296137309789043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8137654350197424873192695 12206481525296137309789043)
          ·
            refine ⟨18309722287944205964683565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12206481525296137309789043 18309722287944205964683565)
            ·
              refine ⟨6866145857979077236756337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18309722287944205964683565 6866145857979077236756337)
              ·
                refine ⟨5149609393484307927567253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6866145857979077236756337 5149609393484307927567253)
                ·
                  refine ⟨241387940319576934104715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5149609393484307927567253 241387940319576934104715)
                  ·
                    rfl

theorem cell20_528864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_528864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528864 prefixEnd_528864 := by exact prefixLift 528864
  have htrace : WordTrace (prefixWord ++ tailWord_528864) baseStart_528864 baseEnd_528864 := by
    simpa [prefixWord, tailWord_528864, baseEnd_528864] using wordTrace_append hprefix tailTrace_528864
  have hstable : (prefixWord ++ tailWord_528864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528864).length < 2 ^ (prefixWord ++ tailWord_528864).sum := by decide
  have hdescent : baseEnd_528864 < baseStart_528864 := by decide
  rcases family_descends (prefixWord ++ tailWord_528864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528866 : List Nat := [3, 3, 3, 2, 2, 1, 1, 2, 3]
def baseStart_528866 : Nat := 118140960795 + 528866 * 2 ^ 59
def prefixEnd_528866 : Nat := 4983230072969 + 3 ^ 40 * 528866 * 2
def baseEnd_528866 : Nat := 241388853174073816038041

theorem tailTrace_528866 : CollatzResearch.WordTrace tailWord_528866 prefixEnd_528866 241388853174073816038041 := by
  unfold tailWord_528866
  simp only [CollatzResearch.WordTrace]
  refine ⟨4822331925504069991729613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12859551801344186644612301 4822331925504069991729613)
  ·
    refine ⟨1808374472064026246898605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4822331925504069991729613 1808374472064026246898605)
    ·
      refine ⟨678140427024009842586977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1808374472064026246898605 678140427024009842586977)
      ·
        refine ⟨508605320268007381940233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 678140427024009842586977 508605320268007381940233)
        ·
          refine ⟨381453990201005536455175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508605320268007381940233 381453990201005536455175)
          ·
            refine ⟨572180985301508304682763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381453990201005536455175 572180985301508304682763)
            ·
              refine ⟨858271477952262457024145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572180985301508304682763 858271477952262457024145)
              ·
                refine ⟨643703608464196842768109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 858271477952262457024145 643703608464196842768109)
                ·
                  refine ⟨241388853174073816038041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 643703608464196842768109 241388853174073816038041)
                  ·
                    rfl

theorem cell20_528866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_528866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528866 prefixEnd_528866 := by exact prefixLift 528866
  have htrace : WordTrace (prefixWord ++ tailWord_528866) baseStart_528866 baseEnd_528866 := by
    simpa [prefixWord, tailWord_528866, baseEnd_528866] using wordTrace_append hprefix tailTrace_528866
  have hstable : (prefixWord ++ tailWord_528866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528866).length < 2 ^ (prefixWord ++ tailWord_528866).sum := by decide
  have hdescent : baseEnd_528866 < baseStart_528866 := by decide
  rcases family_descends (prefixWord ++ tailWord_528866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528874 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 5]
def baseStart_528874 : Nat := 118140960795 + 528874 * 2 ^ 59
def prefixEnd_528874 : Nat := 4983230072969 + 3 ^ 40 * 528874 * 2
def baseEnd_528874 : Nat := 241392504592061343771341

theorem tailTrace_528874 : CollatzResearch.WordTrace tailWord_528874 prefixEnd_528874 241392504592061343771341 := by
  unfold tailWord_528874
  simp only [CollatzResearch.WordTrace]
  refine ⟨4822404871496824333302419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12859746323991531555473117 4822404871496824333302419)
  ·
    refine ⟨7233607307245236499953629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4822404871496824333302419 7233607307245236499953629)
    ·
      refine ⟨2712602740216963687482611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7233607307245236499953629 2712602740216963687482611)
      ·
        refine ⟨4068904110325445531223917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2712602740216963687482611 4068904110325445531223917)
        ·
          refine ⟨1525839041372042074208969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4068904110325445531223917 1525839041372042074208969)
          ·
            refine ⟨1144379281029031555656727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1525839041372042074208969 1144379281029031555656727)
            ·
              refine ⟨1716568921543547333485091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1144379281029031555656727 1716568921543547333485091)
              ·
                refine ⟨2574853382315321000227637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1716568921543547333485091 2574853382315321000227637)
                ·
                  refine ⟨241392504592061343771341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2574853382315321000227637 241392504592061343771341)
                  ·
                    rfl

theorem cell20_528874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_528874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528874 prefixEnd_528874 := by exact prefixLift 528874
  have htrace : WordTrace (prefixWord ++ tailWord_528874) baseStart_528874 baseEnd_528874 := by
    simpa [prefixWord, tailWord_528874, baseEnd_528874] using wordTrace_append hprefix tailTrace_528874
  have hstable : (prefixWord ++ tailWord_528874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528874).length < 2 ^ (prefixWord ++ tailWord_528874).sum := by decide
  have hdescent : baseEnd_528874 < baseStart_528874 := by decide
  rcases family_descends (prefixWord ++ tailWord_528874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528877 : List Nat := [1, 5, 1, 3, 1, 1, 2, 4, 2]
def baseStart_528877 : Nat := 118140960795 + 528877 * 2 ^ 59
def prefixEnd_528877 : Nat := 4983230072969 + 3 ^ 40 * 528877 * 2
def baseEnd_528877 : Nat := 241393873873806666671329

theorem tailTrace_528877 : CollatzResearch.WordTrace tailWord_528877 prefixEnd_528877 241393873873806666671329 := by
  unfold tailWord_528877
  simp only [CollatzResearch.WordTrace]
  refine ⟨19289728904976428845568885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12859819269984285897045923 19289728904976428845568885)
  ·
    refine ⟨1808412084841540204272083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19289728904976428845568885 1808412084841540204272083)
    ·
      refine ⟨2712618127262310306408125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1808412084841540204272083 2712618127262310306408125)
      ·
        refine ⟨1017231797723366364903047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2712618127262310306408125 1017231797723366364903047)
        ·
          refine ⟨1525847696585049547354571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1017231797723366364903047 1525847696585049547354571)
          ·
            refine ⟨2288771544877574321031857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1525847696585049547354571 2288771544877574321031857)
            ·
              refine ⟨1716578658658180740773893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2288771544877574321031857 1716578658658180740773893)
              ·
                refine ⟨321858498498408888895105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1716578658658180740773893 321858498498408888895105)
                ·
                  refine ⟨241393873873806666671329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321858498498408888895105 241393873873806666671329)
                  ·
                    rfl

theorem cell20_528877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_528877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528877 prefixEnd_528877 := by exact prefixLift 528877
  have htrace : WordTrace (prefixWord ++ tailWord_528877) baseStart_528877 baseEnd_528877 := by
    simpa [prefixWord, tailWord_528877, baseEnd_528877] using wordTrace_append hprefix tailTrace_528877
  have hstable : (prefixWord ++ tailWord_528877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528877).length < 2 ^ (prefixWord ++ tailWord_528877).sum := by decide
  have hdescent : baseEnd_528877 < baseStart_528877 := by decide
  rcases family_descends (prefixWord ++ tailWord_528877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528881 : List Nat := [1, 2, 2, 2, 3, 1, 4, 1, 4]
def baseStart_528881 : Nat := 118140960795 + 528881 * 2 ^ 59
def prefixEnd_528881 : Nat := 4983230072969 + 3 ^ 40 * 528881 * 2
def baseEnd_528881 : Nat := 241395699582800430537979

theorem tailTrace_528881 : CollatzResearch.WordTrace tailWord_528881 prefixEnd_528881 241395699582800430537979 := by
  unfold tailWord_528881
  simp only [CollatzResearch.WordTrace]
  refine ⟨19289874796961937528714497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12859916531307958352476331 19289874796961937528714497)
  ·
    refine ⟨14467406097721453146535873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19289874796961937528714497 14467406097721453146535873)
    ·
      refine ⟨10850554573291089859901905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14467406097721453146535873 10850554573291089859901905)
      ·
        refine ⟨8137915929968317394926429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10850554573291089859901905 8137915929968317394926429)
        ·
          refine ⟨3051718473738119023097411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8137915929968317394926429 3051718473738119023097411)
          ·
            refine ⟨4577577710607178534646117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051718473738119023097411 4577577710607178534646117)
            ·
              refine ⟨858295820738845975246147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4577577710607178534646117 858295820738845975246147)
              ·
                refine ⟨1287443731108268962869221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858295820738845975246147 1287443731108268962869221)
                ·
                  refine ⟨241395699582800430537979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1287443731108268962869221 241395699582800430537979)
                  ·
                    rfl

theorem cell20_528881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_528881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528881 prefixEnd_528881 := by exact prefixLift 528881
  have htrace : WordTrace (prefixWord ++ tailWord_528881) baseStart_528881 baseEnd_528881 := by
    simpa [prefixWord, tailWord_528881, baseEnd_528881] using wordTrace_append hprefix tailTrace_528881
  have hstable : (prefixWord ++ tailWord_528881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528881).length < 2 ^ (prefixWord ++ tailWord_528881).sum := by decide
  have hdescent : baseEnd_528881 < baseStart_528881 := by decide
  rcases family_descends (prefixWord ++ tailWord_528881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528932 : List Nat := [2, 3, 1, 5, 2, 1, 1, 1, 4]
def baseStart_528932 : Nat := 118140960795 + 528932 * 2 ^ 59
def prefixEnd_528932 : Nat := 4983230072969 + 3 ^ 40 * 528932 * 2
def baseEnd_528932 : Nat := 241418977372470919837771

theorem tailTrace_528932 : CollatzResearch.WordTrace tailWord_528932 prefixEnd_528932 241418977372470919837771 := by
  unfold tailWord_528932
  simp only [CollatzResearch.WordTrace]
  refine ⟨9645867459888586619410525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12861156613184782159214033 9645867459888586619410525)
  ·
    refine ⟨3617200297458219982278947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9645867459888586619410525 3617200297458219982278947)
    ·
      refine ⟨5425800446187329973418421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3617200297458219982278947 5425800446187329973418421)
      ·
        refine ⟨508668791830062185007977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5425800446187329973418421 508668791830062185007977)
        ·
          refine ⟨381501593872546638755983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508668791830062185007977 381501593872546638755983)
          ·
            refine ⟨572252390808819958133975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381501593872546638755983 572252390808819958133975)
            ·
              refine ⟨858378586213229937200963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572252390808819958133975 858378586213229937200963)
              ·
                refine ⟨1287567879319844905801445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858378586213229937200963 1287567879319844905801445)
                ·
                  refine ⟨241418977372470919837771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1287567879319844905801445 241418977372470919837771)
                  ·
                    rfl

theorem cell20_528932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_528932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528932 prefixEnd_528932 := by exact prefixLift 528932
  have htrace : WordTrace (prefixWord ++ tailWord_528932) baseStart_528932 baseEnd_528932 := by
    simpa [prefixWord, tailWord_528932, baseEnd_528932] using wordTrace_append hprefix tailTrace_528932
  have hstable : (prefixWord ++ tailWord_528932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528932).length < 2 ^ (prefixWord ++ tailWord_528932).sum := by decide
  have hdescent : baseEnd_528932 < baseStart_528932 := by decide
  rcases family_descends (prefixWord ++ tailWord_528932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528933 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 5]
def baseStart_528933 : Nat := 118140960795 + 528933 * 2 ^ 59
def prefixEnd_528933 : Nat := 4983230072969 + 3 ^ 40 * 528933 * 2
def baseEnd_528933 : Nat := 241419433799719360804433

theorem tailTrace_528933 : CollatzResearch.WordTrace tailWord_528933 prefixEnd_528933 241419433799719360804433 := by
  unfold tailWord_528933
  simp only [CollatzResearch.WordTrace]
  refine ⟨19291771392773550409607453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12861180928515700273071635 19291771392773550409607453)
  ·
    refine ⟨7234414272290081403602795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19291771392773550409607453 7234414272290081403602795)
    ·
      refine ⟨10851621408435122105404193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7234414272290081403602795 10851621408435122105404193)
      ·
        refine ⟨8138716056326341579053145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10851621408435122105404193 8138716056326341579053145)
        ·
          refine ⟨6104037042244756184289859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8138716056326341579053145 6104037042244756184289859)
          ·
            refine ⟨9156055563367134276434789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6104037042244756184289859 9156055563367134276434789)
            ·
              refine ⟨1716760418131337676831523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9156055563367134276434789 1716760418131337676831523)
              ·
                refine ⟨2575140627197006515247285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1716760418131337676831523 2575140627197006515247285)
                ·
                  refine ⟨241419433799719360804433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2575140627197006515247285 241419433799719360804433)
                  ·
                    rfl

theorem cell20_528933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_528933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528933 prefixEnd_528933 := by exact prefixLift 528933
  have htrace : WordTrace (prefixWord ++ tailWord_528933) baseStart_528933 baseEnd_528933 := by
    simpa [prefixWord, tailWord_528933, baseEnd_528933] using wordTrace_append hprefix tailTrace_528933
  have hstable : (prefixWord ++ tailWord_528933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528933).length < 2 ^ (prefixWord ++ tailWord_528933).sum := by decide
  have hdescent : baseEnd_528933 < baseStart_528933 := by decide
  rcases family_descends (prefixWord ++ tailWord_528933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528936 : List Nat := [2, 1, 5, 2, 1, 1, 3, 1, 4]
def baseStart_528936 : Nat := 118140960795 + 528936 * 2 ^ 59
def prefixEnd_528936 : Nat := 4983230072969 + 3 ^ 40 * 528936 * 2
def baseEnd_528936 : Nat := 241420803081464683704421

theorem tailTrace_528936 : CollatzResearch.WordTrace tailWord_528936 prefixEnd_528936 241420803081464683704421 := by
  unfold tailWord_528936
  simp only [CollatzResearch.WordTrace]
  refine ⟨9645940405881340960983331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12861253874508454614644441 9645940405881340960983331)
  ·
    refine ⟨14468910608822011441474997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9645940405881340960983331 14468910608822011441474997)
    ·
      refine ⟨1356460369577063572638281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14468910608822011441474997 1356460369577063572638281)
      ·
        refine ⟨1017345277182797679478711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1356460369577063572638281 1017345277182797679478711)
        ·
          refine ⟨1526017915774196519218067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1017345277182797679478711 1526017915774196519218067)
          ·
            refine ⟨2289026873661294778827101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1526017915774196519218067 2289026873661294778827101)
            ·
              refine ⟨858385077622985542060163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2289026873661294778827101 858385077622985542060163)
              ·
                refine ⟨1287577616434478313090245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858385077622985542060163 1287577616434478313090245)
                ·
                  refine ⟨241420803081464683704421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1287577616434478313090245 241420803081464683704421)
                  ·
                    rfl

theorem cell20_528936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_528936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_528936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_528936 prefixEnd_528936 := by exact prefixLift 528936
  have htrace : WordTrace (prefixWord ++ tailWord_528936) baseStart_528936 baseEnd_528936 := by
    simpa [prefixWord, tailWord_528936, baseEnd_528936] using wordTrace_append hprefix tailTrace_528936
  have hstable : (prefixWord ++ tailWord_528936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528936).length < 2 ^ (prefixWord ++ tailWord_528936).sum := by decide
  have hdescent : baseEnd_528936 < baseStart_528936 := by decide
  rcases family_descends (prefixWord ++ tailWord_528936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529016 : List Nat := [2, 1, 2, 1, 1, 1, 2, 6, 4]
def baseStart_529016 : Nat := 118140960795 + 529016 * 2 ^ 59
def prefixEnd_529016 : Nat := 4983230072969 + 3 ^ 40 * 529016 * 2
def baseEnd_529016 : Nat := 241457317261339961037427

theorem tailTrace_529016 : CollatzResearch.WordTrace tailWord_529016 prefixEnd_529016 241457317261339961037427 := by
  unfold tailWord_529016
  simp only [CollatzResearch.WordTrace]
  refine ⟨9647399325736427792439451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12863199100981903723252601 9647399325736427792439451)
  ·
    refine ⟨14471098988604641688659177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9647399325736427792439451 14471098988604641688659177)
    ·
      refine ⟨10853324241453481266494383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14471098988604641688659177 10853324241453481266494383)
      ·
        refine ⟨16279986362180221899741575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10853324241453481266494383 16279986362180221899741575)
        ·
          refine ⟨24419979543270332849612363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16279986362180221899741575 24419979543270332849612363)
          ·
            refine ⟨36629969314905499274418545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24419979543270332849612363 36629969314905499274418545)
            ·
              refine ⟨27472476986179124455813909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36629969314905499274418545 27472476986179124455813909)
              ·
                refine ⟨1287772358727146458866277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27472476986179124455813909 1287772358727146458866277)
                ·
                  refine ⟨241457317261339961037427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1287772358727146458866277 241457317261339961037427)
                  ·
                    rfl

theorem cell20_529016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_529016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529016 prefixEnd_529016 := by exact prefixLift 529016
  have htrace : WordTrace (prefixWord ++ tailWord_529016) baseStart_529016 baseEnd_529016 := by
    simpa [prefixWord, tailWord_529016, baseEnd_529016] using wordTrace_append hprefix tailTrace_529016
  have hstable : (prefixWord ++ tailWord_529016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529016).length < 2 ^ (prefixWord ++ tailWord_529016).sum := by decide
  have hdescent : baseEnd_529016 < baseStart_529016 := by decide
  rcases family_descends (prefixWord ++ tailWord_529016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529047 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 5]
def baseStart_529047 : Nat := 118140960795 + 529047 * 2 ^ 59
def prefixEnd_529047 : Nat := 4983230072969 + 3 ^ 40 * 529047 * 2
def baseEnd_529047 : Nat := 241471466506041631003967

theorem tailTrace_529047 : CollatzResearch.WordTrace tailWord_529047 prefixEnd_529047 241471466506041631003967 := by
  unfold tailWord_529047
  simp only [CollatzResearch.WordTrace]
  refine ⟨19295929314360547879257395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12863952876240365252838263 19295929314360547879257395)
  ·
    refine ⟨28943893971540821818886093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19295929314360547879257395 28943893971540821818886093)
    ·
      refine ⟨10853960239327808182082285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28943893971540821818886093 10853960239327808182082285)
      ·
        refine ⟨4070235089747928068280857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10853960239327808182082285 4070235089747928068280857)
        ·
          refine ⟨3052676317310946051210643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4070235089747928068280857 3052676317310946051210643)
          ·
            refine ⟨4579014475966419076815965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3052676317310946051210643 4579014475966419076815965)
            ·
              refine ⟨1717130428487407153805987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4579014475966419076815965 1717130428487407153805987)
              ·
                refine ⟨2575695642731110730708981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1717130428487407153805987 2575695642731110730708981)
                ·
                  refine ⟨241471466506041631003967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2575695642731110730708981 241471466506041631003967)
                  ·
                    rfl

theorem cell20_529047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 5].length) (baseStart_529047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529047 prefixEnd_529047 := by exact prefixLift 529047
  have htrace : WordTrace (prefixWord ++ tailWord_529047) baseStart_529047 baseEnd_529047 := by
    simpa [prefixWord, tailWord_529047, baseEnd_529047] using wordTrace_append hprefix tailTrace_529047
  have hstable : (prefixWord ++ tailWord_529047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529047).length < 2 ^ (prefixWord ++ tailWord_529047).sum := by decide
  have hdescent : baseEnd_529047 < baseStart_529047 := by decide
  rcases family_descends (prefixWord ++ tailWord_529047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529061 : List Nat := [1, 3, 1, 2, 1, 2, 1, 9]
def baseStart_529061 : Nat := 118140960795 + 529061 * 2 ^ 59
def prefixEnd_529061 : Nat := 4983230072969 + 3 ^ 40 * 529061 * 2
def baseEnd_529061 : Nat := 80492618829173268179081

theorem tailTrace_529061 : CollatzResearch.WordTrace tailWord_529061 prefixEnd_529061 80492618829173268179081 := by
  unfold tailWord_529061
  simp only [CollatzResearch.WordTrace]
  refine ⟨19296439936309828270267037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12864293290873218846844691 19296439936309828270267037)
  ·
    refine ⟨7236164976116185601350139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19296439936309828270267037 7236164976116185601350139)
    ·
      refine ⟨10854247464174278402025209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7236164976116185601350139 10854247464174278402025209)
      ·
        refine ⟨8140685598130708801518907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10854247464174278402025209 8140685598130708801518907)
        ·
          refine ⟨12211028397196063202278361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8140685598130708801518907 12211028397196063202278361)
          ·
            refine ⟨9158271297897047401708771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12211028397196063202278361 9158271297897047401708771)
            ·
              refine ⟨13737406946845571102563157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9158271297897047401708771 13737406946845571102563157)
              ·
                refine ⟨80492618829173268179081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13737406946845571102563157 80492618829173268179081)
                ·
                  rfl

theorem cell20_529061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 9].length) (baseStart_529061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529061 prefixEnd_529061 := by exact prefixLift 529061
  have htrace : WordTrace (prefixWord ++ tailWord_529061) baseStart_529061 baseEnd_529061 := by
    simpa [prefixWord, tailWord_529061, baseEnd_529061] using wordTrace_append hprefix tailTrace_529061
  have hstable : (prefixWord ++ tailWord_529061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529061).length < 2 ^ (prefixWord ++ tailWord_529061).sum := by decide
  have hdescent : baseEnd_529061 < baseStart_529061 := by decide
  rcases family_descends (prefixWord ++ tailWord_529061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529085 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 5]
def baseStart_529085 : Nat := 118140960795 + 529085 * 2 ^ 59
def prefixEnd_529085 : Nat := 4983230072969 + 3 ^ 40 * 529085 * 2
def baseEnd_529085 : Nat := 241488810741482387737145

theorem tailTrace_529085 : CollatzResearch.WordTrace tailWord_529085 prefixEnd_529085 241488810741482387737145 := by
  unfold tailWord_529085
  simp only [CollatzResearch.WordTrace]
  refine ⟨19297315288222880369140709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12864876858815253579427139 19297315288222880369140709)
  ·
    refine ⟨3618246616541790069213883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19297315288222880369140709 3618246616541790069213883)
    ·
      refine ⟨5427369924812685103820825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3618246616541790069213883 5427369924812685103820825)
      ·
        refine ⟨4070527443609513827865619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5427369924812685103820825 4070527443609513827865619)
        ·
          refine ⟨6105791165414270741798429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4070527443609513827865619 6105791165414270741798429)
          ·
            refine ⟨2289671687030351528174411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6105791165414270741798429 2289671687030351528174411)
            ·
              refine ⟨3434507530545527292261617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2289671687030351528174411 3434507530545527292261617)
              ·
                refine ⟨2575880647909145469196213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3434507530545527292261617 2575880647909145469196213)
                ·
                  refine ⟨241488810741482387737145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2575880647909145469196213 241488810741482387737145)
                  ·
                    rfl

theorem cell20_529085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_529085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529085 prefixEnd_529085 := by exact prefixLift 529085
  have htrace : WordTrace (prefixWord ++ tailWord_529085) baseStart_529085 baseEnd_529085 := by
    simpa [prefixWord, tailWord_529085, baseEnd_529085] using wordTrace_append hprefix tailTrace_529085
  have hstable : (prefixWord ++ tailWord_529085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529085).length < 2 ^ (prefixWord ++ tailWord_529085).sum := by decide
  have hdescent : baseEnd_529085 < baseStart_529085 := by decide
  rcases family_descends (prefixWord ++ tailWord_529085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529088 : List Nat := [2, 1, 1, 2, 4, 2, 3, 3, 2]
def baseStart_529088 : Nat := 118140960795 + 529088 * 2 ^ 59
def prefixEnd_529088 : Nat := 4983230072969 + 3 ^ 40 * 529088 * 2
def baseEnd_529088 : Nat := 241490180023227710637133

theorem tailTrace_529088 : CollatzResearch.WordTrace tailWord_529088 prefixEnd_529088 241490180023227710637133 := by
  unfold tailWord_529088
  simp only [CollatzResearch.WordTrace]
  refine ⟨9648712353606005940749959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12864949804808007920999945 9648712353606005940749959)
  ·
    refine ⟨14473068530409008911124939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9648712353606005940749959 14473068530409008911124939)
    ·
      refine ⟨21709602795613513366687409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14473068530409008911124939 21709602795613513366687409)
      ·
        refine ⟨16282202096710135025015557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21709602795613513366687409 16282202096710135025015557)
        ·
          refine ⟨3052912893133150317190417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16282202096710135025015557 3052912893133150317190417)
          ·
            refine ⟨2289684669849862737892813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3052912893133150317190417 2289684669849862737892813)
            ·
              refine ⟨858631751193698526709805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2289684669849862737892813 858631751193698526709805)
              ·
                refine ⟨321986906697636947516177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 858631751193698526709805 321986906697636947516177)
                ·
                  refine ⟨241490180023227710637133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321986906697636947516177 241490180023227710637133)
                  ·
                    rfl

theorem cell20_529088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 2].length) (baseStart_529088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529088 prefixEnd_529088 := by exact prefixLift 529088
  have htrace : WordTrace (prefixWord ++ tailWord_529088) baseStart_529088 baseEnd_529088 := by
    simpa [prefixWord, tailWord_529088, baseEnd_529088] using wordTrace_append hprefix tailTrace_529088
  have hstable : (prefixWord ++ tailWord_529088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529088).length < 2 ^ (prefixWord ++ tailWord_529088).sum := by decide
  have hdescent : baseEnd_529088 < baseStart_529088 := by decide
  rcases family_descends (prefixWord ++ tailWord_529088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529101 : List Nat := [1, 6, 2, 1, 2, 1, 3, 2, 2]
def baseStart_529101 : Nat := 118140960795 + 529101 * 2 ^ 59
def prefixEnd_529101 : Nat := 4983230072969 + 3 ^ 40 * 529101 * 2
def baseEnd_529101 : Nat := 241496113577457443203747

theorem tailTrace_529101 : CollatzResearch.WordTrace tailWord_529101 prefixEnd_529101 241496113577457443203747 := by
  unfold tailWord_529101
  simp only [CollatzResearch.WordTrace]
  refine ⟨19297898856164915101723157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12865265904109943401148771 19297898856164915101723157)
  ·
    refine ⟨904589008882730395393273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19297898856164915101723157 904589008882730395393273)
    ·
      refine ⟨678441756662047796544955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 904589008882730395393273 678441756662047796544955)
      ·
        refine ⟨1017662634993071694817433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678441756662047796544955 1017662634993071694817433)
        ·
          refine ⟨763246976244803771113075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1017662634993071694817433 763246976244803771113075)
          ·
            refine ⟨1144870464367205656669613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763246976244803771113075 1144870464367205656669613)
            ·
              refine ⟨429326424137702121251105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1144870464367205656669613 429326424137702121251105)
              ·
                refine ⟨321994818103276590938329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429326424137702121251105 321994818103276590938329)
                ·
                  refine ⟨241496113577457443203747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321994818103276590938329 241496113577457443203747)
                  ·
                    rfl

theorem cell20_529101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_529101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529101 prefixEnd_529101 := by exact prefixLift 529101
  have htrace : WordTrace (prefixWord ++ tailWord_529101) baseStart_529101 baseEnd_529101 := by
    simpa [prefixWord, tailWord_529101, baseEnd_529101] using wordTrace_append hprefix tailTrace_529101
  have hstable : (prefixWord ++ tailWord_529101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529101).length < 2 ^ (prefixWord ++ tailWord_529101).sum := by decide
  have hdescent : baseEnd_529101 < baseStart_529101 := by decide
  rcases family_descends (prefixWord ++ tailWord_529101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529119 : List Nat := [1, 1, 2, 3, 2, 5, 2, 1, 3]
def baseStart_529119 : Nat := 118140960795 + 529119 * 2 ^ 59
def prefixEnd_529119 : Nat := 4983230072969 + 3 ^ 40 * 529119 * 2
def baseEnd_529119 : Nat := 241504329267929380603673

theorem tailTrace_529119 : CollatzResearch.WordTrace tailWord_529119 prefixEnd_529119 241504329267929380603673 := by
  unfold tailWord_529119
  simp only [CollatzResearch.WordTrace]
  refine ⟨19298555370099704175878411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12865703580066469450585607 19298555370099704175878411)
  ·
    refine ⟨28947833055149556263817617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19298555370099704175878411 28947833055149556263817617)
    ·
      refine ⟨21710874791362167197863213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28947833055149556263817617 21710874791362167197863213)
      ·
        refine ⟨8141578046760812699198705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21710874791362167197863213 8141578046760812699198705)
        ·
          refine ⟨6106183535070609524399029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8141578046760812699198705 6106183535070609524399029)
          ·
            refine ⟨572454706412869642912409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6106183535070609524399029 572454706412869642912409)
            ·
              refine ⟨429341029809652232184307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572454706412869642912409 429341029809652232184307)
              ·
                refine ⟨644011544714478348276461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429341029809652232184307 644011544714478348276461)
                ·
                  refine ⟨241504329267929380603673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644011544714478348276461 241504329267929380603673)
                  ·
                    rfl

theorem cell20_529119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 3].length) (baseStart_529119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529119 prefixEnd_529119 := by exact prefixLift 529119
  have htrace : WordTrace (prefixWord ++ tailWord_529119) baseStart_529119 baseEnd_529119 := by
    simpa [prefixWord, tailWord_529119, baseEnd_529119] using wordTrace_append hprefix tailTrace_529119
  have hstable : (prefixWord ++ tailWord_529119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529119).length < 2 ^ (prefixWord ++ tailWord_529119).sum := by decide
  have hdescent : baseEnd_529119 < baseStart_529119 := by decide
  rcases family_descends (prefixWord ++ tailWord_529119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529130 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_529130 : Nat := 118140960795 + 529130 * 2 ^ 59
def prefixEnd_529130 : Nat := 4983230072969 + 3 ^ 40 * 529130 * 2
def baseEnd_529130 : Nat := 241509349967662231236961

theorem tailTrace_529130 : CollatzResearch.WordTrace tailWord_529130 prefixEnd_529130 241509349967662231236961 := by
  unfold tailWord_529130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4824739143264963263632211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12865971048706568703019229 4824739143264963263632211)
  ·
    refine ⟨7237108714897444895448317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4824739143264963263632211 7237108714897444895448317)
    ·
      refine ⟨2713915768086541835793119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7237108714897444895448317 2713915768086541835793119)
      ·
        refine ⟨4070873652129812753689679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2713915768086541835793119 4070873652129812753689679)
        ·
          refine ⟨6106310478194719130534519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4070873652129812753689679 6106310478194719130534519)
          ·
            refine ⟨9159465717292078695801779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6106310478194719130534519 9159465717292078695801779)
            ·
              refine ⟨13739198575938118043702669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9159465717292078695801779 13739198575938118043702669)
              ·
                refine ⟨5152199465976794266388501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13739198575938118043702669 5152199465976794266388501)
                ·
                  refine ⟨241509349967662231236961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5152199465976794266388501 241509349967662231236961)
                  ·
                    rfl

theorem cell20_529130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_529130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529130 prefixEnd_529130 := by exact prefixLift 529130
  have htrace : WordTrace (prefixWord ++ tailWord_529130) baseStart_529130 baseEnd_529130 := by
    simpa [prefixWord, tailWord_529130, baseEnd_529130] using wordTrace_append hprefix tailTrace_529130
  have hstable : (prefixWord ++ tailWord_529130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529130).length < 2 ^ (prefixWord ++ tailWord_529130).sum := by decide
  have hdescent : baseEnd_529130 < baseStart_529130 := by decide
  rcases family_descends (prefixWord ++ tailWord_529130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529137 : List Nat := [1, 2, 2, 2, 2, 2, 1, 8]
def baseStart_529137 : Nat := 118140960795 + 529137 * 2 ^ 59
def prefixEnd_529137 : Nat := 4983230072969 + 3 ^ 40 * 529137 * 2
def baseEnd_529137 : Nat := 80504181652800439334533

theorem tailTrace_529137 : CollatzResearch.WordTrace tailWord_529137 prefixEnd_529137 80504181652800439334533 := by
  unfold tailWord_529137
  simp only [CollatzResearch.WordTrace]
  refine ⟨19299211884034493250033665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12866141256022995500022443 19299211884034493250033665)
  ·
    refine ⟨14474408913025869937525249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19299211884034493250033665 14474408913025869937525249)
    ·
      refine ⟨10855806684769402453143937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14474408913025869937525249 10855806684769402453143937)
      ·
        refine ⟨8141855013577051839857953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10855806684769402453143937 8141855013577051839857953)
        ·
          refine ⟨6106391260182788879893465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8141855013577051839857953 6106391260182788879893465)
          ·
            refine ⟨4579793445137091659920099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6106391260182788879893465 4579793445137091659920099)
            ·
              refine ⟨6869690167705637489880149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4579793445137091659920099 6869690167705637489880149)
              ·
                refine ⟨80504181652800439334533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6869690167705637489880149 80504181652800439334533)
                ·
                  rfl

theorem cell20_529137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 8].length) (baseStart_529137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529137 prefixEnd_529137 := by exact prefixLift 529137
  have htrace : WordTrace (prefixWord ++ tailWord_529137) baseStart_529137 baseEnd_529137 := by
    simpa [prefixWord, tailWord_529137, baseEnd_529137] using wordTrace_append hprefix tailTrace_529137
  have hstable : (prefixWord ++ tailWord_529137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529137).length < 2 ^ (prefixWord ++ tailWord_529137).sum := by decide
  have hdescent : baseEnd_529137 < baseStart_529137 := by decide
  rcases family_descends (prefixWord ++ tailWord_529137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529154 : List Nat := [3, 4, 1, 1, 1, 10]
def baseStart_529154 : Nat := 118140960795 + 529154 * 2 ^ 59
def prefixEnd_529154 : Nat := 4983230072969 + 3 ^ 40 * 529154 * 2
def baseEnd_529154 : Nat := 8945196452652770905069

theorem tailTrace_529154 : CollatzResearch.WordTrace tailWord_529154 prefixEnd_529154 8945196452652770905069 := by
  unfold tailWord_529154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4824957981243226288350629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12866554616648603435601677 4824957981243226288350629)
  ·
    refine ⟨904679621483104929065743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4824957981243226288350629 904679621483104929065743)
    ·
      refine ⟨1357019432224657393598615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 904679621483104929065743 1357019432224657393598615)
      ·
        refine ⟨2035529148336986090397923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1357019432224657393598615 2035529148336986090397923)
        ·
          refine ⟨3053293722505479135596885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2035529148336986090397923 3053293722505479135596885)
          ·
            refine ⟨8945196452652770905069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3053293722505479135596885 8945196452652770905069)
            ·
              rfl

theorem cell20_529154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 10].length) (baseStart_529154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529154 prefixEnd_529154 := by exact prefixLift 529154
  have htrace : WordTrace (prefixWord ++ tailWord_529154) baseStart_529154 baseEnd_529154 := by
    simpa [prefixWord, tailWord_529154, baseEnd_529154] using wordTrace_append hprefix tailTrace_529154
  have hstable : (prefixWord ++ tailWord_529154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529154).length < 2 ^ (prefixWord ++ tailWord_529154).sum := by decide
  have hdescent : baseEnd_529154 < baseStart_529154 := by decide
  rcases family_descends (prefixWord ++ tailWord_529154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529161 : List Nat := [1, 2, 1, 1, 3, 2, 3, 4, 3]
def baseStart_529161 : Nat := 118140960795 + 529161 * 2 ^ 59
def prefixEnd_529161 : Nat := 4983230072969 + 3 ^ 40 * 529161 * 2
def baseEnd_529161 : Nat := 241523499212363901203501

theorem tailTrace_529161 : CollatzResearch.WordTrace tailWord_529161 prefixEnd_529161 241523499212363901203501 := by
  unfold tailWord_529161
  simp only [CollatzResearch.WordTrace]
  refine ⟨19300087235947545348907337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12866724823965030232604891 19300087235947545348907337)
  ·
    refine ⟨14475065426960659011680503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19300087235947545348907337 14475065426960659011680503)
    ·
      refine ⟨21712598140440988517520755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14475065426960659011680503 21712598140440988517520755)
      ·
        refine ⟨32568897210661482776281133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21712598140440988517520755 32568897210661482776281133)
        ·
          refine ⟨12213336453998056041105425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32568897210661482776281133 12213336453998056041105425)
          ·
            refine ⟨9160002340498542030829069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12213336453998056041105425 9160002340498542030829069)
            ·
              refine ⟨3435000877686953261560901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9160002340498542030829069 3435000877686953261560901)
              ·
                refine ⟨644062664566303736542669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3435000877686953261560901 644062664566303736542669)
                ·
                  refine ⟨241523499212363901203501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644062664566303736542669 241523499212363901203501)
                  ·
                    rfl

theorem cell20_529161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_529161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529161 prefixEnd_529161 := by exact prefixLift 529161
  have htrace : WordTrace (prefixWord ++ tailWord_529161) baseStart_529161 baseEnd_529161 := by
    simpa [prefixWord, tailWord_529161, baseEnd_529161] using wordTrace_append hprefix tailTrace_529161
  have hstable : (prefixWord ++ tailWord_529161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529161).length < 2 ^ (prefixWord ++ tailWord_529161).sum := by decide
  have hdescent : baseEnd_529161 < baseStart_529161 := by decide
  rcases family_descends (prefixWord ++ tailWord_529161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529202 : List Nat := [3, 2, 1, 1, 3, 1, 4, 3, 2]
def baseStart_529202 : Nat := 118140960795 + 529202 * 2 ^ 59
def prefixEnd_529202 : Nat := 4983230072969 + 3 ^ 40 * 529202 * 2
def baseEnd_529202 : Nat := 241542212729549980836667

theorem tailTrace_529202 : CollatzResearch.WordTrace tailWord_529202 prefixEnd_529202 241542212729549980836667 := by
  unfold tailWord_529202
  simp only [CollatzResearch.WordTrace]
  refine ⟨4825395657199752337787465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12867721752532672900766573 4825395657199752337787465)
  ·
    refine ⟨3619046742899814253340599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4825395657199752337787465 3619046742899814253340599)
    ·
      refine ⟨5428570114349721380010899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3619046742899814253340599 5428570114349721380010899)
      ·
        refine ⟨8142855171524582070016349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5428570114349721380010899 8142855171524582070016349)
        ·
          refine ⟨3053570689321718276256131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8142855171524582070016349 3053570689321718276256131)
          ·
            refine ⟨4580356033982577414384197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3053570689321718276256131 4580356033982577414384197)
            ·
              refine ⟨858816756371733265197037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4580356033982577414384197 858816756371733265197037)
              ·
                refine ⟨322056283639399974448889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 858816756371733265197037 322056283639399974448889)
                ·
                  refine ⟨241542212729549980836667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322056283639399974448889 241542212729549980836667)
                  ·
                    rfl

theorem cell20_529202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_529202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529202 prefixEnd_529202 := by exact prefixLift 529202
  have htrace : WordTrace (prefixWord ++ tailWord_529202) baseStart_529202 baseEnd_529202 := by
    simpa [prefixWord, tailWord_529202, baseEnd_529202] using wordTrace_append hprefix tailTrace_529202
  have hstable : (prefixWord ++ tailWord_529202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529202).length < 2 ^ (prefixWord ++ tailWord_529202).sum := by decide
  have hdescent : baseEnd_529202 < baseStart_529202 := by decide
  rcases family_descends (prefixWord ++ tailWord_529202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529233 : List Nat := [1, 2, 2, 1, 6, 1, 3, 1, 3]
def baseStart_529233 : Nat := 118140960795 + 529233 * 2 ^ 59
def prefixEnd_529233 : Nat := 4983230072969 + 3 ^ 40 * 529233 * 2
def baseEnd_529233 : Nat := 241556361974251650803207

theorem tailTrace_529233 : CollatzResearch.WordTrace tailWord_529233 prefixEnd_529233 241556361974251650803207 := by
  unfold tailWord_529233
  simp only [CollatzResearch.WordTrace]
  refine ⟨19302713291686701645528353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12868475527791134430352235 19302713291686701645528353)
  ·
    refine ⟨14477034968765026234146265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19302713291686701645528353 14477034968765026234146265)
    ·
      refine ⟨10857776226573769675609699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14477034968765026234146265 10857776226573769675609699)
      ·
        refine ⟨16286664339860654513414549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10857776226573769675609699 16286664339860654513414549)
        ·
          refine ⟨763437390930968180316307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16286664339860654513414549 763437390930968180316307)
          ·
            refine ⟨1145156086396452270474461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763437390930968180316307 1145156086396452270474461)
            ·
              refine ⟨429433532398669601427923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1145156086396452270474461 429433532398669601427923)
              ·
                refine ⟨644150298598004402141885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429433532398669601427923 644150298598004402141885)
                ·
                  refine ⟨241556361974251650803207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644150298598004402141885 241556361974251650803207)
                  ·
                    rfl

theorem cell20_529233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 3].length) (baseStart_529233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529233 prefixEnd_529233 := by exact prefixLift 529233
  have htrace : WordTrace (prefixWord ++ tailWord_529233) baseStart_529233 baseEnd_529233 := by
    simpa [prefixWord, tailWord_529233, baseEnd_529233] using wordTrace_append hprefix tailTrace_529233
  have hstable : (prefixWord ++ tailWord_529233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529233).length < 2 ^ (prefixWord ++ tailWord_529233).sum := by decide
  have hdescent : baseEnd_529233 < baseStart_529233 := by decide
  rcases family_descends (prefixWord ++ tailWord_529233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529289 : List Nat := [1, 2, 1, 1, 5, 2, 1, 7]
def baseStart_529289 : Nat := 118140960795 + 529289 * 2 ^ 59
def prefixEnd_529289 : Nat := 4983230072969 + 3 ^ 40 * 529289 * 2
def baseEnd_529289 : Nat := 80527307300054781645437

theorem tailTrace_529289 : CollatzResearch.WordTrace tailWord_529289 prefixEnd_529289 80527307300054781645437 := by
  unfold tailWord_529289
  simp only [CollatzResearch.WordTrace]
  refine ⟨19304755779483823209566921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12869837186322548806377947 19304755779483823209566921)
  ·
    refine ⟨14478566834612867407175191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19304755779483823209566921 14478566834612867407175191)
    ·
      refine ⟨21717850251919301110762787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14478566834612867407175191 21717850251919301110762787)
      ·
        refine ⟨32576775377878951666144181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21717850251919301110762787 32576775377878951666144181)
        ·
          refine ⟨3054072691676151718701017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32576775377878951666144181 3054072691676151718701017)
          ·
            refine ⟨2290554518757113789025763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3054072691676151718701017 2290554518757113789025763)
            ·
              refine ⟨3435831778135670683538645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2290554518757113789025763 3435831778135670683538645)
              ·
                refine ⟨80527307300054781645437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3435831778135670683538645 80527307300054781645437)
                ·
                  rfl

theorem cell20_529289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 7].length) (baseStart_529289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529289 prefixEnd_529289 := by exact prefixLift 529289
  have htrace : WordTrace (prefixWord ++ tailWord_529289) baseStart_529289 baseEnd_529289 := by
    simpa [prefixWord, tailWord_529289, baseEnd_529289] using wordTrace_append hprefix tailTrace_529289
  have hstable : (prefixWord ++ tailWord_529289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529289).length < 2 ^ (prefixWord ++ tailWord_529289).sum := by decide
  have hdescent : baseEnd_529289 < baseStart_529289 := by decide
  rcases family_descends (prefixWord ++ tailWord_529289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529292 : List Nat := [2, 2, 1, 2, 1, 2, 6, 1, 3]
def baseStart_529292 : Nat := 118140960795 + 529292 * 2 ^ 59
def prefixEnd_529292 : Nat := 4983230072969 + 3 ^ 40 * 529292 * 2
def baseEnd_529292 : Nat := 241583291181909667836299

theorem tailTrace_529292 : CollatzResearch.WordTrace tailWord_529292 prefixEnd_529292 241583291181909667836299 := by
  unfold tailWord_529292
  simp only [CollatzResearch.WordTrace]
  refine ⟨9652432599236477360963065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12869910132315303147950753 9652432599236477360963065)
  ·
    refine ⟨7239324449427358020722299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9652432599236477360963065 7239324449427358020722299)
    ·
      refine ⟨10858986674141037031083449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7239324449427358020722299 10858986674141037031083449)
      ·
        refine ⟨8144240005605777773312587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10858986674141037031083449 8144240005605777773312587)
        ·
          refine ⟨12216360008408666659968881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8144240005605777773312587 12216360008408666659968881)
          ·
            refine ⟨9162270006306499994976661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12216360008408666659968881 9162270006306499994976661)
            ·
              refine ⟨429481406545617187264531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9162270006306499994976661 429481406545617187264531)
              ·
                refine ⟨644222109818425780896797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429481406545617187264531 644222109818425780896797)
                ·
                  refine ⟨241583291181909667836299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644222109818425780896797 241583291181909667836299)
                  ·
                    rfl

theorem cell20_529292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_529292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529292 prefixEnd_529292 := by exact prefixLift 529292
  have htrace : WordTrace (prefixWord ++ tailWord_529292) baseStart_529292 baseEnd_529292 := by
    simpa [prefixWord, tailWord_529292, baseEnd_529292] using wordTrace_append hprefix tailTrace_529292
  have hstable : (prefixWord ++ tailWord_529292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529292).length < 2 ^ (prefixWord ++ tailWord_529292).sum := by decide
  have hdescent : baseEnd_529292 < baseStart_529292 := by decide
  rcases family_descends (prefixWord ++ tailWord_529292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529302 : List Nat := [5, 3, 1, 1, 1, 1, 2, 6]
def baseStart_529302 : Nat := 118140960795 + 529302 * 2 ^ 59
def prefixEnd_529302 : Nat := 4983230072969 + 3 ^ 40 * 529302 * 2
def baseEnd_529302 : Nat := 80529285151464692500975

theorem tailTrace_529302 : CollatzResearch.WordTrace tailWord_529302 prefixEnd_529302 80529285151464692500975 := by
  unfold tailWord_529302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1206576870527295401861885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12870153285624484286526773 1206576870527295401861885)
  ·
    refine ⟨452466326447735775698207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1206576870527295401861885 452466326447735775698207)
    ·
      refine ⟨678699489671603663547311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452466326447735775698207 678699489671603663547311)
      ·
        refine ⟨1018049234507405495320967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678699489671603663547311 1018049234507405495320967)
        ·
          refine ⟨1527073851761108242981451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1018049234507405495320967 1527073851761108242981451)
          ·
            refine ⟨2290610777641662364472177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527073851761108242981451 2290610777641662364472177)
            ·
              refine ⟨1717958083231246773354133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2290610777641662364472177 1717958083231246773354133)
              ·
                refine ⟨80529285151464692500975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1717958083231246773354133 80529285151464692500975)
                ·
                  rfl

theorem cell20_529302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_529302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529302 prefixEnd_529302 := by exact prefixLift 529302
  have htrace : WordTrace (prefixWord ++ tailWord_529302) baseStart_529302 baseEnd_529302 := by
    simpa [prefixWord, tailWord_529302, baseEnd_529302] using wordTrace_append hprefix tailTrace_529302
  have hstable : (prefixWord ++ tailWord_529302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529302).length < 2 ^ (prefixWord ++ tailWord_529302).sum := by decide
  have hdescent : baseEnd_529302 < baseStart_529302 := by decide
  rcases family_descends (prefixWord ++ tailWord_529302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529344 : List Nat := [2, 1, 1, 2, 3, 5, 1, 5]
def baseStart_529344 : Nat := 118140960795 + 529344 * 2 ^ 59
def prefixEnd_529344 : Nat := 4983230072969 + 3 ^ 40 * 529344 * 2
def baseEnd_529344 : Nat := 80535675132942866034251

theorem tailTrace_529344 : CollatzResearch.WordTrace tailWord_529344 prefixEnd_529344 80535675132942866034251 := by
  unfold tailWord_529344
  simp only [CollatzResearch.WordTrace]
  refine ⟨9653380897142283801409543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12871174529523045068546057 9653380897142283801409543)
  ·
    refine ⟨14480071345713425702114315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9653380897142283801409543 14480071345713425702114315)
    ·
      refine ⟨21720107018570138553171473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14480071345713425702114315 21720107018570138553171473)
      ·
        refine ⟨16290080263927603914878605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21720107018570138553171473 16290080263927603914878605)
        ·
          refine ⟨6108780098972851468079477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16290080263927603914878605 6108780098972851468079477)
          ·
            refine ⟨572698134278704825132451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6108780098972851468079477 572698134278704825132451)
            ·
              refine ⟨859047201418057237698677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572698134278704825132451 859047201418057237698677)
              ·
                refine ⟨80535675132942866034251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 859047201418057237698677 80535675132942866034251)
                ·
                  rfl

theorem cell20_529344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 5].length) (baseStart_529344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529344 prefixEnd_529344 := by exact prefixLift 529344
  have htrace : WordTrace (prefixWord ++ tailWord_529344) baseStart_529344 baseEnd_529344 := by
    simpa [prefixWord, tailWord_529344, baseEnd_529344] using wordTrace_append hprefix tailTrace_529344
  have hstable : (prefixWord ++ tailWord_529344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529344).length < 2 ^ (prefixWord ++ tailWord_529344).sum := by decide
  have hdescent : baseEnd_529344 < baseStart_529344 := by decide
  rcases family_descends (prefixWord ++ tailWord_529344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529351 : List Nat := [1, 1, 4, 1, 1, 2, 4, 3, 3]
def baseStart_529351 : Nat := 118140960795 + 529351 * 2 ^ 59
def prefixEnd_529351 : Nat := 4983230072969 + 3 ^ 40 * 529351 * 2
def baseEnd_529351 : Nat := 241610220389567684869391

theorem tailTrace_529351 : CollatzResearch.WordTrace tailWord_529351 prefixEnd_529351 241610220389567684869391 := by
  unfold tailWord_529351
  simp only [CollatzResearch.WordTrace]
  refine ⟨19307017105259207798323907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12871344736839471865549271 19307017105259207798323907)
  ·
    refine ⟨28960525657888811697485861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19307017105259207798323907 28960525657888811697485861)
    ·
      refine ⟨5430098560854152193278599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28960525657888811697485861 5430098560854152193278599)
      ·
        refine ⟨8145147841281228289917899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5430098560854152193278599 8145147841281228289917899)
        ·
          refine ⟨12217721761921842434876849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8145147841281228289917899 12217721761921842434876849)
          ·
            refine ⟨9163291321441381826157637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12217721761921842434876849 9163291321441381826157637)
            ·
              refine ⟨1718117122770259092404557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9163291321441381826157637 1718117122770259092404557)
              ·
                refine ⟨644293921038847159651709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1718117122770259092404557 644293921038847159651709)
                ·
                  refine ⟨241610220389567684869391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644293921038847159651709 241610220389567684869391)
                  ·
                    rfl

theorem cell20_529351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 3].length) (baseStart_529351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529351 prefixEnd_529351 := by exact prefixLift 529351
  have htrace : WordTrace (prefixWord ++ tailWord_529351) baseStart_529351 baseEnd_529351 := by
    simpa [prefixWord, tailWord_529351, baseEnd_529351] using wordTrace_append hprefix tailTrace_529351
  have hstable : (prefixWord ++ tailWord_529351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529351).length < 2 ^ (prefixWord ++ tailWord_529351).sum := by decide
  have hdescent : baseEnd_529351 < baseStart_529351 := by decide
  rcases family_descends (prefixWord ++ tailWord_529351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529358 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_529358 : Nat := 118140960795 + 529358 * 2 ^ 59
def prefixEnd_529358 : Nat := 4983230072969 + 3 ^ 40 * 529358 * 2
def baseEnd_529358 : Nat := 241613415380306771636029

theorem tailTrace_529358 : CollatzResearch.WordTrace tailWord_529358 prefixEnd_529358 241613415380306771636029 := by
  unfold tailWord_529358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2413409052029230999228591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12871514944155898662552485 2413409052029230999228591)
  ·
    refine ⟨3620113578043846498842887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2413409052029230999228591 3620113578043846498842887)
    ·
      refine ⟨5430170367065769748264331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3620113578043846498842887 5430170367065769748264331)
      ·
        refine ⟨8145255550598654622396497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5430170367065769748264331 8145255550598654622396497)
        ·
          refine ⟨6108941662948990966797373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8145255550598654622396497 6108941662948990966797373)
          ·
            refine ⟨2290853123605871612549015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6108941662948990966797373 2290853123605871612549015)
            ·
              refine ⟨3436279685408807418823523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2290853123605871612549015 3436279685408807418823523)
              ·
                refine ⟨5154419528113211128235285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3436279685408807418823523 5154419528113211128235285)
                ·
                  refine ⟨241613415380306771636029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5154419528113211128235285 241613415380306771636029)
                  ·
                    rfl

theorem cell20_529358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_529358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529358 prefixEnd_529358 := by exact prefixLift 529358
  have htrace : WordTrace (prefixWord ++ tailWord_529358) baseStart_529358 baseEnd_529358 := by
    simpa [prefixWord, tailWord_529358, baseEnd_529358] using wordTrace_append hprefix tailTrace_529358
  have hstable : (prefixWord ++ tailWord_529358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529358).length < 2 ^ (prefixWord ++ tailWord_529358).sum := by decide
  have hdescent : baseEnd_529358 < baseStart_529358 := by decide
  rcases family_descends (prefixWord ++ tailWord_529358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529420 : List Nat := [2, 2, 1, 2, 3, 2, 4, 4]
def baseStart_529420 : Nat := 118140960795 + 529420 * 2 ^ 59
def prefixEnd_529420 : Nat := 4983230072969 + 3 ^ 40 * 529420 * 2
def baseEnd_529420 : Nat := 80547237956570037189703

theorem tailTrace_529420 : CollatzResearch.WordTrace tailWord_529420 prefixEnd_529420 80547237956570037189703 := by
  unfold tailWord_529420
  simp only [CollatzResearch.WordTrace]
  refine ⟨9654766871004616291292857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12873022494672821721723809 9654766871004616291292857)
  ·
    refine ⟨7241075153253462218469643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9654766871004616291292857 7241075153253462218469643)
    ·
      refine ⟨10861612729880193327704465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7241075153253462218469643 10861612729880193327704465)
      ·
        refine ⟨8146209547410144995778349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10861612729880193327704465 8146209547410144995778349)
        ·
          refine ⟨3054828580278804373416881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8146209547410144995778349 3054828580278804373416881)
          ·
            refine ⟨2291121435209103280062661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3054828580278804373416881 2291121435209103280062661)
            ·
              refine ⟨429585269101706865011749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2291121435209103280062661 429585269101706865011749)
              ·
                refine ⟨80547237956570037189703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 429585269101706865011749 80547237956570037189703)
                ·
                  rfl

theorem cell20_529420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 4].length) (baseStart_529420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529420 prefixEnd_529420 := by exact prefixLift 529420
  have htrace : WordTrace (prefixWord ++ tailWord_529420) baseStart_529420 baseEnd_529420 := by
    simpa [prefixWord, tailWord_529420, baseEnd_529420] using wordTrace_append hprefix tailTrace_529420
  have hstable : (prefixWord ++ tailWord_529420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529420).length < 2 ^ (prefixWord ++ tailWord_529420).sum := by decide
  have hdescent : baseEnd_529420 < baseStart_529420 := by decide
  rcases family_descends (prefixWord ++ tailWord_529420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529437 : List Nat := [1, 4, 2, 2, 4, 1, 6]
def baseStart_529437 : Nat := 118140960795 + 529437 * 2 ^ 59
def prefixEnd_529437 : Nat := 4983230072969 + 3 ^ 40 * 529437 * 2
def baseEnd_529437 : Nat := 26849941459214845333597

theorem tailTrace_529437 : CollatzResearch.WordTrace tailWord_529437 prefixEnd_529437 26849941459214845333597 := by
  unfold tailWord_529437
  simp only [CollatzResearch.WordTrace]
  refine ⟨19310153782947644485954565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12873435855298429657303043 19310153782947644485954565)
  ·
    refine ⟨3620653834302683341116481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19310153782947644485954565 3620653834302683341116481)
    ·
      refine ⟨2715490375727012505837361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3620653834302683341116481 2715490375727012505837361)
      ·
        refine ⟨2036617781795259379378021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2715490375727012505837361 2036617781795259379378021)
        ·
          refine ⟨381865834086611133633379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2036617781795259379378021 381865834086611133633379)
          ·
            refine ⟨572798751129916700450069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381865834086611133633379 572798751129916700450069)
            ·
              refine ⟨26849941459214845333597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 572798751129916700450069 26849941459214845333597)
              ·
                rfl

theorem cell20_529437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 6].length) (baseStart_529437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529437 prefixEnd_529437 := by exact prefixLift 529437
  have htrace : WordTrace (prefixWord ++ tailWord_529437) baseStart_529437 baseEnd_529437 := by
    simpa [prefixWord, tailWord_529437, baseEnd_529437] using wordTrace_append hprefix tailTrace_529437
  have hstable : (prefixWord ++ tailWord_529437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529437).length < 2 ^ (prefixWord ++ tailWord_529437).sum := by decide
  have hdescent : baseEnd_529437 < baseStart_529437 := by decide
  rcases family_descends (prefixWord ++ tailWord_529437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529441 : List Nat := [1, 2, 3, 2, 3, 1, 8]
def baseStart_529441 : Nat := 118140960795 + 529441 * 2 ^ 59
def prefixEnd_529441 : Nat := 4983230072969 + 3 ^ 40 * 529441 * 2
def baseEnd_529441 : Nat := 26850144315769707985447

theorem tailTrace_529441 : CollatzResearch.WordTrace tailWord_529441 prefixEnd_529441 26850144315769707985447 := by
  unfold tailWord_529441
  simp only [CollatzResearch.WordTrace]
  refine ⟨19310299674933153169100177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12873533116622102112733451 19310299674933153169100177)
  ·
    refine ⟨14482724756199864876825133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19310299674933153169100177 14482724756199864876825133)
    ·
      refine ⟨5431021783574949328809425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14482724756199864876825133 5431021783574949328809425)
      ·
        refine ⟨4073266337681211996607069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5431021783574949328809425 4073266337681211996607069)
        ·
          refine ⟨1527474876630454498727651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4073266337681211996607069 1527474876630454498727651)
          ·
            refine ⟨2291212314945681748091477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527474876630454498727651 2291212314945681748091477)
            ·
              refine ⟨26850144315769707985447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2291212314945681748091477 26850144315769707985447)
              ·
                rfl

theorem cell20_529441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 8].length) (baseStart_529441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529441 prefixEnd_529441 := by exact prefixLift 529441
  have htrace : WordTrace (prefixWord ++ tailWord_529441) baseStart_529441 baseEnd_529441 := by
    simpa [prefixWord, tailWord_529441, baseEnd_529441] using wordTrace_append hprefix tailTrace_529441
  have hstable : (prefixWord ++ tailWord_529441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529441).length < 2 ^ (prefixWord ++ tailWord_529441).sum := by decide
  have hdescent : baseEnd_529441 < baseStart_529441 := by decide
  rcases family_descends (prefixWord ++ tailWord_529441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529479 : List Nat := [1, 1, 4, 1, 3, 2, 2, 6]
def baseStart_529479 : Nat := 118140960795 + 529479 * 2 ^ 59
def prefixEnd_529479 : Nat := 4983230072969 + 3 ^ 40 * 529479 * 2
def baseEnd_529479 : Nat := 80556214359122709534067

theorem tailTrace_529479 : CollatzResearch.WordTrace tailWord_529479 prefixEnd_529479 80556214359122709534067 := by
  unfold tailWord_529479
  simp only [CollatzResearch.WordTrace]
  refine ⟨19311685648795485658983491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12874457099196990439322327 19311685648795485658983491)
  ·
    refine ⟨28967528473193228488475237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19311685648795485658983491 28967528473193228488475237)
    ·
      refine ⟨5431411588723730341589107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28967528473193228488475237 5431411588723730341589107)
      ·
        refine ⟨8147117383085595512383661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5431411588723730341589107 8147117383085595512383661)
        ·
          refine ⟨3055169018657098317143873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8147117383085595512383661 3055169018657098317143873)
          ·
            refine ⟨2291376763992823737857905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3055169018657098317143873 2291376763992823737857905)
            ·
              refine ⟨1718532572994617803393429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2291376763992823737857905 1718532572994617803393429)
              ·
                refine ⟨80556214359122709534067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1718532572994617803393429 80556214359122709534067)
                ·
                  rfl

theorem cell20_529479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 6].length) (baseStart_529479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529479 prefixEnd_529479 := by exact prefixLift 529479
  have htrace : WordTrace (prefixWord ++ tailWord_529479) baseStart_529479 baseEnd_529479 := by
    simpa [prefixWord, tailWord_529479, baseEnd_529479] using wordTrace_append hprefix tailTrace_529479
  have hstable : (prefixWord ++ tailWord_529479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529479).length < 2 ^ (prefixWord ++ tailWord_529479).sum := by decide
  have hdescent : baseEnd_529479 < baseStart_529479 := by decide
  rcases family_descends (prefixWord ++ tailWord_529479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529502 : List Nat := [4, 4, 1, 1, 1, 2, 1, 4, 2]
def baseStart_529502 : Nat := 118140960795 + 529502 * 2 ^ 59
def prefixEnd_529502 : Nat := 4983230072969 + 3 ^ 40 * 529502 * 2
def baseEnd_529502 : Nat := 241679140904082270835441

theorem tailTrace_529502 : CollatzResearch.WordTrace tailWord_529502 prefixEnd_529502 241679140904082270835441 := by
  unfold tailWord_529502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2414065565964020073383845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12875016351808107058047173 2414065565964020073383845)
  ·
    refine ⟨452637293618253763759471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2414065565964020073383845 452637293618253763759471)
    ·
      refine ⟨678955940427380645639207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452637293618253763759471 678955940427380645639207)
      ·
        refine ⟨1018433910641070968458811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678955940427380645639207 1018433910641070968458811)
        ·
          refine ⟨1527650865961606452688217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1018433910641070968458811 1527650865961606452688217)
          ·
            refine ⟨1145738149471204839516163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1527650865961606452688217 1145738149471204839516163)
            ·
              refine ⟨1718607224206807259274245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145738149471204839516163 1718607224206807259274245)
              ·
                refine ⟨322238854538776361113921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1718607224206807259274245 322238854538776361113921)
                ·
                  refine ⟨241679140904082270835441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322238854538776361113921 241679140904082270835441)
                  ·
                    rfl

theorem cell20_529502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_529502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529502 prefixEnd_529502 := by exact prefixLift 529502
  have htrace : WordTrace (prefixWord ++ tailWord_529502) baseStart_529502 baseEnd_529502 := by
    simpa [prefixWord, tailWord_529502, baseEnd_529502] using wordTrace_append hprefix tailTrace_529502
  have hstable : (prefixWord ++ tailWord_529502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529502).length < 2 ^ (prefixWord ++ tailWord_529502).sum := by decide
  have hdescent : baseEnd_529502 < baseStart_529502 := by decide
  rcases family_descends (prefixWord ++ tailWord_529502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529503 : List Nat := [1, 1, 2, 3, 1, 1, 6, 2, 3]
def baseStart_529503 : Nat := 118140960795 + 529503 * 2 ^ 59
def prefixEnd_529503 : Nat := 4983230072969 + 3 ^ 40 * 529503 * 2
def baseEnd_529503 : Nat := 241679597331330711802103

theorem tailTrace_529503 : CollatzResearch.WordTrace tailWord_529503 prefixEnd_529503 241679597331330711802103 := by
  unfold tailWord_529503
  simp only [CollatzResearch.WordTrace]
  refine ⟨19312561000708537757857163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12875040667139025171904775 19312561000708537757857163)
  ·
    refine ⟨28968841501062806636785745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19312561000708537757857163 28968841501062806636785745)
    ·
      refine ⟨21726631125797104977589309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28968841501062806636785745 21726631125797104977589309)
      ·
        refine ⟨8147486672173914366595991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21726631125797104977589309 8147486672173914366595991)
        ·
          refine ⟨12221230008260871549893987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8147486672173914366595991 12221230008260871549893987)
          ·
            refine ⟨18331845012391307324840981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12221230008260871549893987 18331845012391307324840981)
            ·
              refine ⟨859305234955842530851921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18331845012391307324840981 859305234955842530851921)
              ·
                refine ⟨644478926216881898138941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 859305234955842530851921 644478926216881898138941)
                ·
                  refine ⟨241679597331330711802103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644478926216881898138941 241679597331330711802103)
                  ·
                    rfl

theorem cell20_529503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 3].length) (baseStart_529503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529503 prefixEnd_529503 := by exact prefixLift 529503
  have htrace : WordTrace (prefixWord ++ tailWord_529503) baseStart_529503 baseEnd_529503 := by
    simpa [prefixWord, tailWord_529503, baseEnd_529503] using wordTrace_append hprefix tailTrace_529503
  have hstable : (prefixWord ++ tailWord_529503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529503).length < 2 ^ (prefixWord ++ tailWord_529503).sum := by decide
  have hdescent : baseEnd_529503 < baseStart_529503 := by decide
  rcases family_descends (prefixWord ++ tailWord_529503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529565 : List Nat := [1, 4, 2, 1, 1, 2, 1, 6, 2]
def baseStart_529565 : Nat := 118140960795 + 529565 * 2 ^ 59
def prefixEnd_529565 : Nat := 4983230072969 + 3 ^ 40 * 529565 * 2
def baseEnd_529565 : Nat := 241707895820734051735183

theorem tailTrace_529565 : CollatzResearch.WordTrace tailWord_529565 prefixEnd_529565 241707895820734051735183 := by
  unfold tailWord_529565
  simp only [CollatzResearch.WordTrace]
  refine ⟨19314822326483922346614149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12876548217655948231076099 19314822326483922346614149)
  ·
    refine ⟨3621529186215735439990153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19314822326483922346614149 3621529186215735439990153)
    ·
      refine ⟨2716146889661801579992615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3621529186215735439990153 2716146889661801579992615)
      ·
        refine ⟨4074220334492702369988923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2716146889661801579992615 4074220334492702369988923)
        ·
          refine ⟨6111330501739053554983385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4074220334492702369988923 6111330501739053554983385)
          ·
            refine ⟨4583497876304290166237539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6111330501739053554983385 4583497876304290166237539)
            ·
              refine ⟨6875246814456435249356309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4583497876304290166237539 6875246814456435249356309)
              ·
                refine ⟨322277194427645402313577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6875246814456435249356309 322277194427645402313577)
                ·
                  refine ⟨241707895820734051735183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322277194427645402313577 241707895820734051735183)
                  ·
                    rfl

theorem cell20_529565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_529565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529565 prefixEnd_529565 := by exact prefixLift 529565
  have htrace : WordTrace (prefixWord ++ tailWord_529565) baseStart_529565 baseEnd_529565 := by
    simpa [prefixWord, tailWord_529565, baseEnd_529565] using wordTrace_append hprefix tailTrace_529565
  have hstable : (prefixWord ++ tailWord_529565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529565).length < 2 ^ (prefixWord ++ tailWord_529565).sum := by decide
  have hdescent : baseEnd_529565 < baseStart_529565 := by decide
  rcases family_descends (prefixWord ++ tailWord_529565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529575 : List Nat := [1, 1, 6, 2, 1, 2, 3, 1, 3]
def baseStart_529575 : Nat := 118140960795 + 529575 * 2 ^ 59
def prefixEnd_529575 : Nat := 4983230072969 + 3 ^ 40 * 529575 * 2
def baseEnd_529575 : Nat := 241712460093218461401809

theorem tailTrace_529575 : CollatzResearch.WordTrace tailWord_529575 prefixEnd_529575 241712460093218461401809 := by
  unfold tailWord_529575
  simp only [CollatzResearch.WordTrace]
  refine ⟨19315187056447694054478179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12876791370965129369652119 19315187056447694054478179)
  ·
    refine ⟨28972780584671541081717269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19315187056447694054478179 28972780584671541081717269)
    ·
      refine ⟨1358099089906478488205497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28972780584671541081717269 1358099089906478488205497)
      ·
        refine ⟨1018574317429858866154123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1358099089906478488205497 1018574317429858866154123)
        ·
          refine ⟨1527861476144788299231185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1018574317429858866154123 1527861476144788299231185)
          ·
            refine ⟨1145896107108591224423389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1527861476144788299231185 1145896107108591224423389)
            ·
              refine ⟨429711040165721709158771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1145896107108591224423389 429711040165721709158771)
              ·
                refine ⟨644566560248582563738157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429711040165721709158771 644566560248582563738157)
                ·
                  refine ⟨241712460093218461401809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644566560248582563738157 241712460093218461401809)
                  ·
                    rfl

theorem cell20_529575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 3].length) (baseStart_529575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_529575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_529575 prefixEnd_529575 := by exact prefixLift 529575
  have htrace : WordTrace (prefixWord ++ tailWord_529575) baseStart_529575 baseEnd_529575 := by
    simpa [prefixWord, tailWord_529575, baseEnd_529575] using wordTrace_append hprefix tailTrace_529575
  have hstable : (prefixWord ++ tailWord_529575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529575).length < 2 ^ (prefixWord ++ tailWord_529575).sum := by decide
  have hdescent : baseEnd_529575 < baseStart_529575 := by decide
  rcases family_descends (prefixWord ++ tailWord_529575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
