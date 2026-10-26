import V185TrunkScan23Chunk0125

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_746330 : List Nat := [3, 1, 1, 2, 1, 5, 3, 2, 5]
def baseStart_746330 : Nat := 118140960795 + 746330 * 2 ^ 59
def prefixEnd_746330 : Nat := 4983230072969 + 3 ^ 40 * 746330 * 2
def baseEnd_746330 : Nat := 42580668541130023793633

theorem tailTrace_746330 : CollatzResearch.WordTrace tailWord_746330 prefixEnd_746330 42580668541130023793633 := by
  unfold tailWord_746330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6805222846545336965315111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18147260924120898574173629 6805222846545336965315111)
  ·
    refine ⟨10207834269818005447972667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6805222846545336965315111 10207834269818005447972667)
    ·
      refine ⟨15311751404727008171959001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10207834269818005447972667 15311751404727008171959001)
      ·
        refine ⟨11483813553545256128969251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15311751404727008171959001 11483813553545256128969251)
        ·
          refine ⟨17225720330317884193453877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11483813553545256128969251 17225720330317884193453877)
          ·
            refine ⟨1614911280967301643136301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17225720330317884193453877 1614911280967301643136301)
            ·
              refine ⟨605591730362738116176113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1614911280967301643136301 605591730362738116176113)
              ·
                refine ⟨454193797772053587132085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605591730362738116176113 454193797772053587132085)
                ·
                  refine ⟨42580668541130023793633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 454193797772053587132085 42580668541130023793633)
                  ·
                    rfl

theorem cell23_746330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 5].length) (baseStart_746330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746330 prefixEnd_746330 := by exact prefixLift 746330
  have htrace : WordTrace (prefixWord ++ tailWord_746330) baseStart_746330 baseEnd_746330 := by
    simpa [prefixWord, tailWord_746330, baseEnd_746330] using wordTrace_append hprefix tailTrace_746330
  have hstable : (prefixWord ++ tailWord_746330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746330).length < 2 ^ (prefixWord ++ tailWord_746330).sum := by decide
  have hdescent : baseEnd_746330 < baseStart_746330 := by decide
  rcases family_descends (prefixWord ++ tailWord_746330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746336 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 5]
def baseStart_746336 : Nat := 118140960795 + 746336 * 2 ^ 59
def prefixEnd_746336 : Nat := 4983230072969 + 3 ^ 40 * 746336 * 2
def baseEnd_746336 : Nat := 383229097754097190667669

theorem tailTrace_746336 : CollatzResearch.WordTrace tailWord_746336 prefixEnd_746336 383229097754097190667669 := by
  unfold tailWord_746336
  simp only [CollatzResearch.WordTrace]
  refine ⟨13610555112079805442989431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18147406816106407257319241 13610555112079805442989431)
  ·
    refine ⟨20415832668119708164484147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13610555112079805442989431 20415832668119708164484147)
    ·
      refine ⟨30623749002179562246726221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20415832668119708164484147 30623749002179562246726221)
      ·
        refine ⟨11483905875817335842522333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30623749002179562246726221 11483905875817335842522333)
        ·
          refine ⟨4306464703431500940945875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11483905875817335842522333 4306464703431500940945875)
          ·
            refine ⟨6459697055147251411418813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4306464703431500940945875 6459697055147251411418813)
            ·
              refine ⟨2422386395680219279282055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6459697055147251411418813 2422386395680219279282055)
              ·
                refine ⟨3633579593520328918923083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2422386395680219279282055 3633579593520328918923083)
                ·
                  refine ⟨5450369390280493378384625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3633579593520328918923083 5450369390280493378384625)
                  ·
                    refine ⟨4087777042710370033788469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5450369390280493378384625 4087777042710370033788469)
                    ·
                      refine ⟨383229097754097190667669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4087777042710370033788469 383229097754097190667669)
                      ·
                        rfl

theorem cell23_746336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_746336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746336 prefixEnd_746336 := by exact prefixLift 746336
  have htrace : WordTrace (prefixWord ++ tailWord_746336) baseStart_746336 baseEnd_746336 := by
    simpa [prefixWord, tailWord_746336, baseEnd_746336] using wordTrace_append hprefix tailTrace_746336
  have hstable : (prefixWord ++ tailWord_746336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746336).length < 2 ^ (prefixWord ++ tailWord_746336).sum := by decide
  have hdescent : baseEnd_746336 < baseStart_746336 := by decide
  rcases family_descends (prefixWord ++ tailWord_746336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746417 : List Nat := [1, 2, 2, 4, 3, 2, 1, 1, 2, 2, 3]
def baseStart_746417 : Nat := 118140960795 + 746417 * 2 ^ 59
def prefixEnd_746417 : Nat := 4983230072969 + 3 ^ 40 * 746417 * 2
def baseEnd_746417 : Nat := 383270689687111373754797

theorem tailTrace_746417 : CollatzResearch.WordTrace tailWord_746417 prefixEnd_746417 383270689687111373754797 := by
  unfold tailWord_746417
  simp only [CollatzResearch.WordTrace]
  refine ⟨27224064536866161719677505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18149376357910774479785003 27224064536866161719677505)
  ·
    refine ⟨20418048402649621289758129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27224064536866161719677505 20418048402649621289758129)
    ·
      refine ⟨15313536301987215967318597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20418048402649621289758129 15313536301987215967318597)
      ·
        refine ⟨2871288056622602993872237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15313536301987215967318597 2871288056622602993872237)
        ·
          refine ⟨1076733021233476122702089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2871288056622602993872237 1076733021233476122702089)
          ·
            refine ⟨807549765925107092026567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1076733021233476122702089 807549765925107092026567)
            ·
              refine ⟨1211324648887660638039851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807549765925107092026567 1211324648887660638039851)
              ·
                refine ⟨1816986973331490957059777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1211324648887660638039851 1816986973331490957059777)
                ·
                  refine ⟨1362740229998618217794833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1816986973331490957059777 1362740229998618217794833)
                  ·
                    refine ⟨1022055172498963663346125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1362740229998618217794833 1022055172498963663346125)
                    ·
                      refine ⟨383270689687111373754797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1022055172498963663346125 383270689687111373754797)
                      ·
                        rfl

theorem cell23_746417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_746417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746417 prefixEnd_746417 := by exact prefixLift 746417
  have htrace : WordTrace (prefixWord ++ tailWord_746417) baseStart_746417 baseEnd_746417 := by
    simpa [prefixWord, tailWord_746417, baseEnd_746417] using wordTrace_append hprefix tailTrace_746417
  have hstable : (prefixWord ++ tailWord_746417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746417).length < 2 ^ (prefixWord ++ tailWord_746417).sum := by decide
  have hdescent : baseEnd_746417 < baseStart_746417 := by decide
  rcases family_descends (prefixWord ++ tailWord_746417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746430 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3]
def baseStart_746430 : Nat := 118140960795 + 746430 * 2 ^ 59
def prefixEnd_746430 : Nat := 4983230072969 + 3 ^ 40 * 746430 * 2
def baseEnd_746430 : Nat := 383277364935619822892237

theorem tailTrace_746430 : CollatzResearch.WordTrace tailWord_746430 prefixEnd_746430 383277364935619822892237 := by
  unfold tailWord_746430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3403067335727383117487593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18149692457212709959933829 3403067335727383117487593)
  ·
    refine ⟨2552300501795537338115695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3403067335727383117487593 2552300501795537338115695)
    ·
      refine ⟨3828450752693306007173543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2552300501795537338115695 3828450752693306007173543)
      ·
        refine ⟨5742676129039959010760315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3828450752693306007173543 5742676129039959010760315)
        ·
          refine ⟨8614014193559938516140473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5742676129039959010760315 8614014193559938516140473)
          ·
            refine ⟨6460510645169953887105355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8614014193559938516140473 6460510645169953887105355)
            ·
              refine ⟨9690765967754930830658033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6460510645169953887105355 9690765967754930830658033)
              ·
                refine ⟨7268074475816198122993525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9690765967754930830658033 7268074475816198122993525)
                ·
                  refine ⟨681381982107768574030643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7268074475816198122993525 681381982107768574030643)
                  ·
                    refine ⟨1022072973161652861045965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 681381982107768574030643 1022072973161652861045965)
                    ·
                      refine ⟨383277364935619822892237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1022072973161652861045965 383277364935619822892237)
                      ·
                        rfl

theorem cell23_746430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_746430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746430 prefixEnd_746430 := by exact prefixLift 746430
  have htrace : WordTrace (prefixWord ++ tailWord_746430) baseStart_746430 baseEnd_746430 := by
    simpa [prefixWord, tailWord_746430, baseEnd_746430] using wordTrace_append hprefix tailTrace_746430
  have hstable : (prefixWord ++ tailWord_746430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746430).length < 2 ^ (prefixWord ++ tailWord_746430).sum := by decide
  have hdescent : baseEnd_746430 < baseStart_746430 := by decide
  rcases family_descends (prefixWord ++ tailWord_746430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746447 : List Nat := [1, 1, 2, 1, 1, 6, 2, 4, 1, 1, 3]
def baseStart_746447 : Nat := 118140960795 + 746447 * 2 ^ 59
def prefixEnd_746447 : Nat := 4983230072969 + 3 ^ 40 * 746447 * 2
def baseEnd_746447 : Nat := 383286094106746256379659

theorem tailTrace_746447 : CollatzResearch.WordTrace tailWord_746447 prefixEnd_746447 383286094106746256379659 := by
  unfold tailWord_746447
  simp only [CollatzResearch.WordTrace]
  refine ⟨27225158726757476843269595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18150105817838317895513063 27225158726757476843269595)
  ·
    refine ⟨40837738090136215264904393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27225158726757476843269595 40837738090136215264904393)
    ·
      refine ⟨30628303567602161448678295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40837738090136215264904393 30628303567602161448678295)
      ·
        refine ⟨45942455351403242173017443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30628303567602161448678295 45942455351403242173017443)
        ·
          refine ⟨68913683027104863259526165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45942455351403242173017443 68913683027104863259526165)
          ·
            refine ⟨3230328891895540465290289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68913683027104863259526165 3230328891895540465290289)
            ·
              refine ⟨2422746668921655348967717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3230328891895540465290289 2422746668921655348967717)
              ·
                refine ⟨454265000422810377931447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2422746668921655348967717 454265000422810377931447)
                ·
                  refine ⟨681397500634215566897171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454265000422810377931447 681397500634215566897171)
                  ·
                    refine ⟨1022096250951323350345757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 681397500634215566897171 1022096250951323350345757)
                    ·
                      refine ⟨383286094106746256379659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1022096250951323350345757 383286094106746256379659)
                      ·
                        rfl

theorem cell23_746447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 1, 1, 3].length) (baseStart_746447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746447 prefixEnd_746447 := by exact prefixLift 746447
  have htrace : WordTrace (prefixWord ++ tailWord_746447) baseStart_746447 baseEnd_746447 := by
    simpa [prefixWord, tailWord_746447, baseEnd_746447] using wordTrace_append hprefix tailTrace_746447
  have hstable : (prefixWord ++ tailWord_746447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746447).length < 2 ^ (prefixWord ++ tailWord_746447).sum := by decide
  have hdescent : baseEnd_746447 < baseStart_746447 := by decide
  rcases family_descends (prefixWord ++ tailWord_746447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746498 : List Nat := [3, 4, 1, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_746498 : Nat := 118140960795 + 746498 * 2 ^ 59
def prefixEnd_746498 : Nat := 4983230072969 + 3 ^ 40 * 746498 * 2
def baseEnd_746498 : Nat := 383312281620125556841925

theorem tailTrace_746498 : CollatzResearch.WordTrace tailWord_746498 prefixEnd_746498 383312281620125556841925 := by
  unfold tailWord_746498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6806754712393178138344037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18151345899715141702250765 6806754712393178138344037)
  ·
    refine ⟨1276266508573720900939507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6806754712393178138344037 1276266508573720900939507)
    ·
      refine ⟨1914399762860581351409261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1276266508573720900939507 1914399762860581351409261)
      ·
        refine ⟨717899911072718006778473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1914399762860581351409261 717899911072718006778473)
        ·
          refine ⟨538424933304538505083855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 717899911072718006778473 538424933304538505083855)
          ·
            refine ⟨807637399956807757625783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538424933304538505083855 807637399956807757625783)
            ·
              refine ⟨1211456099935211636438675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807637399956807757625783 1211456099935211636438675)
              ·
                refine ⟨1817184149902817454658013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1211456099935211636438675 1817184149902817454658013)
                ·
                  refine ⟨681444056213556545496755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1817184149902817454658013 681444056213556545496755)
                  ·
                    refine ⟨1022166084320334818245133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 681444056213556545496755 1022166084320334818245133)
                    ·
                      refine ⟨383312281620125556841925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1022166084320334818245133 383312281620125556841925)
                      ·
                        rfl

theorem cell23_746498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_746498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746498 prefixEnd_746498 := by exact prefixLift 746498
  have htrace : WordTrace (prefixWord ++ tailWord_746498) baseStart_746498 baseEnd_746498 := by
    simpa [prefixWord, tailWord_746498, baseEnd_746498] using wordTrace_append hprefix tailTrace_746498
  have hstable : (prefixWord ++ tailWord_746498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746498).length < 2 ^ (prefixWord ++ tailWord_746498).sum := by decide
  have hdescent : baseEnd_746498 < baseStart_746498 := by decide
  rcases family_descends (prefixWord ++ tailWord_746498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746504 : List Nat := [2, 1, 3, 2, 1, 5, 1, 1, 3, 2, 2]
def baseStart_746504 : Nat := 118140960795 + 746504 * 2 ^ 59
def prefixEnd_746504 : Nat := 4983230072969 + 3 ^ 40 * 746504 * 2
def baseEnd_746504 : Nat := 383315362504052533366897

theorem tailTrace_746504 : CollatzResearch.WordTrace tailWord_746504 prefixEnd_746504 383315362504052533366897 := by
  unfold tailWord_746504
  simp only [CollatzResearch.WordTrace]
  refine ⟨13613618843775487789047283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18151491791700650385396377 13613618843775487789047283)
  ·
    refine ⟨20420428265663231683570925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13613618843775487789047283 20420428265663231683570925)
    ·
      refine ⟨7657660599623711881339097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20420428265663231683570925 7657660599623711881339097)
      ·
        refine ⟨5743245449717783911004323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7657660599623711881339097 5743245449717783911004323)
        ·
          refine ⟨8614868174576675866506485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5743245449717783911004323 8614868174576675866506485)
          ·
            refine ⟨807643891366563362484983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8614868174576675866506485 807643891366563362484983)
            ·
              refine ⟨1211465837049845043727475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807643891366563362484983 1211465837049845043727475)
              ·
                refine ⟨1817198755574767565591213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1211465837049845043727475 1817198755574767565591213)
                ·
                  refine ⟨681449533340537837096705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1817198755574767565591213 681449533340537837096705)
                  ·
                    refine ⟨511087150005403377822529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 681449533340537837096705 511087150005403377822529)
                    ·
                      refine ⟨383315362504052533366897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 511087150005403377822529 383315362504052533366897)
                      ·
                        rfl

theorem cell23_746504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_746504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746504 prefixEnd_746504 := by exact prefixLift 746504
  have htrace : WordTrace (prefixWord ++ tailWord_746504) baseStart_746504 baseEnd_746504 := by
    simpa [prefixWord, tailWord_746504, baseEnd_746504] using wordTrace_append hprefix tailTrace_746504
  have hstable : (prefixWord ++ tailWord_746504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746504).length < 2 ^ (prefixWord ++ tailWord_746504).sum := by decide
  have hdescent : baseEnd_746504 < baseStart_746504 := by decide
  rcases family_descends (prefixWord ++ tailWord_746504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746524 : List Nat := [2, 2, 3, 1, 4, 2, 1, 2, 1, 2, 3]
def baseStart_746524 : Nat := 118140960795 + 746524 * 2 ^ 59
def prefixEnd_746524 : Nat := 4983230072969 + 3 ^ 40 * 746524 * 2
def baseEnd_746524 : Nat := 383325632117142455116805

theorem tailTrace_746524 : CollatzResearch.WordTrace tailWord_746524 prefixEnd_746524 383325632117142455116805 := by
  unfold tailWord_746524
  simp only [CollatzResearch.WordTrace]
  refine ⟨13613983573739259496911313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18151978098319012662548417 13613983573739259496911313)
  ·
    refine ⟨10210487680304444622683485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13613983573739259496911313 10210487680304444622683485)
    ·
      refine ⟨3828932880114166733506307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10210487680304444622683485 3828932880114166733506307)
      ·
        refine ⟨5743399320171250100259461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3828932880114166733506307 5743399320171250100259461)
        ·
          refine ⟨1076887372532109393798649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5743399320171250100259461 1076887372532109393798649)
          ·
            refine ⟨807665529399082045348987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1076887372532109393798649 807665529399082045348987)
            ·
              refine ⟨1211498294098623068023481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807665529399082045348987 1211498294098623068023481)
              ·
                refine ⟨908623720573967301017611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1211498294098623068023481 908623720573967301017611)
                ·
                  refine ⟨1362935580860950951526417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 908623720573967301017611 1362935580860950951526417)
                  ·
                    refine ⟨1022201685645713213644813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1362935580860950951526417 1022201685645713213644813)
                    ·
                      refine ⟨383325632117142455116805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1022201685645713213644813 383325632117142455116805)
                      ·
                        rfl

theorem cell23_746524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_746524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746524 prefixEnd_746524 := by exact prefixLift 746524
  have htrace : WordTrace (prefixWord ++ tailWord_746524) baseStart_746524 baseEnd_746524 := by
    simpa [prefixWord, tailWord_746524, baseEnd_746524] using wordTrace_append hprefix tailTrace_746524
  have hstable : (prefixWord ++ tailWord_746524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746524).length < 2 ^ (prefixWord ++ tailWord_746524).sum := by decide
  have hdescent : baseEnd_746524 < baseStart_746524 := by decide
  rcases family_descends (prefixWord ++ tailWord_746524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746560 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 3, 4, 2]
def baseStart_746560 : Nat := 118140960795 + 746560 * 2 ^ 59
def prefixEnd_746560 : Nat := 4983230072969 + 3 ^ 40 * 746560 * 2
def baseEnd_746560 : Nat := 383344117420704314266639

theorem tailTrace_746560 : CollatzResearch.WordTrace tailWord_746560 prefixEnd_746560 383344117420704314266639 := by
  unfold tailWord_746560
  simp only [CollatzResearch.WordTrace]
  refine ⟨13614640087674048571066567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18152853450232064761422089 13614640087674048571066567)
  ·
    refine ⟨20421960131511072856599851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13614640087674048571066567 20421960131511072856599851)
    ·
      refine ⟨30632940197266609284899777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20421960131511072856599851 30632940197266609284899777)
      ·
        refine ⟨22974705147949956963674833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30632940197266609284899777 22974705147949956963674833)
        ·
          refine ⟨17231028860962467722756125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22974705147949956963674833 17231028860962467722756125)
          ·
            refine ⟨6461635822860925396033547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17231028860962467722756125 6461635822860925396033547)
            ·
              refine ⟨9692453734291388094050321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6461635822860925396033547 9692453734291388094050321)
              ·
                refine ⟨7269340300718541070537741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9692453734291388094050321 7269340300718541070537741)
                ·
                  refine ⟨2726002612769452901451653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7269340300718541070537741 2726002612769452901451653)
                  ·
                    refine ⟨511125489894272419022185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2726002612769452901451653 511125489894272419022185)
                    ·
                      refine ⟨383344117420704314266639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 511125489894272419022185 383344117420704314266639)
                      ·
                        rfl

theorem cell23_746560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 3, 4, 2].length) (baseStart_746560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746560 prefixEnd_746560 := by exact prefixLift 746560
  have htrace : WordTrace (prefixWord ++ tailWord_746560) baseStart_746560 baseEnd_746560 := by
    simpa [prefixWord, tailWord_746560, baseEnd_746560] using wordTrace_append hprefix tailTrace_746560
  have hstable : (prefixWord ++ tailWord_746560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746560).length < 2 ^ (prefixWord ++ tailWord_746560).sum := by decide
  have hdescent : baseEnd_746560 < baseStart_746560 := by decide
  rcases family_descends (prefixWord ++ tailWord_746560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746563 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 3]
def baseStart_746563 : Nat := 118140960795 + 746563 * 2 ^ 59
def prefixEnd_746563 : Nat := 4983230072969 + 3 ^ 40 * 746563 * 2
def baseEnd_746563 : Nat := 383345657862667802529125

theorem tailTrace_746563 : CollatzResearch.WordTrace tailWord_746563 prefixEnd_746563 383345657862667802529125 := by
  unfold tailWord_746563
  simp only [CollatzResearch.WordTrace]
  refine ⟨27229389594337228654492343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18152926396224819102994895 27229389594337228654492343)
  ·
    refine ⟨40844084391505842981738515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27229389594337228654492343 40844084391505842981738515)
    ·
      refine ⟨61266126587258764472607773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40844084391505842981738515 61266126587258764472607773)
      ·
        refine ⟨22974797470222036677227915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61266126587258764472607773 22974797470222036677227915)
        ·
          refine ⟨34462196205333055015841873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22974797470222036677227915 34462196205333055015841873)
          ·
            refine ⟨25846647153999791261881405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34462196205333055015841873 25846647153999791261881405)
            ·
              refine ⟨9692492682749921723205527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25846647153999791261881405 9692492682749921723205527)
              ·
                refine ⟨14538739024124882584808291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9692492682749921723205527 14538739024124882584808291)
                ·
                  refine ⟨21808108536187323877212437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14538739024124882584808291 21808108536187323877212437)
                  ·
                    refine ⟨1022255087633780806744333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21808108536187323877212437 1022255087633780806744333)
                    ·
                      refine ⟨383345657862667802529125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1022255087633780806744333 383345657862667802529125)
                      ·
                        rfl

theorem cell23_746563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_746563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746563 prefixEnd_746563 := by exact prefixLift 746563
  have htrace : WordTrace (prefixWord ++ tailWord_746563) baseStart_746563 baseEnd_746563 := by
    simpa [prefixWord, tailWord_746563, baseEnd_746563] using wordTrace_append hprefix tailTrace_746563
  have hstable : (prefixWord ++ tailWord_746563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746563).length < 2 ^ (prefixWord ++ tailWord_746563).sum := by decide
  have hdescent : baseEnd_746563 < baseStart_746563 := by decide
  rcases family_descends (prefixWord ++ tailWord_746563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746594 : List Nat := [3, 3, 2, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_746594 : Nat := 118140960795 + 746594 * 2 ^ 59
def prefixEnd_746594 : Nat := 4983230072969 + 3 ^ 40 * 746594 * 2
def baseEnd_746594 : Nat := 383361575762957181241483

theorem tailTrace_746594 : CollatzResearch.WordTrace tailWord_746594 prefixEnd_746594 383361575762957181241483 := by
  unfold tailWord_746594
  simp only [CollatzResearch.WordTrace]
  refine ⟨6807630064306230237217709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18153680171483280632580557 6807630064306230237217709)
  ·
    refine ⟨2552861274114836338956641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6807630064306230237217709 2552861274114836338956641)
    ·
      refine ⟨1914645955586127254217481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2552861274114836338956641 1914645955586127254217481)
      ·
        refine ⟨1435984466689595440663111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1914645955586127254217481 1435984466689595440663111)
        ·
          refine ⟨2153976700034393160994667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1435984466689595440663111 2153976700034393160994667)
          ·
            refine ⟨3230965050051589741492001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2153976700034393160994667 3230965050051589741492001)
            ·
              refine ⟨2423223787538692306119001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3230965050051589741492001 2423223787538692306119001)
              ·
                refine ⟨1817417840654019229589251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2423223787538692306119001 1817417840654019229589251)
                ·
                  refine ⟨2726126760981028844383877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817417840654019229589251 2726126760981028844383877)
                  ·
                    refine ⟨511148767683942908321977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2726126760981028844383877 511148767683942908321977)
                    ·
                      refine ⟨383361575762957181241483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 511148767683942908321977 383361575762957181241483)
                      ·
                        rfl

theorem cell23_746594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_746594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746594 prefixEnd_746594 := by exact prefixLift 746594
  have htrace : WordTrace (prefixWord ++ tailWord_746594) baseStart_746594 baseEnd_746594 := by
    simpa [prefixWord, tailWord_746594, baseEnd_746594] using wordTrace_append hprefix tailTrace_746594
  have hstable : (prefixWord ++ tailWord_746594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746594).length < 2 ^ (prefixWord ++ tailWord_746594).sum := by decide
  have hdescent : baseEnd_746594 < baseStart_746594 := by decide
  rcases family_descends (prefixWord ++ tailWord_746594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746610 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 4, 3, 3]
def baseStart_746610 : Nat := 118140960795 + 746610 * 2 ^ 59
def prefixEnd_746610 : Nat := 4983230072969 + 3 ^ 40 * 746610 * 2
def baseEnd_746610 : Nat := 383369791453429118641409

theorem tailTrace_746610 : CollatzResearch.WordTrace tailWord_746610 prefixEnd_746610 383369791453429118641409 := by
  unfold tailWord_746610
  simp only [CollatzResearch.WordTrace]
  refine ⟨6807775956291738920363321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18154069216777970454302189 6807775956291738920363321)
  ·
    refine ⟨5105831967218804190272491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6807775956291738920363321 5105831967218804190272491)
    ·
      refine ⟨7658747950828206285408737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5105831967218804190272491 7658747950828206285408737)
      ·
        refine ⟨5744060963121154714056553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7658747950828206285408737 5744060963121154714056553)
        ·
          refine ⟨4308045722340866035542415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5744060963121154714056553 4308045722340866035542415)
          ·
            refine ⟨6462068583511299053313623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4308045722340866035542415 6462068583511299053313623)
            ·
              refine ⟨9693102875266948579970435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6462068583511299053313623 9693102875266948579970435)
              ·
                refine ⟨14539654312900422869955653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9693102875266948579970435 14539654312900422869955653)
                ·
                  refine ⟨2726185183668829288116685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14539654312900422869955653 2726185183668829288116685)
                  ·
                    refine ⟨1022319443875810983043757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2726185183668829288116685 1022319443875810983043757)
                    ·
                      refine ⟨383369791453429118641409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1022319443875810983043757 383369791453429118641409)
                      ·
                        rfl

theorem cell23_746610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_746610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746610 prefixEnd_746610 := by exact prefixLift 746610
  have htrace : WordTrace (prefixWord ++ tailWord_746610) baseStart_746610 baseEnd_746610 := by
    simpa [prefixWord, tailWord_746610, baseEnd_746610] using wordTrace_append hprefix tailTrace_746610
  have hstable : (prefixWord ++ tailWord_746610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746610).length < 2 ^ (prefixWord ++ tailWord_746610).sum := by decide
  have hdescent : baseEnd_746610 < baseStart_746610 := by decide
  rcases family_descends (prefixWord ++ tailWord_746610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746757 : List Nat := [1, 3, 1, 1, 2, 1, 4, 4, 1, 1, 4]
def baseStart_746757 : Nat := 118140960795 + 746757 * 2 ^ 59
def prefixEnd_746757 : Nat := 4983230072969 + 3 ^ 40 * 746757 * 2
def baseEnd_746757 : Nat := 383445273109640043503233

theorem tailTrace_746757 : CollatzResearch.WordTrace tailWord_746757 prefixEnd_746757 383445273109640043503233 := by
  unfold tailWord_746757
  simp only [CollatzResearch.WordTrace]
  refine ⟨27236465355634399787054525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18157643570422933191369683 27236465355634399787054525)
  ·
    refine ⟨10213674508362899920145447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27236465355634399787054525 10213674508362899920145447)
    ·
      refine ⟨15320511762544349880218171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10213674508362899920145447 15320511762544349880218171)
      ·
        refine ⟨22980767643816524820327257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15320511762544349880218171 22980767643816524820327257)
        ·
          refine ⟨17235575732862393615245443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22980767643816524820327257 17235575732862393615245443)
          ·
            refine ⟨25853363599293590422868165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17235575732862393615245443 25853363599293590422868165)
            ·
              refine ⟨4847505674867548204287781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25853363599293590422868165 4847505674867548204287781)
              ·
                refine ⟨908907314037665288303959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4847505674867548204287781 908907314037665288303959)
                ·
                  refine ⟨1363360971056497932455939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 908907314037665288303959 1363360971056497932455939)
                  ·
                    refine ⟨2045041456584746898683909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1363360971056497932455939 2045041456584746898683909)
                    ·
                      refine ⟨383445273109640043503233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2045041456584746898683909 383445273109640043503233)
                      ·
                        rfl

theorem cell23_746757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 1, 4].length) (baseStart_746757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746757 prefixEnd_746757 := by exact prefixLift 746757
  have htrace : WordTrace (prefixWord ++ tailWord_746757) baseStart_746757 baseEnd_746757 := by
    simpa [prefixWord, tailWord_746757, baseEnd_746757] using wordTrace_append hprefix tailTrace_746757
  have hstable : (prefixWord ++ tailWord_746757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746757).length < 2 ^ (prefixWord ++ tailWord_746757).sum := by decide
  have hdescent : baseEnd_746757 < baseStart_746757 := by decide
  rcases family_descends (prefixWord ++ tailWord_746757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746784 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 4, 4]
def baseStart_746784 : Nat := 118140960795 + 746784 * 2 ^ 59
def prefixEnd_746784 : Nat := 4983230072969 + 3 ^ 40 * 746784 * 2
def baseEnd_746784 : Nat := 127819712362437145955203

theorem tailTrace_746784 : CollatzResearch.WordTrace tailWord_746784 prefixEnd_746784 127819712362437145955203 := by
  unfold tailWord_746784
  simp only [CollatzResearch.WordTrace]
  refine ⟨13618725063268291699143703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18158300084357722265524937 13618725063268291699143703)
  ·
    refine ⟨20428087594902437548715555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13618725063268291699143703 20428087594902437548715555)
    ·
      refine ⟨30642131392353656323073333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20428087594902437548715555 30642131392353656323073333)
      ·
        refine ⟨2872699818033155280288125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30642131392353656323073333 2872699818033155280288125)
        ·
          refine ⟨1077262431762433230108047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2872699818033155280288125 1077262431762433230108047)
          ·
            refine ⟨1615893647643649845162071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077262431762433230108047 1615893647643649845162071)
            ·
              refine ⟨2423840471465474767743107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1615893647643649845162071 2423840471465474767743107)
              ·
                refine ⟨3635760707198212151614661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2423840471465474767743107 3635760707198212151614661)
                ·
                  refine ⟨681705132599664778427749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3635760707198212151614661 681705132599664778427749)
                  ·
                    refine ⟨127819712362437145955203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 681705132599664778427749 127819712362437145955203)
                    ·
                      rfl

theorem cell23_746784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 4, 4].length) (baseStart_746784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746784 prefixEnd_746784 := by exact prefixLift 746784
  have htrace : WordTrace (prefixWord ++ tailWord_746784) baseStart_746784 baseEnd_746784 := by
    simpa [prefixWord, tailWord_746784, baseEnd_746784] using wordTrace_append hprefix tailTrace_746784
  have hstable : (prefixWord ++ tailWord_746784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746784).length < 2 ^ (prefixWord ++ tailWord_746784).sum := by decide
  have hdescent : baseEnd_746784 < baseStart_746784 := by decide
  rcases family_descends (prefixWord ++ tailWord_746784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746794 : List Nat := [3, 1, 4, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_746794 : Nat := 118140960795 + 746794 * 2 ^ 59
def prefixEnd_746794 : Nat := 4983230072969 + 3 ^ 40 * 746794 * 2
def baseEnd_746794 : Nat := 383464271893856398740563

theorem tailTrace_746794 : CollatzResearch.WordTrace tailWord_746794 prefixEnd_746794 383464271893856398740563 := by
  unfold tailWord_746794
  simp only [CollatzResearch.WordTrace]
  refine ⟨6809453714125088776537859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18158543237666903404100957 6809453714125088776537859)
  ·
    refine ⟨10214180571187633164806789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6809453714125088776537859 10214180571187633164806789)
    ·
      refine ⟨1915158857097681218401273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10214180571187633164806789 1915158857097681218401273)
      ·
        refine ⟨1436369142823260913800955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1915158857097681218401273 1436369142823260913800955)
        ·
          refine ⟨2154553714234891370701433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1436369142823260913800955 2154553714234891370701433)
          ·
            refine ⟨1615915285676168528026075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2154553714234891370701433 1615915285676168528026075)
            ·
              refine ⟨2423872928514252792039113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1615915285676168528026075 2423872928514252792039113)
              ·
                refine ⟨1817904696385689594029335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2423872928514252792039113 1817904696385689594029335)
                ·
                  refine ⟨2726857044578534391044003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817904696385689594029335 2726857044578534391044003)
                  ·
                    refine ⟨4090285566867801586566005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2726857044578534391044003 4090285566867801586566005)
                    ·
                      refine ⟨383464271893856398740563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4090285566867801586566005 383464271893856398740563)
                      ·
                        rfl

theorem cell23_746794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_746794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746794 prefixEnd_746794 := by exact prefixLift 746794
  have htrace : WordTrace (prefixWord ++ tailWord_746794) baseStart_746794 baseEnd_746794 := by
    simpa [prefixWord, tailWord_746794, baseEnd_746794] using wordTrace_append hprefix tailTrace_746794
  have hstable : (prefixWord ++ tailWord_746794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746794).length < 2 ^ (prefixWord ++ tailWord_746794).sum := by decide
  have hdescent : baseEnd_746794 < baseStart_746794 := by decide
  rcases family_descends (prefixWord ++ tailWord_746794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746801 : List Nat := [1, 2, 2, 3, 3, 2, 3, 1, 2, 4]
def baseStart_746801 : Nat := 118140960795 + 746801 * 2 ^ 59
def prefixEnd_746801 : Nat := 4983230072969 + 3 ^ 40 * 746801 * 2
def baseEnd_746801 : Nat := 127822622086145957117677

theorem tailTrace_746801 : CollatzResearch.WordTrace tailWord_746801 prefixEnd_746801 127822622086145957117677 := by
  unfold tailWord_746801
  simp only [CollatzResearch.WordTrace]
  refine ⟨27238070167474995301656257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18158713444983330201104171 27238070167474995301656257)
  ·
    refine ⟨20428552625606246476242193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27238070167474995301656257 20428552625606246476242193)
    ·
      refine ⟨15321414469204684857181645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20428552625606246476242193 15321414469204684857181645)
      ·
        refine ⟨5745530425951756821443117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15321414469204684857181645 5745530425951756821443117)
        ·
          refine ⟨2154573909731908808041169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5745530425951756821443117 2154573909731908808041169)
          ·
            refine ⟨1615930432298931606030877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2154573909731908808041169 1615930432298931606030877)
            ·
              refine ⟨605973912112099352261579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1615930432298931606030877 605973912112099352261579)
              ·
                refine ⟨908960868168149028392369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605973912112099352261579 908960868168149028392369)
                ·
                  refine ⟨681720651126111771294277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 908960868168149028392369 681720651126111771294277)
                  ·
                    refine ⟨127822622086145957117677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 681720651126111771294277 127822622086145957117677)
                    ·
                      rfl

theorem cell23_746801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 2, 4].length) (baseStart_746801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746801 prefixEnd_746801 := by exact prefixLift 746801
  have htrace : WordTrace (prefixWord ++ tailWord_746801) baseStart_746801 baseEnd_746801 := by
    simpa [prefixWord, tailWord_746801, baseEnd_746801] using wordTrace_append hprefix tailTrace_746801
  have hstable : (prefixWord ++ tailWord_746801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746801).length < 2 ^ (prefixWord ++ tailWord_746801).sum := by decide
  have hdescent : baseEnd_746801 < baseStart_746801 := by decide
  rcases family_descends (prefixWord ++ tailWord_746801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746834 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2]
def baseStart_746834 : Nat := 118140960795 + 746834 * 2 ^ 59
def prefixEnd_746834 : Nat := 4983230072969 + 3 ^ 40 * 746834 * 2
def baseEnd_746834 : Nat := 383484811120036242240379

theorem tailTrace_746834 : CollatzResearch.WordTrace tailWord_746834 prefixEnd_746834 383484811120036242240379 := by
  unfold tailWord_746834
  simp only [CollatzResearch.WordTrace]
  refine ⟨6809818444088860484401889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18159515850903627958405037 6809818444088860484401889)
  ·
    refine ⟨5107363833066645363301417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6809818444088860484401889 5107363833066645363301417)
    ·
      refine ⟨3830522874799984022476063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5107363833066645363301417 3830522874799984022476063)
      ·
        refine ⟨5745784312199976033714095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3830522874799984022476063 5745784312199976033714095)
        ·
          refine ⟨8618676468299964050571143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5745784312199976033714095 8618676468299964050571143)
          ·
            refine ⟨12928014702449946075856715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8618676468299964050571143 12928014702449946075856715)
            ·
              refine ⟨19392022053674919113785073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12928014702449946075856715 19392022053674919113785073)
              ·
                refine ⟨14544016540256189335338805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19392022053674919113785073 14544016540256189335338805)
                ·
                  refine ⟨1363501550649017750188013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14544016540256189335338805 1363501550649017750188013)
                  ·
                    refine ⟨511313081493381656320505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1363501550649017750188013 511313081493381656320505)
                    ·
                      refine ⟨383484811120036242240379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 511313081493381656320505 383484811120036242240379)
                      ·
                        rfl

theorem cell23_746834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_746834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746834 prefixEnd_746834 := by exact prefixLift 746834
  have htrace : WordTrace (prefixWord ++ tailWord_746834) baseStart_746834 baseEnd_746834 := by
    simpa [prefixWord, tailWord_746834, baseEnd_746834] using wordTrace_append hprefix tailTrace_746834
  have hstable : (prefixWord ++ tailWord_746834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746834).length < 2 ^ (prefixWord ++ tailWord_746834).sum := by decide
  have hdescent : baseEnd_746834 < baseStart_746834 := by decide
  rcases family_descends (prefixWord ++ tailWord_746834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746858 : List Nat := [3, 1, 3, 3, 2, 1, 1, 3, 2, 1, 3]
def baseStart_746858 : Nat := 118140960795 + 746858 * 2 ^ 59
def prefixEnd_746858 : Nat := 4983230072969 + 3 ^ 40 * 746858 * 2
def baseEnd_746858 : Nat := 383497134655744148340269

theorem tailTrace_746858 : CollatzResearch.WordTrace tailWord_746858 prefixEnd_746858 383497134655744148340269 := by
  unfold tailWord_746858
  simp only [CollatzResearch.WordTrace]
  refine ⟨6810037282067123509120307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18160099418845662690987485 6810037282067123509120307)
  ·
    refine ⟨10215055923100685263680461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6810037282067123509120307 10215055923100685263680461)
    ·
      refine ⟨3830645971162756973880173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10215055923100685263680461 3830645971162756973880173)
      ·
        refine ⟨1436492239186033865205065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3830645971162756973880173 1436492239186033865205065)
        ·
          refine ⟨1077369179389525398903799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1436492239186033865205065 1077369179389525398903799)
          ·
            refine ⟨1616053769084288098355699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077369179389525398903799 1616053769084288098355699)
            ·
              refine ⟨2424080653626432147533549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1616053769084288098355699 2424080653626432147533549)
              ·
                refine ⟨909030245109912055325081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2424080653626432147533549 909030245109912055325081)
                ·
                  refine ⟨681772683832434041493811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 909030245109912055325081 681772683832434041493811)
                  ·
                    refine ⟨1022659025748651062240717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 681772683832434041493811 1022659025748651062240717)
                    ·
                      refine ⟨383497134655744148340269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1022659025748651062240717 383497134655744148340269)
                      ·
                        rfl

theorem cell23_746858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_746858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746858 prefixEnd_746858 := by exact prefixLift 746858
  have htrace : WordTrace (prefixWord ++ tailWord_746858) baseStart_746858 baseEnd_746858 := by
    simpa [prefixWord, tailWord_746858, baseEnd_746858] using wordTrace_append hprefix tailTrace_746858
  have hstable : (prefixWord ++ tailWord_746858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746858).length < 2 ^ (prefixWord ++ tailWord_746858).sum := by decide
  have hdescent : baseEnd_746858 < baseStart_746858 := by decide
  rcases family_descends (prefixWord ++ tailWord_746858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746864 : List Nat := [2, 1, 1, 1, 4, 2, 2, 3, 1, 4, 2]
def baseStart_746864 : Nat := 118140960795 + 746864 * 2 ^ 59
def prefixEnd_746864 : Nat := 4983230072969 + 3 ^ 40 * 746864 * 2
def baseEnd_746864 : Nat := 383500215539671124865241

theorem tailTrace_746864 : CollatzResearch.WordTrace tailWord_746864 prefixEnd_746864 383500215539671124865241 := by
  unfold tailWord_746864
  simp only [CollatzResearch.WordTrace]
  refine ⟨13620183983123378530599823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18160245310831171374133097 13620183983123378530599823)
  ·
    refine ⟨20430275974685067795899735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13620183983123378530599823 20430275974685067795899735)
    ·
      refine ⟨30645413962027601693849603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20430275974685067795899735 30645413962027601693849603)
      ·
        refine ⟨45968120943041402540774405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30645413962027601693849603 45968120943041402540774405)
        ·
          refine ⟨8619022676820262976395201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45968120943041402540774405 8619022676820262976395201)
          ·
            refine ⟨6464267007615197232296401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8619022676820262976395201 6464267007615197232296401)
            ·
              refine ⟨4848200255711397924222301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6464267007615197232296401 4848200255711397924222301)
              ·
                refine ⟨1818075095891774221583363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4848200255711397924222301 1818075095891774221583363)
                ·
                  refine ⟨2727112643837661332375045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1818075095891774221583363 2727112643837661332375045)
                  ·
                    refine ⟨511333620719561499820321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2727112643837661332375045 511333620719561499820321)
                    ·
                      refine ⟨383500215539671124865241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 511333620719561499820321 383500215539671124865241)
                      ·
                        rfl

theorem cell23_746864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 1, 4, 2].length) (baseStart_746864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746864 prefixEnd_746864 := by exact prefixLift 746864
  have htrace : WordTrace (prefixWord ++ tailWord_746864) baseStart_746864 baseEnd_746864 := by
    simpa [prefixWord, tailWord_746864, baseEnd_746864] using wordTrace_append hprefix tailTrace_746864
  have hstable : (prefixWord ++ tailWord_746864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746864).length < 2 ^ (prefixWord ++ tailWord_746864).sum := by decide
  have hdescent : baseEnd_746864 < baseStart_746864 := by decide
  rcases family_descends (prefixWord ++ tailWord_746864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746897 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 3]
def baseStart_746897 : Nat := 118140960795 + 746897 * 2 ^ 59
def prefixEnd_746897 : Nat := 4983230072969 + 3 ^ 40 * 746897 * 2
def baseEnd_746897 : Nat := 383517160401269495752589

theorem tailTrace_746897 : CollatzResearch.WordTrace tailWord_746897 prefixEnd_746897 383517160401269495752589 := by
  unfold tailWord_746897
  simp only [CollatzResearch.WordTrace]
  refine ⟨27241571575127203697150945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18161047716751469131433963 27241571575127203697150945)
  ·
    refine ⟨20431178681345402772863209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27241571575127203697150945 20431178681345402772863209)
    ·
      refine ⟨15323384011009052079647407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20431178681345402772863209 15323384011009052079647407)
      ·
        refine ⟨22985076016513578119471111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15323384011009052079647407 22985076016513578119471111)
        ·
          refine ⟨34477614024770367179206667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22985076016513578119471111 34477614024770367179206667)
          ·
            refine ⟨51716421037155550768810001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34477614024770367179206667 51716421037155550768810001)
            ·
              refine ⟨38787315777866663076607501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51716421037155550768810001 38787315777866663076607501)
              ·
                refine ⟨14545243416699998653727813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38787315777866663076607501 14545243416699998653727813)
                ·
                  refine ⟨2727233140631249747573965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14545243416699998653727813 2727233140631249747573965)
                  ·
                    refine ⟨1022712427736718655340237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2727233140631249747573965 1022712427736718655340237)
                    ·
                      refine ⟨383517160401269495752589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1022712427736718655340237 383517160401269495752589)
                      ·
                        rfl

theorem cell23_746897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_746897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746897 prefixEnd_746897 := by exact prefixLift 746897
  have htrace : WordTrace (prefixWord ++ tailWord_746897) baseStart_746897 baseEnd_746897 := by
    simpa [prefixWord, tailWord_746897, baseEnd_746897] using wordTrace_append hprefix tailTrace_746897
  have hstable : (prefixWord ++ tailWord_746897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746897).length < 2 ^ (prefixWord ++ tailWord_746897).sum := by decide
  have hdescent : baseEnd_746897 < baseStart_746897 := by decide
  rcases family_descends (prefixWord ++ tailWord_746897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746914 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_746914 : Nat := 118140960795 + 746914 * 2 ^ 59
def prefixEnd_746914 : Nat := 4983230072969 + 3 ^ 40 * 746914 * 2
def baseEnd_746914 : Nat := 383525889572395929240011

theorem tailTrace_746914 : CollatzResearch.WordTrace tailWord_746914 prefixEnd_746914 383525889572395929240011 := by
  unfold tailWord_746914
  simp only [CollatzResearch.WordTrace]
  refine ⟨6810547904016403900129949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18161461077377077067013197 6810547904016403900129949)
  ·
    refine ⟨2553955464006151462548731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6810547904016403900129949 2553955464006151462548731)
    ·
      refine ⟨3830933196009227193823097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2553955464006151462548731 3830933196009227193823097)
      ·
        refine ⟨2873199897006920395367323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3830933196009227193823097 2873199897006920395367323)
        ·
          refine ⟨4309799845510380593050985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2873199897006920395367323 4309799845510380593050985)
          ·
            refine ⟨3232349884132785444788239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4309799845510380593050985 3232349884132785444788239)
            ·
              refine ⟨4848524826199178167182359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3232349884132785444788239 4848524826199178167182359)
              ·
                refine ⟨7272787239298767250773539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4848524826199178167182359 7272787239298767250773539)
                ·
                  refine ⟨10909180858948150876160309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7272787239298767250773539 10909180858948150876160309)
                  ·
                    refine ⟨1022735705526389144640029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10909180858948150876160309 1022735705526389144640029)
                    ·
                      refine ⟨383525889572395929240011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1022735705526389144640029 383525889572395929240011)
                      ·
                        rfl

theorem cell23_746914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_746914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746914 prefixEnd_746914 := by exact prefixLift 746914
  have htrace : WordTrace (prefixWord ++ tailWord_746914) baseStart_746914 baseEnd_746914 := by
    simpa [prefixWord, tailWord_746914, baseEnd_746914] using wordTrace_append hprefix tailTrace_746914
  have hstable : (prefixWord ++ tailWord_746914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746914).length < 2 ^ (prefixWord ++ tailWord_746914).sum := by decide
  have hdescent : baseEnd_746914 < baseStart_746914 := by decide
  rcases family_descends (prefixWord ++ tailWord_746914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746981 : List Nat := [1, 3, 1, 5, 1, 1, 2, 2, 3, 4]
def baseStart_746981 : Nat := 118140960795 + 746981 * 2 ^ 59
def prefixEnd_746981 : Nat := 4983230072969 + 3 ^ 40 * 746981 * 2
def baseEnd_746981 : Nat := 127853430925415722367401

theorem tailTrace_746981 : CollatzResearch.WordTrace tailWord_746981 prefixEnd_746981 127853430925415722367401 := by
  unfold tailWord_746981
  simp only [CollatzResearch.WordTrace]
  refine ⟨27244635306822886043208797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18163090204548590695472531 27244635306822886043208797)
  ·
    refine ⟨10216738240058582266203299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27244635306822886043208797 10216738240058582266203299)
    ·
      refine ⟨15325107360087873399304949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10216738240058582266203299 15325107360087873399304949)
      ·
        refine ⟨1436728815008238131184839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15325107360087873399304949 1436728815008238131184839)
        ·
          refine ⟨2155093222512357196777259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1436728815008238131184839 2155093222512357196777259)
          ·
            refine ⟨3232639833768535795165889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2155093222512357196777259 3232639833768535795165889)
            ·
              refine ⟨2424479875326401846374417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3232639833768535795165889 2424479875326401846374417)
              ·
                refine ⟨1818359906494801384780813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2424479875326401846374417 1818359906494801384780813)
                ·
                  refine ⟨681884964935550519292805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1818359906494801384780813 681884964935550519292805)
                  ·
                    refine ⟨127853430925415722367401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 681884964935550519292805 127853430925415722367401)
                    ·
                      rfl

theorem cell23_746981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 4].length) (baseStart_746981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746981 prefixEnd_746981 := by exact prefixLift 746981
  have htrace : WordTrace (prefixWord ++ tailWord_746981) baseStart_746981 baseEnd_746981 := by
    simpa [prefixWord, tailWord_746981, baseEnd_746981] using wordTrace_append hprefix tailTrace_746981
  have hstable : (prefixWord ++ tailWord_746981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746981).length < 2 ^ (prefixWord ++ tailWord_746981).sum := by decide
  have hdescent : baseEnd_746981 < baseStart_746981 := by decide
  rcases family_descends (prefixWord ++ tailWord_746981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746994 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 8]
def baseStart_746994 : Nat := 118140960795 + 746994 * 2 ^ 59
def prefixEnd_746994 : Nat := 4983230072969 + 3 ^ 40 * 746994 * 2
def baseEnd_746994 : Nat := 42618552002750624026627

theorem tailTrace_746994 : CollatzResearch.WordTrace tailWord_746994 prefixEnd_746994 42618552002750624026627 := by
  unfold tailWord_746994
  simp only [CollatzResearch.WordTrace]
  refine ⟨6811277363943947315858009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18163406303850526175621357 6811277363943947315858009)
  ·
    refine ⟨5108458022957960486893507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6811277363943947315858009 5108458022957960486893507)
    ·
      refine ⟨7662687034436940730340261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5108458022957960486893507 7662687034436940730340261)
      ·
        refine ⟨1436753818956926386938799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7662687034436940730340261 1436753818956926386938799)
        ·
          refine ⟨2155130728435389580408199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1436753818956926386938799 2155130728435389580408199)
          ·
            refine ⟨3232696092653084370612299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2155130728435389580408199 3232696092653084370612299)
            ·
              refine ⟨4849044138979626555918449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3232696092653084370612299 4849044138979626555918449)
              ·
                refine ⟨3636783104234719916938837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4849044138979626555918449 3636783104234719916938837)
                ·
                  refine ⟨42618552002750624026627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3636783104234719916938837 42618552002750624026627)
                  ·
                    rfl

theorem cell23_746994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_746994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746994 prefixEnd_746994 := by exact prefixLift 746994
  have htrace : WordTrace (prefixWord ++ tailWord_746994) baseStart_746994 baseEnd_746994 := by
    simpa [prefixWord, tailWord_746994, baseEnd_746994] using wordTrace_append hprefix tailTrace_746994
  have hstable : (prefixWord ++ tailWord_746994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746994).length < 2 ^ (prefixWord ++ tailWord_746994).sum := by decide
  have hdescent : baseEnd_746994 < baseStart_746994 := by decide
  rcases family_descends (prefixWord ++ tailWord_746994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747015 : List Nat := [1, 1, 4, 3, 2, 2, 3, 2, 1, 4]
def baseStart_747015 : Nat := 118140960795 + 747015 * 2 ^ 59
def prefixEnd_747015 : Nat := 4983230072969 + 3 ^ 40 * 747015 * 2
def baseEnd_747015 : Nat := 127859250372833344692349

theorem tailTrace_747015 : CollatzResearch.WordTrace tailWord_747015 prefixEnd_747015 127859250372833344692349 := by
  unfold tailWord_747015
  simp only [CollatzResearch.WordTrace]
  refine ⟨27245875388699709849946499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18163916925799806566630999 27245875388699709849946499)
  ·
    refine ⟨40868813083049564774919749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27245875388699709849946499 40868813083049564774919749)
    ·
      refine ⟨7662902453071793395297453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40868813083049564774919749 7662902453071793395297453)
      ·
        refine ⟨2873588419901922523236545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7662902453071793395297453 2873588419901922523236545)
        ·
          refine ⟨2155191314926441892427409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2873588419901922523236545 2155191314926441892427409)
          ·
            refine ⟨1616393486194831419320557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2155191314926441892427409 1616393486194831419320557)
            ·
              refine ⟨606147557323061782245209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1616393486194831419320557 606147557323061782245209)
              ·
                refine ⟨454610667992296336683907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 606147557323061782245209 454610667992296336683907)
                ·
                  refine ⟨681916001988444505025861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454610667992296336683907 681916001988444505025861)
                  ·
                    refine ⟨127859250372833344692349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 681916001988444505025861 127859250372833344692349)
                    ·
                      rfl

theorem cell23_747015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_747015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747015 prefixEnd_747015 := by exact prefixLift 747015
  have htrace : WordTrace (prefixWord ++ tailWord_747015) baseStart_747015 baseEnd_747015 := by
    simpa [prefixWord, tailWord_747015, baseEnd_747015] using wordTrace_append hprefix tailTrace_747015
  have hstable : (prefixWord ++ tailWord_747015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747015).length < 2 ^ (prefixWord ++ tailWord_747015).sum := by decide
  have hdescent : baseEnd_747015 < baseStart_747015 := by decide
  rcases family_descends (prefixWord ++ tailWord_747015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747028 : List Nat := [2, 4, 3, 1, 2, 1, 1, 3, 6]
def baseStart_747028 : Nat := 118140960795 + 747028 * 2 ^ 59
def prefixEnd_747028 : Nat := 4983230072969 + 3 ^ 40 * 747028 * 2
def baseEnd_747028 : Nat := 42620491818556498134943

theorem tailTrace_747028 : CollatzResearch.WordTrace tailWord_747028 prefixEnd_747028 42620491818556498134943 := by
  unfold tailWord_747028
  simp only [CollatzResearch.WordTrace]
  refine ⟨13623174768826306535084869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18164233025101742046779825 13623174768826306535084869)
  ·
    refine ⟨2554345269154932475328413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13623174768826306535084869 2554345269154932475328413)
    ·
      refine ⟨957879475933099678248155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2554345269154932475328413 957879475933099678248155)
      ·
        refine ⟨1436819213899649517372233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 957879475933099678248155 1436819213899649517372233)
        ·
          refine ⟨1077614410424737138029175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1436819213899649517372233 1077614410424737138029175)
          ·
            refine ⟨1616421615637105707043763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077614410424737138029175 1616421615637105707043763)
            ·
              refine ⟨2424632423455658560565645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1616421615637105707043763 2424632423455658560565645)
              ·
                refine ⟨909237158795871960212117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2424632423455658560565645 909237158795871960212117)
                ·
                  refine ⟨42620491818556498134943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 909237158795871960212117 42620491818556498134943)
                  ·
                    rfl

theorem cell23_747028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_747028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747028 prefixEnd_747028 := by exact prefixLift 747028
  have htrace : WordTrace (prefixWord ++ tailWord_747028) baseStart_747028 baseEnd_747028 := by
    simpa [prefixWord, tailWord_747028, baseEnd_747028] using wordTrace_append hprefix tailTrace_747028
  have hstable : (prefixWord ++ tailWord_747028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747028).length < 2 ^ (prefixWord ++ tailWord_747028).sum := by decide
  have hdescent : baseEnd_747028 < baseStart_747028 := by decide
  rcases family_descends (prefixWord ++ tailWord_747028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747041 : List Nat := [1, 2, 3, 2, 2, 2, 3, 2, 1, 5]
def baseStart_747041 : Nat := 118140960795 + 747041 * 2 ^ 59
def prefixEnd_747041 : Nat := 4983230072969 + 3 ^ 40 * 747041 * 2
def baseEnd_747041 : Nat := 127863700538505644117309

theorem tailTrace_747041 : CollatzResearch.WordTrace tailWord_747041 prefixEnd_747041 127863700538505644117309 := by
  unfold tailWord_747041
  simp only [CollatzResearch.WordTrace]
  refine ⟨27246823686605516290392977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18164549124403677526928651 27246823686605516290392977)
  ·
    refine ⟨20435117764954137217794733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27246823686605516290392977 20435117764954137217794733)
    ·
      refine ⟨7663169161857801456673025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20435117764954137217794733 7663169161857801456673025)
      ·
        refine ⟨5747376871393351092504769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7663169161857801456673025 5747376871393351092504769)
        ·
          refine ⟨4310532653545013319378577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5747376871393351092504769 4310532653545013319378577)
          ·
            refine ⟨3232899490158759989533933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4310532653545013319378577 3232899490158759989533933)
            ·
              refine ⟨1212337308809534996075225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3232899490158759989533933 1212337308809534996075225)
              ·
                refine ⟨909252981607151247056419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1212337308809534996075225 909252981607151247056419)
                ·
                  refine ⟨1363879472410726870584629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 909252981607151247056419 1363879472410726870584629)
                  ·
                    refine ⟨127863700538505644117309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1363879472410726870584629 127863700538505644117309)
                    ·
                      rfl

theorem cell23_747041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_747041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747041 prefixEnd_747041 := by exact prefixLift 747041
  have htrace : WordTrace (prefixWord ++ tailWord_747041) baseStart_747041 baseEnd_747041 := by
    simpa [prefixWord, tailWord_747041, baseEnd_747041] using wordTrace_append hprefix tailTrace_747041
  have hstable : (prefixWord ++ tailWord_747041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747041).length < 2 ^ (prefixWord ++ tailWord_747041).sum := by decide
  have hdescent : baseEnd_747041 < baseStart_747041 := by decide
  rcases family_descends (prefixWord ++ tailWord_747041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747071 : List Nat := [1, 1, 2, 2, 3, 3, 1, 4, 2, 4]
def baseStart_747071 : Nat := 118140960795 + 747071 * 2 ^ 59
def prefixEnd_747071 : Nat := 4983230072969 + 3 ^ 40 * 747071 * 2
def baseEnd_747071 : Nat := 127868835345050604992263

theorem tailTrace_747071 : CollatzResearch.WordTrace tailWord_747071 prefixEnd_747071 127868835345050604992263 := by
  unfold tailWord_747071
  simp only [CollatzResearch.WordTrace]
  refine ⟨27247917876496831413985067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18165278584331220942656711 27247917876496831413985067)
  ·
    refine ⟨40871876814745247120977601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27247917876496831413985067 40871876814745247120977601)
    ·
      refine ⟨30653907611058935340733201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40871876814745247120977601 30653907611058935340733201)
      ·
        refine ⟨22990430708294201505549901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30653907611058935340733201 22990430708294201505549901)
        ·
          refine ⟨8621411515610325564581213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22990430708294201505549901 8621411515610325564581213)
          ·
            refine ⟨3233029318353872086717955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8621411515610325564581213 3233029318353872086717955)
            ·
              refine ⟨4849543977530808130076933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3233029318353872086717955 4849543977530808130076933)
              ·
                refine ⟨909289495787026524389425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4849543977530808130076933 909289495787026524389425)
                ·
                  refine ⟨681967121840269893292069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 909289495787026524389425 681967121840269893292069)
                  ·
                    refine ⟨127868835345050604992263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 681967121840269893292069 127868835345050604992263)
                    ·
                      rfl

theorem cell23_747071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 4].length) (baseStart_747071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747071 prefixEnd_747071 := by exact prefixLift 747071
  have htrace : WordTrace (prefixWord ++ tailWord_747071) baseStart_747071 baseEnd_747071 := by
    simpa [prefixWord, tailWord_747071, baseEnd_747071] using wordTrace_append hprefix tailTrace_747071
  have hstable : (prefixWord ++ tailWord_747071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747071).length < 2 ^ (prefixWord ++ tailWord_747071).sum := by decide
  have hdescent : baseEnd_747071 < baseStart_747071 := by decide
  rcases family_descends (prefixWord ++ tailWord_747071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747084 : List Nat := [2, 2, 1, 3, 1, 3, 3, 8]
def baseStart_747084 : Nat := 118140960795 + 747084 * 2 ^ 59
def prefixEnd_747084 : Nat := 4983230072969 + 3 ^ 40 * 747084 * 2
def baseEnd_747084 : Nat := 14207895603098528300527

theorem tailTrace_747084 : CollatzResearch.WordTrace tailWord_747084 prefixEnd_747084 14207895603098528300527 := by
  unfold tailWord_747084
  simp only [CollatzResearch.WordTrace]
  refine ⟨13624196012724867317104153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18165594683633156422805537 13624196012724867317104153)
  ·
    refine ⟨10218147009543650487828115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13624196012724867317104153 10218147009543650487828115)
    ·
      refine ⟨15327220514315475731742173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10218147009543650487828115 15327220514315475731742173)
      ·
        refine ⟨5747707692868303399403315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15327220514315475731742173 5747707692868303399403315)
        ·
          refine ⟨8621561539302455099104973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5747707692868303399403315 8621561539302455099104973)
          ·
            refine ⟨3233085577238420662164365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8621561539302455099104973 3233085577238420662164365)
            ·
              refine ⟨1212407091464407748311637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3233085577238420662164365 1212407091464407748311637)
              ·
                refine ⟨14207895603098528300527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1212407091464407748311637 14207895603098528300527)
                ·
                  rfl

theorem cell23_747084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 8].length) (baseStart_747084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747084 prefixEnd_747084 := by exact prefixLift 747084
  have htrace : WordTrace (prefixWord ++ tailWord_747084) baseStart_747084 baseEnd_747084 := by
    simpa [prefixWord, tailWord_747084, baseEnd_747084] using wordTrace_append hprefix tailTrace_747084
  have hstable : (prefixWord ++ tailWord_747084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747084).length < 2 ^ (prefixWord ++ tailWord_747084).sum := by decide
  have hdescent : baseEnd_747084 < baseStart_747084 := by decide
  rcases family_descends (prefixWord ++ tailWord_747084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747111 : List Nat := [1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_747111 : Nat := 118140960795 + 747111 * 2 ^ 59
def prefixEnd_747111 : Nat := 4983230072969 + 3 ^ 40 * 747111 * 2
def baseEnd_747111 : Nat := 383627045261331658476605

theorem tailTrace_747111 : CollatzResearch.WordTrace tailWord_747111 prefixEnd_747111 383627045261331658476605 := by
  unfold tailWord_747111
  simp only [CollatzResearch.WordTrace]
  refine ⟨27249376796351918245441187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18166251197567945496960791 27249376796351918245441187)
  ·
    refine ⟨40874065194527877368161781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27249376796351918245441187 40874065194527877368161781)
    ·
      refine ⟨3831943611986988503265167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40874065194527877368161781 3831943611986988503265167)
      ·
        refine ⟨5747915417980482754897751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3831943611986988503265167 5747915417980482754897751)
        ·
          refine ⟨8621873126970724132346627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5747915417980482754897751 8621873126970724132346627)
          ·
            refine ⟨12932809690456086198519941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8621873126970724132346627 12932809690456086198519941)
            ·
              refine ⟨2424901816960516162222489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12932809690456086198519941 2424901816960516162222489)
              ·
                refine ⟨1818676362720387121666867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2424901816960516162222489 1818676362720387121666867)
                ·
                  refine ⟨2728014544080580682500301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1818676362720387121666867 2728014544080580682500301)
                  ·
                    refine ⟨1023005454030217755937613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2728014544080580682500301 1023005454030217755937613)
                    ·
                      refine ⟨383627045261331658476605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1023005454030217755937613 383627045261331658476605)
                      ·
                        rfl

theorem cell23_747111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_747111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747111 prefixEnd_747111 := by exact prefixLift 747111
  have htrace : WordTrace (prefixWord ++ tailWord_747111) baseStart_747111 baseEnd_747111 := by
    simpa [prefixWord, tailWord_747111, baseEnd_747111] using wordTrace_append hprefix tailTrace_747111
  have hstable : (prefixWord ++ tailWord_747111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747111).length < 2 ^ (prefixWord ++ tailWord_747111).sum := by decide
  have hdescent : baseEnd_747111 < baseStart_747111 := by decide
  rcases family_descends (prefixWord ++ tailWord_747111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747112 : List Nat := [2, 1, 4, 3, 1, 1, 1, 5, 1, 2, 2]
def baseStart_747112 : Nat := 118140960795 + 747112 * 2 ^ 59
def prefixEnd_747112 : Nat := 4983230072969 + 3 ^ 40 * 747112 * 2
def baseEnd_747112 : Nat := 383627558741986154564101

theorem tailTrace_747112 : CollatzResearch.WordTrace tailWord_747112 prefixEnd_747112 383627558741986154564101 := by
  unfold tailWord_747112
  simp only [CollatzResearch.WordTrace]
  refine ⟨13624706634674147708113795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18166275512898863610818393 13624706634674147708113795)
  ·
    refine ⟨20437059952011221562170693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13624706634674147708113795 20437059952011221562170693)
    ·
      refine ⟨3831948741002104042907005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20437059952011221562170693 3831948741002104042907005)
      ·
        refine ⟨1436980777875789016090127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3831948741002104042907005 1436980777875789016090127)
        ·
          refine ⟨2155471166813683524135191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1436980777875789016090127 2155471166813683524135191)
          ·
            refine ⟨3233206750220525286202787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2155471166813683524135191 3233206750220525286202787)
            ·
              refine ⟨4849810125330787929304181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3233206750220525286202787 4849810125330787929304181)
              ·
                refine ⟨454669699249761368372267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4849810125330787929304181 454669699249761368372267)
                ·
                  refine ⟨682004548874642052558401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454669699249761368372267 682004548874642052558401)
                  ·
                    refine ⟨511503411655981539418801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 682004548874642052558401 511503411655981539418801)
                    ·
                      refine ⟨383627558741986154564101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 511503411655981539418801 383627558741986154564101)
                      ·
                        rfl

theorem cell23_747112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_747112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747112 prefixEnd_747112 := by exact prefixLift 747112
  have htrace : WordTrace (prefixWord ++ tailWord_747112) baseStart_747112 baseEnd_747112 := by
    simpa [prefixWord, tailWord_747112, baseEnd_747112] using wordTrace_append hprefix tailTrace_747112
  have hstable : (prefixWord ++ tailWord_747112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747112).length < 2 ^ (prefixWord ++ tailWord_747112).sum := by decide
  have hdescent : baseEnd_747112 < baseStart_747112 := by decide
  rcases family_descends (prefixWord ++ tailWord_747112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747191 : List Nat := [1, 1, 3, 1, 5, 1, 3, 1, 7]
def baseStart_747191 : Nat := 118140960795 + 747191 * 2 ^ 59
def prefixEnd_747191 : Nat := 4983230072969 + 3 ^ 40 * 747191 * 2
def baseEnd_747191 : Nat := 42629791523743482830693

theorem tailTrace_747191 : CollatzResearch.WordTrace tailWord_747191 prefixEnd_747191 42629791523743482830693 := by
  unfold tailWord_747191
  simp only [CollatzResearch.WordTrace]
  refine ⟨27252294636062091908353427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18168196424041394605568951 27252294636062091908353427)
  ·
    refine ⟨40878441954093137862530141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27252294636062091908353427 40878441954093137862530141)
    ·
      refine ⟨15329415732784926698448803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40878441954093137862530141 15329415732784926698448803)
      ·
        refine ⟨22994123599177390047673205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15329415732784926698448803 22994123599177390047673205)
        ·
          refine ⟨2155699087422880316969363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22994123599177390047673205 2155699087422880316969363)
          ·
            refine ⟨3233548631134320475454045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2155699087422880316969363 3233548631134320475454045)
            ·
              refine ⟨1212580736675370178295267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3233548631134320475454045 1212580736675370178295267)
              ·
                refine ⟨1818871105013055267442901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1212580736675370178295267 1818871105013055267442901)
                ·
                  refine ⟨42629791523743482830693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1818871105013055267442901 42629791523743482830693)
                  ·
                    rfl

theorem cell23_747191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 7].length) (baseStart_747191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747191 prefixEnd_747191 := by exact prefixLift 747191
  have htrace : WordTrace (prefixWord ++ tailWord_747191) baseStart_747191 baseEnd_747191 := by
    simpa [prefixWord, tailWord_747191, baseEnd_747191] using wordTrace_append hprefix tailTrace_747191
  have hstable : (prefixWord ++ tailWord_747191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747191).length < 2 ^ (prefixWord ++ tailWord_747191).sum := by decide
  have hdescent : baseEnd_747191 < baseStart_747191 := by decide
  rcases family_descends (prefixWord ++ tailWord_747191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747206 : List Nat := [6, 1, 2, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_747206 : Nat := 118140960795 + 747206 * 2 ^ 59
def prefixEnd_747206 : Nat := 4983230072969 + 3 ^ 40 * 747206 * 2
def baseEnd_747206 : Nat := 383675825923508786788669

theorem tailTrace_747206 : CollatzResearch.WordTrace tailWord_747206 prefixEnd_747206 383675825923508786788669 := by
  unfold tailWord_747206
  simp only [CollatzResearch.WordTrace]
  refine ⟨851651304093992170942171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18168561154005166313432981 851651304093992170942171)
  ·
    refine ⟨1277476956140988256413257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 851651304093992170942171 1277476956140988256413257)
    ·
      refine ⟨958107717105741192309943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1277476956140988256413257 958107717105741192309943)
      ·
        refine ⟨1437161575658611788464915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 958107717105741192309943 1437161575658611788464915)
        ·
          refine ⟨2155742363487917682697373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1437161575658611788464915 2155742363487917682697373)
          ·
            refine ⟨808403386307969131011515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2155742363487917682697373 808403386307969131011515)
            ·
              refine ⟨1212605079461953696517273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808403386307969131011515 1212605079461953696517273)
              ·
                refine ⟨909453809596465272387955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1212605079461953696517273 909453809596465272387955)
                ·
                  refine ⟨1364180714394697908581933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 909453809596465272387955 1364180714394697908581933)
                  ·
                    refine ⟨511567767898011715718225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1364180714394697908581933 511567767898011715718225)
                    ·
                      refine ⟨383675825923508786788669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 511567767898011715718225 383675825923508786788669)
                      ·
                        rfl

theorem cell23_747206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_747206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747206 prefixEnd_747206 := by exact prefixLift 747206
  have htrace : WordTrace (prefixWord ++ tailWord_747206) baseStart_747206 baseEnd_747206 := by
    simpa [prefixWord, tailWord_747206, baseEnd_747206] using wordTrace_append hprefix tailTrace_747206
  have hstable : (prefixWord ++ tailWord_747206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747206).length < 2 ^ (prefixWord ++ tailWord_747206).sum := by decide
  have hdescent : baseEnd_747206 < baseStart_747206 := by decide
  rcases family_descends (prefixWord ++ tailWord_747206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747252 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_747252 : Nat := 118140960795 + 747252 * 2 ^ 59
def prefixEnd_747252 : Nat := 4983230072969 + 3 ^ 40 * 747252 * 2
def baseEnd_747252 : Nat := 383699446033615606813457

theorem tailTrace_747252 : CollatzResearch.WordTrace tailWord_747252 prefixEnd_747252 383699446033615606813457 := by
  unfold tailWord_747252
  simp only [CollatzResearch.WordTrace]
  refine ⟨13627259744420549663162005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18169679659227399550882673 13627259744420549663162005)
  ·
    refine ⟨638777800519713265460719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13627259744420549663162005 638777800519713265460719)
    ·
      refine ⟨958166700779569898191079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 638777800519713265460719 958166700779569898191079)
      ·
        refine ⟨1437250051169354847286619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 958166700779569898191079 1437250051169354847286619)
        ·
          refine ⟨2155875076754032270929929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1437250051169354847286619 2155875076754032270929929)
          ·
            refine ⟨1616906307565524203197447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2155875076754032270929929 1616906307565524203197447)
            ·
              refine ⟨2425359461348286304796171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1616906307565524203197447 2425359461348286304796171)
              ·
                refine ⟨3638039192022429457194257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2425359461348286304796171 3638039192022429457194257)
                ·
                  refine ⟨2728529394016822092895693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3638039192022429457194257 2728529394016822092895693)
                  ·
                    refine ⟨1023198522756308284835885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2728529394016822092895693 1023198522756308284835885)
                    ·
                      refine ⟨383699446033615606813457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1023198522756308284835885 383699446033615606813457)
                      ·
                        rfl

theorem cell23_747252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_747252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747252 prefixEnd_747252 := by exact prefixLift 747252
  have htrace : WordTrace (prefixWord ++ tailWord_747252) baseStart_747252 baseEnd_747252 := by
    simpa [prefixWord, tailWord_747252, baseEnd_747252] using wordTrace_append hprefix tailTrace_747252
  have hstable : (prefixWord ++ tailWord_747252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747252).length < 2 ^ (prefixWord ++ tailWord_747252).sum := by decide
  have hdescent : baseEnd_747252 < baseStart_747252 := by decide
  rcases family_descends (prefixWord ++ tailWord_747252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747268 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 5, 4]
def baseStart_747268 : Nat := 118140960795 + 747268 * 2 ^ 59
def prefixEnd_747268 : Nat := 4983230072969 + 3 ^ 40 * 747268 * 2
def baseEnd_747268 : Nat := 127902553908029181404461

theorem tailTrace_747268 : CollatzResearch.WordTrace tailWord_747268 prefixEnd_747268 127902553908029181404461 := by
  unfold tailWord_747268
  simp only [CollatzResearch.WordTrace]
  refine ⟨13627551528391567029453229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18170068704522089372604305 13627551528391567029453229)
  ·
    refine ⟨5110331823146837636044961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13627551528391567029453229 5110331823146837636044961)
    ·
      refine ⟨3832748867360128227033721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5110331823146837636044961 3832748867360128227033721)
      ·
        refine ⟨2874561650520096170275291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3832748867360128227033721 2874561650520096170275291)
        ·
          refine ⟨4311842475780144255412937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2874561650520096170275291 4311842475780144255412937)
          ·
            refine ⟨3233881856835108191559703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4311842475780144255412937 3233881856835108191559703)
            ·
              refine ⟨4850822785252662287339555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3233881856835108191559703 4850822785252662287339555)
              ·
                refine ⟨7276234177878993431009333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4850822785252662287339555 7276234177878993431009333)
                ·
                  refine ⟨682146954176155634157125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7276234177878993431009333 682146954176155634157125)
                  ·
                    refine ⟨127902553908029181404461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 682146954176155634157125 127902553908029181404461)
                    ·
                      rfl

theorem cell23_747268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_747268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747268 prefixEnd_747268 := by exact prefixLift 747268
  have htrace : WordTrace (prefixWord ++ tailWord_747268) baseStart_747268 baseEnd_747268 := by
    simpa [prefixWord, tailWord_747268, baseEnd_747268] using wordTrace_append hprefix tailTrace_747268
  have hstable : (prefixWord ++ tailWord_747268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747268).length < 2 ^ (prefixWord ++ tailWord_747268).sum := by decide
  have hdescent : baseEnd_747268 < baseStart_747268 := by decide
  rcases family_descends (prefixWord ++ tailWord_747268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747285 : List Nat := [1, 3, 2, 1, 2, 3, 1, 5, 1, 4]
def baseStart_747285 : Nat := 118140960795 + 747285 * 2 ^ 59
def prefixEnd_747285 : Nat := 4983230072969 + 3 ^ 40 * 747285 * 2
def baseEnd_747285 : Nat := 127905463631737992566935

theorem tailTrace_747285 : CollatzResearch.WordTrace tailWord_747285 prefixEnd_747285 127905463631737992566935 := by
  unfold tailWord_747285
  simp only [CollatzResearch.WordTrace]
  refine ⟨27255723097721545962275309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18170482065147697308183539 27255723097721545962275309)
  ·
    refine ⟨10220896161645579735853241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27255723097721545962275309 10220896161645579735853241)
    ·
      refine ⟨7665672121234184801889931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10220896161645579735853241 7665672121234184801889931)
      ·
        refine ⟨11498508181851277202834897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7665672121234184801889931 11498508181851277202834897)
        ·
          refine ⟨8623881136388457902126173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11498508181851277202834897 8623881136388457902126173)
          ·
            refine ⟨3233955426145671713297315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8623881136388457902126173 3233955426145671713297315)
            ·
              refine ⟨4850933139218507569945973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3233955426145671713297315 4850933139218507569945973)
              ·
                refine ⟨454774981801735084682435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4850933139218507569945973 454774981801735084682435)
                ·
                  refine ⟨682162472702602627023653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454774981801735084682435 682162472702602627023653)
                  ·
                    refine ⟨127905463631737992566935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 682162472702602627023653 127905463631737992566935)
                    ·
                      rfl

theorem cell23_747285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_747285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747285 prefixEnd_747285 := by exact prefixLift 747285
  have htrace : WordTrace (prefixWord ++ tailWord_747285) baseStart_747285 baseEnd_747285 := by
    simpa [prefixWord, tailWord_747285, baseEnd_747285] using wordTrace_append hprefix tailTrace_747285
  have hstable : (prefixWord ++ tailWord_747285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747285).length < 2 ^ (prefixWord ++ tailWord_747285).sum := by decide
  have hdescent : baseEnd_747285 < baseStart_747285 := by decide
  rcases family_descends (prefixWord ++ tailWord_747285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747301 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 1, 2, 6]
def baseStart_747301 : Nat := 118140960795 + 747301 * 2 ^ 59
def prefixEnd_747301 : Nat := 4983230072969 + 3 ^ 40 * 747301 * 2
def baseEnd_747301 : Nat := 383724606585685915100731

theorem tailTrace_747301 : CollatzResearch.WordTrace tailWord_747301 prefixEnd_747301 383724606585685915100731 := by
  unfold tailWord_747301
  simp only [CollatzResearch.WordTrace]
  refine ⟨27256306665663580694857757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18170871110442387129905171 27256306665663580694857757)
  ·
    refine ⟨10221114999623842760571659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27256306665663580694857757 10221114999623842760571659)
    ·
      refine ⟨15331672499435764140857489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10221114999623842760571659 15331672499435764140857489)
      ·
        refine ⟨11498754374576823105643117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15331672499435764140857489 11498754374576823105643117)
        ·
          refine ⟨4312032890466308664616169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11498754374576823105643117 4312032890466308664616169)
          ·
            refine ⟨3234024667849731498462127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4312032890466308664616169 3234024667849731498462127)
            ·
              refine ⟨4851037001774597247693191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3234024667849731498462127 4851037001774597247693191)
              ·
                refine ⟨7276555502661895871539787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4851037001774597247693191 7276555502661895871539787)
                ·
                  refine ⟨10914833253992843807309681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7276555502661895871539787 10914833253992843807309681)
                  ·
                    refine ⟨8186124940494632855482261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10914833253992843807309681 8186124940494632855482261)
                    ·
                      refine ⟨383724606585685915100731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8186124940494632855482261 383724606585685915100731)
                      ·
                        rfl

theorem cell23_747301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_747301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747301 prefixEnd_747301 := by exact prefixLift 747301
  have htrace : WordTrace (prefixWord ++ tailWord_747301) baseStart_747301 baseEnd_747301 := by
    simpa [prefixWord, tailWord_747301, baseEnd_747301] using wordTrace_append hprefix tailTrace_747301
  have hstable : (prefixWord ++ tailWord_747301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747301).length < 2 ^ (prefixWord ++ tailWord_747301).sum := by decide
  have hdescent : baseEnd_747301 < baseStart_747301 := by decide
  rcases family_descends (prefixWord ++ tailWord_747301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747315 : List Nat := [1, 1, 1, 2, 7, 1, 3, 1, 6]
def baseStart_747315 : Nat := 118140960795 + 747315 * 2 ^ 59
def prefixEnd_747315 : Nat := 4983230072969 + 3 ^ 40 * 747315 * 2
def baseEnd_747315 : Nat := 42636866146094317813963

theorem tailTrace_747315 : CollatzResearch.WordTrace tailWord_747315 prefixEnd_747315 42636866146094317813963 := by
  unfold tailWord_747315
  simp only [CollatzResearch.WordTrace]
  refine ⟨27256817287612861085867399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18171211525075240723911599 27256817287612861085867399)
  ·
    refine ⟨40885225931419291628801099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27256817287612861085867399 40885225931419291628801099)
    ·
      refine ⟨61327838897128937443201649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40885225931419291628801099 61327838897128937443201649)
      ·
        refine ⟨45995879172846703082401237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61327838897128937443201649 45995879172846703082401237)
        ·
          refine ⟨1078028418113594603493779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 45995879172846703082401237 1078028418113594603493779)
          ·
            refine ⟨1617042627170391905240669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078028418113594603493779 1617042627170391905240669)
            ·
              refine ⟨606390985188896964465251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1617042627170391905240669 606390985188896964465251)
              ·
                refine ⟨909586477783345446697877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 606390985188896964465251 909586477783345446697877)
                ·
                  refine ⟨42636866146094317813963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 909586477783345446697877 42636866146094317813963)
                  ·
                    rfl

theorem cell23_747315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 6].length) (baseStart_747315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747315 prefixEnd_747315 := by exact prefixLift 747315
  have htrace : WordTrace (prefixWord ++ tailWord_747315) baseStart_747315 baseEnd_747315 := by
    simpa [prefixWord, tailWord_747315, baseEnd_747315] using wordTrace_append hprefix tailTrace_747315
  have hstable : (prefixWord ++ tailWord_747315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747315).length < 2 ^ (prefixWord ++ tailWord_747315).sum := by decide
  have hdescent : baseEnd_747315 < baseStart_747315 := by decide
  rcases family_descends (prefixWord ++ tailWord_747315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747359 : List Nat := [1, 1, 2, 3, 1, 5, 3, 2, 1, 1, 3]
def baseStart_747359 : Nat := 118140960795 + 747359 * 2 ^ 59
def prefixEnd_747359 : Nat := 4983230072969 + 3 ^ 40 * 747359 * 2
def baseEnd_747359 : Nat := 383754388463646688175465

theorem tailTrace_747359 : CollatzResearch.WordTrace tailWord_747359 prefixEnd_747359 383754388463646688175465 := by
  unfold tailWord_747359
  simp only [CollatzResearch.WordTrace]
  refine ⟨27258422099453456600469131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18172281399635637733646087 27258422099453456600469131)
  ·
    refine ⟨40887633149180184900703697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27258422099453456600469131 40887633149180184900703697)
    ·
      refine ⟨30665724861885138675527773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40887633149180184900703697 30665724861885138675527773)
      ·
        refine ⟨11499646823206927003322915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30665724861885138675527773 11499646823206927003322915)
        ·
          refine ⟨17249470234810390504984373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11499646823206927003322915 17249470234810390504984373)
          ·
            refine ⟨1617137834513474109842285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17249470234810390504984373 1617137834513474109842285)
            ·
              refine ⟨606426687942552791190857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1617137834513474109842285 606426687942552791190857)
              ·
                refine ⟨454820015956914593393143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 606426687942552791190857 454820015956914593393143)
                ·
                  refine ⟨682230023935371890089715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454820015956914593393143 682230023935371890089715)
                  ·
                    refine ⟨1023345035903057835134573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 682230023935371890089715 1023345035903057835134573)
                    ·
                      refine ⟨383754388463646688175465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1023345035903057835134573 383754388463646688175465)
                      ·
                        rfl

theorem cell23_747359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 1, 1, 3].length) (baseStart_747359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747359 prefixEnd_747359 := by exact prefixLift 747359
  have htrace : WordTrace (prefixWord ++ tailWord_747359) baseStart_747359 baseEnd_747359 := by
    simpa [prefixWord, tailWord_747359, baseEnd_747359] using wordTrace_append hprefix tailTrace_747359
  have hstable : (prefixWord ++ tailWord_747359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747359).length < 2 ^ (prefixWord ++ tailWord_747359).sum := by decide
  have hdescent : baseEnd_747359 < baseStart_747359 := by decide
  rcases family_descends (prefixWord ++ tailWord_747359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747361 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_747361 : Nat := 118140960795 + 747361 * 2 ^ 59
def prefixEnd_747361 : Nat := 4983230072969 + 3 ^ 40 * 747361 * 2
def baseEnd_747361 : Nat := 383755415424955680350455

theorem tailTrace_747361 : CollatzResearch.WordTrace tailWord_747361 prefixEnd_747361 383755415424955680350455 := by
  unfold tailWord_747361
  simp only [CollatzResearch.WordTrace]
  refine ⟨27258495045446210942041937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18172330030297473961361291 27258495045446210942041937)
  ·
    refine ⟨20443871284084658206531453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27258495045446210942041937 20443871284084658206531453)
    ·
      refine ⟨7666451731531746827449295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20443871284084658206531453 7666451731531746827449295)
      ·
        refine ⟨11499677597297620241173943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7666451731531746827449295 11499677597297620241173943)
        ·
          refine ⟨17249516395946430361760915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11499677597297620241173943 17249516395946430361760915)
          ·
            refine ⟨25874274593919645542641373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17249516395946430361760915 25874274593919645542641373)
            ·
              refine ⟨9702852972719867078490515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25874274593919645542641373 9702852972719867078490515)
              ·
                refine ⟨14554279459079800617735773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9702852972719867078490515 14554279459079800617735773)
                ·
                  refine ⟨5457854797154925231650915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14554279459079800617735773 5457854797154925231650915)
                  ·
                    refine ⟨8186782195732387847476373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5457854797154925231650915 8186782195732387847476373)
                    ·
                      refine ⟨383755415424955680350455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8186782195732387847476373 383755415424955680350455)
                      ·
                        rfl

theorem cell23_747361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_747361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747361 prefixEnd_747361 := by exact prefixLift 747361
  have htrace : WordTrace (prefixWord ++ tailWord_747361) baseStart_747361 baseEnd_747361 := by
    simpa [prefixWord, tailWord_747361, baseEnd_747361] using wordTrace_append hprefix tailTrace_747361
  have hstable : (prefixWord ++ tailWord_747361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747361).length < 2 ^ (prefixWord ++ tailWord_747361).sum := by decide
  have hdescent : baseEnd_747361 < baseStart_747361 := by decide
  rcases family_descends (prefixWord ++ tailWord_747361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747368 : List Nat := [2, 1, 4, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_747368 : Nat := 118140960795 + 747368 * 2 ^ 59
def prefixEnd_747368 : Nat := 4983230072969 + 3 ^ 40 * 747368 * 2
def baseEnd_747368 : Nat := 383759009789537152962923

theorem tailTrace_747368 : CollatzResearch.WordTrace tailWord_747368 prefixEnd_747368 383759009789537152962923 := by
  unfold tailWord_747368
  simp only [CollatzResearch.WordTrace]
  refine ⟨13629375178210425568773379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18172500237613900758364505 13629375178210425568773379)
  ·
    refine ⟨20444062767315638353160069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13629375178210425568773379 20444062767315638353160069)
    ·
      refine ⟨3833261768871682191217513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20444062767315638353160069 3833261768871682191217513)
      ·
        refine ⟨2874946326653761643413135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3833261768871682191217513 2874946326653761643413135)
        ·
          refine ⟨4312419489980642465119703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2874946326653761643413135 4312419489980642465119703)
          ·
            refine ⟨6468629234970963697679555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4312419489980642465119703 6468629234970963697679555)
            ·
              refine ⟨9702943852456445546519333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6468629234970963697679555 9702943852456445546519333)
              ·
                refine ⟨1819301972335583539972375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9702943852456445546519333 1819301972335583539972375)
                ·
                  refine ⟨2728952958503375309958563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819301972335583539972375 2728952958503375309958563)
                  ·
                    refine ⟨4093429437755062964937845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2728952958503375309958563 4093429437755062964937845)
                    ·
                      refine ⟨383759009789537152962923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4093429437755062964937845 383759009789537152962923)
                      ·
                        rfl

theorem cell23_747368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_747368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747368 prefixEnd_747368 := by exact prefixLift 747368
  have htrace : WordTrace (prefixWord ++ tailWord_747368) baseStart_747368 baseEnd_747368 := by
    simpa [prefixWord, tailWord_747368, baseEnd_747368] using wordTrace_append hprefix tailTrace_747368
  have hstable : (prefixWord ++ tailWord_747368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747368).length < 2 ^ (prefixWord ++ tailWord_747368).sum := by decide
  have hdescent : baseEnd_747368 < baseStart_747368 := by decide
  rcases family_descends (prefixWord ++ tailWord_747368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747378 : List Nat := [3, 2, 1, 2, 1, 1, 1, 5, 1, 2, 4]
def baseStart_747378 : Nat := 118140960795 + 747378 * 2 ^ 59
def prefixEnd_747378 : Nat := 4983230072969 + 3 ^ 40 * 747378 * 2
def baseEnd_747378 : Nat := 383764144596082113837877

theorem tailTrace_747378 : CollatzResearch.WordTrace tailWord_747378 prefixEnd_747378 383764144596082113837877 := by
  unfold tailWord_747378
  simp only [CollatzResearch.WordTrace]
  refine ⟨6814778771596155711352697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18172743390923081896940525 6814778771596155711352697)
  ·
    refine ⟨5111084078697116783514523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6814778771596155711352697 5111084078697116783514523)
    ·
      refine ⟨7666626118045675175271785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5111084078697116783514523 7666626118045675175271785)
      ·
        refine ⟨5749969588534256381453839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7666626118045675175271785 5749969588534256381453839)
        ·
          refine ⟨8624954382801384572180759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5749969588534256381453839 8624954382801384572180759)
          ·
            refine ⟨12937431574202076858271139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8624954382801384572180759 12937431574202076858271139)
            ·
              refine ⟨19406147361303115287406709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12937431574202076858271139 19406147361303115287406709)
              ·
                refine ⟨1819326315122167058194379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19406147361303115287406709 1819326315122167058194379)
                ·
                  refine ⟨2728989472683250587291569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819326315122167058194379 2728989472683250587291569)
                  ·
                    refine ⟨2046742104512437940468677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2728989472683250587291569 2046742104512437940468677)
                    ·
                      refine ⟨383764144596082113837877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2046742104512437940468677 383764144596082113837877)
                      ·
                        rfl

theorem cell23_747378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_747378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747378 prefixEnd_747378 := by exact prefixLift 747378
  have htrace : WordTrace (prefixWord ++ tailWord_747378) baseStart_747378 baseEnd_747378 := by
    simpa [prefixWord, tailWord_747378, baseEnd_747378] using wordTrace_append hprefix tailTrace_747378
  have hstable : (prefixWord ++ tailWord_747378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747378).length < 2 ^ (prefixWord ++ tailWord_747378).sum := by decide
  have hdescent : baseEnd_747378 < baseStart_747378 := by decide
  rcases family_descends (prefixWord ++ tailWord_747378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747382 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_747382 : Nat := 118140960795 + 747382 * 2 ^ 59
def prefixEnd_747382 : Nat := 4983230072969 + 3 ^ 40 * 747382 * 2
def baseEnd_747382 : Nat := 383766198518700098187859

theorem tailTrace_747382 : CollatzResearch.WordTrace tailWord_747382 prefixEnd_747382 383766198518700098187859 := by
  unfold tailWord_747382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1703703811148133220534775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18172840652246754352370933 1703703811148133220534775)
  ·
    refine ⟨2555555716722199830802163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1703703811148133220534775 2555555716722199830802163)
    ·
      refine ⟨3833333575083299746203245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2555555716722199830802163 3833333575083299746203245)
      ·
        refine ⟨1437500090656237404826217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3833333575083299746203245 1437500090656237404826217)
        ·
          refine ⟨1078125067992178053619663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1437500090656237404826217 1078125067992178053619663)
          ·
            refine ⟨1617187601988267080429495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078125067992178053619663 1617187601988267080429495)
            ·
              refine ⟨2425781402982400620644243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1617187601988267080429495 2425781402982400620644243)
              ·
                refine ⟨3638672104473600930966365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2425781402982400620644243 3638672104473600930966365)
                ·
                  refine ⟨1364502039177600349112387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3638672104473600930966365 1364502039177600349112387)
                  ·
                    refine ⟨2046753058766400523668581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1364502039177600349112387 2046753058766400523668581)
                    ·
                      refine ⟨383766198518700098187859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2046753058766400523668581 383766198518700098187859)
                      ·
                        rfl

theorem cell23_747382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_747382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747382 prefixEnd_747382 := by exact prefixLift 747382
  have htrace : WordTrace (prefixWord ++ tailWord_747382) baseStart_747382 baseEnd_747382 := by
    simpa [prefixWord, tailWord_747382, baseEnd_747382] using wordTrace_append hprefix tailTrace_747382
  have hstable : (prefixWord ++ tailWord_747382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747382).length < 2 ^ (prefixWord ++ tailWord_747382).sum := by decide
  have hdescent : baseEnd_747382 < baseStart_747382 := by decide
  rcases family_descends (prefixWord ++ tailWord_747382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747402 : List Nat := [3, 1, 2, 4, 2, 2, 1, 1, 1, 1, 5]
def baseStart_747402 : Nat := 118140960795 + 747402 * 2 ^ 59
def prefixEnd_747402 : Nat := 4983230072969 + 3 ^ 40 * 747402 * 2
def baseEnd_747402 : Nat := 383776468131790019937767

theorem tailTrace_747402 : CollatzResearch.WordTrace tailWord_747402 prefixEnd_747402 383776468131790019937767 := by
  unfold tailWord_747402
  simp only [CollatzResearch.WordTrace]
  refine ⟨6814997609574418736071115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18173326958865116629522973 6814997609574418736071115)
  ·
    refine ⟨10222496414361628104106673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6814997609574418736071115 10222496414361628104106673)
    ·
      refine ⟨7666872310771221078080005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10222496414361628104106673 7666872310771221078080005)
      ·
        refine ⟨1437538558269603952140001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7666872310771221078080005 1437538558269603952140001)
        ·
          refine ⟨1078153918702202964105001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1437538558269603952140001 1078153918702202964105001)
          ·
            refine ⟨808615439026652223078751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1078153918702202964105001 808615439026652223078751)
            ·
              refine ⟨1212923158539978334618127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808615439026652223078751 1212923158539978334618127)
              ·
                refine ⟨1819384737809967501927191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1212923158539978334618127 1819384737809967501927191)
                ·
                  refine ⟨2729077106714951252890787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819384737809967501927191 2729077106714951252890787)
                  ·
                    refine ⟨4093615660072426879336181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2729077106714951252890787 4093615660072426879336181)
                    ·
                      refine ⟨383776468131790019937767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4093615660072426879336181 383776468131790019937767)
                      ·
                        rfl

theorem cell23_747402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_747402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747402 prefixEnd_747402 := by exact prefixLift 747402
  have htrace : WordTrace (prefixWord ++ tailWord_747402) baseStart_747402 baseEnd_747402 := by
    simpa [prefixWord, tailWord_747402, baseEnd_747402] using wordTrace_append hprefix tailTrace_747402
  have hstable : (prefixWord ++ tailWord_747402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747402).length < 2 ^ (prefixWord ++ tailWord_747402).sum := by decide
  have hdescent : baseEnd_747402 < baseStart_747402 := by decide
  rcases family_descends (prefixWord ++ tailWord_747402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747411 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 5]
def baseStart_747411 : Nat := 118140960795 + 747411 * 2 ^ 59
def prefixEnd_747411 : Nat := 4983230072969 + 3 ^ 40 * 747411 * 2
def baseEnd_747411 : Nat := 383781089457680484725225

theorem tailTrace_747411 : CollatzResearch.WordTrace tailWord_747411 prefixEnd_747411 383781089457680484725225 := by
  unfold tailWord_747411
  simp only [CollatzResearch.WordTrace]
  refine ⟨27260318695265069481362087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18173545796843379654241391 27260318695265069481362087)
  ·
    refine ⟨40890478042897604222043131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27260318695265069481362087 40890478042897604222043131)
    ·
      refine ⟨61335717064346406333064697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40890478042897604222043131 61335717064346406333064697)
      ·
        refine ⟨46001787798259804749798523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61335717064346406333064697 46001787798259804749798523)
        ·
          refine ⟨69002681697389707124697785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46001787798259804749798523 69002681697389707124697785)
          ·
            refine ⟨51752011273042280343523339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69002681697389707124697785 51752011273042280343523339)
            ·
              refine ⟨77628016909563420515285009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51752011273042280343523339 77628016909563420515285009)
              ·
                refine ⟨58221012682172565386463757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77628016909563420515285009 58221012682172565386463757)
                ·
                  refine ⟨21832879755814712019923909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58221012682172565386463757 21832879755814712019923909)
                  ·
                    refine ⟨4093664954215258503735733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21832879755814712019923909 4093664954215258503735733)
                    ·
                      refine ⟨383781089457680484725225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4093664954215258503735733 383781089457680484725225)
                      ·
                        rfl

theorem cell23_747411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_747411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747411 prefixEnd_747411 := by exact prefixLift 747411
  have htrace : WordTrace (prefixWord ++ tailWord_747411) baseStart_747411 baseEnd_747411 := by
    simpa [prefixWord, tailWord_747411, baseEnd_747411] using wordTrace_append hprefix tailTrace_747411
  have hstable : (prefixWord ++ tailWord_747411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747411).length < 2 ^ (prefixWord ++ tailWord_747411).sum := by decide
  have hdescent : baseEnd_747411 < baseStart_747411 := by decide
  rcases family_descends (prefixWord ++ tailWord_747411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747418 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 2, 7]
def baseStart_747418 : Nat := 118140960795 + 747418 * 2 ^ 59
def prefixEnd_747418 : Nat := 4983230072969 + 3 ^ 40 * 747418 * 2
def baseEnd_747418 : Nat := 127928227940753985779231

theorem tailTrace_747418 : CollatzResearch.WordTrace tailWord_747418 prefixEnd_747418 127928227940753985779231 := by
  unfold tailWord_747418
  simp only [CollatzResearch.WordTrace]
  refine ⟨6815143501559927419216727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18173716004159806451244605 6815143501559927419216727)
  ·
    refine ⟨10222715252339891128825091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6815143501559927419216727 10222715252339891128825091)
    ·
      refine ⟨15334072878509836693237637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10222715252339891128825091 15334072878509836693237637)
      ·
        refine ⟨2875138664720594379982057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15334072878509836693237637 2875138664720594379982057)
        ·
          refine ⟨2156353998540445784986543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2875138664720594379982057 2156353998540445784986543)
          ·
            refine ⟨3234530997810668677479815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2156353998540445784986543 3234530997810668677479815)
            ·
              refine ⟨4851796496716003016219723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3234530997810668677479815 4851796496716003016219723)
              ·
                refine ⟨7277694745074004524329585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4851796496716003016219723 7277694745074004524329585)
                ·
                  refine ⟨5458271058805503393247189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7277694745074004524329585 5458271058805503393247189)
                  ·
                    refine ⟨127928227940753985779231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5458271058805503393247189 127928227940753985779231)
                    ·
                      rfl

theorem cell23_747418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_747418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747418 prefixEnd_747418 := by exact prefixLift 747418
  have htrace : WordTrace (prefixWord ++ tailWord_747418) baseStart_747418 baseEnd_747418 := by
    simpa [prefixWord, tailWord_747418, baseEnd_747418] using wordTrace_append hprefix tailTrace_747418
  have hstable : (prefixWord ++ tailWord_747418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747418).length < 2 ^ (prefixWord ++ tailWord_747418).sum := by decide
  have hdescent : baseEnd_747418 < baseStart_747418 := by decide
  rcases family_descends (prefixWord ++ tailWord_747418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747455 : List Nat := [1, 1, 2, 2, 2, 1, 3, 4, 1, 4, 2]
def baseStart_747455 : Nat := 118140960795 + 747455 * 2 ^ 59
def prefixEnd_747455 : Nat := 4983230072969 + 3 ^ 40 * 747455 * 2
def baseEnd_747455 : Nat := 383803682606478312575023

theorem tailTrace_747455 : CollatzResearch.WordTrace tailWord_747455 prefixEnd_747455 383803682606478312575023 := by
  unfold tailWord_747455
  simp only [CollatzResearch.WordTrace]
  refine ⟨27261923507105664995963819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18174615671403776663975879 27261923507105664995963819)
  ·
    refine ⟨40892885260658497493945729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27261923507105664995963819 40892885260658497493945729)
    ·
      refine ⟨30669663945493873120459297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40892885260658497493945729 30669663945493873120459297)
      ·
        refine ⟨23002247959120404840344473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30669663945493873120459297 23002247959120404840344473)
        ·
          refine ⟨17251685969340303630258355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23002247959120404840344473 17251685969340303630258355)
          ·
            refine ⟨25877528954010455445387533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17251685969340303630258355 25877528954010455445387533)
            ·
              refine ⟨9704073357753920792020325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25877528954010455445387533 9704073357753920792020325)
              ·
                refine ⟨1819513754578860148503811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9704073357753920792020325 1819513754578860148503811)
                ·
                  refine ⟨2729270631868290222755717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819513754578860148503811 2729270631868290222755717)
                  ·
                    refine ⟨511738243475304416766697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2729270631868290222755717 511738243475304416766697)
                    ·
                      refine ⟨383803682606478312575023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 511738243475304416766697 383803682606478312575023)
                      ·
                        rfl

theorem cell23_747455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 4, 2].length) (baseStart_747455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747455 prefixEnd_747455 := by exact prefixLift 747455
  have htrace : WordTrace (prefixWord ++ tailWord_747455) baseStart_747455 baseEnd_747455 := by
    simpa [prefixWord, tailWord_747455, baseEnd_747455] using wordTrace_append hprefix tailTrace_747455
  have hstable : (prefixWord ++ tailWord_747455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747455).length < 2 ^ (prefixWord ++ tailWord_747455).sum := by decide
  have hdescent : baseEnd_747455 < baseStart_747455 := by decide
  rcases family_descends (prefixWord ++ tailWord_747455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747525 : List Nat := [1, 3, 1, 1, 2, 5, 1, 2, 2, 5]
def baseStart_747525 : Nat := 118140960795 + 747525 * 2 ^ 59
def prefixEnd_747525 : Nat := 4983230072969 + 3 ^ 40 * 747525 * 2
def baseEnd_747525 : Nat := 127946542084097679566567

theorem tailTrace_747525 : CollatzResearch.WordTrace tailWord_747525 prefixEnd_747525 127946542084097679566567 := by
  unfold tailWord_747525
  simp only [CollatzResearch.WordTrace]
  refine ⟨27264476616852066951012029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18176317744568044634008019 27264476616852066951012029)
  ·
    refine ⟨10224178731319525106629511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27264476616852066951012029 10224178731319525106629511)
    ·
      refine ⟨15336268096979287659944267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10224178731319525106629511 15336268096979287659944267)
      ·
        refine ⟨23004402145468931489916401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15336268096979287659944267 23004402145468931489916401)
        ·
          refine ⟨17253301609101698617437301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23004402145468931489916401 17253301609101698617437301)
          ·
            refine ⟨1617497025853284245384747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17253301609101698617437301 1617497025853284245384747)
            ·
              refine ⟨2426245538779926368077121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1617497025853284245384747 2426245538779926368077121)
              ·
                refine ⟨1819684154084944776057841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2426245538779926368077121 1819684154084944776057841)
                ·
                  refine ⟨1364763115563708582043381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1819684154084944776057841 1364763115563708582043381)
                  ·
                    refine ⟨127946542084097679566567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1364763115563708582043381 127946542084097679566567)
                    ·
                      rfl

theorem cell23_747525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_747525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747525 prefixEnd_747525 := by exact prefixLift 747525
  have htrace : WordTrace (prefixWord ++ tailWord_747525) baseStart_747525 baseEnd_747525 := by
    simpa [prefixWord, tailWord_747525, baseEnd_747525] using wordTrace_append hprefix tailTrace_747525
  have hstable : (prefixWord ++ tailWord_747525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747525).length < 2 ^ (prefixWord ++ tailWord_747525).sum := by decide
  have hdescent : baseEnd_747525 < baseStart_747525 := by decide
  rcases family_descends (prefixWord ++ tailWord_747525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747545 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 1, 6, 2]
def baseStart_747545 : Nat := 118140960795 + 747545 * 2 ^ 59
def prefixEnd_747545 : Nat := 4983230072969 + 3 ^ 40 * 747545 * 2
def baseEnd_747545 : Nat := 383849895865382960449609

theorem tailTrace_747545 : CollatzResearch.WordTrace tailWord_747545 prefixEnd_747545 383849895865382960449609 := by
  unfold tailWord_747545
  simp only [CollatzResearch.WordTrace]
  refine ⟨27265206076779610366740089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18176804051186406911160059 27265206076779610366740089)
  ·
    refine ⟨20448904557584707775055067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27265206076779610366740089 20448904557584707775055067)
    ·
      refine ⟨30673356836377061662582601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20448904557584707775055067 30673356836377061662582601)
      ·
        refine ⟨23005017627282796246936951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30673356836377061662582601 23005017627282796246936951)
        ·
          refine ⟨34507526440924194370405427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23005017627282796246936951 34507526440924194370405427)
          ·
            refine ⟨51761289661386291555608141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34507526440924194370405427 51761289661386291555608141)
            ·
              refine ⟨19410483623019859333353053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51761289661386291555608141 19410483623019859333353053)
              ·
                refine ⟨7278931358632447250007395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19410483623019859333353053 7278931358632447250007395)
                ·
                  refine ⟨10918397037948670875011093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7278931358632447250007395 10918397037948670875011093)
                  ·
                    refine ⟨511799861153843947266145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10918397037948670875011093 511799861153843947266145)
                    ·
                      refine ⟨383849895865382960449609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 511799861153843947266145 383849895865382960449609)
                      ·
                        rfl

theorem cell23_747545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 6, 2].length) (baseStart_747545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747545 prefixEnd_747545 := by exact prefixLift 747545
  have htrace : WordTrace (prefixWord ++ tailWord_747545) baseStart_747545 baseEnd_747545 := by
    simpa [prefixWord, tailWord_747545, baseEnd_747545] using wordTrace_append hprefix tailTrace_747545
  have hstable : (prefixWord ++ tailWord_747545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747545).length < 2 ^ (prefixWord ++ tailWord_747545).sum := by decide
  have hdescent : baseEnd_747545 < baseStart_747545 := by decide
  rcases family_descends (prefixWord ++ tailWord_747545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747555 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 5, 4]
def baseStart_747555 : Nat := 118140960795 + 747555 * 2 ^ 59
def prefixEnd_747555 : Nat := 4983230072969 + 3 ^ 40 * 747555 * 2
def baseEnd_747555 : Nat := 127951676890642640441521

theorem tailTrace_747555 : CollatzResearch.WordTrace tailWord_747555 prefixEnd_747555 127951676890642640441521 := by
  unfold tailWord_747555
  simp only [CollatzResearch.WordTrace]
  refine ⟨27265570806743382074604119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18177047204495588049736079 27265570806743382074604119)
  ·
    refine ⟨40898356210115073111906179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27265570806743382074604119 40898356210115073111906179)
    ·
      refine ⟨61347534315172609667859269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40898356210115073111906179 61347534315172609667859269)
      ·
        refine ⟨11502662684094864312723613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61347534315172609667859269 11502662684094864312723613)
        ·
          refine ⟨4313498506535574117271355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11502662684094864312723613 4313498506535574117271355)
          ·
            refine ⟨6470247759803361175907033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4313498506535574117271355 6470247759803361175907033)
            ·
              refine ⟨4852685819852520881930275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6470247759803361175907033 4852685819852520881930275)
              ·
                refine ⟨7279028729778781322895413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4852685819852520881930275 7279028729778781322895413)
                ·
                  refine ⟨682408943416760749021445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7279028729778781322895413 682408943416760749021445)
                  ·
                    refine ⟨127951676890642640441521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 682408943416760749021445 127951676890642640441521)
                    ·
                      rfl

theorem cell23_747555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 4].length) (baseStart_747555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747555 prefixEnd_747555 := by exact prefixLift 747555
  have htrace : WordTrace (prefixWord ++ tailWord_747555) baseStart_747555 baseEnd_747555 := by
    simpa [prefixWord, tailWord_747555, baseEnd_747555] using wordTrace_append hprefix tailTrace_747555
  have hstable : (prefixWord ++ tailWord_747555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747555).length < 2 ^ (prefixWord ++ tailWord_747555).sum := by decide
  have hdescent : baseEnd_747555 < baseStart_747555 := by decide
  rcases family_descends (prefixWord ++ tailWord_747555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747559 : List Nat := [1, 1, 7, 1, 2, 1, 2, 1, 2, 5]
def baseStart_747559 : Nat := 118140960795 + 747559 * 2 ^ 59
def prefixEnd_747559 : Nat := 4983230072969 + 3 ^ 40 * 747559 * 2
def baseEnd_747559 : Nat := 127952361531515301891515

theorem tailTrace_747559 : CollatzResearch.WordTrace tailWord_747559 prefixEnd_747559 127952361531515301891515 := by
  unfold tailWord_747559
  simp only [CollatzResearch.WordTrace]
  refine ⟨27265716698728890757749731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18177144465819260505166487 27265716698728890757749731)
  ·
    refine ⟨40898575048093336136624597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27265716698728890757749731 40898575048093336136624597)
    ·
      refine ⟨958560352689687565702139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 40898575048093336136624597 958560352689687565702139)
      ·
        refine ⟨1437840529034531348553209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 958560352689687565702139 1437840529034531348553209)
        ·
          refine ⟨1078380396775898511414907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1437840529034531348553209 1078380396775898511414907)
          ·
            refine ⟨1617570595163847767122361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078380396775898511414907 1617570595163847767122361)
            ·
              refine ⟨1213177946372885825341771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1617570595163847767122361 1213177946372885825341771)
              ·
                refine ⟨1819766919559328738012657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213177946372885825341771 1819766919559328738012657)
                ·
                  refine ⟨1364825189669496553509493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1819766919559328738012657 1364825189669496553509493)
                  ·
                    refine ⟨127952361531515301891515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1364825189669496553509493 127952361531515301891515)
                    ·
                      rfl

theorem cell23_747559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_747559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747559 prefixEnd_747559 := by exact prefixLift 747559
  have htrace : WordTrace (prefixWord ++ tailWord_747559) baseStart_747559 baseEnd_747559 := by
    simpa [prefixWord, tailWord_747559, baseEnd_747559] using wordTrace_append hprefix tailTrace_747559
  have hstable : (prefixWord ++ tailWord_747559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747559).length < 2 ^ (prefixWord ++ tailWord_747559).sum := by decide
  have hdescent : baseEnd_747559 < baseStart_747559 := by decide
  rcases family_descends (prefixWord ++ tailWord_747559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747562 : List Nat := [3, 1, 4, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_747562 : Nat := 118140960795 + 747562 * 2 ^ 59
def prefixEnd_747562 : Nat := 4983230072969 + 3 ^ 40 * 747562 * 2
def baseEnd_747562 : Nat := 383858625036509393937031

theorem tailTrace_747562 : CollatzResearch.WordTrace tailWord_747562 prefixEnd_747562 383858625036509393937031 := by
  unfold tailWord_747562
  simp only [CollatzResearch.WordTrace]
  refine ⟨6816456529429505567527235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18177217411812014846739293 6816456529429505567527235)
  ·
    refine ⟨10224684794144258351290853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6816456529429505567527235 10224684794144258351290853)
    ·
      refine ⟨1917128398902048440867035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10224684794144258351290853 1917128398902048440867035)
      ·
        refine ⟨2875692598353072661300553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1917128398902048440867035 2875692598353072661300553)
        ·
          refine ⟨2156769448764804495975415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2875692598353072661300553 2156769448764804495975415)
          ·
            refine ⟨3235154173147206743963123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2156769448764804495975415 3235154173147206743963123)
            ·
              refine ⟨4852731259720810115944685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3235154173147206743963123 4852731259720810115944685)
              ·
                refine ⟨1819774222395303793479257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4852731259720810115944685 1819774222395303793479257)
                ·
                  refine ⟨1364830666796477845109443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1819774222395303793479257 1364830666796477845109443)
                  ·
                    refine ⟨2047246000194716767664165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1364830666796477845109443 2047246000194716767664165)
                    ·
                      refine ⟨383858625036509393937031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2047246000194716767664165 383858625036509393937031)
                      ·
                        rfl

theorem cell23_747562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_747562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747562 prefixEnd_747562 := by exact prefixLift 747562
  have htrace : WordTrace (prefixWord ++ tailWord_747562) baseStart_747562 baseEnd_747562 := by
    simpa [prefixWord, tailWord_747562, baseEnd_747562] using wordTrace_append hprefix tailTrace_747562
  have hstable : (prefixWord ++ tailWord_747562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747562).length < 2 ^ (prefixWord ++ tailWord_747562).sum := by decide
  have hdescent : baseEnd_747562 < baseStart_747562 := by decide
  rcases family_descends (prefixWord ++ tailWord_747562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747606 : List Nat := [5, 2, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_747606 : Nat := 118140960795 + 747606 * 2 ^ 59
def prefixEnd_747606 : Nat := 4983230072969 + 3 ^ 40 * 747606 * 2
def baseEnd_747606 : Nat := 127960406061769073928943

theorem tailTrace_747606 : CollatzResearch.WordTrace tailWord_747606 prefixEnd_747606 127960406061769073928943 := by
  unfold tailWord_747606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1704214433097413611544417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18178287286372411856473781 1704214433097413611544417)
  ·
    refine ⟨1278160824823060208658313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1704214433097413611544417 1278160824823060208658313)
    ·
      refine ⟨958620618617295156493735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1278160824823060208658313 958620618617295156493735)
      ·
        refine ⟨1437930927925942734740603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 958620618617295156493735 1437930927925942734740603)
        ·
          refine ⟨2156896391888914102110905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1437930927925942734740603 2156896391888914102110905)
          ·
            refine ⟨1617672293916685576583179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2156896391888914102110905 1617672293916685576583179)
            ·
              refine ⟨2426508440875028364874769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1617672293916685576583179 2426508440875028364874769)
              ·
                refine ⟨1819881330656271273656077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2426508440875028364874769 1819881330656271273656077)
                ·
                  refine ⟨682455498996101727621029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1819881330656271273656077 682455498996101727621029)
                  ·
                    refine ⟨127960406061769073928943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 682455498996101727621029 127960406061769073928943)
                    ·
                      rfl

theorem cell23_747606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_747606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747606 prefixEnd_747606 := by exact prefixLift 747606
  have htrace : WordTrace (prefixWord ++ tailWord_747606) baseStart_747606 baseEnd_747606 := by
    simpa [prefixWord, tailWord_747606, baseEnd_747606] using wordTrace_append hprefix tailTrace_747606
  have hstable : (prefixWord ++ tailWord_747606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747606).length < 2 ^ (prefixWord ++ tailWord_747606).sum := by decide
  have hdescent : baseEnd_747606 < baseStart_747606 := by decide
  rcases family_descends (prefixWord ++ tailWord_747606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747632 : List Nat := [2, 1, 1, 1, 5, 3, 1, 3, 1, 5]
def baseStart_747632 : Nat := 118140960795 + 747632 * 2 ^ 59
def prefixEnd_747632 : Nat := 4983230072969 + 3 ^ 40 * 747632 * 2
def baseEnd_747632 : Nat := 127964856227441373353903

theorem tailTrace_747632 : CollatzResearch.WordTrace tailWord_747632 prefixEnd_747632 127964856227441373353903 := by
  unfold tailWord_747632
  simp only [CollatzResearch.WordTrace]
  refine ⟨13634189613732212112578575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18178919484976282816771433 13634189613732212112578575)
  ·
    refine ⟨20451284420598318168867863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13634189613732212112578575 20451284420598318168867863)
    ·
      refine ⟨30676926630897477253301795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20451284420598318168867863 30676926630897477253301795)
      ·
        refine ⟨46015389946346215879952693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30676926630897477253301795 46015389946346215879952693)
        ·
          refine ⟨4313942807469957738745565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46015389946346215879952693 4313942807469957738745565)
          ·
            refine ⟨1617728552801234152029587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4313942807469957738745565 1617728552801234152029587)
            ·
              refine ⟨2426592829201851228044381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1617728552801234152029587 2426592829201851228044381)
              ·
                refine ⟨909972310950694210516643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2426592829201851228044381 909972310950694210516643)
                ·
                  refine ⟨1364958466426041315774965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 909972310950694210516643 1364958466426041315774965)
                  ·
                    refine ⟨127964856227441373353903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1364958466426041315774965 127964856227441373353903)
                    ·
                      rfl

theorem cell23_747632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 1, 5].length) (baseStart_747632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747632 prefixEnd_747632 := by exact prefixLift 747632
  have htrace : WordTrace (prefixWord ++ tailWord_747632) baseStart_747632 baseEnd_747632 := by
    simpa [prefixWord, tailWord_747632, baseEnd_747632] using wordTrace_append hprefix tailTrace_747632
  have hstable : (prefixWord ++ tailWord_747632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747632).length < 2 ^ (prefixWord ++ tailWord_747632).sum := by decide
  have hdescent : baseEnd_747632 < baseStart_747632 := by decide
  rcases family_descends (prefixWord ++ tailWord_747632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747655 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_747655 : Nat := 118140960795 + 747655 * 2 ^ 59
def prefixEnd_747655 : Nat := 4983230072969 + 3 ^ 40 * 747655 * 2
def baseEnd_747655 : Nat := 383906378737377530074103

theorem tailTrace_747655 : CollatzResearch.WordTrace tailWord_747655 prefixEnd_747655 383906378737377530074103 := by
  unfold tailWord_747655
  simp only [CollatzResearch.WordTrace]
  refine ⟨27269218106381099153244419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18179478737587399435496279 27269218106381099153244419)
  ·
    refine ⟨40903827159571648729866629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27269218106381099153244419 40903827159571648729866629)
    ·
      refine ⟨7669467592419684136849993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40903827159571648729866629 7669467592419684136849993)
      ·
        refine ⟨5752100694314763102637495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7669467592419684136849993 5752100694314763102637495)
        ·
          refine ⟨8628151041472144653956243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5752100694314763102637495 8628151041472144653956243)
          ·
            refine ⟨12942226562208216980934365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8628151041472144653956243 12942226562208216980934365)
            ·
              refine ⟨4853334960828081367850387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12942226562208216980934365 4853334960828081367850387)
              ·
                refine ⟨7280002441242122051775581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4853334960828081367850387 7280002441242122051775581)
                ·
                  refine ⟨2730000915465795769415843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7280002441242122051775581 2730000915465795769415843)
                  ·
                    refine ⟨4095001373198693654123765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2730000915465795769415843 4095001373198693654123765)
                    ·
                      refine ⟨383906378737377530074103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4095001373198693654123765 383906378737377530074103)
                      ·
                        rfl

theorem cell23_747655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_747655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747655 prefixEnd_747655 := by exact prefixLift 747655
  have htrace : WordTrace (prefixWord ++ tailWord_747655) baseStart_747655 baseEnd_747655 := by
    simpa [prefixWord, tailWord_747655, baseEnd_747655] using wordTrace_append hprefix tailTrace_747655
  have hstable : (prefixWord ++ tailWord_747655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747655).length < 2 ^ (prefixWord ++ tailWord_747655).sum := by decide
  have hdescent : baseEnd_747655 < baseStart_747655 := by decide
  rcases family_descends (prefixWord ++ tailWord_747655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747669 : List Nat := [1, 3, 2, 1, 1, 1, 3, 4, 3, 2, 2]
def baseStart_747669 : Nat := 118140960795 + 747669 * 2 ^ 59
def prefixEnd_747669 : Nat := 4983230072969 + 3 ^ 40 * 747669 * 2
def baseEnd_747669 : Nat := 383913567466540475299039

theorem tailTrace_747669 : CollatzResearch.WordTrace tailWord_747669 prefixEnd_747669 383913567466540475299039 := by
  unfold tailWord_747669
  simp only [CollatzResearch.WordTrace]
  refine ⟨27269728728330379544254061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18179819152220253029502707 27269728728330379544254061)
  ·
    refine ⟨10226148273123892329095273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27269728728330379544254061 10226148273123892329095273)
    ·
      refine ⟨7669611204842919246821455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10226148273123892329095273 7669611204842919246821455)
      ·
        refine ⟨11504416807264378870232183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7669611204842919246821455 11504416807264378870232183)
        ·
          refine ⟨17256625210896568305348275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11504416807264378870232183 17256625210896568305348275)
          ·
            refine ⟨25884937816344852458022413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17256625210896568305348275 25884937816344852458022413)
            ·
              refine ⟨9706851681129319671758405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25884937816344852458022413 9706851681129319671758405)
              ·
                refine ⟨1820034690211747438454701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9706851681129319671758405 1820034690211747438454701)
                ·
                  refine ⟨682513008829405289420513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1820034690211747438454701 682513008829405289420513)
                  ·
                    refine ⟨511884756622053967065385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 682513008829405289420513 511884756622053967065385)
                    ·
                      refine ⟨383913567466540475299039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 511884756622053967065385 383913567466540475299039)
                      ·
                        rfl

theorem cell23_747669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_747669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747669 prefixEnd_747669 := by exact prefixLift 747669
  have htrace : WordTrace (prefixWord ++ tailWord_747669) baseStart_747669 baseEnd_747669 := by
    simpa [prefixWord, tailWord_747669, baseEnd_747669] using wordTrace_append hprefix tailTrace_747669
  have hstable : (prefixWord ++ tailWord_747669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747669).length < 2 ^ (prefixWord ++ tailWord_747669).sum := by decide
  have hdescent : baseEnd_747669 < baseStart_747669 := by decide
  rcases family_descends (prefixWord ++ tailWord_747669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747705 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 2, 7]
def baseStart_747705 : Nat := 118140960795 + 747705 * 2 ^ 59
def prefixEnd_747705 : Nat := 4983230072969 + 3 ^ 40 * 747705 * 2
def baseEnd_747705 : Nat := 127977350923367444816291

theorem tailTrace_747705 : CollatzResearch.WordTrace tailWord_747705 prefixEnd_747705 127977350923367444816291 := by
  unfold tailWord_747705
  simp only [CollatzResearch.WordTrace]
  refine ⟨27271041756199957692564569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18180694504133305128376379 27271041756199957692564569)
  ·
    refine ⟨20453281317149968269423427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27271041756199957692564569 20453281317149968269423427)
    ·
      refine ⟨30679921975724952404135141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20453281317149968269423427 30679921975724952404135141)
      ·
        refine ⟨5752485370448428575775339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30679921975724952404135141 5752485370448428575775339)
        ·
          refine ⟨8628728055672642863663009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5752485370448428575775339 8628728055672642863663009)
          ·
            refine ⟨6471546041754482147747257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8628728055672642863663009 6471546041754482147747257)
            ·
              refine ⟨4853659531315861610810443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6471546041754482147747257 4853659531315861610810443)
              ·
                refine ⟨7280489296973792416215665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4853659531315861610810443 7280489296973792416215665)
                ·
                  refine ⟨5460366972730344312161749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7280489296973792416215665 5460366972730344312161749)
                  ·
                    refine ⟨127977350923367444816291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5460366972730344312161749 127977350923367444816291)
                    ·
                      rfl

theorem cell23_747705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 7].length) (baseStart_747705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747705 prefixEnd_747705 := by exact prefixLift 747705
  have htrace : WordTrace (prefixWord ++ tailWord_747705) baseStart_747705 baseEnd_747705 := by
    simpa [prefixWord, tailWord_747705, baseEnd_747705] using wordTrace_append hprefix tailTrace_747705
  have hstable : (prefixWord ++ tailWord_747705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747705).length < 2 ^ (prefixWord ++ tailWord_747705).sum := by decide
  have hdescent : baseEnd_747705 < baseStart_747705 := by decide
  rcases family_descends (prefixWord ++ tailWord_747705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747735 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 4, 6]
def baseStart_747735 : Nat := 118140960795 + 747735 * 2 ^ 59
def prefixEnd_747735 : Nat := 4983230072969 + 3 ^ 40 * 747735 * 2
def baseEnd_747735 : Nat := 127982485729912405691245

theorem tailTrace_747735 : CollatzResearch.WordTrace tailWord_747735 prefixEnd_747735 127982485729912405691245 := by
  unfold tailWord_747735
  simp only [CollatzResearch.WordTrace]
  refine ⟨27272135946091272816156659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18181423964060848544104439 27272135946091272816156659)
  ·
    refine ⟨40908203919136909224234989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27272135946091272816156659 40908203919136909224234989)
    ·
      refine ⟨15340576469676340959088121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40908203919136909224234989 15340576469676340959088121)
      ·
        refine ⟨11505432352257255719316091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15340576469676340959088121 11505432352257255719316091)
        ·
          refine ⟨17258148528385883578974137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11505432352257255719316091 17258148528385883578974137)
          ·
            refine ⟨12943611396289412684230603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17258148528385883578974137 12943611396289412684230603)
            ·
              refine ⟨19415417094434119026345905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12943611396289412684230603 19415417094434119026345905)
              ·
                refine ⟨14561562820825589269759429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19415417094434119026345905 14561562820825589269759429)
                ·
                  refine ⟨2730293028904797988079893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14561562820825589269759429 2730293028904797988079893)
                  ·
                    refine ⟨127982485729912405691245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2730293028904797988079893 127982485729912405691245)
                    ·
                      rfl

theorem cell23_747735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_747735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747735 prefixEnd_747735 := by exact prefixLift 747735
  have htrace : WordTrace (prefixWord ++ tailWord_747735) baseStart_747735 baseEnd_747735 := by
    simpa [prefixWord, tailWord_747735, baseEnd_747735] using wordTrace_append hprefix tailTrace_747735
  have hstable : (prefixWord ++ tailWord_747735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747735).length < 2 ^ (prefixWord ++ tailWord_747735).sum := by decide
  have hdescent : baseEnd_747735 < baseStart_747735 := by decide
  rcases family_descends (prefixWord ++ tailWord_747735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747740 : List Nat := [2, 2, 5, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_747740 : Nat := 118140960795 + 747740 * 2 ^ 59
def prefixEnd_747740 : Nat := 4983230072969 + 3 ^ 40 * 747740 * 2
def baseEnd_747740 : Nat := 383950024593009697511213

theorem tailTrace_747740 : CollatzResearch.WordTrace tailWord_747740 prefixEnd_747740 383950024593009697511213 := by
  unfold tailWord_747740
  simp only [CollatzResearch.WordTrace]
  refine ⟨13636159155536579335044337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18181545540715439113392449 13636159155536579335044337)
  ·
    refine ⟨10227119366652434501283253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13636159155536579335044337 10227119366652434501283253)
    ·
      refine ⟨958792440623665734495305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10227119366652434501283253 958792440623665734495305)
      ·
        refine ⟨719094330467749300871479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 958792440623665734495305 719094330467749300871479)
        ·
          refine ⟨1078641495701623951307219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719094330467749300871479 1078641495701623951307219)
          ·
            refine ⟨1617962243552435926960829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078641495701623951307219 1617962243552435926960829)
            ·
              refine ⟨606735841332163472610311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1617962243552435926960829 606735841332163472610311)
              ·
                refine ⟨910103761998245208915467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 606735841332163472610311 910103761998245208915467)
                ·
                  refine ⟨1365155642997367813373201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 910103761998245208915467 1365155642997367813373201)
                  ·
                    refine ⟨1023866732248025860029901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1365155642997367813373201 1023866732248025860029901)
                    ·
                      refine ⟨383950024593009697511213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1023866732248025860029901 383950024593009697511213)
                      ·
                        rfl

theorem cell23_747740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_747740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747740 prefixEnd_747740 := by exact prefixLift 747740
  have htrace : WordTrace (prefixWord ++ tailWord_747740) baseStart_747740 baseEnd_747740 := by
    simpa [prefixWord, tailWord_747740, baseEnd_747740] using wordTrace_append hprefix tailTrace_747740
  have hstable : (prefixWord ++ tailWord_747740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747740).length < 2 ^ (prefixWord ++ tailWord_747740).sum := by decide
  have hdescent : baseEnd_747740 < baseStart_747740 := by decide
  rcases family_descends (prefixWord ++ tailWord_747740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747772 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_747772 : Nat := 118140960795 + 747772 * 2 ^ 59
def prefixEnd_747772 : Nat := 4983230072969 + 3 ^ 40 * 747772 * 2
def baseEnd_747772 : Nat := 383966455973953572311065

theorem tailTrace_747772 : CollatzResearch.WordTrace tailWord_747772 prefixEnd_747772 383966455973953572311065 := by
  unfold tailWord_747772
  simp only [CollatzResearch.WordTrace]
  refine ⟨13636742723478614067626785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18182323631304818756835713 13636742723478614067626785)
  ·
    refine ⟨10227557042608960550720089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13636742723478614067626785 10227557042608960550720089)
    ·
      refine ⟨7670667781956720413040067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10227557042608960550720089 7670667781956720413040067)
      ·
        refine ⟨11506001672935080619560101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7670667781956720413040067 11506001672935080619560101)
        ·
          refine ⟨2157375313675327616167519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11506001672935080619560101 2157375313675327616167519)
          ·
            refine ⟨3236062970512991424251279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157375313675327616167519 3236062970512991424251279)
            ·
              refine ⟨4854094455769487136376919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3236062970512991424251279 4854094455769487136376919)
              ·
                refine ⟨7281141683654230704565379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4854094455769487136376919 7281141683654230704565379)
                ·
                  refine ⟨10921712525481346056848069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7281141683654230704565379 10921712525481346056848069)
                  ·
                    refine ⟨2047821098527752385659013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10921712525481346056848069 2047821098527752385659013)
                    ·
                      refine ⟨383966455973953572311065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2047821098527752385659013 383966455973953572311065)
                      ·
                        rfl

theorem cell23_747772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_747772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747772 prefixEnd_747772 := by exact prefixLift 747772
  have htrace : WordTrace (prefixWord ++ tailWord_747772) baseStart_747772 baseEnd_747772 := by
    simpa [prefixWord, tailWord_747772, baseEnd_747772] using wordTrace_append hprefix tailTrace_747772
  have hstable : (prefixWord ++ tailWord_747772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747772).length < 2 ^ (prefixWord ++ tailWord_747772).sum := by decide
  have hdescent : baseEnd_747772 < baseStart_747772 := by decide
  rcases family_descends (prefixWord ++ tailWord_747772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747776 : List Nat := [2, 1, 1, 2, 1, 1, 6, 3, 2, 2, 2]
def baseStart_747776 : Nat := 118140960795 + 747776 * 2 ^ 59
def prefixEnd_747776 : Nat := 4983230072969 + 3 ^ 40 * 747776 * 2
def baseEnd_747776 : Nat := 383968509896571556661047

theorem tailTrace_747776 : CollatzResearch.WordTrace tailWord_747776 prefixEnd_747776 383968509896571556661047 := by
  unfold tailWord_747776
  simp only [CollatzResearch.WordTrace]
  refine ⟨13636815669471368409199591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18182420892628491212266121 13636815669471368409199591)
  ·
    refine ⟨20455223504207052613799387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13636815669471368409199591 20455223504207052613799387)
    ·
      refine ⟨30682835256310578920699081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20455223504207052613799387 30682835256310578920699081)
      ·
        refine ⟨23012126442232934190524311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30682835256310578920699081 23012126442232934190524311)
        ·
          refine ⟨34518189663349401285786467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23012126442232934190524311 34518189663349401285786467)
          ·
            refine ⟨51777284495024101928679701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34518189663349401285786467 51777284495024101928679701)
            ·
              refine ⟨2427060210704254777906861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51777284495024101928679701 2427060210704254777906861)
              ·
                refine ⟨910147579014095541715073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2427060210704254777906861 910147579014095541715073)
                ·
                  refine ⟨682610684260571656286305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 910147579014095541715073 682610684260571656286305)
                  ·
                    refine ⟨511958013195428742214729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 682610684260571656286305 511958013195428742214729)
                    ·
                      refine ⟨383968509896571556661047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 511958013195428742214729 383968509896571556661047)
                      ·
                        rfl

theorem cell23_747776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 2, 2, 2].length) (baseStart_747776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747776 prefixEnd_747776 := by exact prefixLift 747776
  have htrace : WordTrace (prefixWord ++ tailWord_747776) baseStart_747776 baseEnd_747776 := by
    simpa [prefixWord, tailWord_747776, baseEnd_747776] using wordTrace_append hprefix tailTrace_747776
  have hstable : (prefixWord ++ tailWord_747776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747776).length < 2 ^ (prefixWord ++ tailWord_747776).sum := by decide
  have hdescent : baseEnd_747776 < baseStart_747776 := by decide
  rcases family_descends (prefixWord ++ tailWord_747776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747799 : List Nat := [1, 1, 3, 4, 1, 2, 1, 5, 5]
def baseStart_747799 : Nat := 118140960795 + 747799 * 2 ^ 59
def prefixEnd_747799 : Nat := 4983230072969 + 3 ^ 40 * 747799 * 2
def baseEnd_747799 : Nat := 42664479994624996297049

theorem tailTrace_747799 : CollatzResearch.WordTrace tailWord_747799 prefixEnd_747799 42664479994624996297049 := by
  unfold tailWord_747799
  simp only [CollatzResearch.WordTrace]
  refine ⟨27274470217859411746486451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18182980145239607830990967 27274470217859411746486451)
  ·
    refine ⟨40911705326789117619729677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27274470217859411746486451 40911705326789117619729677)
    ·
      refine ⟨15341889497545919107398629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40911705326789117619729677 15341889497545919107398629)
      ·
        refine ⟨2876604280789859832637243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15341889497545919107398629 2876604280789859832637243)
        ·
          refine ⟨4314906421184789748955865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2876604280789859832637243 4314906421184789748955865)
          ·
            refine ⟨3236179815888592311716899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4314906421184789748955865 3236179815888592311716899)
            ·
              refine ⟨4854269723832888467575349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3236179815888592311716899 4854269723832888467575349)
              ·
                refine ⟨455087786609333293835189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4854269723832888467575349 455087786609333293835189)
                ·
                  refine ⟨42664479994624996297049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 455087786609333293835189 42664479994624996297049)
                  ·
                    rfl

theorem cell23_747799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 5].length) (baseStart_747799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747799 prefixEnd_747799 := by exact prefixLift 747799
  have htrace : WordTrace (prefixWord ++ tailWord_747799) baseStart_747799 baseEnd_747799 := by
    simpa [prefixWord, tailWord_747799, baseEnd_747799] using wordTrace_append hprefix tailTrace_747799
  have hstable : (prefixWord ++ tailWord_747799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747799).length < 2 ^ (prefixWord ++ tailWord_747799).sum := by decide
  have hdescent : baseEnd_747799 < baseStart_747799 := by decide
  rcases family_descends (prefixWord ++ tailWord_747799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747806 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_747806 : Nat := 118140960795 + 747806 * 2 ^ 59
def prefixEnd_747806 : Nat := 4983230072969 + 3 ^ 40 * 747806 * 2
def baseEnd_747806 : Nat := 383983914316206439285909

theorem tailTrace_747806 : CollatzResearch.WordTrace tailWord_747806 prefixEnd_747806 383983914316206439285909 := by
  unfold tailWord_747806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3409340691104256492748909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18183150352556034627994181 3409340691104256492748909)
  ·
    refine ⟨1278502759164096184780841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3409340691104256492748909 1278502759164096184780841)
    ·
      refine ⟨958877069373072138585631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1278502759164096184780841 958877069373072138585631)
      ·
        refine ⟨1438315604059608207878447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 958877069373072138585631 1438315604059608207878447)
        ·
          refine ⟨2157473406089412311817671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438315604059608207878447 2157473406089412311817671)
          ·
            refine ⟨3236210109134118467726507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157473406089412311817671 3236210109134118467726507)
            ·
              refine ⟨4854315163701177701589761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3236210109134118467726507 4854315163701177701589761)
              ·
                refine ⟨3640736372775883276192321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4854315163701177701589761 3640736372775883276192321)
                ·
                  refine ⟨2730552279581912457144241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3640736372775883276192321 2730552279581912457144241)
                  ·
                    refine ⟨2047914209686434342858181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2730552279581912457144241 2047914209686434342858181)
                    ·
                      refine ⟨383983914316206439285909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2047914209686434342858181 383983914316206439285909)
                      ·
                        rfl

theorem cell23_747806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_747806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747806 prefixEnd_747806 := by exact prefixLift 747806
  have htrace : WordTrace (prefixWord ++ tailWord_747806) baseStart_747806 baseEnd_747806 := by
    simpa [prefixWord, tailWord_747806, baseEnd_747806] using wordTrace_append hprefix tailTrace_747806
  have hstable : (prefixWord ++ tailWord_747806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747806).length < 2 ^ (prefixWord ++ tailWord_747806).sum := by decide
  have hdescent : baseEnd_747806 < baseStart_747806 := by decide
  rcases family_descends (prefixWord ++ tailWord_747806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747810 : List Nat := [3, 3, 1, 1, 3, 3, 1, 2, 2, 2, 2]
def baseStart_747810 : Nat := 118140960795 + 747810 * 2 ^ 59
def prefixEnd_747810 : Nat := 4983230072969 + 3 ^ 40 * 747810 * 2
def baseEnd_747810 : Nat := 383985968238824423635891

theorem tailTrace_747810 : CollatzResearch.WordTrace tailWord_747810 prefixEnd_747810 383985968238824423635891 := by
  unfold tailWord_747810
  simp only [CollatzResearch.WordTrace]
  refine ⟨6818717855204890156284221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18183247613879707083424589 6818717855204890156284221)
  ·
    refine ⟨2557019195701833808606583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6818717855204890156284221 2557019195701833808606583)
    ·
      refine ⟨3835528793552750712909875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2557019195701833808606583 3835528793552750712909875)
      ·
        refine ⟨5753293190329126069364813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3835528793552750712909875 5753293190329126069364813)
        ·
          refine ⟨2157484946373422276011805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5753293190329126069364813 2157484946373422276011805)
          ·
            refine ⟨809056854890033353504427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2157484946373422276011805 809056854890033353504427)
            ·
              refine ⟨1213585282335050030256641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809056854890033353504427 1213585282335050030256641)
              ·
                refine ⟨910188961751287522692481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1213585282335050030256641 910188961751287522692481)
                ·
                  refine ⟨682641721313465642019361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 910188961751287522692481 682641721313465642019361)
                  ·
                    refine ⟨511981290985099231514521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 682641721313465642019361 511981290985099231514521)
                    ·
                      refine ⟨383985968238824423635891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 511981290985099231514521 383985968238824423635891)
                      ·
                        rfl

theorem cell23_747810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_747810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747810 prefixEnd_747810 := by exact prefixLift 747810
  have htrace : WordTrace (prefixWord ++ tailWord_747810) baseStart_747810 baseEnd_747810 := by
    simpa [prefixWord, tailWord_747810, baseEnd_747810] using wordTrace_append hprefix tailTrace_747810
  have hstable : (prefixWord ++ tailWord_747810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747810).length < 2 ^ (prefixWord ++ tailWord_747810).sum := by decide
  have hdescent : baseEnd_747810 < baseStart_747810 := by decide
  rcases family_descends (prefixWord ++ tailWord_747810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747832 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 1, 3, 4]
def baseStart_747832 : Nat := 118140960795 + 747832 * 2 ^ 59
def prefixEnd_747832 : Nat := 4983230072969 + 3 ^ 40 * 747832 * 2
def baseEnd_747832 : Nat := 383997264813223337560789

theorem tailTrace_747832 : CollatzResearch.WordTrace tailWord_747832 prefixEnd_747832 383997264813223337560789 := by
  unfold tailWord_747832
  simp only [CollatzResearch.WordTrace]
  refine ⟨13637836913369929191218875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18183782551159905588291833 13637836913369929191218875)
  ·
    refine ⟨20456755370054893786828313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13637836913369929191218875 20456755370054893786828313)
    ·
      refine ⟨15342566527541170340121235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20456755370054893786828313 15342566527541170340121235)
      ·
        refine ⟨23013849791311755510181853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15342566527541170340121235 23013849791311755510181853)
        ·
          refine ⟨8630193671741908316318195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23013849791311755510181853 8630193671741908316318195)
          ·
            refine ⟨12945290507612862474477293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8630193671741908316318195 12945290507612862474477293)
            ·
              refine ⟨4854483940354823427928985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12945290507612862474477293 4854483940354823427928985)
              ·
                refine ⟨3640862955266117570946739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4854483940354823427928985 3640862955266117570946739)
                ·
                  refine ⟨5461294432899176356420109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3640862955266117570946739 5461294432899176356420109)
                  ·
                    refine ⟨2047985412337191133657541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5461294432899176356420109 2047985412337191133657541)
                    ·
                      refine ⟨383997264813223337560789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2047985412337191133657541 383997264813223337560789)
                      ·
                        rfl

theorem cell23_747832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_747832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747832 prefixEnd_747832 := by exact prefixLift 747832
  have htrace : WordTrace (prefixWord ++ tailWord_747832) baseStart_747832 baseEnd_747832 := by
    simpa [prefixWord, tailWord_747832, baseEnd_747832] using wordTrace_append hprefix tailTrace_747832
  have hstable : (prefixWord ++ tailWord_747832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747832).length < 2 ^ (prefixWord ++ tailWord_747832).sum := by decide
  have hdescent : baseEnd_747832 < baseStart_747832 := by decide
  rcases family_descends (prefixWord ++ tailWord_747832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747939 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 4]
def baseStart_747939 : Nat := 118140960795 + 747939 * 2 ^ 59
def prefixEnd_747939 : Nat := 4983230072969 + 3 ^ 40 * 747939 * 2
def baseEnd_747939 : Nat := 384052207243254418922797

theorem tailTrace_747939 : CollatzResearch.WordTrace tailWord_747939 prefixEnd_747939 384052207243254418922797 := by
  unfold tailWord_747939
  simp only [CollatzResearch.WordTrace]
  refine ⟨27279576437352215656582871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18186384291568143771055247 27279576437352215656582871)
  ·
    refine ⟨40919364656028323484874307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27279576437352215656582871 40919364656028323484874307)
    ·
      refine ⟨61379046984042485227311461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40919364656028323484874307 61379046984042485227311461)
      ·
        refine ⟨11508571309507965980120899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61379046984042485227311461 11508571309507965980120899)
        ·
          refine ⟨17262856964261948970181349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11508571309507965980120899 17262856964261948970181349)
          ·
            refine ⟨3236785680799115431909003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17262856964261948970181349 3236785680799115431909003)
            ·
              refine ⟨4855178521198673147863505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3236785680799115431909003 4855178521198673147863505)
              ·
                refine ⟨3641383890899004860897629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4855178521198673147863505 3641383890899004860897629)
                ·
                  refine ⟨1365518959087126822836611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3641383890899004860897629 1365518959087126822836611)
                  ·
                    refine ⟨2048278438630690234254917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1365518959087126822836611 2048278438630690234254917)
                    ·
                      refine ⟨384052207243254418922797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2048278438630690234254917 384052207243254418922797)
                      ·
                        rfl

theorem cell23_747939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_747939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747939 prefixEnd_747939 := by exact prefixLift 747939
  have htrace : WordTrace (prefixWord ++ tailWord_747939) baseStart_747939 baseEnd_747939 := by
    simpa [prefixWord, tailWord_747939, baseEnd_747939] using wordTrace_append hprefix tailTrace_747939
  have hstable : (prefixWord ++ tailWord_747939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747939).length < 2 ^ (prefixWord ++ tailWord_747939).sum := by decide
  have hdescent : baseEnd_747939 < baseStart_747939 := by decide
  rcases family_descends (prefixWord ++ tailWord_747939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747952 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 6]
def baseStart_747952 : Nat := 118140960795 + 747952 * 2 ^ 59
def prefixEnd_747952 : Nat := 4983230072969 + 3 ^ 40 * 747952 * 2
def baseEnd_747952 : Nat := 384058882491762868060237

theorem tailTrace_747952 : CollatzResearch.WordTrace tailWord_747952 prefixEnd_747952 384058882491762868060237 := by
  unfold tailWord_747952
  simp only [CollatzResearch.WordTrace]
  refine ⟨13640025293152559438403055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18186700390870079251204073 13640025293152559438403055)
  ·
    refine ⟨20460037939728839157604583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13640025293152559438403055 20460037939728839157604583)
    ·
      refine ⟨30690056909593258736406875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20460037939728839157604583 30690056909593258736406875)
      ·
        refine ⟨46035085364389888104610313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30690056909593258736406875 46035085364389888104610313)
        ·
          refine ⟨34526314023292416078457735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46035085364389888104610313 34526314023292416078457735)
          ·
            refine ⟨51789471034938624117686603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34526314023292416078457735 51789471034938624117686603)
            ·
              refine ⟨77684206552407936176529905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51789471034938624117686603 77684206552407936176529905)
              ·
                refine ⟨58263154914305952132397429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77684206552407936176529905 58263154914305952132397429)
                ·
                  refine ⟨5462170773216183012412259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58263154914305952132397429 5462170773216183012412259)
                  ·
                    refine ⟨8193256159824274518618389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5462170773216183012412259 8193256159824274518618389)
                    ·
                      refine ⟨384058882491762868060237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8193256159824274518618389 384058882491762868060237)
                      ·
                        rfl

theorem cell23_747952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_747952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747952 prefixEnd_747952 := by exact prefixLift 747952
  have htrace : WordTrace (prefixWord ++ tailWord_747952) baseStart_747952 baseEnd_747952 := by
    simpa [prefixWord, tailWord_747952, baseEnd_747952] using wordTrace_append hprefix tailTrace_747952
  have hstable : (prefixWord ++ tailWord_747952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747952).length < 2 ^ (prefixWord ++ tailWord_747952).sum := by decide
  have hdescent : baseEnd_747952 < baseStart_747952 := by decide
  rcases family_descends (prefixWord ++ tailWord_747952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747962 : List Nat := [3, 1, 1, 1, 2, 1, 1, 13]
def baseStart_747962 : Nat := 118140960795 + 747962 * 2 ^ 59
def prefixEnd_747962 : Nat := 4983230072969 + 3 ^ 40 * 747962 * 2
def baseEnd_747962 : Nat := 14224593233270660330933

theorem tailTrace_747962 : CollatzResearch.WordTrace tailWord_747962 prefixEnd_747962 14224593233270660330933 := by
  unfold tailWord_747962
  simp only [CollatzResearch.WordTrace]
  refine ⟨6820103829067222646167535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18186943544179260389780093 6820103829067222646167535)
  ·
    refine ⟨10230155743600833969251303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6820103829067222646167535 10230155743600833969251303)
    ·
      refine ⟨15345233615401250953876955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10230155743600833969251303 15345233615401250953876955)
      ·
        refine ⟨23017850423101876430815433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15345233615401250953876955 23017850423101876430815433)
        ·
          refine ⟨17263387817326407323111575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23017850423101876430815433 17263387817326407323111575)
          ·
            refine ⟨25895081725989610984667363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17263387817326407323111575 25895081725989610984667363)
            ·
              refine ⟨38842622588984416477001045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25895081725989610984667363 38842622588984416477001045)
              ·
                refine ⟨14224593233270660330933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 38842622588984416477001045 14224593233270660330933)
                ·
                  rfl

theorem cell23_747962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 13].length) (baseStart_747962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_747962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_747962 prefixEnd_747962 := by exact prefixLift 747962
  have htrace : WordTrace (prefixWord ++ tailWord_747962) baseStart_747962 baseEnd_747962 := by
    simpa [prefixWord, tailWord_747962, baseEnd_747962] using wordTrace_append hprefix tailTrace_747962
  have hstable : (prefixWord ++ tailWord_747962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747962).length < 2 ^ (prefixWord ++ tailWord_747962).sum := by decide
  have hdescent : baseEnd_747962 < baseStart_747962 := by decide
  rcases family_descends (prefixWord ++ tailWord_747962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748003 : List Nat := [1, 1, 1, 6, 3, 2, 1, 1, 1, 2, 4]
def baseStart_748003 : Nat := 118140960795 + 748003 * 2 ^ 59
def prefixEnd_748003 : Nat := 4983230072969 + 3 ^ 40 * 748003 * 2
def baseEnd_748003 : Nat := 384085070005142168522503

theorem tailTrace_748003 : CollatzResearch.WordTrace tailWord_748003 prefixEnd_748003 384085070005142168522503 := by
  unfold tailWord_748003
  simp only [CollatzResearch.WordTrace]
  refine ⟨27281910709120354586912663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18187940472746903057941775 27281910709120354586912663)
  ·
    refine ⟨40922866063680531880368995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27281910709120354586912663 40922866063680531880368995)
    ·
      refine ⟨61384299095520797820553493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40922866063680531880368995 61384299095520797820553493)
      ·
        refine ⟨2877389020102537397838445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61384299095520797820553493 2877389020102537397838445)
        ·
          refine ⟨1079020882538451524189417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2877389020102537397838445 1079020882538451524189417)
          ·
            refine ⟨809265661903838643142063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1079020882538451524189417 809265661903838643142063)
            ·
              refine ⟨1213898492855757964713095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809265661903838643142063 1213898492855757964713095)
              ·
                refine ⟨1820847739283636947069643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213898492855757964713095 1820847739283636947069643)
                ·
                  refine ⟨2731271608925455420604465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1820847739283636947069643 2731271608925455420604465)
                  ·
                    refine ⟨2048453706694091565453349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2731271608925455420604465 2048453706694091565453349)
                    ·
                      refine ⟨384085070005142168522503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2048453706694091565453349 384085070005142168522503)
                      ·
                        rfl

theorem cell23_748003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_748003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748003 prefixEnd_748003 := by exact prefixLift 748003
  have htrace : WordTrace (prefixWord ++ tailWord_748003) baseStart_748003 baseEnd_748003 := by
    simpa [prefixWord, tailWord_748003, baseEnd_748003] using wordTrace_append hprefix tailTrace_748003
  have hstable : (prefixWord ++ tailWord_748003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748003).length < 2 ^ (prefixWord ++ tailWord_748003).sum := by decide
  have hdescent : baseEnd_748003 < baseStart_748003 := by decide
  rcases family_descends (prefixWord ++ tailWord_748003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748013 : List Nat := [1, 5, 1, 3, 1, 3, 2, 7]
def baseStart_748013 : Nat := 118140960795 + 748013 * 2 ^ 59
def prefixEnd_748013 : Nat := 4983230072969 + 3 ^ 40 * 748013 * 2
def baseEnd_748013 : Nat := 14225563141173597385091

theorem tailTrace_748013 : CollatzResearch.WordTrace tailWord_748013 prefixEnd_748013 14225563141173597385091 := by
  unfold tailWord_748013
  simp only [CollatzResearch.WordTrace]
  refine ⟨27282275439084126294776693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18188183626056084196517795 27282275439084126294776693)
  ·
    refine ⟨2557713322414136840135315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27282275439084126294776693 2557713322414136840135315)
    ·
      refine ⟨3836569983621205260202973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2557713322414136840135315 3836569983621205260202973)
      ·
        refine ⟨1438713743857951972576115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3836569983621205260202973 1438713743857951972576115)
        ·
          refine ⟨2158070615786927958864173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438713743857951972576115 2158070615786927958864173)
          ·
            refine ⟨809276480920097984574065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2158070615786927958864173 809276480920097984574065)
            ·
              refine ⟨606957360690073488430549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 809276480920097984574065 606957360690073488430549)
              ·
                refine ⟨14225563141173597385091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 606957360690073488430549 14225563141173597385091)
                ·
                  rfl

theorem cell23_748013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 7].length) (baseStart_748013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748013 prefixEnd_748013 := by exact prefixLift 748013
  have htrace : WordTrace (prefixWord ++ tailWord_748013) baseStart_748013 baseEnd_748013 := by
    simpa [prefixWord, tailWord_748013, baseEnd_748013] using wordTrace_append hprefix tailTrace_748013
  have hstable : (prefixWord ++ tailWord_748013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748013).length < 2 ^ (prefixWord ++ tailWord_748013).sum := by decide
  have hdescent : baseEnd_748013 < baseStart_748013 := by decide
  rcases family_descends (prefixWord ++ tailWord_748013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748069 : List Nat := [1, 3, 1, 2, 2, 1, 2, 4, 7]
def baseStart_748069 : Nat := 118140960795 + 748069 * 2 ^ 59
def prefixEnd_748069 : Nat := 4983230072969 + 3 ^ 40 * 748069 * 2
def baseEnd_748069 : Nat := 42679884414259878921911

theorem tailTrace_748069 : CollatzResearch.WordTrace tailWord_748069 prefixEnd_748069 42679884414259878921911 := by
  unfold tailWord_748069
  simp only [CollatzResearch.WordTrace]
  refine ⟨27284317926881247858815261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18189545284587498572543507 27284317926881247858815261)
  ·
    refine ⟨10231619222580467947055723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27284317926881247858815261 10231619222580467947055723)
    ·
      refine ⟨15347428833870701920583585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10231619222580467947055723 15347428833870701920583585)
      ·
        refine ⟨11510571625403026440437689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15347428833870701920583585 11510571625403026440437689)
        ·
          refine ⟨8632928719052269830328267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11510571625403026440437689 8632928719052269830328267)
          ·
            refine ⟨12949393078578404745492401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8632928719052269830328267 12949393078578404745492401)
            ·
              refine ⟨9712044808933803559119301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12949393078578404745492401 9712044808933803559119301)
              ·
                refine ⟨1821008401675088167334869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9712044808933803559119301 1821008401675088167334869)
                ·
                  refine ⟨42679884414259878921911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1821008401675088167334869 42679884414259878921911)
                  ·
                    rfl

theorem cell23_748069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 7].length) (baseStart_748069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748069 prefixEnd_748069 := by exact prefixLift 748069
  have htrace : WordTrace (prefixWord ++ tailWord_748069) baseStart_748069 baseEnd_748069 := by
    simpa [prefixWord, tailWord_748069, baseEnd_748069] using wordTrace_append hprefix tailTrace_748069
  have hstable : (prefixWord ++ tailWord_748069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748069).length < 2 ^ (prefixWord ++ tailWord_748069).sum := by decide
  have hdescent : baseEnd_748069 < baseStart_748069 := by decide
  rcases family_descends (prefixWord ++ tailWord_748069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748097 : List Nat := [1, 2, 5, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_748097 : Nat := 118140960795 + 748097 * 2 ^ 59
def prefixEnd_748097 : Nat := 4983230072969 + 3 ^ 40 * 748097 * 2
def baseEnd_748097 : Nat := 384133337186664800747071

theorem tailTrace_748097 : CollatzResearch.WordTrace tailWord_748097 prefixEnd_748097 384133337186664800747071 := by
  unfold tailWord_748097
  simp only [CollatzResearch.WordTrace]
  refine ⟨27285339170779808640834545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18190226113853205760556363 27285339170779808640834545)
  ·
    refine ⟨20464004378084856480625909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27285339170779808640834545 20464004378084856480625909)
    ·
      refine ⟨1918500410445455295058679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20464004378084856480625909 1918500410445455295058679)
      ·
        refine ⟨2877750615668182942588019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1918500410445455295058679 2877750615668182942588019)
        ·
          refine ⟨4316625923502274413882029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2877750615668182942588019 4316625923502274413882029)
          ·
            refine ⟨1618734721313352905205761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4316625923502274413882029 1618734721313352905205761)
            ·
              refine ⟨1214051040985014678904321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1618734721313352905205761 1214051040985014678904321)
              ·
                refine ⟨910538280738761009178241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1214051040985014678904321 910538280738761009178241)
                ·
                  refine ⟨682903710554070756883681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 910538280738761009178241 682903710554070756883681)
                  ·
                    refine ⟨512177782915553067662761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 682903710554070756883681 512177782915553067662761)
                    ·
                      refine ⟨384133337186664800747071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 512177782915553067662761 384133337186664800747071)
                      ·
                        rfl

theorem cell23_748097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_748097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748097 prefixEnd_748097 := by exact prefixLift 748097
  have htrace : WordTrace (prefixWord ++ tailWord_748097) baseStart_748097 baseEnd_748097 := by
    simpa [prefixWord, tailWord_748097, baseEnd_748097] using wordTrace_append hprefix tailTrace_748097
  have hstable : (prefixWord ++ tailWord_748097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748097).length < 2 ^ (prefixWord ++ tailWord_748097).sum := by decide
  have hdescent : baseEnd_748097 < baseStart_748097 := by decide
  rcases family_descends (prefixWord ++ tailWord_748097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748103 : List Nat := [1, 1, 4, 1, 4, 2, 1, 4, 5]
def baseStart_748103 : Nat := 118140960795 + 748103 * 2 ^ 59
def prefixEnd_748103 : Nat := 4983230072969 + 3 ^ 40 * 748103 * 2
def baseEnd_748103 : Nat := 42681824230065753030227

theorem tailTrace_748103 : CollatzResearch.WordTrace tailWord_748103 prefixEnd_748103 42681824230065753030227 := by
  unfold tailWord_748103
  simp only [CollatzResearch.WordTrace]
  refine ⟨27285558008758071665552963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18190372005838714443701975 27285558008758071665552963)
  ·
    refine ⟨40928337013137107498329445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27285558008758071665552963 40928337013137107498329445)
    ·
      refine ⟨7674063189963207655936771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40928337013137107498329445 7674063189963207655936771)
      ·
        refine ⟨11511094784944811483905157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7674063189963207655936771 11511094784944811483905157)
        ·
          refine ⟨2158330272177152153232217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11511094784944811483905157 2158330272177152153232217)
          ·
            refine ⟨1618747704132864114924163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2158330272177152153232217 1618747704132864114924163)
            ·
              refine ⟨2428121556199296172386245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1618747704132864114924163 2428121556199296172386245)
              ·
                refine ⟨455272791787368032322421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2428121556199296172386245 455272791787368032322421)
                ·
                  refine ⟨42681824230065753030227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 455272791787368032322421 42681824230065753030227)
                  ·
                    rfl

theorem cell23_748103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 5].length) (baseStart_748103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748103 prefixEnd_748103 := by exact prefixLift 748103
  have htrace : WordTrace (prefixWord ++ tailWord_748103) baseStart_748103 baseEnd_748103 := by
    simpa [prefixWord, tailWord_748103, baseEnd_748103] using wordTrace_append hprefix tailTrace_748103
  have hstable : (prefixWord ++ tailWord_748103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748103).length < 2 ^ (prefixWord ++ tailWord_748103).sum := by decide
  have hdescent : baseEnd_748103 < baseStart_748103 := by decide
  rcases family_descends (prefixWord ++ tailWord_748103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748139 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 5]
def baseStart_748139 : Nat := 118140960795 + 748139 * 2 ^ 59
def prefixEnd_748139 : Nat := 4983230072969 + 3 ^ 40 * 748139 * 2
def baseEnd_748139 : Nat := 384154903374153636421877

theorem tailTrace_748139 : CollatzResearch.WordTrace tailWord_748139 prefixEnd_748139 384154903374153636421877 := by
  unfold tailWord_748139
  simp only [CollatzResearch.WordTrace]
  refine ⟨27286871036627649813863471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18191247357751766542575647 27286871036627649813863471)
  ·
    refine ⟨40930306554941474720795207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27286871036627649813863471 40930306554941474720795207)
    ·
      refine ⟨61395459832412212081192811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40930306554941474720795207 61395459832412212081192811)
      ·
        refine ⟨92093189748618318121789217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61395459832412212081192811 92093189748618318121789217)
        ·
          refine ⟨69069892311463738591341913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92093189748618318121789217 69069892311463738591341913)
          ·
            refine ⟨51802419233597803943506435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69069892311463738591341913 51802419233597803943506435)
            ·
              refine ⟨77703628850396705915259653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51802419233597803943506435 77703628850396705915259653)
              ·
                refine ⟨14569430409449382359111185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77703628850396705915259653 14569430409449382359111185)
                ·
                  refine ⟨10927072807087036769333389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14569430409449382359111185 10927072807087036769333389)
                  ·
                    refine ⟨4097652302657638788500021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10927072807087036769333389 4097652302657638788500021)
                    ·
                      refine ⟨384154903374153636421877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4097652302657638788500021 384154903374153636421877)
                      ·
                        rfl

theorem cell23_748139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 5].length) (baseStart_748139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748139 prefixEnd_748139 := by exact prefixLift 748139
  have htrace : WordTrace (prefixWord ++ tailWord_748139) baseStart_748139 baseEnd_748139 := by
    simpa [prefixWord, tailWord_748139, baseEnd_748139] using wordTrace_append hprefix tailTrace_748139
  have hstable : (prefixWord ++ tailWord_748139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748139).length < 2 ^ (prefixWord ++ tailWord_748139).sum := by decide
  have hdescent : baseEnd_748139 < baseStart_748139 := by decide
  rcases family_descends (prefixWord ++ tailWord_748139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748153 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 2, 4, 2]
def baseStart_748153 : Nat := 118140960795 + 748153 * 2 ^ 59
def prefixEnd_748153 : Nat := 4983230072969 + 3 ^ 40 * 748153 * 2
def baseEnd_748153 : Nat := 384162092103316581646813

theorem tailTrace_748153 : CollatzResearch.WordTrace tailWord_748153 prefixEnd_748153 384162092103316581646813 := by
  unfold tailWord_748153
  simp only [CollatzResearch.WordTrace]
  refine ⟨27287381658576930204873113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18191587772384620136582075 27287381658576930204873113)
  ·
    refine ⟨20465536243932697653654835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27287381658576930204873113 20465536243932697653654835)
    ·
      refine ⟨30698304365899046480482253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20465536243932697653654835 30698304365899046480482253)
      ·
        refine ⟨11511864137212142430180845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30698304365899046480482253 11511864137212142430180845)
        ·
          refine ⟨4316949051454553411317817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11511864137212142430180845 4316949051454553411317817)
          ·
            refine ⟨3237711788590915058488363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4316949051454553411317817 3237711788590915058488363)
            ·
              refine ⟨4856567682886372587732545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3237711788590915058488363 4856567682886372587732545)
              ·
                refine ⟨3642425762164779440799409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4856567682886372587732545 3642425762164779440799409)
                ·
                  refine ⟨2731819321623584580599557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3642425762164779440799409 2731819321623584580599557)
                  ·
                    refine ⟨512216122804422108862417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2731819321623584580599557 512216122804422108862417)
                    ·
                      refine ⟨384162092103316581646813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 512216122804422108862417 384162092103316581646813)
                      ·
                        rfl

theorem cell23_748153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_748153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748153 prefixEnd_748153 := by exact prefixLift 748153
  have htrace : WordTrace (prefixWord ++ tailWord_748153) baseStart_748153 baseEnd_748153 := by
    simpa [prefixWord, tailWord_748153, baseEnd_748153] using wordTrace_append hprefix tailTrace_748153
  have hstable : (prefixWord ++ tailWord_748153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748153).length < 2 ^ (prefixWord ++ tailWord_748153).sum := by decide
  have hdescent : baseEnd_748153 < baseStart_748153 := by decide
  rcases family_descends (prefixWord ++ tailWord_748153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748180 : List Nat := [2, 4, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_748180 : Nat := 118140960795 + 748180 * 2 ^ 59
def prefixEnd_748180 : Nat := 4983230072969 + 3 ^ 40 * 748180 * 2
def baseEnd_748180 : Nat := 128058652026995992003063

theorem tailTrace_748180 : CollatzResearch.WordTrace tailWord_748180 prefixEnd_748180 128058652026995992003063 := by
  unfold tailWord_748180
  simp only [CollatzResearch.WordTrace]
  refine ⟨13644183214739556908052997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18192244286319409210737329 13644183214739556908052997)
  ·
    refine ⟨2558284352763666920259937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13644183214739556908052997 2558284352763666920259937)
    ·
      refine ⟨1918713264572750190194953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2558284352763666920259937 1918713264572750190194953)
      ·
        refine ⟨1439034948429562642646215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1918713264572750190194953 1439034948429562642646215)
        ·
          refine ⟨2158552422644343963969323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1439034948429562642646215 2158552422644343963969323)
          ·
            refine ⟨3237828633966515945953985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2158552422644343963969323 3237828633966515945953985)
            ·
              refine ⟨2428371475474886959465489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3237828633966515945953985 2428371475474886959465489)
              ·
                refine ⟨1821278606606165219599117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2428371475474886959465489 1821278606606165219599117)
                ·
                  refine ⟨682979477477311957349669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1821278606606165219599117 682979477477311957349669)
                  ·
                    refine ⟨128058652026995992003063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 682979477477311957349669 128058652026995992003063)
                    ·
                      rfl

theorem cell23_748180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_748180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748180 prefixEnd_748180 := by exact prefixLift 748180
  have htrace : WordTrace (prefixWord ++ tailWord_748180) baseStart_748180 baseEnd_748180 := by
    simpa [prefixWord, tailWord_748180, baseEnd_748180] using wordTrace_append hprefix tailTrace_748180
  have hstable : (prefixWord ++ tailWord_748180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748180).length < 2 ^ (prefixWord ++ tailWord_748180).sum := by decide
  have hdescent : baseEnd_748180 < baseStart_748180 := by decide
  rcases family_descends (prefixWord ++ tailWord_748180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748190 : List Nat := [4, 3, 1, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_748190 : Nat := 118140960795 + 748190 * 2 ^ 59
def prefixEnd_748190 : Nat := 4983230072969 + 3 ^ 40 * 748190 * 2
def baseEnd_748190 : Nat := 384181090887532936884143

theorem tailTrace_748190 : CollatzResearch.WordTrace tailWord_748190 prefixEnd_748190 384181090887532936884143 := by
  unfold tailWord_748190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3411091394930360690496253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18192487439628590349313349 3411091394930360690496253)
  ·
    refine ⟨1279159273098885258936095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3411091394930360690496253 1279159273098885258936095)
    ·
      refine ⟨1918738909648327888404143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1279159273098885258936095 1918738909648327888404143)
      ·
        refine ⟨2878108364472491832606215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1918738909648327888404143 2878108364472491832606215)
        ·
          refine ⟨4317162546708737748909323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2878108364472491832606215 4317162546708737748909323)
          ·
            refine ⟨6475743820063106623363985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4317162546708737748909323 6475743820063106623363985)
            ·
              refine ⟨4856807865047329967522989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6475743820063106623363985 4856807865047329967522989)
              ·
                refine ⟨1821302949392748737821121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4856807865047329967522989 1821302949392748737821121)
                ·
                  refine ⟨1365977212044561553365841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1821302949392748737821121 1365977212044561553365841)
                  ·
                    refine ⟨1024482909033421165024381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1365977212044561553365841 1024482909033421165024381)
                    ·
                      refine ⟨384181090887532936884143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1024482909033421165024381 384181090887532936884143)
                      ·
                        rfl

theorem cell23_748190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_748190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748190 prefixEnd_748190 := by exact prefixLift 748190
  have htrace : WordTrace (prefixWord ++ tailWord_748190) baseStart_748190 baseEnd_748190 := by
    simpa [prefixWord, tailWord_748190, baseEnd_748190] using wordTrace_append hprefix tailTrace_748190
  have hstable : (prefixWord ++ tailWord_748190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748190).length < 2 ^ (prefixWord ++ tailWord_748190).sum := by decide
  have hdescent : baseEnd_748190 < baseStart_748190 := by decide
  rcases family_descends (prefixWord ++ tailWord_748190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748214 : List Nat := [5, 1, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_748214 : Nat := 118140960795 + 748214 * 2 ^ 59
def prefixEnd_748214 : Nat := 4983230072969 + 3 ^ 40 * 748214 * 2
def baseEnd_748214 : Nat := 128064471474413614328011

theorem tailTrace_748214 : CollatzResearch.WordTrace tailWord_748214 prefixEnd_748214 128064471474413614328011 := by
  unfold tailWord_748214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1705600406959746101427731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18193071007570625081895797 1705600406959746101427731)
  ·
    refine ⟨2558400610439619152141597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1705600406959746101427731 2558400610439619152141597)
    ·
      refine ⟨959400228914857182053099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2558400610439619152141597 959400228914857182053099)
      ·
        refine ⟨1439100343372285773079649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 959400228914857182053099 1439100343372285773079649)
        ·
          refine ⟨1079325257529214329809737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1439100343372285773079649 1079325257529214329809737)
          ·
            refine ⟨809493943146910747357303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1079325257529214329809737 809493943146910747357303)
            ·
              refine ⟨1214240914720366121035955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809493943146910747357303 1214240914720366121035955)
              ·
                refine ⟨1821361372080549181553933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1214240914720366121035955 1821361372080549181553933)
                ·
                  refine ⟨683010514530205943082725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1821361372080549181553933 683010514530205943082725)
                  ·
                    refine ⟨128064471474413614328011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 683010514530205943082725 128064471474413614328011)
                    ·
                      rfl

theorem cell23_748214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_748214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748214 prefixEnd_748214 := by exact prefixLift 748214
  have htrace : WordTrace (prefixWord ++ tailWord_748214) baseStart_748214 baseEnd_748214 := by
    simpa [prefixWord, tailWord_748214, baseEnd_748214] using wordTrace_append hprefix tailTrace_748214
  have hstable : (prefixWord ++ tailWord_748214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748214).length < 2 ^ (prefixWord ++ tailWord_748214).sum := by decide
  have hdescent : baseEnd_748214 < baseStart_748214 := by decide
  rcases family_descends (prefixWord ++ tailWord_748214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748270 : List Nat := [4, 1, 2, 1, 1, 3, 1, 4, 2, 4]
def baseStart_748270 : Nat := 118140960795 + 748270 * 2 ^ 59
def prefixEnd_748270 : Nat := 4983230072969 + 3 ^ 40 * 748270 * 2
def baseEnd_748270 : Nat := 128074056446630874627925

theorem tailTrace_748270 : CollatzResearch.WordTrace tailWord_748270 prefixEnd_748270 128074056446630874627925 := by
  unfold tailWord_748270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3411456124894132398360283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18194432666102039457921509 3411456124894132398360283)
  ·
    refine ⟨5117184187341198597540425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3411456124894132398360283 5117184187341198597540425)
    ·
      refine ⟨3837888140505898948155319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5117184187341198597540425 3837888140505898948155319)
      ·
        refine ⟨5756832210758848422232979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3837888140505898948155319 5756832210758848422232979)
        ·
          refine ⟨8635248316138272633349469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5756832210758848422232979 8635248316138272633349469)
          ·
            refine ⟨3238218118551852237506051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8635248316138272633349469 3238218118551852237506051)
            ·
              refine ⟨4857327177827778356259077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3238218118551852237506051 4857327177827778356259077)
              ·
                refine ⟨910748845842708441798577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4857327177827778356259077 910748845842708441798577)
                ·
                  refine ⟨683061634382031331348933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 910748845842708441798577 683061634382031331348933)
                  ·
                    refine ⟨128074056446630874627925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 683061634382031331348933 128074056446630874627925)
                    ·
                      rfl

theorem cell23_748270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_748270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748270 prefixEnd_748270 := by exact prefixLift 748270
  have htrace : WordTrace (prefixWord ++ tailWord_748270) baseStart_748270 baseEnd_748270 := by
    simpa [prefixWord, tailWord_748270, baseEnd_748270] using wordTrace_append hprefix tailTrace_748270
  have hstable : (prefixWord ++ tailWord_748270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748270).length < 2 ^ (prefixWord ++ tailWord_748270).sum := by decide
  have hdescent : baseEnd_748270 < baseStart_748270 := by decide
  rcases family_descends (prefixWord ++ tailWord_748270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748290 : List Nat := [3, 4, 1, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_748290 : Nat := 118140960795 + 748290 * 2 ^ 59
def prefixEnd_748290 : Nat := 4983230072969 + 3 ^ 40 * 748290 * 2
def baseEnd_748290 : Nat := 384232438952982545633683

theorem tailTrace_748290 : CollatzResearch.WordTrace tailWord_748290 prefixEnd_748290 384232438952982545633683 := by
  unfold tailWord_748290
  simp only [CollatzResearch.WordTrace]
  refine ⟨6823094614770150650652581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18194918972720401735073549 6823094614770150650652581)
  ·
    refine ⟨1279330240269403246997359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6823094614770150650652581 1279330240269403246997359)
    ·
      refine ⟨1918995360404104870496039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1279330240269403246997359 1918995360404104870496039)
      ·
        refine ⟨2878493040606157305744059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1918995360404104870496039 2878493040606157305744059)
        ·
          refine ⟨4317739560909235958616089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2878493040606157305744059 4317739560909235958616089)
          ·
            refine ⟨3238304670681926968962067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4317739560909235958616089 3238304670681926968962067)
            ·
              refine ⟨4857457006022890453443101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3238304670681926968962067 4857457006022890453443101)
              ·
                refine ⟨1821546377258583920041163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4857457006022890453443101 1821546377258583920041163)
                ·
                  refine ⟨2732319565887875880061745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1821546377258583920041163 2732319565887875880061745)
                  ·
                    refine ⟨2049239674415906910046309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2732319565887875880061745 2049239674415906910046309)
                    ·
                      refine ⟨384232438952982545633683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2049239674415906910046309 384232438952982545633683)
                      ·
                        rfl

theorem cell23_748290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_748290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748290 prefixEnd_748290 := by exact prefixLift 748290
  have htrace : WordTrace (prefixWord ++ tailWord_748290) baseStart_748290 baseEnd_748290 := by
    simpa [prefixWord, tailWord_748290, baseEnd_748290] using wordTrace_append hprefix tailTrace_748290
  have hstable : (prefixWord ++ tailWord_748290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748290).length < 2 ^ (prefixWord ++ tailWord_748290).sum := by decide
  have hdescent : baseEnd_748290 < baseStart_748290 := by decide
  rcases family_descends (prefixWord ++ tailWord_748290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748311 : List Nat := [1, 1, 3, 4, 3, 1, 2, 3, 1, 2, 2]
def baseStart_748311 : Nat := 118140960795 + 748311 * 2 ^ 59
def prefixEnd_748311 : Nat := 4983230072969 + 3 ^ 40 * 748311 * 2
def baseEnd_748311 : Nat := 384243222046726963471087

theorem tailTrace_748311 : CollatzResearch.WordTrace tailWord_748311 prefixEnd_748311 384243222046726963471087 := by
  unfold tailWord_748311
  simp only [CollatzResearch.WordTrace]
  refine ⟨27293144392004523189124787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18195429594669682126083191 27293144392004523189124787)
  ·
    refine ⟨40939716588006784783687181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27293144392004523189124787 40939716588006784783687181)
    ·
      refine ⟨15352393720502544293882693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40939716588006784783687181 15352393720502544293882693)
      ·
        refine ⟨2878573822594227055103005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15352393720502544293882693 2878573822594227055103005)
        ·
          refine ⟨1079465183472835145663627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2878573822594227055103005 1079465183472835145663627)
          ·
            refine ⟨1619197775209252718495441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079465183472835145663627 1619197775209252718495441)
            ·
              refine ⟨1214398331406939538871581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1619197775209252718495441 1214398331406939538871581)
              ·
                refine ⟨455399374277602327076843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1214398331406939538871581 455399374277602327076843)
                ·
                  refine ⟨683099061416403490615265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 455399374277602327076843 683099061416403490615265)
                  ·
                    refine ⟨512324296062302617961449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 683099061416403490615265 512324296062302617961449)
                    ·
                      refine ⟨384243222046726963471087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 512324296062302617961449 384243222046726963471087)
                      ·
                        rfl

theorem cell23_748311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_748311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748311 prefixEnd_748311 := by exact prefixLift 748311
  have htrace : WordTrace (prefixWord ++ tailWord_748311) baseStart_748311 baseEnd_748311 := by
    simpa [prefixWord, tailWord_748311, baseEnd_748311] using wordTrace_append hprefix tailTrace_748311
  have hstable : (prefixWord ++ tailWord_748311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748311).length < 2 ^ (prefixWord ++ tailWord_748311).sum := by decide
  have hdescent : baseEnd_748311 < baseStart_748311 := by decide
  rcases family_descends (prefixWord ++ tailWord_748311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748401 : List Nat := [1, 2, 2, 2, 1, 6, 2, 1, 2, 2, 2]
def baseStart_748401 : Nat := 118140960795 + 748401 * 2 ^ 59
def prefixEnd_748401 : Nat := 4983230072969 + 3 ^ 40 * 748401 * 2
def baseEnd_748401 : Nat := 384289435305631611345673

theorem tailTrace_748401 : CollatzResearch.WordTrace tailWord_748401 prefixEnd_748401 384289435305631611345673 := by
  unfold tailWord_748401
  simp only [CollatzResearch.WordTrace]
  refine ⟨27296426961678468559901057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18197617974452312373267371 27296426961678468559901057)
  ·
    refine ⟨20472320221258851419925793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27296426961678468559901057 20472320221258851419925793)
    ·
      refine ⟨15354240165944138564944345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20472320221258851419925793 15354240165944138564944345)
      ·
        refine ⟨11515680124458103923708259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15354240165944138564944345 11515680124458103923708259)
        ·
          refine ⟨17273520186687155885562389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11515680124458103923708259 17273520186687155885562389)
          ·
            refine ⟨809696258750960432135737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17273520186687155885562389 809696258750960432135737)
            ·
              refine ⟨607272194063220324101803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 809696258750960432135737 607272194063220324101803)
              ·
                refine ⟨910908291094830486152705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607272194063220324101803 910908291094830486152705)
                ·
                  refine ⟨683181218321122864614529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 910908291094830486152705 683181218321122864614529)
                  ·
                    refine ⟨512385913740842148460897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 683181218321122864614529 512385913740842148460897)
                    ·
                      refine ⟨384289435305631611345673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 512385913740842148460897 384289435305631611345673)
                      ·
                        rfl

theorem cell23_748401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_748401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748401 prefixEnd_748401 := by exact prefixLift 748401
  have htrace : WordTrace (prefixWord ++ tailWord_748401) baseStart_748401 baseEnd_748401 := by
    simpa [prefixWord, tailWord_748401, baseEnd_748401] using wordTrace_append hprefix tailTrace_748401
  have hstable : (prefixWord ++ tailWord_748401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748401).length < 2 ^ (prefixWord ++ tailWord_748401).sum := by decide
  have hdescent : baseEnd_748401 < baseStart_748401 := by decide
  rcases family_descends (prefixWord ++ tailWord_748401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748443 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 3]
def baseStart_748443 : Nat := 118140960795 + 748443 * 2 ^ 59
def prefixEnd_748443 : Nat := 4983230072969 + 3 ^ 40 * 748443 * 2
def baseEnd_748443 : Nat := 384311001493120447020479

theorem tailTrace_748443 : CollatzResearch.WordTrace tailWord_748443 prefixEnd_748443 384311001493120447020479 := by
  unfold tailWord_748443
  simp only [CollatzResearch.WordTrace]
  refine ⟨27297958827526309732929983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18198639218350873155286655 27297958827526309732929983)
  ·
    refine ⟨40946938241289464599394975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27297958827526309732929983 40946938241289464599394975)
    ·
      refine ⟨61420407361934196899092463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40946938241289464599394975 61420407361934196899092463)
      ·
        refine ⟨92130611042901295348638695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61420407361934196899092463 92130611042901295348638695)
        ·
          refine ⟨138195916564351943022958043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92130611042901295348638695 138195916564351943022958043)
          ·
            refine ⟨207293874846527914534437065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138195916564351943022958043 207293874846527914534437065)
            ·
              refine ⟨155470406134895935900827799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207293874846527914534437065 155470406134895935900827799)
              ·
                refine ⟨233205609202343903851241699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155470406134895935900827799 233205609202343903851241699)
                ·
                  refine ⟨349808413803515855776862549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233205609202343903851241699 349808413803515855776862549)
                  ·
                    refine ⟨1024829337314987858721277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 349808413803515855776862549 1024829337314987858721277)
                    ·
                      refine ⟨384311001493120447020479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1024829337314987858721277 384311001493120447020479)
                      ·
                        rfl

theorem cell23_748443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 3].length) (baseStart_748443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748443 prefixEnd_748443 := by exact prefixLift 748443
  have htrace : WordTrace (prefixWord ++ tailWord_748443) baseStart_748443 baseEnd_748443 := by
    simpa [prefixWord, tailWord_748443, baseEnd_748443] using wordTrace_append hprefix tailTrace_748443
  have hstable : (prefixWord ++ tailWord_748443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748443).length < 2 ^ (prefixWord ++ tailWord_748443).sum := by decide
  have hdescent : baseEnd_748443 < baseStart_748443 := by decide
  rcases family_descends (prefixWord ++ tailWord_748443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748453 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 4, 4, 4]
def baseStart_748453 : Nat := 118140960795 + 748453 * 2 ^ 59
def prefixEnd_748453 : Nat := 4983230072969 + 3 ^ 40 * 748453 * 2
def baseEnd_748453 : Nat := 384316136299665407895433

theorem tailTrace_748453 : CollatzResearch.WordTrace tailWord_748453 prefixEnd_748453 384316136299665407895433 := by
  unfold tailWord_748453
  simp only [CollatzResearch.WordTrace]
  refine ⟨27298323557490081440794013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18198882371660054293862675 27298323557490081440794013)
  ·
    refine ⟨10236871334058780540297755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27298323557490081440794013 10236871334058780540297755)
    ·
      refine ⟨15355307001088170810446633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10236871334058780540297755 15355307001088170810446633)
      ·
        refine ⟨11516480250816128107834975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15355307001088170810446633 11516480250816128107834975)
        ·
          refine ⟨17274720376224192161752463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11516480250816128107834975 17274720376224192161752463)
          ·
            refine ⟨25912080564336288242628695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17274720376224192161752463 25912080564336288242628695)
            ·
              refine ⟨38868120846504432363943043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25912080564336288242628695 38868120846504432363943043)
              ·
                refine ⟨58302181269756648545914565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38868120846504432363943043 58302181269756648545914565)
                ·
                  refine ⟨10931658988079371602358981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58302181269756648545914565 10931658988079371602358981)
                  ·
                    refine ⟨2049686060264882175442309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10931658988079371602358981 2049686060264882175442309)
                    ·
                      refine ⟨384316136299665407895433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2049686060264882175442309 384316136299665407895433)
                      ·
                        rfl

theorem cell23_748453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_748453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748453 prefixEnd_748453 := by exact prefixLift 748453
  have htrace : WordTrace (prefixWord ++ tailWord_748453) baseStart_748453 baseEnd_748453 := by
    simpa [prefixWord, tailWord_748453, baseEnd_748453] using wordTrace_append hprefix tailTrace_748453
  have hstable : (prefixWord ++ tailWord_748453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748453).length < 2 ^ (prefixWord ++ tailWord_748453).sum := by decide
  have hdescent : baseEnd_748453 < baseStart_748453 := by decide
  rcases family_descends (prefixWord ++ tailWord_748453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748477 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 1, 4, 3]
def baseStart_748477 : Nat := 118140960795 + 748477 * 2 ^ 59
def prefixEnd_748477 : Nat := 4983230072969 + 3 ^ 40 * 748477 * 2
def baseEnd_748477 : Nat := 384328459835373313995323

theorem tailTrace_748477 : CollatzResearch.WordTrace tailWord_748477 prefixEnd_748477 384328459835373313995323 := by
  unfold tailWord_748477
  simp only [CollatzResearch.WordTrace]
  refine ⟨27299198909403133539667685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18199465939602089026445123 27299198909403133539667685)
  ·
    refine ⟨5118599795513087538687691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27299198909403133539667685 5118599795513087538687691)
    ·
      refine ⟨7677899693269631308031537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5118599795513087538687691 7677899693269631308031537)
      ·
        refine ⟨5758424769952223481023653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7677899693269631308031537 5758424769952223481023653)
        ·
          refine ⟨1079704644366041902691935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5758424769952223481023653 1079704644366041902691935)
          ·
            refine ⟨1619556966549062854037903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079704644366041902691935 1619556966549062854037903)
            ·
              refine ⟨2429335449823594281056855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619556966549062854037903 2429335449823594281056855)
              ·
                refine ⟨3644003174735391421585283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2429335449823594281056855 3644003174735391421585283)
                ·
                  refine ⟨5466004762103087132377925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3644003174735391421585283 5466004762103087132377925)
                  ·
                    refine ⟨1024875892894328837320861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5466004762103087132377925 1024875892894328837320861)
                    ·
                      refine ⟨384328459835373313995323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1024875892894328837320861 384328459835373313995323)
                      ·
                        rfl

theorem cell23_748477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_748477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748477 prefixEnd_748477 := by exact prefixLift 748477
  have htrace : WordTrace (prefixWord ++ tailWord_748477) baseStart_748477 baseEnd_748477 := by
    simpa [prefixWord, tailWord_748477, baseEnd_748477] using wordTrace_append hprefix tailTrace_748477
  have hstable : (prefixWord ++ tailWord_748477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748477).length < 2 ^ (prefixWord ++ tailWord_748477).sum := by decide
  have hdescent : baseEnd_748477 < baseStart_748477 := by decide
  rcases family_descends (prefixWord ++ tailWord_748477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748500 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_748500 : Nat := 118140960795 + 748500 * 2 ^ 59
def prefixEnd_748500 : Nat := 4983230072969 + 3 ^ 40 * 748500 * 2
def baseEnd_748500 : Nat := 384340269890426724007717

theorem tailTrace_748500 : CollatzResearch.WordTrace tailWord_748500 prefixEnd_748500 384340269890426724007717 := by
  unfold tailWord_748500
  simp only [CollatzResearch.WordTrace]
  refine ⟨13650018894159904233877477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18200025192213205645169969 13650018894159904233877477)
  ·
    refine ⟨2559378542654982043852027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13650018894159904233877477 2559378542654982043852027)
    ·
      refine ⟨3839067813982473065778041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2559378542654982043852027 3839067813982473065778041)
      ·
        refine ⟨2879300860486854799333531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3839067813982473065778041 2879300860486854799333531)
        ·
          refine ⟨4318951290730282199000297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2879300860486854799333531 4318951290730282199000297)
          ·
            refine ⟨3239213468047711649250223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4318951290730282199000297 3239213468047711649250223)
            ·
              refine ⟨4858820202071567473875335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3239213468047711649250223 4858820202071567473875335)
              ·
                refine ⟨7288230303107351210813003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4858820202071567473875335 7288230303107351210813003)
                ·
                  refine ⟨10932345454661026816219505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7288230303107351210813003 10932345454661026816219505)
                  ·
                    refine ⟨8199259090995770112164629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10932345454661026816219505 8199259090995770112164629)
                    ·
                      refine ⟨384340269890426724007717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8199259090995770112164629 384340269890426724007717)
                      ·
                        rfl

theorem cell23_748500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_748500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748500 prefixEnd_748500 := by exact prefixLift 748500
  have htrace : WordTrace (prefixWord ++ tailWord_748500) baseStart_748500 baseEnd_748500 := by
    simpa [prefixWord, tailWord_748500, baseEnd_748500] using wordTrace_append hprefix tailTrace_748500
  have hstable : (prefixWord ++ tailWord_748500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748500).length < 2 ^ (prefixWord ++ tailWord_748500).sum := by decide
  have hdescent : baseEnd_748500 < baseStart_748500 := by decide
  rcases family_descends (prefixWord ++ tailWord_748500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748503 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 7]
def baseStart_748503 : Nat := 118140960795 + 748503 * 2 ^ 59
def prefixEnd_748503 : Nat := 4983230072969 + 3 ^ 40 * 748503 * 2
def baseEnd_748503 : Nat := 384341810332390212270203

theorem tailTrace_748503 : CollatzResearch.WordTrace tailWord_748503 prefixEnd_748503 384341810332390212270203 := by
  unfold tailWord_748503
  simp only [CollatzResearch.WordTrace]
  refine ⟨27300147207308939980114163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18200098138205959986742775 27300147207308939980114163)
  ·
    refine ⟨40950220810963409970171245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27300147207308939980114163 40950220810963409970171245)
    ·
      refine ⟨15356332804111278738814217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40950220810963409970171245 15356332804111278738814217)
      ·
        refine ⟨11517249603083459054110663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15356332804111278738814217 11517249603083459054110663)
        ·
          refine ⟨17275874404625188581165995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11517249603083459054110663 17275874404625188581165995)
          ·
            refine ⟨25913811606937782871748993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17275874404625188581165995 25913811606937782871748993)
            ·
              refine ⟨19435358705203337153811745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25913811606937782871748993 19435358705203337153811745)
              ·
                refine ⟨14576519028902502865358809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19435358705203337153811745 14576519028902502865358809)
                ·
                  refine ⟨10932389271676877149019107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14576519028902502865358809 10932389271676877149019107)
                  ·
                    refine ⟨16398583907515315723528661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10932389271676877149019107 16398583907515315723528661)
                    ·
                      refine ⟨384341810332390212270203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16398583907515315723528661 384341810332390212270203)
                      ·
                        rfl

theorem cell23_748503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_748503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748503 prefixEnd_748503 := by exact prefixLift 748503
  have htrace : WordTrace (prefixWord ++ tailWord_748503) baseStart_748503 baseEnd_748503 := by
    simpa [prefixWord, tailWord_748503, baseEnd_748503] using wordTrace_append hprefix tailTrace_748503
  have hstable : (prefixWord ++ tailWord_748503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748503).length < 2 ^ (prefixWord ++ tailWord_748503).sum := by decide
  have hdescent : baseEnd_748503 < baseStart_748503 := by decide
  rcases family_descends (prefixWord ++ tailWord_748503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748527 : List Nat := [1, 1, 2, 1, 4, 4, 2, 2, 1, 5]
def baseStart_748527 : Nat := 118140960795 + 748527 * 2 ^ 59
def prefixEnd_748527 : Nat := 4983230072969 + 3 ^ 40 * 748527 * 2
def baseEnd_748527 : Nat := 128118044622699372790031

theorem tailTrace_748527 : CollatzResearch.WordTrace tailWord_748527 prefixEnd_748527 128118044622699372790031 := by
  unfold tailWord_748527
  simp only [CollatzResearch.WordTrace]
  refine ⟨27301022559221992078987835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18200681706147994719325223 27301022559221992078987835)
  ·
    refine ⟨40951533838832988118481753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27301022559221992078987835 40951533838832988118481753)
    ·
      refine ⟨30713650379124741088861315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40951533838832988118481753 30713650379124741088861315)
      ·
        refine ⟨46070475568687111633291973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30713650379124741088861315 46070475568687111633291973)
        ·
          refine ⟨8638214169128833431242245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46070475568687111633291973 8638214169128833431242245)
          ·
            refine ⟨1619665156711656268357921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8638214169128833431242245 1619665156711656268357921)
            ·
              refine ⟨1214748867533742201268441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1619665156711656268357921 1214748867533742201268441)
              ·
                refine ⟨911061650650306650951331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1214748867533742201268441 911061650650306650951331)
                ·
                  refine ⟨1366592475975459976426997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 911061650650306650951331 1366592475975459976426997)
                  ·
                    refine ⟨128118044622699372790031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1366592475975459976426997 128118044622699372790031)
                    ·
                      rfl

theorem cell23_748527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 5].length) (baseStart_748527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748527 prefixEnd_748527 := by exact prefixLift 748527
  have htrace : WordTrace (prefixWord ++ tailWord_748527) baseStart_748527 baseEnd_748527 := by
    simpa [prefixWord, tailWord_748527, baseEnd_748527] using wordTrace_append hprefix tailTrace_748527
  have hstable : (prefixWord ++ tailWord_748527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748527).length < 2 ^ (prefixWord ++ tailWord_748527).sum := by decide
  have hdescent : baseEnd_748527 < baseStart_748527 := by decide
  rcases family_descends (prefixWord ++ tailWord_748527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748534 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2]
def baseStart_748534 : Nat := 118140960795 + 748534 * 2 ^ 59
def prefixEnd_748534 : Nat := 4983230072969 + 3 ^ 40 * 748534 * 2
def baseEnd_748534 : Nat := 384357728232679590982561

theorem tailTrace_748534 : CollatzResearch.WordTrace tailWord_748534 prefixEnd_748534 384357728232679590982561 := by
  unfold tailWord_748534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1706329866887289517155791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18200851913464421516328437 1706329866887289517155791)
  ·
    refine ⟨2559494800330934275733687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1706329866887289517155791 2559494800330934275733687)
    ·
      refine ⟨3839242200496401413600531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2559494800330934275733687 3839242200496401413600531)
      ·
        refine ⟨5758863300744602120400797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3839242200496401413600531 5758863300744602120400797)
        ·
          refine ⟨2159573737779225795150299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5758863300744602120400797 2159573737779225795150299)
          ·
            refine ⟨3239360606668838692725449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2159573737779225795150299 3239360606668838692725449)
            ·
              refine ⟨2429520455001629019544087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3239360606668838692725449 2429520455001629019544087)
              ·
                refine ⟨3644280682502443529316131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2429520455001629019544087 3644280682502443529316131)
                ·
                  refine ⟨5466421023753665293974197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3644280682502443529316131 5466421023753665293974197)
                  ·
                    refine ⟨512476970976906121310081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5466421023753665293974197 512476970976906121310081)
                    ·
                      refine ⟨384357728232679590982561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 512476970976906121310081 384357728232679590982561)
                      ·
                        rfl

theorem cell23_748534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_748534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748534 prefixEnd_748534 := by exact prefixLift 748534
  have htrace : WordTrace (prefixWord ++ tailWord_748534) baseStart_748534 baseEnd_748534 := by
    simpa [prefixWord, tailWord_748534, baseEnd_748534] using wordTrace_append hprefix tailTrace_748534
  have hstable : (prefixWord ++ tailWord_748534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748534).length < 2 ^ (prefixWord ++ tailWord_748534).sum := by decide
  have hdescent : baseEnd_748534 < baseStart_748534 := by decide
  rcases family_descends (prefixWord ++ tailWord_748534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748558 : List Nat := [4, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3]
def baseStart_748558 : Nat := 118140960795 + 748558 * 2 ^ 59
def prefixEnd_748558 : Nat := 4983230072969 + 3 ^ 40 * 748558 * 2
def baseEnd_748558 : Nat := 384370051768387497082451

theorem tailTrace_748558 : CollatzResearch.WordTrace tailWord_748558 prefixEnd_748558 384370051768387497082451 := by
  unfold tailWord_748558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3412769152763710546670791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18201435481406456248910885 3412769152763710546670791)
  ·
    refine ⟨5119153729145565820006187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3412769152763710546670791 5119153729145565820006187)
    ·
      refine ⟨7678730593718348730009281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5119153729145565820006187 7678730593718348730009281)
      ·
        refine ⟨5759047945288761547506961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7678730593718348730009281 5759047945288761547506961)
        ·
          refine ⟨4319285958966571160630221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5759047945288761547506961 4319285958966571160630221)
          ·
            refine ⟨1619732234612464185236333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4319285958966571160630221 1619732234612464185236333)
            ·
              refine ⟨607399587979674069463625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1619732234612464185236333 607399587979674069463625)
              ·
                refine ⟨455549690984755552097719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 607399587979674069463625 455549690984755552097719)
                ·
                  refine ⟨683324536477133328146579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 455549690984755552097719 683324536477133328146579)
                  ·
                    refine ⟨1024986804715699992219869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 683324536477133328146579 1024986804715699992219869)
                    ·
                      refine ⟨384370051768387497082451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1024986804715699992219869 384370051768387497082451)
                      ·
                        rfl

theorem cell23_748558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_748558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748558 prefixEnd_748558 := by exact prefixLift 748558
  have htrace : WordTrace (prefixWord ++ tailWord_748558) baseStart_748558 baseEnd_748558 := by
    simpa [prefixWord, tailWord_748558, baseEnd_748558] using wordTrace_append hprefix tailTrace_748558
  have hstable : (prefixWord ++ tailWord_748558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748558).length < 2 ^ (prefixWord ++ tailWord_748558).sum := by decide
  have hdescent : baseEnd_748558 < baseStart_748558 := by decide
  rcases family_descends (prefixWord ++ tailWord_748558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748567 : List Nat := [1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 5]
def baseStart_748567 : Nat := 118140960795 + 748567 * 2 ^ 59
def prefixEnd_748567 : Nat := 4983230072969 + 3 ^ 40 * 748567 * 2
def baseEnd_748567 : Nat := 384374673094277961869909

theorem tailTrace_748567 : CollatzResearch.WordTrace tailWord_748567 prefixEnd_748567 384374673094277961869909 := by
  unfold tailWord_748567
  simp only [CollatzResearch.WordTrace]
  refine ⟨27302481479077078910443955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18201654319384719273629303 27302481479077078910443955)
  ·
    refine ⟨40953722218615618365665933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27302481479077078910443955 40953722218615618365665933)
    ·
      refine ⟨15357645831980856887124725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40953722218615618365665933 15357645831980856887124725)
      ·
        refine ⟨1439779296748205333167943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15357645831980856887124725 1439779296748205333167943)
        ·
          refine ⟨2159668945122307999751915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1439779296748205333167943 2159668945122307999751915)
          ·
            refine ⟨3239503417683461999627873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2159668945122307999751915 3239503417683461999627873)
            ·
              refine ⟨2429627563262596499720905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3239503417683461999627873 2429627563262596499720905)
              ·
                refine ⟨1822220672446947374790679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2429627563262596499720905 1822220672446947374790679)
                ·
                  refine ⟨2733331008670421062186019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1822220672446947374790679 2733331008670421062186019)
                  ·
                    refine ⟨4099996513005631593279029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2733331008670421062186019 4099996513005631593279029)
                    ·
                      refine ⟨384374673094277961869909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4099996513005631593279029 384374673094277961869909)
                      ·
                        rfl

theorem cell23_748567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_748567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748567 prefixEnd_748567 := by exact prefixLift 748567
  have htrace : WordTrace (prefixWord ++ tailWord_748567) baseStart_748567 baseEnd_748567 := by
    simpa [prefixWord, tailWord_748567, baseEnd_748567] using wordTrace_append hprefix tailTrace_748567
  have hstable : (prefixWord ++ tailWord_748567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748567).length < 2 ^ (prefixWord ++ tailWord_748567).sum := by decide
  have hdescent : baseEnd_748567 < baseStart_748567 := by decide
  rcases family_descends (prefixWord ++ tailWord_748567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748570 : List Nat := [3, 1, 1, 3, 1, 2, 4, 8]
def baseStart_748570 : Nat := 118140960795 + 748570 * 2 ^ 59
def prefixEnd_748570 : Nat := 4983230072969 + 3 ^ 40 * 748570 * 2
def baseEnd_748570 : Nat := 14236156056897831486385

theorem tailTrace_748570 : CollatzResearch.WordTrace tailWord_748570 prefixEnd_748570 14236156056897831486385 := by
  unfold tailWord_748570
  simp only [CollatzResearch.WordTrace]
  refine ⟨6825647724516552605700791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18201727265377473615202109 6825647724516552605700791)
  ·
    refine ⟨10238471586774828908551187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6825647724516552605700791 10238471586774828908551187)
    ·
      refine ⟨15357707380162243362826781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10238471586774828908551187 15357707380162243362826781)
      ·
        refine ⟨5759140267560841261060043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15357707380162243362826781 5759140267560841261060043)
        ·
          refine ⟨8638710401341261891590065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5759140267560841261060043 8638710401341261891590065)
          ·
            refine ⟨6479032801005946418692549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8638710401341261891590065 6479032801005946418692549)
            ·
              refine ⟨1214818650188614953504853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6479032801005946418692549 1214818650188614953504853)
              ·
                refine ⟨14236156056897831486385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1214818650188614953504853 14236156056897831486385)
                ·
                  rfl

theorem cell23_748570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 8].length) (baseStart_748570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748570 prefixEnd_748570 := by exact prefixLift 748570
  have htrace : WordTrace (prefixWord ++ tailWord_748570) baseStart_748570 baseEnd_748570 := by
    simpa [prefixWord, tailWord_748570, baseEnd_748570] using wordTrace_append hprefix tailTrace_748570
  have hstable : (prefixWord ++ tailWord_748570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748570).length < 2 ^ (prefixWord ++ tailWord_748570).sum := by decide
  have hdescent : baseEnd_748570 < baseStart_748570 := by decide
  rcases family_descends (prefixWord ++ tailWord_748570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748601 : List Nat := [1, 2, 1, 5, 2, 2, 3, 1, 1, 2, 3]
def baseStart_748601 : Nat := 118140960795 + 748601 * 2 ^ 59
def prefixEnd_748601 : Nat := 4983230072969 + 3 ^ 40 * 748601 * 2
def baseEnd_748601 : Nat := 384392131436530828844753

theorem tailTrace_748601 : CollatzResearch.WordTrace tailWord_748601 prefixEnd_748601 384392131436530828844753 := by
  unfold tailWord_748601
  simp only [CollatzResearch.WordTrace]
  refine ⟨27303721560953902717181657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18202481040635935144787771 27303721560953902717181657)
  ·
    refine ⟨20477791170715427037886243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27303721560953902717181657 20477791170715427037886243)
    ·
      refine ⟨30716686756073140556829365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20477791170715427037886243 30716686756073140556829365)
      ·
        refine ⟨2879689383381856927202753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30716686756073140556829365 2879689383381856927202753)
        ·
          refine ⟨2159767037536392695402065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2879689383381856927202753 2159767037536392695402065)
          ·
            refine ⟨1619825278152294521551549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2159767037536392695402065 1619825278152294521551549)
            ·
              refine ⟨607434479307110445581831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1619825278152294521551549 607434479307110445581831)
              ·
                refine ⟨911151718960665668372747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607434479307110445581831 911151718960665668372747)
                ·
                  refine ⟨1366727578440998502559121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 911151718960665668372747 1366727578440998502559121)
                  ·
                    refine ⟨1025045683830748876919341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1366727578440998502559121 1025045683830748876919341)
                    ·
                      refine ⟨384392131436530828844753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1025045683830748876919341 384392131436530828844753)
                      ·
                        rfl

theorem cell23_748601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_748601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748601 prefixEnd_748601 := by exact prefixLift 748601
  have htrace : WordTrace (prefixWord ++ tailWord_748601) baseStart_748601 baseEnd_748601 := by
    simpa [prefixWord, tailWord_748601, baseEnd_748601] using wordTrace_append hprefix tailTrace_748601
  have hstable : (prefixWord ++ tailWord_748601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748601).length < 2 ^ (prefixWord ++ tailWord_748601).sum := by decide
  have hdescent : baseEnd_748601 < baseStart_748601 := by decide
  rcases family_descends (prefixWord ++ tailWord_748601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748615 : List Nat := [1, 1, 4, 1, 3, 4, 2, 2, 1, 2, 2]
def baseStart_748615 : Nat := 118140960795 + 748615 * 2 ^ 59
def prefixEnd_748615 : Nat := 4983230072969 + 3 ^ 40 * 748615 * 2
def baseEnd_748615 : Nat := 384399320165693774069689

theorem tailTrace_748615 : CollatzResearch.WordTrace tailWord_748615 prefixEnd_748615 384399320165693774069689 := by
  unfold tailWord_748615
  simp only [CollatzResearch.WordTrace]
  refine ⟨27304232182903183108191299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18202821455268788738794199 27304232182903183108191299)
  ·
    refine ⟨40956348274354774662286949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27304232182903183108191299 40956348274354774662286949)
    ·
      refine ⟨7679315301441520249178803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40956348274354774662286949 7679315301441520249178803)
      ·
        refine ⟨11518972952162280373768205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7679315301441520249178803 11518972952162280373768205)
        ·
          refine ⟨4319614857060855140163077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11518972952162280373768205 4319614857060855140163077)
          ·
            refine ⟨809927785698910338780577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4319614857060855140163077 809927785698910338780577)
            ·
              refine ⟨607445839274182754085433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 809927785698910338780577 607445839274182754085433)
              ·
                refine ⟨455584379455637065564075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 607445839274182754085433 455584379455637065564075)
                ·
                  refine ⟨683376569183455598346113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 455584379455637065564075 683376569183455598346113)
                  ·
                    refine ⟨512532426887591698759585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 683376569183455598346113 512532426887591698759585)
                    ·
                      refine ⟨384399320165693774069689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 512532426887591698759585 384399320165693774069689)
                      ·
                        rfl

theorem cell23_748615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 1, 2, 2].length) (baseStart_748615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748615 prefixEnd_748615 := by exact prefixLift 748615
  have htrace : WordTrace (prefixWord ++ tailWord_748615) baseStart_748615 baseEnd_748615 := by
    simpa [prefixWord, tailWord_748615, baseEnd_748615] using wordTrace_append hprefix tailTrace_748615
  have hstable : (prefixWord ++ tailWord_748615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748615).length < 2 ^ (prefixWord ++ tailWord_748615).sum := by decide
  have hdescent : baseEnd_748615 < baseStart_748615 := by decide
  rcases family_descends (prefixWord ++ tailWord_748615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748711 : List Nat := [1, 1, 6, 2, 1, 1, 3, 3, 5]
def baseStart_748711 : Nat := 118140960795 + 748711 * 2 ^ 59
def prefixEnd_748711 : Nat := 4983230072969 + 3 ^ 40 * 748711 * 2
def baseEnd_748711 : Nat := 42716512700947266496583

theorem tailTrace_748711 : CollatzResearch.WordTrace tailWord_748711 prefixEnd_748711 42716512700947266496583 := by
  unfold tailWord_748711
  simp only [CollatzResearch.WordTrace]
  refine ⟨27307733590555391503685987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18205155727036927669123991 27307733590555391503685987)
  ·
    refine ⟨40961600385833087255528981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27307733590555391503685987 40961600385833087255528981)
    ·
      refine ⟨1920075018085925965102921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40961600385833087255528981 1920075018085925965102921)
      ·
        refine ⟨1440056263564444473827191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1920075018085925965102921 1440056263564444473827191)
        ·
          refine ⟨2160084395346666710740787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1440056263564444473827191 2160084395346666710740787)
          ·
            refine ⟨3240126593020000066111181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2160084395346666710740787 3240126593020000066111181)
            ·
              refine ⟨1215047472382500024791693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3240126593020000066111181 1215047472382500024791693)
              ·
                refine ⟨455642802143437509296885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1215047472382500024791693 455642802143437509296885)
                ·
                  refine ⟨42716512700947266496583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 455642802143437509296885 42716512700947266496583)
                  ·
                    rfl

theorem cell23_748711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 5].length) (baseStart_748711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748711 prefixEnd_748711 := by exact prefixLift 748711
  have htrace : WordTrace (prefixWord ++ tailWord_748711) baseStart_748711 baseEnd_748711 := by
    simpa [prefixWord, tailWord_748711, baseEnd_748711] using wordTrace_append hprefix tailTrace_748711
  have hstable : (prefixWord ++ tailWord_748711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748711).length < 2 ^ (prefixWord ++ tailWord_748711).sum := by decide
  have hdescent : baseEnd_748711 < baseStart_748711 := by decide
  rcases family_descends (prefixWord ++ tailWord_748711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748720 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 1, 10]
def baseStart_748720 : Nat := 118140960795 + 748720 * 2 ^ 59
def prefixEnd_748720 : Nat := 4983230072969 + 3 ^ 40 * 748720 * 2
def baseEnd_748720 : Nat := 128151078544805287752235

theorem tailTrace_748720 : CollatzResearch.WordTrace tailWord_748720 prefixEnd_748720 128151078544805287752235 := by
  unfold tailWord_748720
  simp only [CollatzResearch.WordTrace]
  refine ⟨13654030923761393020381807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18205374565015190693842409 13654030923761393020381807)
  ·
    refine ⟨20481046385642089530572711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13654030923761393020381807 20481046385642089530572711)
    ·
      refine ⟨30721569578463134295859067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20481046385642089530572711 30721569578463134295859067)
      ·
        refine ⟨46082354367694701443788601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30721569578463134295859067 46082354367694701443788601)
        ·
          refine ⟨34561765775771026082841451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46082354367694701443788601 34561765775771026082841451)
          ·
            refine ⟨51842648663656539124262177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34561765775771026082841451 51842648663656539124262177)
            ·
              refine ⟨38881986497742404343196633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51842648663656539124262177 38881986497742404343196633)
              ·
                refine ⟨29161489873306803257397475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38881986497742404343196633 29161489873306803257397475)
                ·
                  refine ⟨43742234809960204886096213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29161489873306803257397475 43742234809960204886096213)
                  ·
                    refine ⟨128151078544805287752235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 43742234809960204886096213 128151078544805287752235)
                    ·
                      rfl

theorem cell23_748720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 10].length) (baseStart_748720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748720 prefixEnd_748720 := by exact prefixLift 748720
  have htrace : WordTrace (prefixWord ++ tailWord_748720) baseStart_748720 baseEnd_748720 := by
    simpa [prefixWord, tailWord_748720, baseEnd_748720] using wordTrace_append hprefix tailTrace_748720
  have hstable : (prefixWord ++ tailWord_748720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748720).length < 2 ^ (prefixWord ++ tailWord_748720).sum := by decide
  have hdescent : baseEnd_748720 < baseStart_748720 := by decide
  rcases family_descends (prefixWord ++ tailWord_748720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748734 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_748734 : Nat := 118140960795 + 748734 * 2 ^ 59
def prefixEnd_748734 : Nat := 4983230072969 + 3 ^ 40 * 748734 * 2
def baseEnd_748734 : Nat := 384460424363578808481641

theorem tailTrace_748734 : CollatzResearch.WordTrace tailWord_748734 prefixEnd_748734 384460424363578808481641 := by
  unfold tailWord_748734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3413571558684008303971657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18205714979648044287848837 3413571558684008303971657)
  ·
    refine ⟨2560178669013006227978743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3413571558684008303971657 2560178669013006227978743)
    ·
      refine ⟨3840268003519509341968115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2560178669013006227978743 3840268003519509341968115)
      ·
        refine ⟨5760402005279264012952173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3840268003519509341968115 5760402005279264012952173)
        ·
          refine ⟨2160150751979724004857065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5760402005279264012952173 2160150751979724004857065)
          ·
            refine ⟨1620113063984793003642799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2160150751979724004857065 1620113063984793003642799)
            ·
              refine ⟨2430169595977189505464199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620113063984793003642799 2430169595977189505464199)
              ·
                refine ⟨3645254393965784258196299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2430169595977189505464199 3645254393965784258196299)
                ·
                  refine ⟨5467881590948676387294449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3645254393965784258196299 5467881590948676387294449)
                  ·
                    refine ⟨4100911193211507290470837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5467881590948676387294449 4100911193211507290470837)
                    ·
                      refine ⟨384460424363578808481641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4100911193211507290470837 384460424363578808481641)
                      ·
                        rfl

theorem cell23_748734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_748734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748734 prefixEnd_748734 := by exact prefixLift 748734
  have htrace : WordTrace (prefixWord ++ tailWord_748734) baseStart_748734 baseEnd_748734 := by
    simpa [prefixWord, tailWord_748734, baseEnd_748734] using wordTrace_append hprefix tailTrace_748734
  have hstable : (prefixWord ++ tailWord_748734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748734).length < 2 ^ (prefixWord ++ tailWord_748734).sum := by decide
  have hdescent : baseEnd_748734 < baseStart_748734 := by decide
  rcases family_descends (prefixWord ++ tailWord_748734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748744 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 2, 4, 2]
def baseStart_748744 : Nat := 118140960795 + 748744 * 2 ^ 59
def prefixEnd_748744 : Nat := 4983230072969 + 3 ^ 40 * 748744 * 2
def baseEnd_748744 : Nat := 384465559170123769356595

theorem tailTrace_748744 : CollatzResearch.WordTrace tailWord_748744 prefixEnd_748744 384465559170123769356595 := by
  unfold tailWord_748744
  simp only [CollatzResearch.WordTrace]
  refine ⟨13654468599717919069818643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18205958132957225426424857 13654468599717919069818643)
  ·
    refine ⟨20481702899576878604727965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13654468599717919069818643 20481702899576878604727965)
    ·
      refine ⟨7680638587341329476772987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20481702899576878604727965 7680638587341329476772987)
      ·
        refine ⟨11520957881011994215159481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7680638587341329476772987 11520957881011994215159481)
        ·
          refine ⟨8640718410758995661369611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11520957881011994215159481 8640718410758995661369611)
          ·
            refine ⟨12961077616138493492054417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8640718410758995661369611 12961077616138493492054417)
            ·
              refine ⟨9720808212103870119040813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12961077616138493492054417 9720808212103870119040813)
              ·
                refine ⟨3645303079538951294640305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9720808212103870119040813 3645303079538951294640305)
                ·
                  refine ⟨2733977309654213470980229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3645303079538951294640305 2733977309654213470980229)
                  ·
                    refine ⟨512620745560165025808793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2733977309654213470980229 512620745560165025808793)
                    ·
                      refine ⟨384465559170123769356595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 512620745560165025808793 384465559170123769356595)
                      ·
                        rfl

theorem cell23_748744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_748744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748744 prefixEnd_748744 := by exact prefixLift 748744
  have htrace : WordTrace (prefixWord ++ tailWord_748744) baseStart_748744 baseEnd_748744 := by
    simpa [prefixWord, tailWord_748744, baseEnd_748744] using wordTrace_append hprefix tailTrace_748744
  have hstable : (prefixWord ++ tailWord_748744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748744).length < 2 ^ (prefixWord ++ tailWord_748744).sum := by decide
  have hdescent : baseEnd_748744 < baseStart_748744 := by decide
  rcases family_descends (prefixWord ++ tailWord_748744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748747 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 3]
def baseStart_748747 : Nat := 118140960795 + 748747 * 2 ^ 59
def prefixEnd_748747 : Nat := 4983230072969 + 3 ^ 40 * 748747 * 2
def baseEnd_748747 : Nat := 384467099612087257619081

theorem tailTrace_748747 : CollatzResearch.WordTrace tailWord_748747 prefixEnd_748747 384467099612087257619081 := by
  unfold tailWord_748747
  simp only [CollatzResearch.WordTrace]
  refine ⟨27309046618424969651996495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18206031078949979767997663 27309046618424969651996495)
  ·
    refine ⟨40963569927637454477994743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27309046618424969651996495 40963569927637454477994743)
    ·
      refine ⟨61445354891456181716992115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40963569927637454477994743 61445354891456181716992115)
      ·
        refine ⟨92168032337184272575488173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61445354891456181716992115 92168032337184272575488173)
        ·
          refine ⟨34563012126444102215808065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92168032337184272575488173 34563012126444102215808065)
          ·
            refine ⟨25922259094833076661856049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34563012126444102215808065 25922259094833076661856049)
            ·
              refine ⟨19441694321124807496392037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25922259094833076661856049 19441694321124807496392037)
              ·
                refine ⟨3645317685210901405573507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19441694321124807496392037 3645317685210901405573507)
                ·
                  refine ⟨5467976527816352108360261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3645317685210901405573507 5467976527816352108360261)
                  ·
                    refine ⟨1025245598965566020317549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5467976527816352108360261 1025245598965566020317549)
                    ·
                      refine ⟨384467099612087257619081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1025245598965566020317549 384467099612087257619081)
                      ·
                        rfl

theorem cell23_748747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 3].length) (baseStart_748747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748747 prefixEnd_748747 := by exact prefixLift 748747
  have htrace : WordTrace (prefixWord ++ tailWord_748747) baseStart_748747 baseEnd_748747 := by
    simpa [prefixWord, tailWord_748747, baseEnd_748747] using wordTrace_append hprefix tailTrace_748747
  have hstable : (prefixWord ++ tailWord_748747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748747).length < 2 ^ (prefixWord ++ tailWord_748747).sum := by decide
  have hdescent : baseEnd_748747 < baseStart_748747 := by decide
  rcases family_descends (prefixWord ++ tailWord_748747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748754 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 5, 4]
def baseStart_748754 : Nat := 118140960795 + 748754 * 2 ^ 59
def prefixEnd_748754 : Nat := 4983230072969 + 3 ^ 40 * 748754 * 2
def baseEnd_748754 : Nat := 128156897992222910077183

theorem tailTrace_748754 : CollatzResearch.WordTrace tailWord_748754 prefixEnd_748754 128156897992222910077183 := by
  unfold tailWord_748754
  simp only [CollatzResearch.WordTrace]
  refine ⟨6827325482349902461875329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18206201286266406565000877 6827325482349902461875329)
  ·
    refine ⟨5120494111762426846406497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6827325482349902461875329 5120494111762426846406497)
    ·
      refine ⟨3840370583821820134804873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5120494111762426846406497 3840370583821820134804873)
      ·
        refine ⟨2880277937866365101103655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3840370583821820134804873 2880277937866365101103655)
        ·
          refine ⟨4320416906799547651655483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2880277937866365101103655 4320416906799547651655483)
          ·
            refine ⟨6480625360199321477483225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4320416906799547651655483 6480625360199321477483225)
            ·
              refine ⟨4860469020149491108112419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6480625360199321477483225 4860469020149491108112419)
              ·
                refine ⟨7290703530224236662168629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4860469020149491108112419 7290703530224236662168629)
                ·
                  refine ⟨683503455958522187078309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7290703530224236662168629 683503455958522187078309)
                  ·
                    refine ⟨128156897992222910077183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 683503455958522187078309 128156897992222910077183)
                    ·
                      rfl

theorem cell23_748754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_748754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748754 prefixEnd_748754 := by exact prefixLift 748754
  have htrace : WordTrace (prefixWord ++ tailWord_748754) baseStart_748754 baseEnd_748754 := by
    simpa [prefixWord, tailWord_748754, baseEnd_748754] using wordTrace_append hprefix tailTrace_748754
  have hstable : (prefixWord ++ tailWord_748754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748754).length < 2 ^ (prefixWord ++ tailWord_748754).sum := by decide
  have hdescent : baseEnd_748754 < baseStart_748754 := by decide
  rcases family_descends (prefixWord ++ tailWord_748754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748758 : List Nat := [5, 2, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_748758 : Nat := 118140960795 + 748758 * 2 ^ 59
def prefixEnd_748758 : Nat := 4983230072969 + 3 ^ 40 * 748758 * 2
def baseEnd_748758 : Nat := 128157582633095571527177

theorem tailTrace_748758 : CollatzResearch.WordTrace tailWord_748758 prefixEnd_748758 128157582633095571527177 := by
  unfold tailWord_748758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1706840488836569908165433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18206298547590079020431285 1706840488836569908165433)
  ·
    refine ⟨1280130366627427431124075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1706840488836569908165433 1280130366627427431124075)
    ·
      refine ⟨1920195549941141146686113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1280130366627427431124075 1920195549941141146686113)
      ·
        refine ⟨1440146662455855860014585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1920195549941141146686113 1440146662455855860014585)
        ·
          refine ⟨1080109996841891895010939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1440146662455855860014585 1080109996841891895010939)
          ·
            refine ⟨1620164995262837842516409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1080109996841891895010939 1620164995262837842516409)
            ·
              refine ⟨1215123746447128381887307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1620164995262837842516409 1215123746447128381887307)
              ·
                refine ⟨1822685619670692572830961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215123746447128381887307 1822685619670692572830961)
                ·
                  refine ⟨1367014214753019429623221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1822685619670692572830961 1367014214753019429623221)
                  ·
                    refine ⟨128157582633095571527177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1367014214753019429623221 128157582633095571527177)
                    ·
                      rfl

theorem cell23_748758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_748758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748758 prefixEnd_748758 := by exact prefixLift 748758
  have htrace : WordTrace (prefixWord ++ tailWord_748758) baseStart_748758 baseEnd_748758 := by
    simpa [prefixWord, tailWord_748758, baseEnd_748758] using wordTrace_append hprefix tailTrace_748758
  have hstable : (prefixWord ++ tailWord_748758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748758).length < 2 ^ (prefixWord ++ tailWord_748758).sum := by decide
  have hdescent : baseEnd_748758 < baseStart_748758 := by decide
  rcases family_descends (prefixWord ++ tailWord_748758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748781 : List Nat := [1, 5, 1, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_748781 : Nat := 118140960795 + 748781 * 2 ^ 59
def prefixEnd_748781 : Nat := 4983230072969 + 3 ^ 40 * 748781 * 2
def baseEnd_748781 : Nat := 384484557954340124593925

theorem tailTrace_748781 : CollatzResearch.WordTrace tailWord_748781 prefixEnd_748781 384484557954340124593925 := by
  unfold tailWord_748781
  simp only [CollatzResearch.WordTrace]
  refine ⟨27310286700301793458734197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18206857800201195639156131 27310286700301793458734197)
  ·
    refine ⟨2560339378153293136756331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27310286700301793458734197 2560339378153293136756331)
    ·
      refine ⟨3840509067229939705134497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2560339378153293136756331 3840509067229939705134497)
      ·
        refine ⟨2880381800422454778850873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3840509067229939705134497 2880381800422454778850873)
        ·
          refine ⟨2160286350316841084138155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2880381800422454778850873 2160286350316841084138155)
          ·
            refine ⟨3240429525475261626207233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2160286350316841084138155 3240429525475261626207233)
            ·
              refine ⟨2430322144106446219655425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3240429525475261626207233 2430322144106446219655425)
              ·
                refine ⟨1822741608079834664741569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2430322144106446219655425 1822741608079834664741569)
                ·
                  refine ⟨1367056206059875998556177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1822741608079834664741569 1367056206059875998556177)
                  ·
                    refine ⟨1025292154544906998917133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1367056206059875998556177 1025292154544906998917133)
                    ·
                      refine ⟨384484557954340124593925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1025292154544906998917133 384484557954340124593925)
                      ·
                        rfl

theorem cell23_748781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_748781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748781 prefixEnd_748781 := by exact prefixLift 748781
  have htrace : WordTrace (prefixWord ++ tailWord_748781) baseStart_748781 baseEnd_748781 := by
    simpa [prefixWord, tailWord_748781, baseEnd_748781] using wordTrace_append hprefix tailTrace_748781
  have hstable : (prefixWord ++ tailWord_748781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748781).length < 2 ^ (prefixWord ++ tailWord_748781).sum := by decide
  have hdescent : baseEnd_748781 < baseStart_748781 := by decide
  rcases family_descends (prefixWord ++ tailWord_748781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748811 : List Nat := [1, 1, 1, 1, 5, 4, 1, 2, 3, 1, 3]
def baseStart_748811 : Nat := 118140960795 + 748811 * 2 ^ 59
def prefixEnd_748811 : Nat := 4983230072969 + 3 ^ 40 * 748811 * 2
def baseEnd_748811 : Nat := 384499962373975007218787

theorem tailTrace_748811 : CollatzResearch.WordTrace tailWord_748811 prefixEnd_748811 384499962373975007218787 := by
  unfold tailWord_748811
  simp only [CollatzResearch.WordTrace]
  refine ⟨27311380890193108582326287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18207587260128739054884191 27311380890193108582326287)
  ·
    refine ⟨40967071335289662873489431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27311380890193108582326287 40967071335289662873489431)
    ·
      refine ⟨61450607002934494310234147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40967071335289662873489431 61450607002934494310234147)
      ·
        refine ⟨92175910504401741465351221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61450607002934494310234147 92175910504401741465351221)
        ·
          refine ⟨8641491609787663262376677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92175910504401741465351221 8641491609787663262376677)
          ·
            refine ⟨1620279676835186861695627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8641491609787663262376677 1620279676835186861695627)
            ·
              refine ⟨2430419515252780292543441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620279676835186861695627 2430419515252780292543441)
              ·
                refine ⟨1822814636439585219407581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2430419515252780292543441 1822814636439585219407581)
                ·
                  refine ⟨683555488664844457277843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1822814636439585219407581 683555488664844457277843)
                  ·
                    refine ⟨1025333232997266685916765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 683555488664844457277843 1025333232997266685916765)
                    ·
                      refine ⟨384499962373975007218787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1025333232997266685916765 384499962373975007218787)
                      ·
                        rfl

theorem cell23_748811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 1, 3].length) (baseStart_748811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748811 prefixEnd_748811 := by exact prefixLift 748811
  have htrace : WordTrace (prefixWord ++ tailWord_748811) baseStart_748811 baseEnd_748811 := by
    simpa [prefixWord, tailWord_748811, baseEnd_748811] using wordTrace_append hprefix tailTrace_748811
  have hstable : (prefixWord ++ tailWord_748811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748811).length < 2 ^ (prefixWord ++ tailWord_748811).sum := by decide
  have hdescent : baseEnd_748811 < baseStart_748811 := by decide
  rcases family_descends (prefixWord ++ tailWord_748811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748814 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 3, 5]
def baseStart_748814 : Nat := 118140960795 + 748814 * 2 ^ 59
def prefixEnd_748814 : Nat := 4983230072969 + 3 ^ 40 * 748814 * 2
def baseEnd_748814 : Nat := 128167167605312831827091

theorem tailTrace_748814 : CollatzResearch.WordTrace tailWord_748814 prefixEnd_748814 128167167605312831827091 := by
  unfold tailWord_748814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3413936288647780011835687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18207660206121493396456997 3413936288647780011835687)
  ·
    refine ⟨5120904432971670017753531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3413936288647780011835687 5120904432971670017753531)
    ·
      refine ⟨7681356649457505026630297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5120904432971670017753531 7681356649457505026630297)
      ·
        refine ⟨5761017487093128769972723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7681356649457505026630297 5761017487093128769972723)
        ·
          refine ⟨8641526230639693154959085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5761017487093128769972723 8641526230639693154959085)
          ·
            refine ⟨3240572336489884933109657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8641526230639693154959085 3240572336489884933109657)
            ·
              refine ⟨2430429252367413699832243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3240572336489884933109657 2430429252367413699832243)
              ·
                refine ⟨3645643878551120549748365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2430429252367413699832243 3645643878551120549748365)
                ·
                  refine ⟨1367116454456670206155637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3645643878551120549748365 1367116454456670206155637)
                  ·
                    refine ⟨128167167605312831827091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1367116454456670206155637 128167167605312831827091)
                    ·
                      rfl

theorem cell23_748814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_748814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748814 prefixEnd_748814 := by exact prefixLift 748814
  have htrace : WordTrace (prefixWord ++ tailWord_748814) baseStart_748814 baseEnd_748814 := by
    simpa [prefixWord, tailWord_748814, baseEnd_748814] using wordTrace_append hprefix tailTrace_748814
  have hstable : (prefixWord ++ tailWord_748814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748814).length < 2 ^ (prefixWord ++ tailWord_748814).sum := by decide
  have hdescent : baseEnd_748814 < baseStart_748814 := by decide
  rcases family_descends (prefixWord ++ tailWord_748814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748828 : List Nat := [2, 2, 3, 1, 1, 1, 3, 5, 1, 1, 3]
def baseStart_748828 : Nat := 118140960795 + 748828 * 2 ^ 59
def prefixEnd_748828 : Nat := 4983230072969 + 3 ^ 40 * 748828 * 2
def baseEnd_748828 : Nat := 384508691545101440706209

theorem tailTrace_748828 : CollatzResearch.WordTrace tailWord_748828 prefixEnd_748828 384508691545101440706209 := by
  unfold tailWord_748828
  simp only [CollatzResearch.WordTrace]
  refine ⟨13656000465565760242847569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18208000620754346990463425 13656000465565760242847569)
  ·
    refine ⟨10242000349174320182135677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13656000465565760242847569 10242000349174320182135677)
    ·
      refine ⟨3840750130940370068300879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10242000349174320182135677 3840750130940370068300879)
      ·
        refine ⟨5761125196410555102451319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3840750130940370068300879 5761125196410555102451319)
        ·
          refine ⟨8641687794615832653676979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5761125196410555102451319 8641687794615832653676979)
          ·
            refine ⟨12962531691923748980515469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8641687794615832653676979 12962531691923748980515469)
            ·
              refine ⟨4860949384471405867693301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12962531691923748980515469 4860949384471405867693301)
              ·
                refine ⟨455714004794194300096247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4860949384471405867693301 455714004794194300096247)
                ·
                  refine ⟨683571007191291450144371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 455714004794194300096247 683571007191291450144371)
                  ·
                    refine ⟨1025356510786937175216557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 683571007191291450144371 1025356510786937175216557)
                    ·
                      refine ⟨384508691545101440706209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1025356510786937175216557 384508691545101440706209)
                      ·
                        rfl

theorem cell23_748828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_748828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748828 prefixEnd_748828 := by exact prefixLift 748828
  have htrace : WordTrace (prefixWord ++ tailWord_748828) baseStart_748828 baseEnd_748828 := by
    simpa [prefixWord, tailWord_748828, baseEnd_748828] using wordTrace_append hprefix tailTrace_748828
  have hstable : (prefixWord ++ tailWord_748828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748828).length < 2 ^ (prefixWord ++ tailWord_748828).sum := by decide
  have hdescent : baseEnd_748828 < baseStart_748828 := by decide
  rcases family_descends (prefixWord ++ tailWord_748828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748831 : List Nat := [1, 1, 2, 4, 4, 1, 1, 3, 1, 5]
def baseStart_748831 : Nat := 118140960795 + 748831 * 2 ^ 59
def prefixEnd_748831 : Nat := 4983230072969 + 3 ^ 40 * 748831 * 2
def baseEnd_748831 : Nat := 128170077329021642989565

theorem tailTrace_748831 : CollatzResearch.WordTrace tailWord_748831 prefixEnd_748831 128170077329021642989565 := by
  unfold tailWord_748831
  simp only [CollatzResearch.WordTrace]
  refine ⟨27312110350120651998054347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18208073566747101332036231 27312110350120651998054347)
  ·
    refine ⟨40968165525180977997081521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27312110350120651998054347 40968165525180977997081521)
    ·
      refine ⟨30726124143885733497811141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40968165525180977997081521 30726124143885733497811141)
      ·
        refine ⟨5761148276978575030839589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30726124143885733497811141 5761148276978575030839589)
        ·
          refine ⟨1080215301933482818282423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5761148276978575030839589 1080215301933482818282423)
          ·
            refine ⟨1620322952900224227423635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1080215301933482818282423 1620322952900224227423635)
            ·
              refine ⟨2430484429350336341135453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620322952900224227423635 2430484429350336341135453)
              ·
                refine ⟨911431661006376127925795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2430484429350336341135453 911431661006376127925795)
                ·
                  refine ⟨1367147491509564191888693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 911431661006376127925795 1367147491509564191888693)
                  ·
                    refine ⟨128170077329021642989565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1367147491509564191888693 128170077329021642989565)
                    ·
                      rfl

theorem cell23_748831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 5].length) (baseStart_748831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748831 prefixEnd_748831 := by exact prefixLift 748831
  have htrace : WordTrace (prefixWord ++ tailWord_748831) baseStart_748831 baseEnd_748831 := by
    simpa [prefixWord, tailWord_748831, baseEnd_748831] using wordTrace_append hprefix tailTrace_748831
  have hstable : (prefixWord ++ tailWord_748831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748831).length < 2 ^ (prefixWord ++ tailWord_748831).sum := by decide
  have hdescent : baseEnd_748831 < baseStart_748831 := by decide
  rcases family_descends (prefixWord ++ tailWord_748831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748845 : List Nat := [1, 5, 3, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_748845 : Nat := 118140960795 + 748845 * 2 ^ 59
def prefixEnd_748845 : Nat := 4983230072969 + 3 ^ 40 * 748845 * 2
def baseEnd_748845 : Nat := 384517420716227874193631

theorem tailTrace_748845 : CollatzResearch.WordTrace tailWord_748845 prefixEnd_748845 384517420716227874193631 := by
  unfold tailWord_748845
  simp only [CollatzResearch.WordTrace]
  refine ⟨27312620972069932389063989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18208413981379954926042659 27312620972069932389063989)
  ·
    refine ⟨2560558216131556161474749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27312620972069932389063989 2560558216131556161474749)
    ·
      refine ⟨960209331049333560553031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2560558216131556161474749 960209331049333560553031)
      ·
        refine ⟨1440313996574000340829547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 960209331049333560553031 1440313996574000340829547)
        ·
          refine ⟨2160470994861000511244321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1440313996574000340829547 2160470994861000511244321)
          ·
            refine ⟨1620353246145750383433241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2160470994861000511244321 1620353246145750383433241)
            ·
              refine ⟨1215264934609312787574931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1620353246145750383433241 1215264934609312787574931)
              ·
                refine ⟨1822897401913969181362397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215264934609312787574931 1822897401913969181362397)
                ·
                  refine ⟨683586525717738443010899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1822897401913969181362397 683586525717738443010899)
                  ·
                    refine ⟨1025379788576607664516349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 683586525717738443010899 1025379788576607664516349)
                    ·
                      refine ⟨384517420716227874193631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1025379788576607664516349 384517420716227874193631)
                      ·
                        rfl

theorem cell23_748845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_748845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748845 prefixEnd_748845 := by exact prefixLift 748845
  have htrace : WordTrace (prefixWord ++ tailWord_748845) baseStart_748845 baseEnd_748845 := by
    simpa [prefixWord, tailWord_748845, baseEnd_748845] using wordTrace_append hprefix tailTrace_748845
  have hstable : (prefixWord ++ tailWord_748845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748845).length < 2 ^ (prefixWord ++ tailWord_748845).sum := by decide
  have hdescent : baseEnd_748845 < baseStart_748845 := by decide
  rcases family_descends (prefixWord ++ tailWord_748845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748847 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 6]
def baseStart_748847 : Nat := 118140960795 + 748847 * 2 ^ 59
def prefixEnd_748847 : Nat := 4983230072969 + 3 ^ 40 * 748847 * 2
def baseEnd_748847 : Nat := 384518447677536866368621

theorem tailTrace_748847 : CollatzResearch.WordTrace tailWord_748847 prefixEnd_748847 384518447677536866368621 := by
  unfold tailWord_748847
  simp only [CollatzResearch.WordTrace]
  refine ⟨27312693918062686730636795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18208462612041791153757863 27312693918062686730636795)
  ·
    refine ⟨40969040877094030095955193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27312693918062686730636795 40969040877094030095955193)
    ·
      refine ⟨30726780657820522571966395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40969040877094030095955193 30726780657820522571966395)
      ·
        refine ⟨46090170986730783857949593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30726780657820522571966395 46090170986730783857949593)
        ·
          refine ⟨34567628240048087893462195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46090170986730783857949593 34567628240048087893462195)
          ·
            refine ⟨51851442360072131840193293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34567628240048087893462195 51851442360072131840193293)
            ·
              refine ⟨19444290885027049440072485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51851442360072131840193293 19444290885027049440072485)
              ·
                refine ⟨3645804540942571770013591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19444290885027049440072485 3645804540942571770013591)
                ·
                  refine ⟨5468706811413857655020387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3645804540942571770013591 5468706811413857655020387)
                  ·
                    refine ⟨8203060217120786482530581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5468706811413857655020387 8203060217120786482530581)
                    ·
                      refine ⟨384518447677536866368621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8203060217120786482530581 384518447677536866368621)
                      ·
                        rfl

theorem cell23_748847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_748847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748847 prefixEnd_748847 := by exact prefixLift 748847
  have htrace : WordTrace (prefixWord ++ tailWord_748847) baseStart_748847 baseEnd_748847 := by
    simpa [prefixWord, tailWord_748847, baseEnd_748847] using wordTrace_append hprefix tailTrace_748847
  have hstable : (prefixWord ++ tailWord_748847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748847).length < 2 ^ (prefixWord ++ tailWord_748847).sum := by decide
  have hdescent : baseEnd_748847 < baseStart_748847 := by decide
  rcases family_descends (prefixWord ++ tailWord_748847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748868 : List Nat := [2, 3, 4, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_748868 : Nat := 118140960795 + 748868 * 2 ^ 59
def prefixEnd_748868 : Nat := 4983230072969 + 3 ^ 40 * 748868 * 2
def baseEnd_748868 : Nat := 384529230771281284206025

theorem tailTrace_748868 : CollatzResearch.WordTrace tailWord_748868 prefixEnd_748868 384529230771281284206025 := by
  unfold tailWord_748868
  simp only [CollatzResearch.WordTrace]
  refine ⟨13656729925493303658575629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18208973233991071544767505 13656729925493303658575629)
  ·
    refine ⟨5121273722059988871965861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13656729925493303658575629 5121273722059988871965861)
    ·
      refine ⟨960238822886247913493599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5121273722059988871965861 960238822886247913493599)
      ·
        refine ⟨1440358234329371870240399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 960238822886247913493599 1440358234329371870240399)
        ·
          refine ⟨2160537351494057805360599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1440358234329371870240399 2160537351494057805360599)
          ·
            refine ⟨3240806027241086708040899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2160537351494057805360599 3240806027241086708040899)
            ·
              refine ⟨4861209040861630062061349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3240806027241086708040899 4861209040861630062061349)
              ·
                refine ⟨911476695161555636636503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4861209040861630062061349 911476695161555636636503)
                ·
                  refine ⟨1367215042742333454954755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 911476695161555636636503 1367215042742333454954755)
                  ·
                    refine ⟨2050822564113500182432133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1367215042742333454954755 2050822564113500182432133)
                    ·
                      refine ⟨384529230771281284206025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2050822564113500182432133 384529230771281284206025)
                      ·
                        rfl

theorem cell23_748868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_748868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748868 prefixEnd_748868 := by exact prefixLift 748868
  have htrace : WordTrace (prefixWord ++ tailWord_748868) baseStart_748868 baseEnd_748868 := by
    simpa [prefixWord, tailWord_748868, baseEnd_748868] using wordTrace_append hprefix tailTrace_748868
  have hstable : (prefixWord ++ tailWord_748868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748868).length < 2 ^ (prefixWord ++ tailWord_748868).sum := by decide
  have hdescent : baseEnd_748868 < baseStart_748868 := by decide
  rcases family_descends (prefixWord ++ tailWord_748868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748871 : List Nat := [1, 1, 4, 1, 2, 3, 1, 4, 1, 2, 3]
def baseStart_748871 : Nat := 118140960795 + 748871 * 2 ^ 59
def prefixEnd_748871 : Nat := 4983230072969 + 3 ^ 40 * 748871 * 2
def baseEnd_748871 : Nat := 384530771213244772468511

theorem tailTrace_748871 : CollatzResearch.WordTrace tailWord_748871 prefixEnd_748871 384530771213244772468511 := by
  unfold tailWord_748871
  simp only [CollatzResearch.WordTrace]
  refine ⟨27313569269975738829510467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18209046179983825886340311 27313569269975738829510467)
  ·
    refine ⟨40970353904963608244265701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27313569269975738829510467 40970353904963608244265701)
    ·
      refine ⟨7681941357180676545799819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40970353904963608244265701 7681941357180676545799819)
      ·
        refine ⟨11522912035771014818699729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7681941357180676545799819 11522912035771014818699729)
        ·
          refine ⟨8642184026828261114024797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11522912035771014818699729 8642184026828261114024797)
          ·
            refine ⟨3240819010060597917759299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8642184026828261114024797 3240819010060597917759299)
            ·
              refine ⟨4861228515090896876638949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3240819010060597917759299 4861228515090896876638949)
              ·
                refine ⟨911480346579543164369803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4861228515090896876638949 911480346579543164369803)
                ·
                  refine ⟨1367220519869314746554705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 911480346579543164369803 1367220519869314746554705)
                  ·
                    refine ⟨1025415389901986059916029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1367220519869314746554705 1025415389901986059916029)
                    ·
                      refine ⟨384530771213244772468511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1025415389901986059916029 384530771213244772468511)
                      ·
                        rfl

theorem cell23_748871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_748871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748871 prefixEnd_748871 := by exact prefixLift 748871
  have htrace : WordTrace (prefixWord ++ tailWord_748871) baseStart_748871 baseEnd_748871 := by
    simpa [prefixWord, tailWord_748871, baseEnd_748871] using wordTrace_append hprefix tailTrace_748871
  have hstable : (prefixWord ++ tailWord_748871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748871).length < 2 ^ (prefixWord ++ tailWord_748871).sum := by decide
  have hdescent : baseEnd_748871 < baseStart_748871 := by decide
  rcases family_descends (prefixWord ++ tailWord_748871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748901 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 4, 1, 3]
def baseStart_748901 : Nat := 118140960795 + 748901 * 2 ^ 59
def prefixEnd_748901 : Nat := 4983230072969 + 3 ^ 40 * 748901 * 2
def baseEnd_748901 : Nat := 384546175632879655093373

theorem tailTrace_748901 : CollatzResearch.WordTrace tailWord_748901 prefixEnd_748901 384546175632879655093373 := by
  unfold tailWord_748901
  simp only [CollatzResearch.WordTrace]
  refine ⟨27314663459867053953102557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18209775639911369302068371 27314663459867053953102557)
  ·
    refine ⟨10242998797450145232413459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27314663459867053953102557 10242998797450145232413459)
    ·
      refine ⟨15364498196175217848620189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10242998797450145232413459 15364498196175217848620189)
      ·
        refine ⟨5761686823565706693232571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15364498196175217848620189 5761686823565706693232571)
        ·
          refine ⟨8642530235348560039848857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5761686823565706693232571 8642530235348560039848857)
          ·
            refine ⟨6481897676511420029886643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8642530235348560039848857 6481897676511420029886643)
            ·
              refine ⟨9722846514767130044829965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6481897676511420029886643 9722846514767130044829965)
              ·
                refine ⟨3646067443037673766811237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9722846514767130044829965 3646067443037673766811237)
                ·
                  refine ⟨683637645569563831277107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3646067443037673766811237 683637645569563831277107)
                  ·
                    refine ⟨1025456468354345746915661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 683637645569563831277107 1025456468354345746915661)
                    ·
                      refine ⟨384546175632879655093373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1025456468354345746915661 384546175632879655093373)
                      ·
                        rfl

theorem cell23_748901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_748901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748901 prefixEnd_748901 := by exact prefixLift 748901
  have htrace : WordTrace (prefixWord ++ tailWord_748901) baseStart_748901 baseEnd_748901 := by
    simpa [prefixWord, tailWord_748901, baseEnd_748901] using wordTrace_append hprefix tailTrace_748901
  have hstable : (prefixWord ++ tailWord_748901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748901).length < 2 ^ (prefixWord ++ tailWord_748901).sum := by decide
  have hdescent : baseEnd_748901 < baseStart_748901 := by decide
  rcases family_descends (prefixWord ++ tailWord_748901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748911 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 3, 3, 2]
def baseStart_748911 : Nat := 118140960795 + 748911 * 2 ^ 59
def prefixEnd_748911 : Nat := 4983230072969 + 3 ^ 40 * 748911 * 2
def baseEnd_748911 : Nat := 384551310439424615968327

theorem tailTrace_748911 : CollatzResearch.WordTrace tailWord_748911 prefixEnd_748911 384551310439424615968327 := by
  unfold tailWord_748911
  simp only [CollatzResearch.WordTrace]
  refine ⟨27315028189830825660966587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18210018793220550440644391 27315028189830825660966587)
  ·
    refine ⟨40972542284746238491449881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27315028189830825660966587 40972542284746238491449881)
    ·
      refine ⟨30729406713559678868587411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40972542284746238491449881 30729406713559678868587411)
      ·
        refine ⟨46094110070339518302881117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30729406713559678868587411 46094110070339518302881117)
        ·
          refine ⟨17285291276377319363580419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46094110070339518302881117 17285291276377319363580419)
          ·
            refine ⟨25927936914565979045370629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17285291276377319363580419 25927936914565979045370629)
            ·
              refine ⟨4861488171481121071006993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25927936914565979045370629 4861488171481121071006993)
              ·
                refine ⟨3646116128610840803255245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4861488171481121071006993 3646116128610840803255245)
                ·
                  refine ⟨1367293548229065301220717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3646116128610840803255245 1367293548229065301220717)
                  ·
                    refine ⟨512735080585899487957769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1367293548229065301220717 512735080585899487957769)
                    ·
                      refine ⟨384551310439424615968327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 512735080585899487957769 384551310439424615968327)
                      ·
                        rfl

theorem cell23_748911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 3, 2].length) (baseStart_748911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748911 prefixEnd_748911 := by exact prefixLift 748911
  have htrace : WordTrace (prefixWord ++ tailWord_748911) baseStart_748911 baseEnd_748911 := by
    simpa [prefixWord, tailWord_748911, baseEnd_748911] using wordTrace_append hprefix tailTrace_748911
  have hstable : (prefixWord ++ tailWord_748911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748911).length < 2 ^ (prefixWord ++ tailWord_748911).sum := by decide
  have hdescent : baseEnd_748911 < baseStart_748911 := by decide
  rcases family_descends (prefixWord ++ tailWord_748911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748964 : List Nat := [2, 3, 1, 2, 1, 1, 1, 5, 7]
def baseStart_748964 : Nat := 118140960795 + 748964 * 2 ^ 59
def prefixEnd_748964 : Nat := 4983230072969 + 3 ^ 40 * 748964 * 2
def baseEnd_748964 : Nat := 42730947212679212067287

theorem tailTrace_748964 : CollatzResearch.WordTrace tailWord_748964 prefixEnd_748964 42730947212679212067287 := by
  unfold tailWord_748964
  simp only [CollatzResearch.WordTrace]
  refine ⟨13658480629319407856322973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18211307505759210475097297 13658480629319407856322973)
  ·
    refine ⟨5121930235994777946121115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13658480629319407856322973 5121930235994777946121115)
    ·
      refine ⟨7682895353992166919181673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5121930235994777946121115 7682895353992166919181673)
      ·
        refine ⟨5762171515494125189386255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7682895353992166919181673 5762171515494125189386255)
        ·
          refine ⟨8643257273241187784079383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5762171515494125189386255 8643257273241187784079383)
          ·
            refine ⟨12964885909861781676119075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8643257273241187784079383 12964885909861781676119075)
            ·
              refine ⟨19447328864792672514178613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12964885909861781676119075 19447328864792672514178613)
              ·
                refine ⟨1823187081074313048204245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19447328864792672514178613 1823187081074313048204245)
                ·
                  refine ⟨42730947212679212067287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1823187081074313048204245 42730947212679212067287)
                  ·
                    rfl

theorem cell23_748964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_748964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748964 prefixEnd_748964 := by exact prefixLift 748964
  have htrace : WordTrace (prefixWord ++ tailWord_748964) baseStart_748964 baseEnd_748964 := by
    simpa [prefixWord, tailWord_748964, baseEnd_748964] using wordTrace_append hprefix tailTrace_748964
  have hstable : (prefixWord ++ tailWord_748964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748964).length < 2 ^ (prefixWord ++ tailWord_748964).sum := by decide
  have hdescent : baseEnd_748964 < baseStart_748964 := by decide
  rcases family_descends (prefixWord ++ tailWord_748964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748968 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 2, 6]
def baseStart_748968 : Nat := 118140960795 + 748968 * 2 ^ 59
def prefixEnd_748968 : Nat := 4983230072969 + 3 ^ 40 * 748968 * 2
def baseEnd_748968 : Nat := 128193526278910297651855

theorem tailTrace_748968 : CollatzResearch.WordTrace tailWord_748968 prefixEnd_748968 128193526278910297651855 := by
  unfold tailWord_748968
  simp only [CollatzResearch.WordTrace]
  refine ⟨13658553575312162197895779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18211404767082882930527705 13658553575312162197895779)
  ·
    refine ⟨20487830362968243296843669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13658553575312162197895779 20487830362968243296843669)
    ·
      refine ⟨960367048264136404539547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20487830362968243296843669 960367048264136404539547)
      ·
        refine ⟨1440550572396204606809321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 960367048264136404539547 1440550572396204606809321)
        ·
          refine ⟨1080412929297153455106991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1440550572396204606809321 1080412929297153455106991)
          ·
            refine ⟨1620619393945730182660487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1080412929297153455106991 1620619393945730182660487)
            ·
              refine ⟨2430929090918595273990731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620619393945730182660487 2430929090918595273990731)
              ·
                refine ⟨3646393636377892910986097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2430929090918595273990731 3646393636377892910986097)
                ·
                  refine ⟨2734795227283419683239573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3646393636377892910986097 2734795227283419683239573)
                  ·
                    refine ⟨128193526278910297651855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2734795227283419683239573 128193526278910297651855)
                    ·
                      rfl

theorem cell23_748968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_748968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748968 prefixEnd_748968 := by exact prefixLift 748968
  have htrace : WordTrace (prefixWord ++ tailWord_748968) baseStart_748968 baseEnd_748968 := by
    simpa [prefixWord, tailWord_748968, baseEnd_748968] using wordTrace_append hprefix tailTrace_748968
  have hstable : (prefixWord ++ tailWord_748968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748968).length < 2 ^ (prefixWord ++ tailWord_748968).sum := by decide
  have hdescent : baseEnd_748968 < baseStart_748968 := by decide
  rcases family_descends (prefixWord ++ tailWord_748968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748981 : List Nat := [1, 3, 3, 2, 2, 2, 1, 2, 7]
def baseStart_748981 : Nat := 118140960795 + 748981 * 2 ^ 59
def prefixEnd_748981 : Nat := 4983230072969 + 3 ^ 40 * 748981 * 2
def baseEnd_748981 : Nat := 42731917120582149121445

theorem tailTrace_748981 : CollatzResearch.WordTrace tailWord_748981 prefixEnd_748981 42731917120582149121445 := by
  unfold tailWord_748981
  simp only [CollatzResearch.WordTrace]
  refine ⟨27317581299577227616014797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18211720866384818410676531 27317581299577227616014797)
  ·
    refine ⟨10244092987341460356005549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27317581299577227616014797 10244092987341460356005549)
    ·
      refine ⟨3841534870253047633502081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10244092987341460356005549 3841534870253047633502081)
      ·
        refine ⟨2881151152689785725126561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3841534870253047633502081 2881151152689785725126561)
        ·
          refine ⟨2160863364517339293844921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2881151152689785725126561 2160863364517339293844921)
          ·
            refine ⟨1620647523388004470383691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2160863364517339293844921 1620647523388004470383691)
            ·
              refine ⟨2430971285082006705575537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620647523388004470383691 2430971285082006705575537)
              ·
                refine ⟨1823228463811505029181653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2430971285082006705575537 1823228463811505029181653)
                ·
                  refine ⟨42731917120582149121445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1823228463811505029181653 42731917120582149121445)
                  ·
                    rfl

theorem cell23_748981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 7].length) (baseStart_748981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_748981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_748981 prefixEnd_748981 := by exact prefixLift 748981
  have htrace : WordTrace (prefixWord ++ tailWord_748981) baseStart_748981 baseEnd_748981 := by
    simpa [prefixWord, tailWord_748981, baseEnd_748981] using wordTrace_append hprefix tailTrace_748981
  have hstable : (prefixWord ++ tailWord_748981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748981).length < 2 ^ (prefixWord ++ tailWord_748981).sum := by decide
  have hdescent : baseEnd_748981 < baseStart_748981 := by decide
  rcases family_descends (prefixWord ++ tailWord_748981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749031 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_749031 : Nat := 118140960795 + 749031 * 2 ^ 59
def prefixEnd_749031 : Nat := 4983230072969 + 3 ^ 40 * 749031 * 2
def baseEnd_749031 : Nat := 384612928117964146467775

theorem tailTrace_749031 : CollatzResearch.WordTrace tailWord_749031 prefixEnd_749031 384612928117964146467775 := by
  unfold tailWord_749031
  simp only [CollatzResearch.WordTrace]
  refine ⟨27319404949396086155334947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18212936632930724103556631 27319404949396086155334947)
  ·
    refine ⟨40979107424094129233002421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27319404949396086155334947 40979107424094129233002421)
    ·
      refine ⟨3841791321008824615593977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40979107424094129233002421 3841791321008824615593977)
      ·
        refine ⟨2881343490756618461695483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3841791321008824615593977 2881343490756618461695483)
        ·
          refine ⟨4322015236134927692543225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2881343490756618461695483 4322015236134927692543225)
          ·
            refine ⟨3241511427101195769407419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4322015236134927692543225 3241511427101195769407419)
            ·
              refine ⟨4862267140651793654111129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3241511427101195769407419 4862267140651793654111129)
              ·
                refine ⟨3646700355488845240583347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4862267140651793654111129 3646700355488845240583347)
                ·
                  refine ⟨5470050533233267860875021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3646700355488845240583347 5470050533233267860875021)
                  ·
                    refine ⟨2051268949962475447828133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5470050533233267860875021 2051268949962475447828133)
                    ·
                      refine ⟨384612928117964146467775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2051268949962475447828133 384612928117964146467775)
                      ·
                        rfl

theorem cell23_749031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_749031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749031 prefixEnd_749031 := by exact prefixLift 749031
  have htrace : WordTrace (prefixWord ++ tailWord_749031) baseStart_749031 baseEnd_749031 := by
    simpa [prefixWord, tailWord_749031, baseEnd_749031] using wordTrace_append hprefix tailTrace_749031
  have hstable : (prefixWord ++ tailWord_749031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749031).length < 2 ^ (prefixWord ++ tailWord_749031).sum := by decide
  have hdescent : baseEnd_749031 < baseStart_749031 := by decide
  rcases family_descends (prefixWord ++ tailWord_749031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749088 : List Nat := [2, 1, 1, 6, 1, 2, 1, 3, 6]
def baseStart_749088 : Nat := 118140960795 + 749088 * 2 ^ 59
def prefixEnd_749088 : Nat := 4983230072969 + 3 ^ 40 * 749088 * 2
def baseEnd_749088 : Nat := 42738021835030047050557

theorem tailTrace_749088 : CollatzResearch.WordTrace tailWord_749088 prefixEnd_749088 42738021835030047050557 := by
  unfold tailWord_749088
  simp only [CollatzResearch.WordTrace]
  refine ⟨13660741955094792445079959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18214322606793056593439945 13660741955094792445079959)
  ·
    refine ⟨20491112932642188667619939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13660741955094792445079959 20491112932642188667619939)
    ·
      refine ⟨30736669398963283001429909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20491112932642188667619939 30736669398963283001429909)
      ·
        refine ⟨1440781378076403890692027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30736669398963283001429909 1440781378076403890692027)
        ·
          refine ⟨2161172067114605836038041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1440781378076403890692027 2161172067114605836038041)
          ·
            refine ⟨1620879050335954377028531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2161172067114605836038041 1620879050335954377028531)
            ·
              refine ⟨2431318575503931565542797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620879050335954377028531 2431318575503931565542797)
              ·
                refine ⟨911744465813974337078549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2431318575503931565542797 911744465813974337078549)
                ·
                  refine ⟨42738021835030047050557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 911744465813974337078549 42738021835030047050557)
                  ·
                    rfl

theorem cell23_749088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 6].length) (baseStart_749088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749088 prefixEnd_749088 := by exact prefixLift 749088
  have htrace : WordTrace (prefixWord ++ tailWord_749088) baseStart_749088 baseEnd_749088 := by
    simpa [prefixWord, tailWord_749088, baseEnd_749088] using wordTrace_append hprefix tailTrace_749088
  have hstable : (prefixWord ++ tailWord_749088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749088).length < 2 ^ (prefixWord ++ tailWord_749088).sum := by decide
  have hdescent : baseEnd_749088 < baseStart_749088 := by decide
  rcases family_descends (prefixWord ++ tailWord_749088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749132 : List Nat := [2, 2, 1, 3, 1, 4, 1, 4, 1, 1, 3]
def baseStart_749132 : Nat := 118140960795 + 749132 * 2 ^ 59
def prefixEnd_749132 : Nat := 4983230072969 + 3 ^ 40 * 749132 * 2
def baseEnd_749132 : Nat := 384664789664068251304811

theorem tailTrace_749132 : CollatzResearch.WordTrace tailWord_749132 prefixEnd_749132 384664789664068251304811 := by
  unfold tailWord_749132
  simp only [CollatzResearch.WordTrace]
  refine ⟨13661544361015090202380825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18215392481353453603174433 13661544361015090202380825)
  ·
    refine ⟨10246158270761317651785619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13661544361015090202380825 10246158270761317651785619)
    ·
      refine ⟨15369237406141976477678429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10246158270761317651785619 15369237406141976477678429)
      ·
        refine ⟨5763464027303241179129411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15369237406141976477678429 5763464027303241179129411)
        ·
          refine ⟨8645196040954861768694117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5763464027303241179129411 8645196040954861768694117)
          ·
            refine ⟨1620974257679036581630147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8645196040954861768694117 1620974257679036581630147)
            ·
              refine ⟨2431461386518554872445221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620974257679036581630147 2431461386518554872445221)
              ·
                refine ⟨455899009972229038583479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2431461386518554872445221 455899009972229038583479)
                ·
                  refine ⟨683848514958343557875219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 455899009972229038583479 683848514958343557875219)
                  ·
                    refine ⟨1025772772437515336812829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 683848514958343557875219 1025772772437515336812829)
                    ·
                      refine ⟨384664789664068251304811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1025772772437515336812829 384664789664068251304811)
                      ·
                        rfl

theorem cell23_749132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_749132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749132 prefixEnd_749132 := by exact prefixLift 749132
  have htrace : WordTrace (prefixWord ++ tailWord_749132) baseStart_749132 baseEnd_749132 := by
    simpa [prefixWord, tailWord_749132, baseEnd_749132] using wordTrace_append hprefix tailTrace_749132
  have hstable : (prefixWord ++ tailWord_749132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749132).length < 2 ^ (prefixWord ++ tailWord_749132).sum := by decide
  have hdescent : baseEnd_749132 < baseStart_749132 := by decide
  rcases family_descends (prefixWord ++ tailWord_749132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749138 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_749138 : Nat := 118140960795 + 749138 * 2 ^ 59
def prefixEnd_749138 : Nat := 4983230072969 + 3 ^ 40 * 749138 * 2
def baseEnd_749138 : Nat := 384667870547995227829783

theorem tailTrace_749138 : CollatzResearch.WordTrace tailWord_749138 prefixEnd_749138 384667870547995227829783 := by
  unfold tailWord_749138
  simp only [CollatzResearch.WordTrace]
  refine ⟨6830826890002110857370017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18215538373338962286320045 6830826890002110857370017)
  ·
    refine ⟨5123120167501583143027513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6830826890002110857370017 5123120167501583143027513)
    ·
      refine ⟨3842340125626187357270635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5123120167501583143027513 3842340125626187357270635)
      ·
        refine ⟨5763510188439281035905953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3842340125626187357270635 5763510188439281035905953)
        ·
          refine ⟨4322632641329460776929465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5763510188439281035905953 4322632641329460776929465)
          ·
            refine ⟨3241974480997095582697099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4322632641329460776929465 3241974480997095582697099)
            ·
              refine ⟨4862961721495643374045649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3241974480997095582697099 4862961721495643374045649)
              ·
                refine ⟨3647221291121732530534237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4862961721495643374045649 3647221291121732530534237)
                ·
                  refine ⟨1367707984170649698950339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3647221291121732530534237 1367707984170649698950339)
                  ·
                    refine ⟨2051561976255974548425509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1367707984170649698950339 2051561976255974548425509)
                    ·
                      refine ⟨384667870547995227829783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2051561976255974548425509 384667870547995227829783)
                      ·
                        rfl

theorem cell23_749138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_749138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749138 prefixEnd_749138 := by exact prefixLift 749138
  have htrace : WordTrace (prefixWord ++ tailWord_749138) baseStart_749138 baseEnd_749138 := by
    simpa [prefixWord, tailWord_749138, baseEnd_749138] using wordTrace_append hprefix tailTrace_749138
  have hstable : (prefixWord ++ tailWord_749138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749138).length < 2 ^ (prefixWord ++ tailWord_749138).sum := by decide
  have hdescent : baseEnd_749138 < baseStart_749138 := by decide
  rcases family_descends (prefixWord ++ tailWord_749138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749141 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_749141 : Nat := 118140960795 + 749141 * 2 ^ 59
def prefixEnd_749141 : Nat := 4983230072969 + 3 ^ 40 * 749141 * 2
def baseEnd_749141 : Nat := 384669410989958716092269

theorem tailTrace_749141 : CollatzResearch.WordTrace tailWord_749141 prefixEnd_749141 384669410989958716092269 := by
  unfold tailWord_749141
  simp only [CollatzResearch.WordTrace]
  refine ⟨27323416978997574941839277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18215611319331716627892851 27323416978997574941839277)
  ·
    refine ⟨10246281367124090603189729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27323416978997574941839277 10246281367124090603189729)
    ·
      refine ⟨7684711025343067952392297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10246281367124090603189729 7684711025343067952392297)
      ·
        refine ⟨5763533269007300964294223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7684711025343067952392297 5763533269007300964294223)
        ·
          refine ⟨8645299903510951446441335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5763533269007300964294223 8645299903510951446441335)
          ·
            refine ⟨12967949855266427169662003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8645299903510951446441335 12967949855266427169662003)
            ·
              refine ⟨19451924782899640754493005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12967949855266427169662003 19451924782899640754493005)
              ·
                refine ⟨7294471793587365282934877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19451924782899640754493005 7294471793587365282934877)
                ·
                  refine ⟨2735426922595261981100579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7294471793587365282934877 2735426922595261981100579)
                  ·
                    refine ⟨4103140383892892971650869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2735426922595261981100579 4103140383892892971650869)
                    ·
                      refine ⟨384669410989958716092269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4103140383892892971650869 384669410989958716092269)
                      ·
                        rfl

theorem cell23_749141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_749141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749141 prefixEnd_749141 := by exact prefixLift 749141
  have htrace : WordTrace (prefixWord ++ tailWord_749141) baseStart_749141 baseEnd_749141 := by
    simpa [prefixWord, tailWord_749141, baseEnd_749141] using wordTrace_append hprefix tailTrace_749141
  have hstable : (prefixWord ++ tailWord_749141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749141).length < 2 ^ (prefixWord ++ tailWord_749141).sum := by decide
  have hdescent : baseEnd_749141 < baseStart_749141 := by decide
  rcases family_descends (prefixWord ++ tailWord_749141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749148 : List Nat := [2, 2, 4, 1, 2, 1, 1, 3, 1, 6]
def baseStart_749148 : Nat := 118140960795 + 749148 * 2 ^ 59
def prefixEnd_749148 : Nat := 4983230072969 + 3 ^ 40 * 749148 * 2
def baseEnd_749148 : Nat := 128224335118180062901579

theorem tailTrace_749148 : CollatzResearch.WordTrace tailWord_749148 prefixEnd_749148 128224335118180062901579 := by
  unfold tailWord_749148
  simp only [CollatzResearch.WordTrace]
  refine ⟨13661836144986107568672049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18215781526648143424896065 13661836144986107568672049)
  ·
    refine ⟨10246377108739580676504037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13661836144986107568672049 10246377108739580676504037)
    ·
      refine ⟨1921195707888671376844507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10246377108739580676504037 1921195707888671376844507)
      ·
        refine ⟨2881793561833007065266761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1921195707888671376844507 2881793561833007065266761)
        ·
          refine ⟨2161345171374755298950071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2881793561833007065266761 2161345171374755298950071)
          ·
            refine ⟨3242017757062132948425107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2161345171374755298950071 3242017757062132948425107)
            ·
              refine ⟨4863026635593199422637661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3242017757062132948425107 4863026635593199422637661)
              ·
                refine ⟨1823634988347449783489123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4863026635593199422637661 1823634988347449783489123)
                ·
                  refine ⟨2735452482521174675233685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823634988347449783489123 2735452482521174675233685)
                  ·
                    refine ⟨128224335118180062901579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2735452482521174675233685 128224335118180062901579)
                    ·
                      rfl

theorem cell23_749148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_749148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749148 prefixEnd_749148 := by exact prefixLift 749148
  have htrace : WordTrace (prefixWord ++ tailWord_749148) baseStart_749148 baseEnd_749148 := by
    simpa [prefixWord, tailWord_749148, baseEnd_749148] using wordTrace_append hprefix tailTrace_749148
  have hstable : (prefixWord ++ tailWord_749148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749148).length < 2 ^ (prefixWord ++ tailWord_749148).sum := by decide
  have hdescent : baseEnd_749148 < baseStart_749148 := by decide
  rcases family_descends (prefixWord ++ tailWord_749148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749149 : List Nat := [1, 4, 4, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_749149 : Nat := 118140960795 + 749149 * 2 ^ 59
def prefixEnd_749149 : Nat := 4983230072969 + 3 ^ 40 * 749149 * 2
def baseEnd_749149 : Nat := 384673518835194684792233

theorem tailTrace_749149 : CollatzResearch.WordTrace tailWord_749149 prefixEnd_749149 384673518835194684792233 := by
  unfold tailWord_749149
  simp only [CollatzResearch.WordTrace]
  refine ⟨27323708762968592308130501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18215805841979061538753667 27323708762968592308130501)
  ·
    refine ⟨5123195393056611057774469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27323708762968592308130501 5123195393056611057774469)
    ·
      refine ⟨960599136198114573332713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5123195393056611057774469 960599136198114573332713)
      ·
        refine ⟨720449352148585929999535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 960599136198114573332713 720449352148585929999535)
        ·
          refine ⟨1080674028222878894999303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720449352148585929999535 1080674028222878894999303)
          ·
            refine ⟨1621011042334318342498955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1080674028222878894999303 1621011042334318342498955)
            ·
              refine ⟨2431516563501477513748433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1621011042334318342498955 2431516563501477513748433)
              ·
                refine ⟨1823637422626108135311325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2431516563501477513748433 1823637422626108135311325)
                ·
                  refine ⟨683864033484790550741747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1823637422626108135311325 683864033484790550741747)
                  ·
                    refine ⟨1025796050227185826112621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 683864033484790550741747 1025796050227185826112621)
                    ·
                      refine ⟨384673518835194684792233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1025796050227185826112621 384673518835194684792233)
                      ·
                        rfl

theorem cell23_749149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_749149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749149 prefixEnd_749149 := by exact prefixLift 749149
  have htrace : WordTrace (prefixWord ++ tailWord_749149) baseStart_749149 baseEnd_749149 := by
    simpa [prefixWord, tailWord_749149, baseEnd_749149] using wordTrace_append hprefix tailTrace_749149
  have hstable : (prefixWord ++ tailWord_749149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749149).length < 2 ^ (prefixWord ++ tailWord_749149).sum := by decide
  have hdescent : baseEnd_749149 < baseStart_749149 := by decide
  rcases family_descends (prefixWord ++ tailWord_749149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749155 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 5, 2, 2]
def baseStart_749155 : Nat := 118140960795 + 749155 * 2 ^ 59
def prefixEnd_749155 : Nat := 4983230072969 + 3 ^ 40 * 749155 * 2
def baseEnd_749155 : Nat := 384676599719121661317205

theorem tailTrace_749155 : CollatzResearch.WordTrace tailWord_749155 prefixEnd_749155 384676599719121661317205 := by
  unfold tailWord_749155
  simp only [CollatzResearch.WordTrace]
  refine ⟨27323927600946855332848919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18215951733964570221899279 27323927600946855332848919)
  ·
    refine ⟨40985891401420282999273379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27323927600946855332848919 40985891401420282999273379)
    ·
      refine ⟨61478837102130424498910069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40985891401420282999273379 61478837102130424498910069)
      ·
        refine ⟨5763640978324727296772819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61478837102130424498910069 5763640978324727296772819)
        ·
          refine ⟨8645461467487090945159229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5763640978324727296772819 8645461467487090945159229)
          ·
            refine ⟨3242048050307659104434711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8645461467487090945159229 3242048050307659104434711)
            ·
              refine ⟨4863072075461488656652067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3242048050307659104434711 4863072075461488656652067)
              ·
                refine ⟨7294608113192232984978101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4863072075461488656652067 7294608113192232984978101)
                ·
                  refine ⟨683869510611771842341697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7294608113192232984978101 683869510611771842341697)
                  ·
                    refine ⟨512902132958828881756273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 683869510611771842341697 512902132958828881756273)
                    ·
                      refine ⟨384676599719121661317205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 512902132958828881756273 384676599719121661317205)
                      ·
                        rfl

theorem cell23_749155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_749155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749155 prefixEnd_749155 := by exact prefixLift 749155
  have htrace : WordTrace (prefixWord ++ tailWord_749155) baseStart_749155 baseEnd_749155 := by
    simpa [prefixWord, tailWord_749155, baseEnd_749155] using wordTrace_append hprefix tailTrace_749155
  have hstable : (prefixWord ++ tailWord_749155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749155).length < 2 ^ (prefixWord ++ tailWord_749155).sum := by decide
  have hdescent : baseEnd_749155 < baseStart_749155 := by decide
  rcases family_descends (prefixWord ++ tailWord_749155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749168 : List Nat := [2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 4]
def baseStart_749168 : Nat := 118140960795 + 749168 * 2 ^ 59
def prefixEnd_749168 : Nat := 4983230072969 + 3 ^ 40 * 749168 * 2
def baseEnd_749168 : Nat := 384683274967630110454645

theorem tailTrace_749168 : CollatzResearch.WordTrace tailWord_749168 prefixEnd_749168 384683274967630110454645 := by
  unfold tailWord_749168
  simp only [CollatzResearch.WordTrace]
  refine ⟨13662200874949879276536079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18216267833266505702048105 13662200874949879276536079)
  ·
    refine ⟨20493301312424818914804119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13662200874949879276536079 20493301312424818914804119)
    ·
      refine ⟨30739951968637228372206179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20493301312424818914804119 30739951968637228372206179)
      ·
        refine ⟨46109927952955842558309269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30739951968637228372206179 46109927952955842558309269)
        ·
          refine ⟨2161402872794805119920747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46109927952955842558309269 2161402872794805119920747)
          ·
            refine ⟨3242104309192207679881121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2161402872794805119920747 3242104309192207679881121)
            ·
              refine ⟨2431578231894155759910841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3242104309192207679881121 2431578231894155759910841)
              ·
                refine ⟨1823683673920616819933131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2431578231894155759910841 1823683673920616819933131)
                ·
                  refine ⟨2735525510880925229899697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823683673920616819933131 2735525510880925229899697)
                  ·
                    refine ⟨2051644133160693922424773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2735525510880925229899697 2051644133160693922424773)
                    ·
                      refine ⟨384683274967630110454645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2051644133160693922424773 384683274967630110454645)
                      ·
                        rfl

theorem cell23_749168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 4].length) (baseStart_749168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749168 prefixEnd_749168 := by exact prefixLift 749168
  have htrace : WordTrace (prefixWord ++ tailWord_749168) baseStart_749168 baseEnd_749168 := by
    simpa [prefixWord, tailWord_749168, baseEnd_749168] using wordTrace_append hprefix tailTrace_749168
  have hstable : (prefixWord ++ tailWord_749168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749168).length < 2 ^ (prefixWord ++ tailWord_749168).sum := by decide
  have hdescent : baseEnd_749168 < baseStart_749168 := by decide
  rcases family_descends (prefixWord ++ tailWord_749168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749171 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 3]
def baseStart_749171 : Nat := 118140960795 + 749171 * 2 ^ 59
def prefixEnd_749171 : Nat := 4983230072969 + 3 ^ 40 * 749171 * 2
def baseEnd_749171 : Nat := 384684815409593598717131

theorem tailTrace_749171 : CollatzResearch.WordTrace tailWord_749171 prefixEnd_749171 384684815409593598717131 := by
  unfold tailWord_749171
  simp only [CollatzResearch.WordTrace]
  refine ⟨27324511168888890065431367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18216340779259260043620911 27324511168888890065431367)
  ·
    refine ⟨40986766753333335098147051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27324511168888890065431367 40986766753333335098147051)
    ·
      refine ⟨61480150130000002647220577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40986766753333335098147051 61480150130000002647220577)
      ·
        refine ⟨46110112597500001985415433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61480150130000002647220577 46110112597500001985415433)
        ·
          refine ⟨34582584448125001489061575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46110112597500001985415433 34582584448125001489061575)
          ·
            refine ⟨51873876672187502233592363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34582584448125001489061575 51873876672187502233592363)
            ·
              refine ⟨77810815008281253350388545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51873876672187502233592363 77810815008281253350388545)
              ·
                refine ⟨58358111256210940012791409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77810815008281253350388545 58358111256210940012791409)
                ·
                  refine ⟨43768583442158205009593557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58358111256210940012791409 43768583442158205009593557)
                  ·
                    refine ⟨1025826174425582929912349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43768583442158205009593557 1025826174425582929912349)
                    ·
                      refine ⟨384684815409593598717131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1025826174425582929912349 384684815409593598717131)
                      ·
                        rfl

theorem cell23_749171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 3].length) (baseStart_749171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749171 prefixEnd_749171 := by exact prefixLift 749171
  have htrace : WordTrace (prefixWord ++ tailWord_749171) baseStart_749171 baseEnd_749171 := by
    simpa [prefixWord, tailWord_749171, baseEnd_749171] using wordTrace_append hprefix tailTrace_749171
  have hstable : (prefixWord ++ tailWord_749171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749171).length < 2 ^ (prefixWord ++ tailWord_749171).sum := by decide
  have hdescent : baseEnd_749171 < baseStart_749171 := by decide
  rcases family_descends (prefixWord ++ tailWord_749171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749202 : List Nat := [3, 2, 3, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_749202 : Nat := 118140960795 + 749202 * 2 ^ 59
def prefixEnd_749202 : Nat := 4983230072969 + 3 ^ 40 * 749202 * 2
def baseEnd_749202 : Nat := 384700733309882977429489

theorem tailTrace_749202 : CollatzResearch.WordTrace tailWord_749202 prefixEnd_749202 384700733309882977429489 := by
  unfold tailWord_749202
  simp only [CollatzResearch.WordTrace]
  refine ⟨6831410457944145589952465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18217094554517721573206573 6831410457944145589952465)
  ·
    refine ⟨5123557843458109192464349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6831410457944145589952465 5123557843458109192464349)
    ·
      refine ⟨1921334191296790947174131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5123557843458109192464349 1921334191296790947174131)
      ·
        refine ⟨2882001286945186420761197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1921334191296790947174131 2882001286945186420761197)
        ·
          refine ⟨1080750482604444907785449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2882001286945186420761197 1080750482604444907785449)
          ·
            refine ⟨810562861953333680839087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1080750482604444907785449 810562861953333680839087)
            ·
              refine ⟨1215844292930000521258631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810562861953333680839087 1215844292930000521258631)
              ·
                refine ⟨1823766439395000781887947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215844292930000521258631 1823766439395000781887947)
                ·
                  refine ⟨2735649659092501172831921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823766439395000781887947 2735649659092501172831921)
                  ·
                    refine ⟨2051737244319375879623941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2735649659092501172831921 2051737244319375879623941)
                    ·
                      refine ⟨384700733309882977429489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2051737244319375879623941 384700733309882977429489)
                      ·
                        rfl

theorem cell23_749202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_749202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749202 prefixEnd_749202 := by exact prefixLift 749202
  have htrace : WordTrace (prefixWord ++ tailWord_749202) baseStart_749202 baseEnd_749202 := by
    simpa [prefixWord, tailWord_749202, baseEnd_749202] using wordTrace_append hprefix tailTrace_749202
  have hstable : (prefixWord ++ tailWord_749202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749202).length < 2 ^ (prefixWord ++ tailWord_749202).sum := by decide
  have hdescent : baseEnd_749202 < baseStart_749202 := by decide
  rcases family_descends (prefixWord ++ tailWord_749202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749205 : List Nat := [1, 3, 2, 1, 1, 1, 1, 7, 2, 1, 3]
def baseStart_749205 : Nat := 118140960795 + 749205 * 2 ^ 59
def prefixEnd_749205 : Nat := 4983230072969 + 3 ^ 40 * 749205 * 2
def baseEnd_749205 : Nat := 384702273751846465691975

theorem tailTrace_749205 : CollatzResearch.WordTrace tailWord_749205 prefixEnd_749205 384702273751846465691975 := by
  unfold tailWord_749205
  simp only [CollatzResearch.WordTrace]
  refine ⟨27325751250765713872169069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18217167500510475914779379 27325751250765713872169069)
  ·
    refine ⟨10247156719037142702063401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27325751250765713872169069 10247156719037142702063401)
    ·
      refine ⟨7685367539277857026547551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10247156719037142702063401 7685367539277857026547551)
      ·
        refine ⟨11528051308916785539821327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7685367539277857026547551 11528051308916785539821327)
        ·
          refine ⟨17292076963375178309731991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11528051308916785539821327 17292076963375178309731991)
          ·
            refine ⟨25938115445062767464597987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17292076963375178309731991 25938115445062767464597987)
            ·
              refine ⟨38907173167594151196896981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25938115445062767464597987 38907173167594151196896981)
              ·
                refine ⟨911886871115487918677273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 38907173167594151196896981 911886871115487918677273)
                ·
                  refine ⟨683915153336615939007955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 911886871115487918677273 683915153336615939007955)
                  ·
                    refine ⟨1025872730004923908511933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 683915153336615939007955 1025872730004923908511933)
                    ·
                      refine ⟨384702273751846465691975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1025872730004923908511933 384702273751846465691975)
                      ·
                        rfl

theorem cell23_749205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_749205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749205 prefixEnd_749205 := by exact prefixLift 749205
  have htrace : WordTrace (prefixWord ++ tailWord_749205) baseStart_749205 baseEnd_749205 := by
    simpa [prefixWord, tailWord_749205, baseEnd_749205] using wordTrace_append hprefix tailTrace_749205
  have hstable : (prefixWord ++ tailWord_749205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749205).length < 2 ^ (prefixWord ++ tailWord_749205).sum := by decide
  have hdescent : baseEnd_749205 < baseStart_749205 := by decide
  rcases family_descends (prefixWord ++ tailWord_749205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749212 : List Nat := [2, 2, 3, 2, 4, 1, 2, 7]
def baseStart_749212 : Nat := 118140960795 + 749212 * 2 ^ 59
def prefixEnd_749212 : Nat := 4983230072969 + 3 ^ 40 * 749212 * 2
def baseEnd_749212 : Nat := 14248365485793627344609

theorem tailTrace_749212 : CollatzResearch.WordTrace tailWord_749212 prefixEnd_749212 14248365485793627344609 := by
  unfold tailWord_749212
  simp only [CollatzResearch.WordTrace]
  refine ⟨13663003280870177033836945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18217337707826902711782593 13663003280870177033836945)
  ·
    refine ⟨10247252460652632775377709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13663003280870177033836945 10247252460652632775377709)
    ·
      refine ⟨3842719672744737290766641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10247252460652632775377709 3842719672744737290766641)
      ·
        refine ⟨2882039754558552968074981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3842719672744737290766641 2882039754558552968074981)
        ·
          refine ⟨540382453979728681514059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2882039754558552968074981 540382453979728681514059)
          ·
            refine ⟨810573680969593022271089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540382453979728681514059 810573680969593022271089)
            ·
              refine ⟨607930260727194766703317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 810573680969593022271089 607930260727194766703317)
              ·
                refine ⟨14248365485793627344609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 607930260727194766703317 14248365485793627344609)
                ·
                  rfl

theorem cell23_749212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 7].length) (baseStart_749212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749212 prefixEnd_749212 := by exact prefixLift 749212
  have htrace : WordTrace (prefixWord ++ tailWord_749212) baseStart_749212 baseEnd_749212 := by
    simpa [prefixWord, tailWord_749212, baseEnd_749212] using wordTrace_append hprefix tailTrace_749212
  have hstable : (prefixWord ++ tailWord_749212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749212).length < 2 ^ (prefixWord ++ tailWord_749212).sum := by decide
  have hdescent : baseEnd_749212 < baseStart_749212 := by decide
  rcases family_descends (prefixWord ++ tailWord_749212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749221 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 1, 8]
def baseStart_749221 : Nat := 118140960795 + 749221 * 2 ^ 59
def prefixEnd_749221 : Nat := 4983230072969 + 3 ^ 40 * 749221 * 2
def baseEnd_749221 : Nat := 128236829814106134363967

theorem tailTrace_749221 : CollatzResearch.WordTrace tailWord_749221 prefixEnd_749221 128236829814106134363967 := by
  unfold tailWord_749221
  simp only [CollatzResearch.WordTrace]
  refine ⟨27326334818707748604751517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18217556545805165736501011 27326334818707748604751517)
  ·
    refine ⟨10247375557015405726781819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27326334818707748604751517 10247375557015405726781819)
    ·
      refine ⟨15371063335523108590172729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10247375557015405726781819 15371063335523108590172729)
      ·
        refine ⟨11528297501642331442629547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15371063335523108590172729 11528297501642331442629547)
        ·
          refine ⟨17292446252463497163944321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11528297501642331442629547 17292446252463497163944321)
          ·
            refine ⟨12969334689347622872958241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17292446252463497163944321 12969334689347622872958241)
            ·
              refine ⟨9727001017010717154718681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12969334689347622872958241 9727001017010717154718681)
              ·
                refine ⟨7295250762758037866039011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9727001017010717154718681 7295250762758037866039011)
                ·
                  refine ⟨10942876144137056799058517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7295250762758037866039011 10942876144137056799058517)
                  ·
                    refine ⟨128236829814106134363967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10942876144137056799058517 128236829814106134363967)
                    ·
                      rfl

theorem cell23_749221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_749221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749221 prefixEnd_749221 := by exact prefixLift 749221
  have htrace : WordTrace (prefixWord ++ tailWord_749221) baseStart_749221 baseEnd_749221 := by
    simpa [prefixWord, tailWord_749221, baseEnd_749221] using wordTrace_append hprefix tailTrace_749221
  have hstable : (prefixWord ++ tailWord_749221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749221).length < 2 ^ (prefixWord ++ tailWord_749221).sum := by decide
  have hdescent : baseEnd_749221 < baseStart_749221 := by decide
  rcases family_descends (prefixWord ++ tailWord_749221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749248 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 3]
def baseStart_749248 : Nat := 118140960795 + 749248 * 2 ^ 59
def prefixEnd_749248 : Nat := 4983230072969 + 3 ^ 40 * 749248 * 2
def baseEnd_749248 : Nat := 384724353419989797454277

theorem tailTrace_749248 : CollatzResearch.WordTrace tailWord_749248 prefixEnd_749248 384724353419989797454277 := by
  unfold tailWord_749248
  simp only [CollatzResearch.WordTrace]
  refine ⟨13663659794804966107992199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18218213059739954810656265 13663659794804966107992199)
  ·
    refine ⟨20495489692207449161988299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13663659794804966107992199 20495489692207449161988299)
    ·
      refine ⟨30743234538311173742982449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20495489692207449161988299 30743234538311173742982449)
      ·
        refine ⟨23057425903733380307236837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30743234538311173742982449 23057425903733380307236837)
        ·
          refine ⟨4323267356950008807606907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23057425903733380307236837 4323267356950008807606907)
          ·
            refine ⟨6484901035425013211410361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4323267356950008807606907 6484901035425013211410361)
            ·
              refine ⟨4863675776568759908557771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6484901035425013211410361 4863675776568759908557771)
              ·
                refine ⟨7295513664853139862836657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4863675776568759908557771 7295513664853139862836657)
                ·
                  refine ⟨5471635248639854897127493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7295513664853139862836657 5471635248639854897127493)
                  ·
                    refine ⟨1025931609119972793211405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5471635248639854897127493 1025931609119972793211405)
                    ·
                      refine ⟨384724353419989797454277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1025931609119972793211405 384724353419989797454277)
                      ·
                        rfl

theorem cell23_749248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_749248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749248 prefixEnd_749248 := by exact prefixLift 749248
  have htrace : WordTrace (prefixWord ++ tailWord_749248) baseStart_749248 baseEnd_749248 := by
    simpa [prefixWord, tailWord_749248, baseEnd_749248] using wordTrace_append hprefix tailTrace_749248
  have hstable : (prefixWord ++ tailWord_749248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749248).length < 2 ^ (prefixWord ++ tailWord_749248).sum := by decide
  have hdescent : baseEnd_749248 < baseStart_749248 := by decide
  rcases family_descends (prefixWord ++ tailWord_749248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749250 : List Nat := [3, 5, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_749250 : Nat := 118140960795 + 749250 * 2 ^ 59
def prefixEnd_749250 : Nat := 4983230072969 + 3 ^ 40 * 749250 * 2
def baseEnd_749250 : Nat := 128241793460432929876423

theorem tailTrace_749250 : CollatzResearch.WordTrace tailWord_749250 prefixEnd_749250 128241793460432929876423 := by
  unfold tailWord_749250
  simp only [CollatzResearch.WordTrace]
  refine ⟨6831848133900671639389301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18218261690401791038371469 6831848133900671639389301)
  ·
    refine ⟨640485762553187966192747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6831848133900671639389301 640485762553187966192747)
    ·
      refine ⟨960728643829781949289121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 640485762553187966192747 960728643829781949289121)
      ·
        refine ⟨720546482872336461966841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 960728643829781949289121 720546482872336461966841)
        ·
          refine ⟨540409862154252346475131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 720546482872336461966841 540409862154252346475131)
          ·
            refine ⟨810614793231378519712697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540409862154252346475131 810614793231378519712697)
            ·
              refine ⟨607961094923533889784523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 810614793231378519712697 607961094923533889784523)
              ·
                refine ⟨911941642385300834676785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607961094923533889784523 911941642385300834676785)
                ·
                  refine ⟨683956231788975626007589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 911941642385300834676785 683956231788975626007589)
                  ·
                    refine ⟨128241793460432929876423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 683956231788975626007589 128241793460432929876423)
                    ·
                      rfl

theorem cell23_749250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_749250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749250 prefixEnd_749250 := by exact prefixLift 749250
  have htrace : WordTrace (prefixWord ++ tailWord_749250) baseStart_749250 baseEnd_749250 := by
    simpa [prefixWord, tailWord_749250, baseEnd_749250] using wordTrace_append hprefix tailTrace_749250
  have hstable : (prefixWord ++ tailWord_749250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749250).length < 2 ^ (prefixWord ++ tailWord_749250).sum := by decide
  have hdescent : baseEnd_749250 < baseStart_749250 := by decide
  rcases family_descends (prefixWord ++ tailWord_749250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749285 : List Nat := [1, 3, 1, 4, 1, 1, 2, 5, 5]
def baseStart_749285 : Nat := 118140960795 + 749285 * 2 ^ 59
def prefixEnd_749285 : Nat := 4983230072969 + 3 ^ 40 * 749285 * 2
def baseEnd_749285 : Nat := 42749261356022905854623

theorem tailTrace_749285 : CollatzResearch.WordTrace tailWord_749285 prefixEnd_749285 42749261356022905854623 := by
  unfold tailWord_749285
  simp only [CollatzResearch.WordTrace]
  refine ⟨27328669090475887535081309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18219112726983925023387539 27328669090475887535081309)
  ·
    refine ⟨10248250908928457825655491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27328669090475887535081309 10248250908928457825655491)
    ·
      refine ⟨15372376363392686738483237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10248250908928457825655491 15372376363392686738483237)
      ·
        refine ⟨2882320568136128763465607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15372376363392686738483237 2882320568136128763465607)
        ·
          refine ⟨4323480852204193145198411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2882320568136128763465607 4323480852204193145198411)
          ·
            refine ⟨6485221278306289717797617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4323480852204193145198411 6485221278306289717797617)
            ·
              refine ⟨4863915958729717288348213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6485221278306289717797617 4863915958729717288348213)
              ·
                refine ⟨455992121130910995782645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4863915958729717288348213 455992121130910995782645)
                ·
                  refine ⟨42749261356022905854623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 455992121130910995782645 42749261356022905854623)
                  ·
                    rfl

theorem cell23_749285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 5].length) (baseStart_749285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749285 prefixEnd_749285 := by exact prefixLift 749285
  have htrace : WordTrace (prefixWord ++ tailWord_749285) baseStart_749285 baseEnd_749285 := by
    simpa [prefixWord, tailWord_749285, baseEnd_749285] using wordTrace_append hprefix tailTrace_749285
  have hstable : (prefixWord ++ tailWord_749285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749285).length < 2 ^ (prefixWord ++ tailWord_749285).sum := by decide
  have hdescent : baseEnd_749285 < baseStart_749285 := by decide
  rcases family_descends (prefixWord ++ tailWord_749285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749302 : List Nat := [5, 1, 1, 1, 1, 4, 1, 4, 5]
def baseStart_749302 : Nat := 118140960795 + 749302 * 2 ^ 59
def prefixEnd_749302 : Nat := 4983230072969 + 3 ^ 40 * 749302 * 2
def baseEnd_749302 : Nat := 42750231263925842908781

theorem tailTrace_749302 : CollatzResearch.WordTrace tailWord_749302 prefixEnd_749302 42750231263925842908781 := by
  unfold tailWord_749302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1708080570713393714903135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18219526087609532958966773 1708080570713393714903135)
  ·
    refine ⟨2562120856070090572354703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1708080570713393714903135 2562120856070090572354703)
    ·
      refine ⟨3843181284105135858532055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2562120856070090572354703 3843181284105135858532055)
      ·
        refine ⟨5764771926157703787798083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3843181284105135858532055 5764771926157703787798083)
        ·
          refine ⟨8647157889236555681697125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5764771926157703787798083 8647157889236555681697125)
          ·
            refine ⟨1621342104231854190318211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8647157889236555681697125 1621342104231854190318211)
            ·
              refine ⟨2432013156347781285477317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1621342104231854190318211 2432013156347781285477317)
              ·
                refine ⟨456002466815208991026997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2432013156347781285477317 456002466815208991026997)
                ·
                  refine ⟨42750231263925842908781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 456002466815208991026997 42750231263925842908781)
                  ·
                    rfl

theorem cell23_749302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_749302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749302 prefixEnd_749302 := by exact prefixLift 749302
  have htrace : WordTrace (prefixWord ++ tailWord_749302) baseStart_749302 baseEnd_749302 := by
    simpa [prefixWord, tailWord_749302, baseEnd_749302] using wordTrace_append hprefix tailTrace_749302
  have hstable : (prefixWord ++ tailWord_749302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749302).length < 2 ^ (prefixWord ++ tailWord_749302).sum := by decide
  have hdescent : baseEnd_749302 < baseStart_749302 := by decide
  rcases family_descends (prefixWord ++ tailWord_749302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749308 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_749308 : Nat := 118140960795 + 749308 * 2 ^ 59
def prefixEnd_749308 : Nat := 4983230072969 + 3 ^ 40 * 749308 * 2
def baseEnd_749308 : Nat := 384755162259259562704001

theorem tailTrace_749308 : CollatzResearch.WordTrace tailWord_749308 prefixEnd_749308 384755162259259562704001 := by
  unfold tailWord_749308
  simp only [CollatzResearch.WordTrace]
  refine ⟨13664753984696281231584289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18219671979595041642112385 13664753984696281231584289)
  ·
    refine ⟨10248565488522210923688217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13664753984696281231584289 10248565488522210923688217)
    ·
      refine ⟨7686424116391658192766163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10248565488522210923688217 7686424116391658192766163)
      ·
        refine ⟨11529636174587487289149245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7686424116391658192766163 11529636174587487289149245)
        ·
          refine ⟨4323613565470307733430967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11529636174587487289149245 4323613565470307733430967)
          ·
            refine ⟨6485420348205461600146451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4323613565470307733430967 6485420348205461600146451)
            ·
              refine ⟨9728130522308192400219677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6485420348205461600146451 9728130522308192400219677)
              ·
                refine ⟨3648048945865572150082379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9728130522308192400219677 3648048945865572150082379)
                ·
                  refine ⟨5472073418798358225123569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3648048945865572150082379 5472073418798358225123569)
                  ·
                    refine ⟨4104055064098768668842677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5472073418798358225123569 4104055064098768668842677)
                    ·
                      refine ⟨384755162259259562704001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4104055064098768668842677 384755162259259562704001)
                      ·
                        rfl

theorem cell23_749308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_749308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749308 prefixEnd_749308 := by exact prefixLift 749308
  have htrace : WordTrace (prefixWord ++ tailWord_749308) baseStart_749308 baseEnd_749308 := by
    simpa [prefixWord, tailWord_749308, baseEnd_749308] using wordTrace_append hprefix tailTrace_749308
  have hstable : (prefixWord ++ tailWord_749308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749308).length < 2 ^ (prefixWord ++ tailWord_749308).sum := by decide
  have hdescent : baseEnd_749308 < baseStart_749308 := by decide
  rcases family_descends (prefixWord ++ tailWord_749308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749335 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 4]
def baseStart_749335 : Nat := 118140960795 + 749335 * 2 ^ 59
def prefixEnd_749335 : Nat := 4983230072969 + 3 ^ 40 * 749335 * 2
def baseEnd_749335 : Nat := 384769026236930957066377

theorem tailTrace_749335 : CollatzResearch.WordTrace tailWord_749335 prefixEnd_749335 384769026236930957066377 := by
  unfold tailWord_749335
  simp only [CollatzResearch.WordTrace]
  refine ⟨27330492740294746074401459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18220328493529830716267639 27330492740294746074401459)
  ·
    refine ⟨40995739110442119111602189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27330492740294746074401459 40995739110442119111602189)
    ·
      refine ⟨15373402166415794666850821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40995739110442119111602189 15373402166415794666850821)
      ·
        refine ⟨2882512906202961500034529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15373402166415794666850821 2882512906202961500034529)
        ·
          refine ⟨2161884679652221125025897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2882512906202961500034529 2161884679652221125025897)
          ·
            refine ⟨1621413509739165843769423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2161884679652221125025897 1621413509739165843769423)
            ·
              refine ⟨2432120264608748765654135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1621413509739165843769423 2432120264608748765654135)
              ·
                refine ⟨3648180396913123148481203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2432120264608748765654135 3648180396913123148481203)
                ·
                  refine ⟨5472270595369684722721805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3648180396913123148481203 5472270595369684722721805)
                  ·
                    refine ⟨2052101473263631771020677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5472270595369684722721805 2052101473263631771020677)
                    ·
                      refine ⟨384769026236930957066377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2052101473263631771020677 384769026236930957066377)
                      ·
                        rfl

theorem cell23_749335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_749335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749335 prefixEnd_749335 := by exact prefixLift 749335
  have htrace : WordTrace (prefixWord ++ tailWord_749335) baseStart_749335 baseEnd_749335 := by
    simpa [prefixWord, tailWord_749335, baseEnd_749335] using wordTrace_append hprefix tailTrace_749335
  have hstable : (prefixWord ++ tailWord_749335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749335).length < 2 ^ (prefixWord ++ tailWord_749335).sum := by decide
  have hdescent : baseEnd_749335 < baseStart_749335 := by decide
  rcases family_descends (prefixWord ++ tailWord_749335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749352 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_749352 : Nat := 118140960795 + 749352 * 2 ^ 59
def prefixEnd_749352 : Nat := 4983230072969 + 3 ^ 40 * 749352 * 2
def baseEnd_749352 : Nat := 384777755408057390553799

theorem tailTrace_749352 : CollatzResearch.WordTrace tailWord_749352 prefixEnd_749352 384777755408057390553799 := by
  unfold tailWord_749352
  simp only [CollatzResearch.WordTrace]
  refine ⟨13665556390616578988885155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18220741854155438651846873 13665556390616578988885155)
  ·
    refine ⟨20498334585924868483327733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13665556390616578988885155 20498334585924868483327733)
    ·
      refine ⟨1921718867430456420311975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20498334585924868483327733 1921718867430456420311975)
      ·
        refine ⟨2882578301145684630467963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1921718867430456420311975 2882578301145684630467963)
        ·
          refine ⟨4323867451718526945701945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2882578301145684630467963 4323867451718526945701945)
          ·
            refine ⟨3242900588788895209276459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4323867451718526945701945 3242900588788895209276459)
            ·
              refine ⟨4864350883183342813914689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3242900588788895209276459 4864350883183342813914689)
              ·
                refine ⟨3648263162387507110436017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4864350883183342813914689 3648263162387507110436017)
                ·
                  refine ⟨2736197371790630332827013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3648263162387507110436017 2736197371790630332827013)
                  ·
                    refine ⟨513037007210743187405065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2736197371790630332827013 513037007210743187405065)
                    ·
                      refine ⟨384777755408057390553799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 513037007210743187405065 384777755408057390553799)
                      ·
                        rfl

theorem cell23_749352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_749352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749352 prefixEnd_749352 := by exact prefixLift 749352
  have htrace : WordTrace (prefixWord ++ tailWord_749352) baseStart_749352 baseEnd_749352 := by
    simpa [prefixWord, tailWord_749352, baseEnd_749352] using wordTrace_append hprefix tailTrace_749352
  have hstable : (prefixWord ++ tailWord_749352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749352).length < 2 ^ (prefixWord ++ tailWord_749352).sum := by decide
  have hdescent : baseEnd_749352 < baseStart_749352 := by decide
  rcases family_descends (prefixWord ++ tailWord_749352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749362 : List Nat := [3, 2, 1, 1, 3, 3, 2, 1, 3, 4]
def baseStart_749362 : Nat := 118140960795 + 749362 * 2 ^ 59
def prefixEnd_749362 : Nat := 4983230072969 + 3 ^ 40 * 749362 * 2
def baseEnd_749362 : Nat := 128260963404867450476251

theorem tailTrace_749362 : CollatzResearch.WordTrace tailWord_749362 prefixEnd_749362 128260963404867450476251 := by
  unfold tailWord_749362
  simp only [CollatzResearch.WordTrace]
  refine ⟨6832869377799232421408585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18220985007464619790422893 6832869377799232421408585)
  ·
    refine ⟨5124652033349424316056439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6832869377799232421408585 5124652033349424316056439)
    ·
      refine ⟨7686978050024136474084659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5124652033349424316056439 7686978050024136474084659)
      ·
        refine ⟨11530467075036204711126989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7686978050024136474084659 11530467075036204711126989)
        ·
          refine ⟨4323925153138576766672621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11530467075036204711126989 4323925153138576766672621)
          ·
            refine ⟨1621471932426966287502233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4323925153138576766672621 1621471932426966287502233)
            ·
              refine ⟨1216103949320224715626675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1621471932426966287502233 1216103949320224715626675)
              ·
                refine ⟨1824155923980337073440013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1216103949320224715626675 1824155923980337073440013)
                ·
                  refine ⟨684058471492626402540005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1824155923980337073440013 684058471492626402540005)
                  ·
                    refine ⟨128260963404867450476251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 684058471492626402540005 128260963404867450476251)
                    ·
                      rfl

theorem cell23_749362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_749362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749362 prefixEnd_749362 := by exact prefixLift 749362
  have htrace : WordTrace (prefixWord ++ tailWord_749362) baseStart_749362 baseEnd_749362 := by
    simpa [prefixWord, tailWord_749362, baseEnd_749362] using wordTrace_append hprefix tailTrace_749362
  have hstable : (prefixWord ++ tailWord_749362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749362).length < 2 ^ (prefixWord ++ tailWord_749362).sum := by decide
  have hdescent : baseEnd_749362 < baseStart_749362 := by decide
  rcases family_descends (prefixWord ++ tailWord_749362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749396 : List Nat := [2, 4, 1, 1, 3, 3, 1, 3, 1, 4]
def baseStart_749396 : Nat := 118140960795 + 749396 * 2 ^ 59
def prefixEnd_749396 : Nat := 4983230072969 + 3 ^ 40 * 749396 * 2
def baseEnd_749396 : Nat := 128266782852285072801199

theorem tailTrace_749396 : CollatzResearch.WordTrace tailWord_749396 prefixEnd_749396 128266782852285072801199 := by
  unfold tailWord_749396
  simp only [CollatzResearch.WordTrace]
  refine ⟨13666358796536876746186021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18221811728715835661581361 13666358796536876746186021)
  ·
    refine ⟨2562442274350664389909879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13666358796536876746186021 2562442274350664389909879)
    ·
      refine ⟨3843663411525996584864819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2562442274350664389909879 3843663411525996584864819)
      ·
        refine ⟨5765495117288994877297229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3843663411525996584864819 5765495117288994877297229)
        ·
          refine ⟨2162060668983373078986461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5765495117288994877297229 2162060668983373078986461)
          ·
            refine ⟨810772750868764904619923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2162060668983373078986461 810772750868764904619923)
            ·
              refine ⟨1216159126303147356929885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810772750868764904619923 1216159126303147356929885)
              ·
                refine ⟨456059672363680258848707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1216159126303147356929885 456059672363680258848707)
                ·
                  refine ⟨684089508545520388273061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456059672363680258848707 684089508545520388273061)
                  ·
                    refine ⟨128266782852285072801199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 684089508545520388273061 128266782852285072801199)
                    ·
                      rfl

theorem cell23_749396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_749396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749396 prefixEnd_749396 := by exact prefixLift 749396
  have htrace : WordTrace (prefixWord ++ tailWord_749396) baseStart_749396 baseEnd_749396 := by
    simpa [prefixWord, tailWord_749396, baseEnd_749396] using wordTrace_append hprefix tailTrace_749396
  have hstable : (prefixWord ++ tailWord_749396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749396).length < 2 ^ (prefixWord ++ tailWord_749396).sum := by decide
  have hdescent : baseEnd_749396 < baseStart_749396 := by decide
  rcases family_descends (prefixWord ++ tailWord_749396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749425 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 3, 1, 4]
def baseStart_749425 : Nat := 118140960795 + 749425 * 2 ^ 59
def prefixEnd_749425 : Nat := 4983230072969 + 3 ^ 40 * 749425 * 2
def baseEnd_749425 : Nat := 384815239495835604940963

theorem tailTrace_749425 : CollatzResearch.WordTrace tailWord_749425 prefixEnd_749425 384815239495835604940963 := by
  unfold tailWord_749425
  simp only [CollatzResearch.WordTrace]
  refine ⟨27333775309968691445177729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18222516873312460963451819 27333775309968691445177729)
  ·
    refine ⟨20500331482476518583883297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27333775309968691445177729 20500331482476518583883297)
    ·
      refine ⟨15375248611857388937912473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20500331482476518583883297 15375248611857388937912473)
      ·
        refine ⟨11531436458893041703434355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15375248611857388937912473 11531436458893041703434355)
        ·
          refine ⟨17297154688339562555151533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11531436458893041703434355 17297154688339562555151533)
          ·
            refine ⟨6486433008127335958181825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17297154688339562555151533 6486433008127335958181825)
            ·
              refine ⟨4864824756095501968636369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6486433008127335958181825 4864824756095501968636369)
              ·
                refine ⟨3648618567071626476477277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4864824756095501968636369 3648618567071626476477277)
                ·
                  refine ⟨1368231962651859928678979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3648618567071626476477277 1368231962651859928678979)
                  ·
                    refine ⟨2052347943977789893018469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1368231962651859928678979 2052347943977789893018469)
                    ·
                      refine ⟨384815239495835604940963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2052347943977789893018469 384815239495835604940963)
                      ·
                        rfl

theorem cell23_749425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_749425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749425 prefixEnd_749425 := by exact prefixLift 749425
  have htrace : WordTrace (prefixWord ++ tailWord_749425) baseStart_749425 baseEnd_749425 := by
    simpa [prefixWord, tailWord_749425, baseEnd_749425] using wordTrace_append hprefix tailTrace_749425
  have hstable : (prefixWord ++ tailWord_749425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749425).length < 2 ^ (prefixWord ++ tailWord_749425).sum := by decide
  have hdescent : baseEnd_749425 < baseStart_749425 := by decide
  rcases family_descends (prefixWord ++ tailWord_749425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749469 : List Nat := [1, 4, 2, 1, 2, 3, 2, 2, 2, 4]
def baseStart_749469 : Nat := 118140960795 + 749469 * 2 ^ 59
def prefixEnd_749469 : Nat := 4983230072969 + 3 ^ 40 * 749469 * 2
def baseEnd_749469 : Nat := 128279277548211144263587

theorem tailTrace_749469 : CollatzResearch.WordTrace tailWord_749469 prefixEnd_749469 128279277548211144263587 := by
  unfold tailWord_749469
  simp only [CollatzResearch.WordTrace]
  refine ⟨27335380121809286959779461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18223586747872857973186307 27335380121809286959779461)
  ·
    refine ⟨5125383772839241304958649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27335380121809286959779461 5125383772839241304958649)
    ·
      refine ⟨3844037829629430978718987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5125383772839241304958649 3844037829629430978718987)
      ·
        refine ⟨5766056744444146468078481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3844037829629430978718987 5766056744444146468078481)
        ·
          refine ⟨4324542558333109851058861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5766056744444146468078481 4324542558333109851058861)
          ·
            refine ⟨1621703459374916194147073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4324542558333109851058861 1621703459374916194147073)
            ·
              refine ⟨1216277594531187145610305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1621703459374916194147073 1216277594531187145610305)
              ·
                refine ⟨912208195898390359207729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1216277594531187145610305 912208195898390359207729)
                ·
                  refine ⟨684156146923792769405797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 912208195898390359207729 684156146923792769405797)
                  ·
                    refine ⟨128279277548211144263587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 684156146923792769405797 128279277548211144263587)
                    ·
                      rfl

theorem cell23_749469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_749469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749469 prefixEnd_749469 := by exact prefixLift 749469
  have htrace : WordTrace (prefixWord ++ tailWord_749469) baseStart_749469 baseEnd_749469 := by
    simpa [prefixWord, tailWord_749469, baseEnd_749469] using wordTrace_append hprefix tailTrace_749469
  have hstable : (prefixWord ++ tailWord_749469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749469).length < 2 ^ (prefixWord ++ tailWord_749469).sum := by decide
  have hdescent : baseEnd_749469 < baseStart_749469 := by decide
  rcases family_descends (prefixWord ++ tailWord_749469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749470 : List Nat := [4, 3, 1, 3, 1, 1, 1, 4, 1, 1, 3]
def baseStart_749470 : Nat := 118140960795 + 749470 * 2 ^ 59
def prefixEnd_749470 : Nat := 4983230072969 + 3 ^ 40 * 749470 * 2
def baseEnd_749470 : Nat := 384838346125287928878257

theorem tailTrace_749470 : CollatzResearch.WordTrace tailWord_749470 prefixEnd_749470 384838346125287928878257 := by
  unfold tailWord_749470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3416927074350708016320733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18223611063203776087043909 3416927074350708016320733)
  ·
    refine ⟨1281347652881515506120275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3416927074350708016320733 1281347652881515506120275)
    ·
      refine ⟨1922021479322273259180413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1281347652881515506120275 1922021479322273259180413)
      ·
        refine ⟨720758054745852472192655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1922021479322273259180413 720758054745852472192655)
        ·
          refine ⟨1081137082118778708288983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720758054745852472192655 1081137082118778708288983)
          ·
            refine ⟨1621705623178168062433475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081137082118778708288983 1621705623178168062433475)
            ·
              refine ⟨2432558434767252093650213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1621705623178168062433475 2432558434767252093650213)
              ·
                refine ⟨456104706518859767559415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2432558434767252093650213 456104706518859767559415)
                ·
                  refine ⟨684157059778289651339123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456104706518859767559415 684157059778289651339123)
                  ·
                    refine ⟨1026235589667434477008685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 684157059778289651339123 1026235589667434477008685)
                    ·
                      refine ⟨384838346125287928878257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1026235589667434477008685 384838346125287928878257)
                      ·
                        rfl

theorem cell23_749470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_749470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749470 prefixEnd_749470 := by exact prefixLift 749470
  have htrace : WordTrace (prefixWord ++ tailWord_749470) baseStart_749470 baseEnd_749470 := by
    simpa [prefixWord, tailWord_749470, baseEnd_749470] using wordTrace_append hprefix tailTrace_749470
  have hstable : (prefixWord ++ tailWord_749470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749470).length < 2 ^ (prefixWord ++ tailWord_749470).sum := by decide
  have hdescent : baseEnd_749470 < baseStart_749470 := by decide
  rcases family_descends (prefixWord ++ tailWord_749470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749475 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 3]
def baseStart_749475 : Nat := 118140960795 + 749475 * 2 ^ 59
def prefixEnd_749475 : Nat := 4983230072969 + 3 ^ 40 * 749475 * 2
def baseEnd_749475 : Nat := 384840913528560409315733

theorem tailTrace_749475 : CollatzResearch.WordTrace tailWord_749475 prefixEnd_749475 384840913528560409315733 := by
  unfold tailWord_749475
  simp only [CollatzResearch.WordTrace]
  refine ⟨27335598959787549984497879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18223732639858366656331919 27335598959787549984497879)
  ·
    refine ⟨41003398439681324976746819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27335598959787549984497879 41003398439681324976746819)
    ·
      refine ⟨61505097659521987465120229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41003398439681324976746819 61505097659521987465120229)
      ·
        refine ⟨11532205811160372649710043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61505097659521987465120229 11532205811160372649710043)
        ·
          refine ⟨17298308716740558974565065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11532205811160372649710043 17298308716740558974565065)
          ·
            refine ⟨12973731537555419230923799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17298308716740558974565065 12973731537555419230923799)
            ·
              refine ⟨19460597306333128846385699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12973731537555419230923799 19460597306333128846385699)
              ·
                refine ⟨29190895959499693269578549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19460597306333128846385699 29190895959499693269578549)
                ·
                  refine ⟨2736646496203096244022989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29190895959499693269578549 2736646496203096244022989)
                  ·
                    refine ⟨1026242436076161091508621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2736646496203096244022989 1026242436076161091508621)
                    ·
                      refine ⟨384840913528560409315733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1026242436076161091508621 384840913528560409315733)
                      ·
                        rfl

theorem cell23_749475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_749475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749475 prefixEnd_749475 := by exact prefixLift 749475
  have htrace : WordTrace (prefixWord ++ tailWord_749475) baseStart_749475 baseEnd_749475 := by
    simpa [prefixWord, tailWord_749475, baseEnd_749475] using wordTrace_append hprefix tailTrace_749475
  have hstable : (prefixWord ++ tailWord_749475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749475).length < 2 ^ (prefixWord ++ tailWord_749475).sum := by decide
  have hdescent : baseEnd_749475 < baseStart_749475 := by decide
  rcases family_descends (prefixWord ++ tailWord_749475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749519 : List Nat := [1, 1, 2, 1, 1, 5, 3, 3, 1, 3, 2]
def baseStart_749519 : Nat := 118140960795 + 749519 * 2 ^ 59
def prefixEnd_749519 : Nat := 4983230072969 + 3 ^ 40 * 749519 * 2
def baseEnd_749519 : Nat := 384863506677358237165531

theorem tailTrace_749519 : CollatzResearch.WordTrace tailWord_749519 prefixEnd_749519 384863506677358237165531 := by
  unfold tailWord_749519
  simp only [CollatzResearch.WordTrace]
  refine ⟨27337203771628145499099611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18224802514418763666066407 27337203771628145499099611)
  ·
    refine ⟨41005805657442218248649417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27337203771628145499099611 41005805657442218248649417)
    ·
      refine ⟨30754354243081663686487063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41005805657442218248649417 30754354243081663686487063)
      ·
        refine ⟨46131531364622495529730595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30754354243081663686487063 46131531364622495529730595)
        ·
          refine ⟨69197297046933743294595893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46131531364622495529730595 69197297046933743294595893)
          ·
            refine ⟨6487246598150038433868365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69197297046933743294595893 6487246598150038433868365)
            ·
              refine ⟨2432717474306264412700637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6487246598150038433868365 2432717474306264412700637)
              ·
                refine ⟨912269052864849154762739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2432717474306264412700637 912269052864849154762739)
                ·
                  refine ⟨1368403579297273732144109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 912269052864849154762739 1368403579297273732144109)
                  ·
                    refine ⟨513151342236477649554041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1368403579297273732144109 513151342236477649554041)
                    ·
                      refine ⟨384863506677358237165531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 513151342236477649554041 384863506677358237165531)
                      ·
                        rfl

theorem cell23_749519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 3, 2].length) (baseStart_749519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749519 prefixEnd_749519 := by exact prefixLift 749519
  have htrace : WordTrace (prefixWord ++ tailWord_749519) baseStart_749519 baseEnd_749519 := by
    simpa [prefixWord, tailWord_749519, baseEnd_749519] using wordTrace_append hprefix tailTrace_749519
  have hstable : (prefixWord ++ tailWord_749519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749519).length < 2 ^ (prefixWord ++ tailWord_749519).sum := by decide
  have hdescent : baseEnd_749519 < baseStart_749519 := by decide
  rcases family_descends (prefixWord ++ tailWord_749519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749543 : List Nat := [1, 1, 5, 2, 3, 1, 3, 1, 2, 1, 3]
def baseStart_749543 : Nat := 118140960795 + 749543 * 2 ^ 59
def prefixEnd_749543 : Nat := 4983230072969 + 3 ^ 40 * 749543 * 2
def baseEnd_749543 : Nat := 384875830213066143265421

theorem tailTrace_749543 : CollatzResearch.WordTrace tailWord_749543 prefixEnd_749543 384875830213066143265421 := by
  unfold tailWord_749543
  simp only [CollatzResearch.WordTrace]
  refine ⟨27338079123541197597973283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18225386082360798398648855 27338079123541197597973283)
  ·
    refine ⟨41007118685311796396959925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27338079123541197597973283 41007118685311796396959925)
    ·
      refine ⟨3844417376747980912214993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41007118685311796396959925 3844417376747980912214993)
      ·
        refine ⟨2883313032560985684161245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3844417376747980912214993 2883313032560985684161245)
        ·
          refine ⟨1081242387210369631560467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2883313032560985684161245 1081242387210369631560467)
          ·
            refine ⟨1621863580815554447340701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081242387210369631560467 1621863580815554447340701)
            ·
              refine ⟨608198842805832917752763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1621863580815554447340701 608198842805832917752763)
              ·
                refine ⟨912298264208749376629145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608198842805832917752763 912298264208749376629145)
                ·
                  refine ⟨684223698156562032471859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 912298264208749376629145 684223698156562032471859)
                  ·
                    refine ⟨1026335547234843048707789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 684223698156562032471859 1026335547234843048707789)
                    ·
                      refine ⟨384875830213066143265421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1026335547234843048707789 384875830213066143265421)
                      ·
                        rfl

theorem cell23_749543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_749543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749543 prefixEnd_749543 := by exact prefixLift 749543
  have htrace : WordTrace (prefixWord ++ tailWord_749543) baseStart_749543 baseEnd_749543 := by
    simpa [prefixWord, tailWord_749543, baseEnd_749543] using wordTrace_append hprefix tailTrace_749543
  have hstable : (prefixWord ++ tailWord_749543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749543).length < 2 ^ (prefixWord ++ tailWord_749543).sum := by decide
  have hdescent : baseEnd_749543 < baseStart_749543 := by decide
  rcases family_descends (prefixWord ++ tailWord_749543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749589 : List Nat := [1, 3, 2, 1, 5, 2, 1, 1, 7]
def baseStart_749589 : Nat := 118140960795 + 749589 * 2 ^ 59
def prefixEnd_749589 : Nat := 4983230072969 + 3 ^ 40 * 749589 * 2
def baseEnd_749589 : Nat := 42766605591463662587801

theorem tailTrace_749589 : CollatzResearch.WordTrace tailWord_749589 prefixEnd_749589 42766605591463662587801 := by
  unfold tailWord_749589
  simp only [CollatzResearch.WordTrace]
  refine ⟨27339756881374547454147821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18226504587583031636098547 27339756881374547454147821)
  ·
    refine ⟨10252408830515455295305433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27339756881374547454147821 10252408830515455295305433)
    ·
      refine ⟨7689306622886591471479075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10252408830515455295305433 7689306622886591471479075)
      ·
        refine ⟨11533959934329887207218613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7689306622886591471479075 11533959934329887207218613)
        ·
          refine ⟨1081308743843426925676745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11533959934329887207218613 1081308743843426925676745)
          ·
            refine ⟨810981557882570194257559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1081308743843426925676745 810981557882570194257559)
            ·
              refine ⟨1216472336823855291386339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810981557882570194257559 1216472336823855291386339)
              ·
                refine ⟨1824708505235782937079509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1216472336823855291386339 1824708505235782937079509)
                ·
                  refine ⟨42766605591463662587801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1824708505235782937079509 42766605591463662587801)
                  ·
                    rfl

theorem cell23_749589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 7].length) (baseStart_749589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749589 prefixEnd_749589 := by exact prefixLift 749589
  have htrace : WordTrace (prefixWord ++ tailWord_749589) baseStart_749589 baseEnd_749589 := by
    simpa [prefixWord, tailWord_749589, baseEnd_749589] using wordTrace_append hprefix tailTrace_749589
  have hstable : (prefixWord ++ tailWord_749589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749589).length < 2 ^ (prefixWord ++ tailWord_749589).sum := by decide
  have hdescent : baseEnd_749589 < baseStart_749589 := by decide
  rcases family_descends (prefixWord ++ tailWord_749589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749602 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_749602 : Nat := 118140960795 + 749602 * 2 ^ 59
def prefixEnd_749602 : Nat := 4983230072969 + 3 ^ 40 * 749602 * 2
def baseEnd_749602 : Nat := 128302041857227137475883

theorem tailTrace_749602 : CollatzResearch.WordTrace tailWord_749602 prefixEnd_749602 128302041857227137475883 := by
  unfold tailWord_749602
  simp only [CollatzResearch.WordTrace]
  refine ⟨6835057757581862668592765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18226820686884967116247373 6835057757581862668592765)
  ·
    refine ⟨2563146659093198500722287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6835057757581862668592765 2563146659093198500722287)
    ·
      refine ⟨3844719988639797751083431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2563146659093198500722287 3844719988639797751083431)
      ·
        refine ⟨5767079982959696626625147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3844719988639797751083431 5767079982959696626625147)
        ·
          refine ⟨8650619974439544939937721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5767079982959696626625147 8650619974439544939937721)
          ·
            refine ⟨6487964980829658704953291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8650619974439544939937721 6487964980829658704953291)
            ·
              refine ⟨9731947471244488057429937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6487964980829658704953291 9731947471244488057429937)
              ·
                refine ⟨7298960603433366043072453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9731947471244488057429937 7298960603433366043072453)
                ·
                  refine ⟨1368555113143756133076085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7298960603433366043072453 1368555113143756133076085)
                  ·
                    refine ⟨128302041857227137475883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1368555113143756133076085 128302041857227137475883)
                    ·
                      rfl

theorem cell23_749602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_749602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749602 prefixEnd_749602 := by exact prefixLift 749602
  have htrace : WordTrace (prefixWord ++ tailWord_749602) baseStart_749602 baseEnd_749602 := by
    simpa [prefixWord, tailWord_749602, baseEnd_749602] using wordTrace_append hprefix tailTrace_749602
  have hstable : (prefixWord ++ tailWord_749602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749602).length < 2 ^ (prefixWord ++ tailWord_749602).sum := by decide
  have hdescent : baseEnd_749602 < baseStart_749602 := by decide
  rcases family_descends (prefixWord ++ tailWord_749602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749639 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 2, 4, 2]
def baseStart_749639 : Nat := 118140960795 + 749639 * 2 ^ 59
def prefixEnd_749639 : Nat := 4983230072969 + 3 ^ 40 * 749639 * 2
def baseEnd_749639 : Nat := 384925124355897767664979

theorem tailTrace_749639 : CollatzResearch.WordTrace tailWord_749639 prefixEnd_749639 384925124355897767664979 := by
  unfold tailWord_749639
  simp only [CollatzResearch.WordTrace]
  refine ⟨27341580531193405993467971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18227720354128937328978647 27341580531193405993467971)
  ·
    refine ⟨41012370796790108990201957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27341580531193405993467971 41012370796790108990201957)
    ·
      refine ⟨7689819524398145435662867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41012370796790108990201957 7689819524398145435662867)
      ·
        refine ⟨11534729286597218153494301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7689819524398145435662867 11534729286597218153494301)
        ·
          refine ⟨4325523482473956807560363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11534729286597218153494301 4325523482473956807560363)
          ·
            refine ⟨6488285223710935211340545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4325523482473956807560363 6488285223710935211340545)
            ·
              refine ⟨4866213917783201408505409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6488285223710935211340545 4866213917783201408505409)
              ·
                refine ⟨3649660438337401056379057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4866213917783201408505409 3649660438337401056379057)
                ·
                  refine ⟨2737245328753050792284293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3649660438337401056379057 2737245328753050792284293)
                  ·
                    refine ⟨513233499141197023553305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2737245328753050792284293 513233499141197023553305)
                    ·
                      refine ⟨384925124355897767664979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 513233499141197023553305 384925124355897767664979)
                      ·
                        rfl

theorem cell23_749639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_749639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749639 prefixEnd_749639 := by exact prefixLift 749639
  have htrace : WordTrace (prefixWord ++ tailWord_749639) baseStart_749639 baseEnd_749639 := by
    simpa [prefixWord, tailWord_749639, baseEnd_749639] using wordTrace_append hprefix tailTrace_749639
  have hstable : (prefixWord ++ tailWord_749639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749639).length < 2 ^ (prefixWord ++ tailWord_749639).sum := by decide
  have hdescent : baseEnd_749639 < baseStart_749639 := by decide
  rcases family_descends (prefixWord ++ tailWord_749639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749642 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 3, 4, 3]
def baseStart_749642 : Nat := 118140960795 + 749642 * 2 ^ 59
def prefixEnd_749642 : Nat := 4983230072969 + 3 ^ 40 * 749642 * 2
def baseEnd_749642 : Nat := 384926664797861255927465

theorem tailTrace_749642 : CollatzResearch.WordTrace tailWord_749642 prefixEnd_749642 384926664797861255927465 := by
  unfold tailWord_749642
  simp only [CollatzResearch.WordTrace]
  refine ⟨6835422487545634376456795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18227793300121691670551453 6835422487545634376456795)
  ·
    refine ⟨10253133731318451564685193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6835422487545634376456795 10253133731318451564685193)
    ·
      refine ⟨7689850298488838673513895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10253133731318451564685193 7689850298488838673513895)
      ·
        refine ⟨11534775447733258010270843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7689850298488838673513895 11534775447733258010270843)
        ·
          refine ⟨17302163171599887015406265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11534775447733258010270843 17302163171599887015406265)
          ·
            refine ⟨12976622378699915261554699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17302163171599887015406265 12976622378699915261554699)
            ·
              refine ⟨19464933568049872892332049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12976622378699915261554699 19464933568049872892332049)
              ·
                refine ⟨14598700176037404669249037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19464933568049872892332049 14598700176037404669249037)
                ·
                  refine ⟨5474512566014026750968389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14598700176037404669249037 5474512566014026750968389)
                  ·
                    refine ⟨1026471106127630015806573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5474512566014026750968389 1026471106127630015806573)
                    ·
                      refine ⟨384926664797861255927465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1026471106127630015806573 384926664797861255927465)
                      ·
                        rfl

theorem cell23_749642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_749642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749642 prefixEnd_749642 := by exact prefixLift 749642
  have htrace : WordTrace (prefixWord ++ tailWord_749642) baseStart_749642 baseEnd_749642 := by
    simpa [prefixWord, tailWord_749642, baseEnd_749642] using wordTrace_append hprefix tailTrace_749642
  have hstable : (prefixWord ++ tailWord_749642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749642).length < 2 ^ (prefixWord ++ tailWord_749642).sum := by decide
  have hdescent : baseEnd_749642 < baseStart_749642 := by decide
  rcases family_descends (prefixWord ++ tailWord_749642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749652 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_749652 : Nat := 118140960795 + 749652 * 2 ^ 59
def prefixEnd_749652 : Nat := 4983230072969 + 3 ^ 40 * 749652 * 2
def baseEnd_749652 : Nat := 384931799604406216802419

theorem tailTrace_749652 : CollatzResearch.WordTrace tailWord_749652 prefixEnd_749652 384931799604406216802419 := by
  unfold tailWord_749652
  simp only [CollatzResearch.WordTrace]
  refine ⟨13671027340073154606845605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18228036453430872809127473 13671027340073154606845605)
  ·
    refine ⟨2563317626263716488783551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13671027340073154606845605 2563317626263716488783551)
    ·
      refine ⟨3844976439395574733175327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2563317626263716488783551 3844976439395574733175327)
      ·
        refine ⟨5767464659093362099762991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3844976439395574733175327 5767464659093362099762991)
        ·
          refine ⟨8651196988640043149644487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5767464659093362099762991 8651196988640043149644487)
          ·
            refine ⟨12976795482960064724466731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8651196988640043149644487 12976795482960064724466731)
            ·
              refine ⟨19465193224440097086700097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12976795482960064724466731 19465193224440097086700097)
              ·
                refine ⟨14598894918330072815025073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19465193224440097086700097 14598894918330072815025073)
                ·
                  refine ⟨10949171188747554611268805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14598894918330072815025073 10949171188747554611268805)
                  ·
                    refine ⟨2052969597890166489612901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10949171188747554611268805 2052969597890166489612901)
                    ·
                      refine ⟨384931799604406216802419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2052969597890166489612901 384931799604406216802419)
                      ·
                        rfl

theorem cell23_749652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_749652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749652 prefixEnd_749652 := by exact prefixLift 749652
  have htrace : WordTrace (prefixWord ++ tailWord_749652) baseStart_749652 baseEnd_749652 := by
    simpa [prefixWord, tailWord_749652, baseEnd_749652] using wordTrace_append hprefix tailTrace_749652
  have hstable : (prefixWord ++ tailWord_749652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749652).length < 2 ^ (prefixWord ++ tailWord_749652).sum := by decide
  have hdescent : baseEnd_749652 < baseStart_749652 := by decide
  rcases family_descends (prefixWord ++ tailWord_749652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749676 : List Nat := [2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 3]
def baseStart_749676 : Nat := 118140960795 + 749676 * 2 ^ 59
def prefixEnd_749676 : Nat := 4983230072969 + 3 ^ 40 * 749676 * 2
def baseEnd_749676 : Nat := 384944123140114122902309

theorem tailTrace_749676 : CollatzResearch.WordTrace tailWord_749676 prefixEnd_749676 384944123140114122902309 := by
  unfold tailWord_749676
  simp only [CollatzResearch.WordTrace]
  refine ⟨13671465016029680656282441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18228620021372907541709921 13671465016029680656282441)
  ·
    refine ⟨10253598762022260492211831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13671465016029680656282441 10253598762022260492211831)
    ·
      refine ⟨15380398143033390738317747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10253598762022260492211831 15380398143033390738317747)
      ·
        refine ⟨23070597214550086107476621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15380398143033390738317747 23070597214550086107476621)
        ·
          refine ⟨8651473955456282290303733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23070597214550086107476621 8651473955456282290303733)
          ·
            refine ⟨811075683324026464715975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8651473955456282290303733 811075683324026464715975)
            ·
              refine ⟨1216613524986039697073963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 811075683324026464715975 1216613524986039697073963)
              ·
                refine ⟨1824920287479059545610945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1216613524986039697073963 1824920287479059545610945)
                ·
                  refine ⟨1368690215609294659208209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1824920287479059545610945 1368690215609294659208209)
                  ·
                    refine ⟨1026517661706970994406157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1368690215609294659208209 1026517661706970994406157)
                    ·
                      refine ⟨384944123140114122902309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1026517661706970994406157 384944123140114122902309)
                      ·
                        rfl

theorem cell23_749676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 3].length) (baseStart_749676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749676 prefixEnd_749676 := by exact prefixLift 749676
  have htrace : WordTrace (prefixWord ++ tailWord_749676) baseStart_749676 baseEnd_749676 := by
    simpa [prefixWord, tailWord_749676, baseEnd_749676] using wordTrace_append hprefix tailTrace_749676
  have hstable : (prefixWord ++ tailWord_749676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749676).length < 2 ^ (prefixWord ++ tailWord_749676).sum := by decide
  have hdescent : baseEnd_749676 < baseStart_749676 := by decide
  rcases family_descends (prefixWord ++ tailWord_749676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749706 : List Nat := [3, 1, 2, 3, 1, 2, 1, 3, 3, 1, 3]
def baseStart_749706 : Nat := 118140960795 + 749706 * 2 ^ 59
def prefixEnd_749706 : Nat := 4983230072969 + 3 ^ 40 * 749706 * 2
def baseEnd_749706 : Nat := 384959527559749005527171

theorem tailTrace_749706 : CollatzResearch.WordTrace tailWord_749706 prefixEnd_749706 384959527559749005527171 := by
  unfold tailWord_749706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6836006055487669109039243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18229349481300450957437981 6836006055487669109039243)
  ·
    refine ⟨10254009083231503663558865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6836006055487669109039243 10254009083231503663558865)
    ·
      refine ⟨7690506812423627747669149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10254009083231503663558865 7690506812423627747669149)
      ·
        refine ⟨2883940054658860405375931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7690506812423627747669149 2883940054658860405375931)
        ·
          refine ⟨4325910081988290608063897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2883940054658860405375931 4325910081988290608063897)
          ·
            refine ⟨3244432561491217956047923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4325910081988290608063897 3244432561491217956047923)
            ·
              refine ⟨4866648842236826934071885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3244432561491217956047923 4866648842236826934071885)
              ·
                refine ⟨1824993315838810100276957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4866648842236826934071885 1824993315838810100276957)
                ·
                  refine ⟨684372493439553787603859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1824993315838810100276957 684372493439553787603859)
                  ·
                    refine ⟨1026558740159330681405789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 684372493439553787603859 1026558740159330681405789)
                    ·
                      refine ⟨384959527559749005527171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1026558740159330681405789 384959527559749005527171)
                      ·
                        rfl

theorem cell23_749706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_749706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749706 prefixEnd_749706 := by exact prefixLift 749706
  have htrace : WordTrace (prefixWord ++ tailWord_749706) baseStart_749706 baseEnd_749706 := by
    simpa [prefixWord, tailWord_749706, baseEnd_749706] using wordTrace_append hprefix tailTrace_749706
  have hstable : (prefixWord ++ tailWord_749706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749706).length < 2 ^ (prefixWord ++ tailWord_749706).sum := by decide
  have hdescent : baseEnd_749706 < baseStart_749706 := by decide
  rcases family_descends (prefixWord ++ tailWord_749706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749876 : List Nat := [2, 5, 1, 1, 1, 2, 1, 3, 7]
def baseStart_749876 : Nat := 118140960795 + 749876 * 2 ^ 59
def prefixEnd_749876 : Nat := 4983230072969 + 3 ^ 40 * 749876 * 2
def baseEnd_749876 : Nat := 42782979919001482266821

theorem tailTrace_749876 : CollatzResearch.WordTrace tailWord_749876 prefixEnd_749876 42782979919001482266821 := by
  unfold tailWord_749876
  simp only [CollatzResearch.WordTrace]
  refine ⟨13675112315667397734922741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18233483087556530313230321 13675112315667397734922741)
  ·
    refine ⟨1282041779593818537649007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13675112315667397734922741 1282041779593818537649007)
    ·
      refine ⟨1923062669390727806473511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1282041779593818537649007 1923062669390727806473511)
      ·
        refine ⟨2884594004086091709710267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1923062669390727806473511 2884594004086091709710267)
        ·
          refine ⟨4326891006129137564565401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2884594004086091709710267 4326891006129137564565401)
          ·
            refine ⟨3245168254596853173424051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4326891006129137564565401 3245168254596853173424051)
            ·
              refine ⟨4867752381895279760136077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3245168254596853173424051 4867752381895279760136077)
              ·
                refine ⟨1825407143210729910051029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4867752381895279760136077 1825407143210729910051029)
                ·
                  refine ⟨42782979919001482266821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1825407143210729910051029 42782979919001482266821)
                  ·
                    rfl

theorem cell23_749876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_749876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749876 prefixEnd_749876 := by exact prefixLift 749876
  have htrace : WordTrace (prefixWord ++ tailWord_749876) baseStart_749876 baseEnd_749876 := by
    simpa [prefixWord, tailWord_749876, baseEnd_749876] using wordTrace_append hprefix tailTrace_749876
  have hstable : (prefixWord ++ tailWord_749876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749876).length < 2 ^ (prefixWord ++ tailWord_749876).sum := by decide
  have hdescent : baseEnd_749876 < baseStart_749876 := by decide
  rcases family_descends (prefixWord ++ tailWord_749876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749896 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 2, 5, 2]
def baseStart_749896 : Nat := 118140960795 + 749896 * 2 ^ 59
def prefixEnd_749896 : Nat := 4983230072969 + 3 ^ 40 * 749896 * 2
def baseEnd_749896 : Nat := 385057088884103262151297

theorem tailTrace_749896 : CollatzResearch.WordTrace tailWord_749896 prefixEnd_749896 385057088884103262151297 := by
  unfold tailWord_749896
  simp only [CollatzResearch.WordTrace]
  refine ⟨13675477045631169442786771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18233969394174892590382361 13675477045631169442786771)
  ·
    refine ⟨20513215568446754164180157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13675477045631169442786771 20513215568446754164180157)
    ·
      refine ⟨7692455838167532811567559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20513215568446754164180157 7692455838167532811567559)
      ·
        refine ⟨11538683757251299217351339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7692455838167532811567559 11538683757251299217351339)
        ·
          refine ⟨17308025635876948826027009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11538683757251299217351339 17308025635876948826027009)
          ·
            refine ⟨12981019226907711619520257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17308025635876948826027009 12981019226907711619520257)
            ·
              refine ⟨9735764420180783714640193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12981019226907711619520257 9735764420180783714640193)
              ·
                refine ⟨7301823315135587785980145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9735764420180783714640193 7301823315135587785980145)
                ·
                  refine ⟨5476367486351690839485109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7301823315135587785980145 5476367486351690839485109)
                  ·
                    refine ⟨513409451845471016201729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5476367486351690839485109 513409451845471016201729)
                    ·
                      refine ⟨385057088884103262151297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 513409451845471016201729 385057088884103262151297)
                      ·
                        rfl

theorem cell23_749896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_749896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749896 prefixEnd_749896 := by exact prefixLift 749896
  have htrace : WordTrace (prefixWord ++ tailWord_749896) baseStart_749896 baseEnd_749896 := by
    simpa [prefixWord, tailWord_749896, baseEnd_749896] using wordTrace_append hprefix tailTrace_749896
  have hstable : (prefixWord ++ tailWord_749896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749896).length < 2 ^ (prefixWord ++ tailWord_749896).sum := by decide
  have hdescent : baseEnd_749896 < baseStart_749896 := by decide
  rcases family_descends (prefixWord ++ tailWord_749896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749963 : List Nat := [1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 3]
def baseStart_749963 : Nat := 118140960795 + 749963 * 2 ^ 59
def prefixEnd_749963 : Nat := 4983230072969 + 3 ^ 40 * 749963 * 2
def baseEnd_749963 : Nat := 385091492087954500013489

theorem tailTrace_749963 : CollatzResearch.WordTrace tailWord_749963 prefixEnd_749963 385091492087954500013489 := by
  unfold tailWord_749963
  simp only [CollatzResearch.WordTrace]
  refine ⟨27353397782019609328262543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18235598521346406218841695 27353397782019609328262543)
  ·
    refine ⟨41030096673029413992393815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27353397782019609328262543 41030096673029413992393815)
    ·
      refine ⟨61545145009544120988590723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41030096673029413992393815 61545145009544120988590723)
      ·
        refine ⟨92317717514316181482886085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61545145009544120988590723 92317717514316181482886085)
        ·
          refine ⟨17309572033934284028041141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92317717514316181482886085 17309572033934284028041141)
          ·
            refine ⟨1622772378181339127628857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17309572033934284028041141 1622772378181339127628857)
            ·
              refine ⟨1217079283636004345721643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1622772378181339127628857 1217079283636004345721643)
              ·
                refine ⟨1825618925454006518582465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1217079283636004345721643 1825618925454006518582465)
                ·
                  refine ⟨1369214194090504888936849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1825618925454006518582465 1369214194090504888936849)
                  ·
                    refine ⟨1026910645567878666702637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1369214194090504888936849 1026910645567878666702637)
                    ·
                      refine ⟨385091492087954500013489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1026910645567878666702637 385091492087954500013489)
                      ·
                        rfl

theorem cell23_749963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 3].length) (baseStart_749963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749963 prefixEnd_749963 := by exact prefixLift 749963
  have htrace : WordTrace (prefixWord ++ tailWord_749963) baseStart_749963 baseEnd_749963 := by
    simpa [prefixWord, tailWord_749963, baseEnd_749963] using wordTrace_append hprefix tailTrace_749963
  have hstable : (prefixWord ++ tailWord_749963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749963).length < 2 ^ (prefixWord ++ tailWord_749963).sum := by decide
  have hdescent : baseEnd_749963 < baseStart_749963 := by decide
  rcases family_descends (prefixWord ++ tailWord_749963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749986 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_749986 : Nat := 118140960795 + 749986 * 2 ^ 59
def prefixEnd_749986 : Nat := 4983230072969 + 3 ^ 40 * 749986 * 2
def baseEnd_749986 : Nat := 385103302143007910025883

theorem tailTrace_749986 : CollatzResearch.WordTrace tailWord_749986 prefixEnd_749986 385103302143007910025883 := by
  unfold tailWord_749986
  simp only [CollatzResearch.WordTrace]
  refine ⟨6838559165234071064087453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18236157773957522837566541 6838559165234071064087453)
  ·
    refine ⟨2564459686962776649032795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6838559165234071064087453 2564459686962776649032795)
    ·
      refine ⟨3846689530444164973549193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2564459686962776649032795 3846689530444164973549193)
      ·
        refine ⟨2885017147833123730161895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3846689530444164973549193 2885017147833123730161895)
        ·
          refine ⟨4327525721749685595242843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2885017147833123730161895 4327525721749685595242843)
          ·
            refine ⟨6491288582624528392864265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4327525721749685595242843 6491288582624528392864265)
            ·
              refine ⟨4868466436968396294648199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6491288582624528392864265 4868466436968396294648199)
              ·
                refine ⟨7302699655452594441972299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4868466436968396294648199 7302699655452594441972299)
                ·
                  refine ⟨10954049483178891662958449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7302699655452594441972299 10954049483178891662958449)
                  ·
                    refine ⟨8215537112384168747218837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10954049483178891662958449 8215537112384168747218837)
                    ·
                      refine ⟨385103302143007910025883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8215537112384168747218837 385103302143007910025883)
                      ·
                        rfl

theorem cell23_749986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_749986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749986 prefixEnd_749986 := by exact prefixLift 749986
  have htrace : WordTrace (prefixWord ++ tailWord_749986) baseStart_749986 baseEnd_749986 := by
    simpa [prefixWord, tailWord_749986, baseEnd_749986] using wordTrace_append hprefix tailTrace_749986
  have hstable : (prefixWord ++ tailWord_749986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749986).length < 2 ^ (prefixWord ++ tailWord_749986).sum := by decide
  have hdescent : baseEnd_749986 < baseStart_749986 := by decide
  rcases family_descends (prefixWord ++ tailWord_749986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749987 : List Nat := [1, 1, 1, 4, 1, 6, 2, 2, 1, 4]
def baseStart_749987 : Nat := 118140960795 + 749987 * 2 ^ 59
def prefixEnd_749987 : Nat := 4983230072969 + 3 ^ 40 * 749987 * 2
def baseEnd_749987 : Nat := 128367938541220802037793

theorem tailTrace_749987 : CollatzResearch.WordTrace tailWord_749987 prefixEnd_749987 128367938541220802037793 := by
  unfold tailWord_749987
  simp only [CollatzResearch.WordTrace]
  refine ⟨27354273133932661427136215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18236182089288440951424143 27354273133932661427136215)
  ·
    refine ⟨41031409700898992140704323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27354273133932661427136215 41031409700898992140704323)
    ·
      refine ⟨61547114551348488211056485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41031409700898992140704323 61547114551348488211056485)
      ·
        refine ⟨11540083978377841539573091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61547114551348488211056485 11540083978377841539573091)
        ·
          refine ⟨17310125967566762309359637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11540083978377841539573091 17310125967566762309359637)
          ·
            refine ⟨811412154729691983251233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17310125967566762309359637 811412154729691983251233)
            ·
              refine ⟨608559116047268987438425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 811412154729691983251233 608559116047268987438425)
              ·
                refine ⟨456419337035451740578819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 608559116047268987438425 456419337035451740578819)
                ·
                  refine ⟨684629005553177610868229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456419337035451740578819 684629005553177610868229)
                  ·
                    refine ⟨128367938541220802037793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 684629005553177610868229 128367938541220802037793)
                    ·
                      rfl

theorem cell23_749987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 1, 4].length) (baseStart_749987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749987 prefixEnd_749987 := by exact prefixLift 749987
  have htrace : WordTrace (prefixWord ++ tailWord_749987) baseStart_749987 baseEnd_749987 := by
    simpa [prefixWord, tailWord_749987, baseEnd_749987] using wordTrace_append hprefix tailTrace_749987
  have hstable : (prefixWord ++ tailWord_749987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749987).length < 2 ^ (prefixWord ++ tailWord_749987).sum := by decide
  have hdescent : baseEnd_749987 < baseStart_749987 := by decide
  rcases family_descends (prefixWord ++ tailWord_749987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749994 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_749994 : Nat := 118140960795 + 749994 * 2 ^ 59
def prefixEnd_749994 : Nat := 4983230072969 + 3 ^ 40 * 749994 * 2
def baseEnd_749994 : Nat := 385107409988243878725847

theorem tailTrace_749994 : CollatzResearch.WordTrace tailWord_749994 prefixEnd_749994 385107409988243878725847 := by
  unfold tailWord_749994
  simp only [CollatzResearch.WordTrace]
  refine ⟨6838632111226825405660259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18236352296604867748427357 6838632111226825405660259)
  ·
    refine ⟨10257948166840238108490389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6838632111226825405660259 10257948166840238108490389)
    ·
      refine ⟨480841320320636161335487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10257948166840238108490389 480841320320636161335487)
      ·
        refine ⟨721261980480954242003231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480841320320636161335487 721261980480954242003231)
        ·
          refine ⟨1081892970721431363004847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721261980480954242003231 1081892970721431363004847)
          ·
            refine ⟨1622839456082147044507271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081892970721431363004847 1622839456082147044507271)
            ·
              refine ⟨2434259184123220566760907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1622839456082147044507271 2434259184123220566760907)
              ·
                refine ⟨3651388776184830850141361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2434259184123220566760907 3651388776184830850141361)
                ·
                  refine ⟨2738541582138623137606021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3651388776184830850141361 2738541582138623137606021)
                  ·
                    refine ⟨513476546650991838301129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2738541582138623137606021 513476546650991838301129)
                    ·
                      refine ⟨385107409988243878725847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 513476546650991838301129 385107409988243878725847)
                      ·
                        rfl

theorem cell23_749994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_749994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_749994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_749994 prefixEnd_749994 := by exact prefixLift 749994
  have htrace : WordTrace (prefixWord ++ tailWord_749994) baseStart_749994 baseEnd_749994 := by
    simpa [prefixWord, tailWord_749994, baseEnd_749994] using wordTrace_append hprefix tailTrace_749994
  have hstable : (prefixWord ++ tailWord_749994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749994).length < 2 ^ (prefixWord ++ tailWord_749994).sum := by decide
  have hdescent : baseEnd_749994 < baseStart_749994 := by decide
  rcases family_descends (prefixWord ++ tailWord_749994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750026 : List Nat := [3, 1, 2, 1, 2, 2, 1, 4, 1, 6]
def baseStart_750026 : Nat := 118140960795 + 750026 * 2 ^ 59
def prefixEnd_750026 : Nat := 4983230072969 + 3 ^ 40 * 750026 * 2
def baseEnd_750026 : Nat := 128374613789729251175233

theorem tailTrace_750026 : CollatzResearch.WordTrace tailWord_750026 prefixEnd_750026 128374613789729251175233 := by
  unfold tailWord_750026
  simp only [CollatzResearch.WordTrace]
  refine ⟨6838923895197842771951483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18237130387194247391870621 6838923895197842771951483)
  ·
    refine ⟨10258385842796764157927225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6838923895197842771951483 10258385842796764157927225)
    ·
      refine ⟨7693789382097573118445419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10258385842796764157927225 7693789382097573118445419)
      ·
        refine ⟨11540684073146359677668129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7693789382097573118445419 11540684073146359677668129)
        ·
          refine ⟨8655513054859769758251097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11540684073146359677668129 8655513054859769758251097)
          ·
            refine ⟨6491634791144827318688323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8655513054859769758251097 6491634791144827318688323)
            ·
              refine ⟨9737452186717240978032485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6491634791144827318688323 9737452186717240978032485)
              ·
                refine ⟨1825772285009482683381091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9737452186717240978032485 1825772285009482683381091)
                ·
                  refine ⟨2738658427514224025071637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1825772285009482683381091 2738658427514224025071637)
                  ·
                    refine ⟨128374613789729251175233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2738658427514224025071637 128374613789729251175233)
                    ·
                      rfl

theorem cell23_750026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_750026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750026 prefixEnd_750026 := by exact prefixLift 750026
  have htrace : WordTrace (prefixWord ++ tailWord_750026) baseStart_750026 baseEnd_750026 := by
    simpa [prefixWord, tailWord_750026, baseEnd_750026] using wordTrace_append hprefix tailTrace_750026
  have hstable : (prefixWord ++ tailWord_750026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750026).length < 2 ^ (prefixWord ++ tailWord_750026).sum := by decide
  have hdescent : baseEnd_750026 < baseStart_750026 := by decide
  rcases family_descends (prefixWord ++ tailWord_750026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750060 : List Nat := [2, 2, 1, 1, 2, 1, 7, 1, 2, 4]
def baseStart_750060 : Nat := 118140960795 + 750060 * 2 ^ 59
def prefixEnd_750060 : Nat := 4983230072969 + 3 ^ 40 * 750060 * 2
def baseEnd_750060 : Nat := 128380433237146873500181

theorem tailTrace_750060 : CollatzResearch.WordTrace tailWord_750060 prefixEnd_750060 128380433237146873500181 := by
  unfold tailWord_750060
  simp only [CollatzResearch.WordTrace]
  refine ⟨13678467831334097447271817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18237957108445463263029089 13678467831334097447271817)
  ·
    refine ⟨10258850873500573085453863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13678467831334097447271817 10258850873500573085453863)
    ·
      refine ⟨15388276310250859628180795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10258850873500573085453863 15388276310250859628180795)
      ·
        refine ⟨23082414465376289442271193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15388276310250859628180795 23082414465376289442271193)
        ·
          refine ⟨17311810849032217081703395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23082414465376289442271193 17311810849032217081703395)
          ·
            refine ⟨25967716273548325622555093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17311810849032217081703395 25967716273548325622555093)
            ·
              refine ⟨608618350161288881778635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 25967716273548325622555093 608618350161288881778635)
              ·
                refine ⟨912927525241933322667953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608618350161288881778635 912927525241933322667953)
                ·
                  refine ⟨684695643931449992000965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 912927525241933322667953 684695643931449992000965)
                  ·
                    refine ⟨128380433237146873500181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 684695643931449992000965 128380433237146873500181)
                    ·
                      rfl

theorem cell23_750060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 4].length) (baseStart_750060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750060 prefixEnd_750060 := by exact prefixLift 750060
  have htrace : WordTrace (prefixWord ++ tailWord_750060) baseStart_750060 baseEnd_750060 := by
    simpa [prefixWord, tailWord_750060, baseEnd_750060] using wordTrace_append hprefix tailTrace_750060
  have hstable : (prefixWord ++ tailWord_750060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750060).length < 2 ^ (prefixWord ++ tailWord_750060).sum := by decide
  have hdescent : baseEnd_750060 < baseStart_750060 := by decide
  rcases family_descends (prefixWord ++ tailWord_750060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750083 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 6, 1, 3]
def baseStart_750083 : Nat := 118140960795 + 750083 * 2 ^ 59
def prefixEnd_750083 : Nat := 4983230072969 + 3 ^ 40 * 750083 * 2
def baseEnd_750083 : Nat := 385153109766494030512937

theorem tailTrace_750083 : CollatzResearch.WordTrace tailWord_750083 prefixEnd_750083 385153109766494030512937 := by
  unfold tailWord_750083
  simp only [CollatzResearch.WordTrace]
  refine ⟨27357774541584869822630903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18238516361056579881753935 27357774541584869822630903)
  ·
    refine ⟨41036661812377304733946355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27357774541584869822630903 41036661812377304733946355)
    ·
      refine ⟨61554992718565957100919533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41036661812377304733946355 61554992718565957100919533)
      ·
        refine ⟨23083122269462233912844825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61554992718565957100919533 23083122269462233912844825)
        ·
          refine ⟨17312341702096675434633619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23083122269462233912844825 17312341702096675434633619)
          ·
            refine ⟨25968512553145013151950429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17312341702096675434633619 25968512553145013151950429)
            ·
              refine ⟨9738192207429379931981411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25968512553145013151950429 9738192207429379931981411)
              ·
                refine ⟨14607288311144069897972117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9738192207429379931981411 14607288311144069897972117)
                ·
                  refine ⟨684716639584878276467443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14607288311144069897972117 684716639584878276467443)
                  ·
                    refine ⟨1027074959377317414701165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 684716639584878276467443 1027074959377317414701165)
                    ·
                      refine ⟨385153109766494030512937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1027074959377317414701165 385153109766494030512937)
                      ·
                        rfl

theorem cell23_750083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 1, 3].length) (baseStart_750083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750083 prefixEnd_750083 := by exact prefixLift 750083
  have htrace : WordTrace (prefixWord ++ tailWord_750083) baseStart_750083 baseEnd_750083 := by
    simpa [prefixWord, tailWord_750083, baseEnd_750083] using wordTrace_append hprefix tailTrace_750083
  have hstable : (prefixWord ++ tailWord_750083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750083).length < 2 ^ (prefixWord ++ tailWord_750083).sum := by decide
  have hdescent : baseEnd_750083 < baseStart_750083 := by decide
  rcases family_descends (prefixWord ++ tailWord_750083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750117 : List Nat := [1, 3, 1, 2, 2, 1, 6, 1, 2, 1, 3]
def baseStart_750117 : Nat := 118140960795 + 750117 * 2 ^ 59
def prefixEnd_750117 : Nat := 4983230072969 + 3 ^ 40 * 750117 * 2
def baseEnd_750117 : Nat := 385170568108746897487781

theorem tailTrace_750117 : CollatzResearch.WordTrace tailWord_750117 prefixEnd_750117 385170568108746897487781 := by
  unfold tailWord_750117
  simp only [CollatzResearch.WordTrace]
  refine ⟨27359014623461693629368605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18239343082307795752912403 27359014623461693629368605)
  ·
    refine ⟨10259630483798135111013227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27359014623461693629368605 10259630483798135111013227)
    ·
      refine ⟨15389445725697202666519841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10259630483798135111013227 15389445725697202666519841)
      ·
        refine ⟨11542084294272901999889881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15389445725697202666519841 11542084294272901999889881)
        ·
          refine ⟨8656563220704676499917411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11542084294272901999889881 8656563220704676499917411)
          ·
            refine ⟨12984844831057014749876117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8656563220704676499917411 12984844831057014749876117)
            ·
              refine ⟨608664601455797566400443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12984844831057014749876117 608664601455797566400443)
              ·
                refine ⟨912996902183696349600665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608664601455797566400443 912996902183696349600665)
                ·
                  refine ⟨684747676637772262200499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 912996902183696349600665 684747676637772262200499)
                  ·
                    refine ⟨1027121514956658393300749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 684747676637772262200499 1027121514956658393300749)
                    ·
                      refine ⟨385170568108746897487781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1027121514956658393300749 385170568108746897487781)
                      ·
                        rfl

theorem cell23_750117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_750117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750117 prefixEnd_750117 := by exact prefixLift 750117
  have htrace : WordTrace (prefixWord ++ tailWord_750117) baseStart_750117 baseEnd_750117 := by
    simpa [prefixWord, tailWord_750117, baseEnd_750117] using wordTrace_append hprefix tailTrace_750117
  have hstable : (prefixWord ++ tailWord_750117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750117).length < 2 ^ (prefixWord ++ tailWord_750117).sum := by decide
  have hdescent : baseEnd_750117 < baseStart_750117 := by decide
  rcases family_descends (prefixWord ++ tailWord_750117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750123 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 5, 4, 2]
def baseStart_750123 : Nat := 118140960795 + 750123 * 2 ^ 59
def prefixEnd_750123 : Nat := 4983230072969 + 3 ^ 40 * 750123 * 2
def baseEnd_750123 : Nat := 385173648992673874012753

theorem tailTrace_750123 : CollatzResearch.WordTrace tailWord_750123 prefixEnd_750123 385173648992673874012753 := by
  unfold tailWord_750123
  simp only [CollatzResearch.WordTrace]
  refine ⟨27359233461439956654087023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18239488974293304436058015 27359233461439956654087023)
  ·
    refine ⟨41038850192159934981130535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27359233461439956654087023 41038850192159934981130535)
    ·
      refine ⟨61558275288239902471695803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41038850192159934981130535 61558275288239902471695803)
      ·
        refine ⟨92337412932359853707543705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61558275288239902471695803 92337412932359853707543705)
        ·
          refine ⟨69253059699269890280657779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92337412932359853707543705 69253059699269890280657779)
          ·
            refine ⟨103879589548904835420986669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69253059699269890280657779 103879589548904835420986669)
            ·
              refine ⟨38954846080839313282870001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103879589548904835420986669 38954846080839313282870001)
              ·
                refine ⟨29216134560629484962152501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38954846080839313282870001 29216134560629484962152501)
                ·
                  refine ⟨2739012615059014215201797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29216134560629484962152501 2739012615059014215201797)
                  ·
                    refine ⟨513564865323565165350337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2739012615059014215201797 513564865323565165350337)
                    ·
                      refine ⟨385173648992673874012753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 513564865323565165350337 385173648992673874012753)
                      ·
                        rfl

theorem cell23_750123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 4, 2].length) (baseStart_750123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750123 prefixEnd_750123 := by exact prefixLift 750123
  have htrace : WordTrace (prefixWord ++ tailWord_750123) baseStart_750123 baseEnd_750123 := by
    simpa [prefixWord, tailWord_750123, baseEnd_750123] using wordTrace_append hprefix tailTrace_750123
  have hstable : (prefixWord ++ tailWord_750123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750123).length < 2 ^ (prefixWord ++ tailWord_750123).sum := by decide
  have hdescent : baseEnd_750123 < baseStart_750123 := by decide
  rcases family_descends (prefixWord ++ tailWord_750123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750140 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 3, 4, 2]
def baseStart_750140 : Nat := 118140960795 + 750140 * 2 ^ 59
def prefixEnd_750140 : Nat := 4983230072969 + 3 ^ 40 * 750140 * 2
def baseEnd_750140 : Nat := 385182378163800307500175

theorem tailTrace_750140 : CollatzResearch.WordTrace tailWord_750140 prefixEnd_750140 385182378163800307500175 := by
  unfold tailWord_750140
  simp only [CollatzResearch.WordTrace]
  refine ⟨13679926751189184278727937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18239902334918912371637249 13679926751189184278727937)
  ·
    refine ⟨10259945063391888209045953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13679926751189184278727937 10259945063391888209045953)
    ·
      refine ⟨7694958797543916156784465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10259945063391888209045953 7694958797543916156784465)
      ·
        refine ⟨5771219098157937117588349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7694958797543916156784465 5771219098157937117588349)
        ·
          refine ⟨2164207161809226419095631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5771219098157937117588349 2164207161809226419095631)
          ·
            refine ⟨3246310742713839628643447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2164207161809226419095631 3246310742713839628643447)
            ·
              refine ⟨4869466114070759442965171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3246310742713839628643447 4869466114070759442965171)
              ·
                refine ⟨7304199171106139164447757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4869466114070759442965171 7304199171106139164447757)
                ·
                  refine ⟨2739074689164802186667909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7304199171106139164447757 2739074689164802186667909)
                  ·
                    refine ⟨513576504218400410000233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2739074689164802186667909 513576504218400410000233)
                    ·
                      refine ⟨385182378163800307500175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 513576504218400410000233 385182378163800307500175)
                      ·
                        rfl

theorem cell23_750140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_750140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750140 prefixEnd_750140 := by exact prefixLift 750140
  have htrace : WordTrace (prefixWord ++ tailWord_750140) baseStart_750140 baseEnd_750140 := by
    simpa [prefixWord, tailWord_750140, baseEnd_750140] using wordTrace_append hprefix tailTrace_750140
  have hstable : (prefixWord ++ tailWord_750140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750140).length < 2 ^ (prefixWord ++ tailWord_750140).sum := by decide
  have hdescent : baseEnd_750140 < baseStart_750140 := by decide
  rcases family_descends (prefixWord ++ tailWord_750140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750223 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 7, 4]
def baseStart_750223 : Nat := 118140960795 + 750223 * 2 ^ 59
def prefixEnd_750223 : Nat := 4983230072969 + 3 ^ 40 * 750223 * 2
def baseEnd_750223 : Nat := 128408332352707827587431

theorem tailTrace_750223 : CollatzResearch.WordTrace tailWord_750223 prefixEnd_750223 128408332352707827587431 := by
  unfold tailWord_750223
  simp only [CollatzResearch.WordTrace]
  refine ⟨27362880761077673732727323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18241920507385115821818215 27362880761077673732727323)
  ·
    refine ⟨41044321141616510599090985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27362880761077673732727323 41044321141616510599090985)
    ·
      refine ⟨30783240856212382949318239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41044321141616510599090985 30783240856212382949318239)
      ·
        refine ⟨46174861284318574423977359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30783240856212382949318239 46174861284318574423977359)
        ·
          refine ⟨69262291926477861635966039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46174861284318574423977359 69262291926477861635966039)
          ·
            refine ⟨103893437889716792453949059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69262291926477861635966039 103893437889716792453949059)
            ·
              refine ⟨155840156834575188680923589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103893437889716792453949059 155840156834575188680923589)
              ·
                refine ⟨29220029406482847877673173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155840156834575188680923589 29220029406482847877673173)
                ·
                  refine ⟨684844439214441747132965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 29220029406482847877673173 684844439214441747132965)
                  ·
                    refine ⟨128408332352707827587431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 684844439214441747132965 128408332352707827587431)
                    ·
                      rfl

theorem cell23_750223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 4].length) (baseStart_750223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750223 prefixEnd_750223 := by exact prefixLift 750223
  have htrace : WordTrace (prefixWord ++ tailWord_750223) baseStart_750223 baseEnd_750223 := by
    simpa [prefixWord, tailWord_750223, baseEnd_750223] using wordTrace_append hprefix tailTrace_750223
  have hstable : (prefixWord ++ tailWord_750223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750223).length < 2 ^ (prefixWord ++ tailWord_750223).sum := by decide
  have hdescent : baseEnd_750223 < baseStart_750223 := by decide
  rcases family_descends (prefixWord ++ tailWord_750223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750233 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 3, 4, 3]
def baseStart_750233 : Nat := 118140960795 + 750233 * 2 ^ 59
def prefixEnd_750233 : Nat := 4983230072969 + 3 ^ 40 * 750233 * 2
def baseEnd_750233 : Nat := 385230131864668443637247

theorem tailTrace_750233 : CollatzResearch.WordTrace tailWord_750233 prefixEnd_750233 385230131864668443637247 := by
  unfold tailWord_750233
  simp only [CollatzResearch.WordTrace]
  refine ⟨27363245491041445440591353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18242163660694296960394235 27363245491041445440591353)
  ·
    refine ⟨20522434118281084080443515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27363245491041445440591353 20522434118281084080443515)
    ·
      refine ⟨30783651177421626120665273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20522434118281084080443515 30783651177421626120665273)
      ·
        refine ⟨23087738383066219590498955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30783651177421626120665273 23087738383066219590498955)
        ·
          refine ⟨34631607574599329385748433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23087738383066219590498955 34631607574599329385748433)
          ·
            refine ⟨25973705680949497039311325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34631607574599329385748433 25973705680949497039311325)
            ·
              refine ⟨9740139630356061389741747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25973705680949497039311325 9740139630356061389741747)
              ·
                refine ⟨14610209445534092084612621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9740139630356061389741747 14610209445534092084612621)
                ·
                  refine ⟨5478828542075284531729733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14610209445534092084612621 5478828542075284531729733)
                  ·
                    refine ⟨1027280351639115849699325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5478828542075284531729733 1027280351639115849699325)
                    ·
                      refine ⟨385230131864668443637247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1027280351639115849699325 385230131864668443637247)
                      ·
                        rfl

theorem cell23_750233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_750233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750233 prefixEnd_750233 := by exact prefixLift 750233
  have htrace : WordTrace (prefixWord ++ tailWord_750233) baseStart_750233 baseEnd_750233 := by
    simpa [prefixWord, tailWord_750233, baseEnd_750233] using wordTrace_append hprefix tailTrace_750233
  have hstable : (prefixWord ++ tailWord_750233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750233).length < 2 ^ (prefixWord ++ tailWord_750233).sum := by decide
  have hdescent : baseEnd_750233 < baseStart_750233 := by decide
  rcases family_descends (prefixWord ++ tailWord_750233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750270 : List Nat := [4, 2, 1, 1, 2, 1, 2, 4, 6]
def baseStart_750270 : Nat := 118140960795 + 750270 * 2 ^ 59
def prefixEnd_750270 : Nat := 4983230072969 + 3 ^ 40 * 750270 * 2
def baseEnd_750270 : Nat := 42805458960987199874953

theorem tailTrace_750270 : CollatzResearch.WordTrace tailWord_750270 prefixEnd_750270 42805458960987199874953 := by
  unfold tailWord_750270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3420574373988425094961033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18243063327938267173125509 3420574373988425094961033)
  ·
    refine ⟨2565430780491318821220775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3420574373988425094961033 2565430780491318821220775)
    ·
      refine ⟨3848146170736978231831163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2565430780491318821220775 3848146170736978231831163)
      ·
        refine ⟨5772219256105467347746745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3848146170736978231831163 5772219256105467347746745)
        ·
          refine ⟨4329164442079100510810059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5772219256105467347746745 4329164442079100510810059)
          ·
            refine ⟨6493746663118650766215089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4329164442079100510810059 6493746663118650766215089)
            ·
              refine ⟨4870309997338988074661317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6493746663118650766215089 4870309997338988074661317)
              ·
                refine ⟨913183124501060263998997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4870309997338988074661317 913183124501060263998997)
                ·
                  refine ⟨42805458960987199874953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 913183124501060263998997 42805458960987199874953)
                  ·
                    rfl

theorem cell23_750270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_750270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750270 prefixEnd_750270 := by exact prefixLift 750270
  have htrace : WordTrace (prefixWord ++ tailWord_750270) baseStart_750270 baseEnd_750270 := by
    simpa [prefixWord, tailWord_750270, baseEnd_750270] using wordTrace_append hprefix tailTrace_750270
  have hstable : (prefixWord ++ tailWord_750270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750270).length < 2 ^ (prefixWord ++ tailWord_750270).sum := by decide
  have hdescent : baseEnd_750270 < baseStart_750270 := by decide
  rcases family_descends (prefixWord ++ tailWord_750270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750313 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 3, 6]
def baseStart_750313 : Nat := 118140960795 + 750313 * 2 ^ 59
def prefixEnd_750313 : Nat := 4983230072969 + 3 ^ 40 * 750313 * 2
def baseEnd_750313 : Nat := 128423736772342710212293

theorem tailTrace_750313 : CollatzResearch.WordTrace tailWord_750313 prefixEnd_750313 128423736772342710212293 := by
  unfold tailWord_750313
  simp only [CollatzResearch.WordTrace]
  refine ⟨27366163330751619103503593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18244108887167746069002395 27366163330751619103503593)
  ·
    refine ⟨20524622498063714327627695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27366163330751619103503593 20524622498063714327627695)
    ·
      refine ⟨30786933747095571491441543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20524622498063714327627695 30786933747095571491441543)
      ·
        refine ⟨46180400620643357237162315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30786933747095571491441543 46180400620643357237162315)
        ·
          refine ⟨69270600930965035855743473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46180400620643357237162315 69270600930965035855743473)
          ·
            refine ⟨51952950698223776891807605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69270600930965035855743473 51952950698223776891807605)
            ·
              refine ⟨4870589127958479083606963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51952950698223776891807605 4870589127958479083606963)
              ·
                refine ⟨7305883691937718625410445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4870589127958479083606963 7305883691937718625410445)
                ·
                  refine ⟨2739706384476644484528917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7305883691937718625410445 2739706384476644484528917)
                  ·
                    refine ⟨128423736772342710212293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2739706384476644484528917 128423736772342710212293)
                    ·
                      rfl

theorem cell23_750313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 6].length) (baseStart_750313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750313 prefixEnd_750313 := by exact prefixLift 750313
  have htrace : WordTrace (prefixWord ++ tailWord_750313) baseStart_750313 baseEnd_750313 := by
    simpa [prefixWord, tailWord_750313, baseEnd_750313] using wordTrace_append hprefix tailTrace_750313
  have hstable : (prefixWord ++ tailWord_750313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750313).length < 2 ^ (prefixWord ++ tailWord_750313).sum := by decide
  have hdescent : baseEnd_750313 < baseStart_750313 := by decide
  rcases family_descends (prefixWord ++ tailWord_750313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750314 : List Nat := [3, 1, 3, 1, 1, 1, 1, 7, 1, 1, 3]
def baseStart_750314 : Nat := 118140960795 + 750314 * 2 ^ 59
def prefixEnd_750314 : Nat := 4983230072969 + 3 ^ 40 * 750314 * 2
def baseEnd_750314 : Nat := 385271723797682626724375

theorem tailTrace_750314 : CollatzResearch.WordTrace tailWord_750314 prefixEnd_750314 385271723797682626724375 := by
  unfold tailWord_750314
  simp only [CollatzResearch.WordTrace]
  refine ⟨6841549950936999068572499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18244133202498664182859997 6841549950936999068572499)
  ·
    refine ⟨10262324926405498602858749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6841549950936999068572499 10262324926405498602858749)
    ·
      refine ⟨3848371847402061976072031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10262324926405498602858749 3848371847402061976072031)
      ·
        refine ⟨5772557771103092964108047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3848371847402061976072031 5772557771103092964108047)
        ·
          refine ⟨8658836656654639446162071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5772557771103092964108047 8658836656654639446162071)
          ·
            refine ⟨12988254984981959169243107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8658836656654639446162071 12988254984981959169243107)
            ·
              refine ⟨19482382477472938753864661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12988254984981959169243107 19482382477472938753864661)
              ·
                refine ⟨456618339315772002043703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19482382477472938753864661 456618339315772002043703)
                ·
                  refine ⟨684927508973658003065555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456618339315772002043703 684927508973658003065555)
                  ·
                    refine ⟨1027391263460487004598333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 684927508973658003065555 1027391263460487004598333)
                    ·
                      refine ⟨385271723797682626724375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1027391263460487004598333 385271723797682626724375)
                      ·
                        rfl

theorem cell23_750314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_750314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750314 prefixEnd_750314 := by exact prefixLift 750314
  have htrace : WordTrace (prefixWord ++ tailWord_750314) baseStart_750314 baseEnd_750314 := by
    simpa [prefixWord, tailWord_750314, baseEnd_750314] using wordTrace_append hprefix tailTrace_750314
  have hstable : (prefixWord ++ tailWord_750314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750314).length < 2 ^ (prefixWord ++ tailWord_750314).sum := by decide
  have hdescent : baseEnd_750314 < baseStart_750314 := by decide
  rcases family_descends (prefixWord ++ tailWord_750314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750330 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 4, 4]
def baseStart_750330 : Nat := 118140960795 + 750330 * 2 ^ 59
def prefixEnd_750330 : Nat := 4983230072969 + 3 ^ 40 * 750330 * 2
def baseEnd_750330 : Nat := 128426646496051521374767

theorem tailTrace_750330 : CollatzResearch.WordTrace tailWord_750330 prefixEnd_750330 128426646496051521374767 := by
  unfold tailWord_750330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6841695842922507751718111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18244522247793354004581629 6841695842922507751718111)
  ·
    refine ⟨10262543764383761627577167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6841695842922507751718111 10262543764383761627577167)
    ·
      refine ⟨15393815646575642441365751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10262543764383761627577167 15393815646575642441365751)
      ·
        refine ⟨23090723469863463662048627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15393815646575642441365751 23090723469863463662048627)
        ·
          refine ⟨34636085204795195493072941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23090723469863463662048627 34636085204795195493072941)
          ·
            refine ⟨12988531951798198309902353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34636085204795195493072941 12988531951798198309902353)
            ·
              refine ⟨9741398963848648732426765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12988531951798198309902353 9741398963848648732426765)
              ·
                refine ⟨3653024611443243274660037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9741398963848648732426765 3653024611443243274660037)
                ·
                  refine ⟨684942114645608113998757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3653024611443243274660037 684942114645608113998757)
                  ·
                    refine ⟨128426646496051521374767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 684942114645608113998757 128426646496051521374767)
                    ·
                      rfl

theorem cell23_750330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 4, 4].length) (baseStart_750330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750330 prefixEnd_750330 := by exact prefixLift 750330
  have htrace : WordTrace (prefixWord ++ tailWord_750330) baseStart_750330 baseEnd_750330 := by
    simpa [prefixWord, tailWord_750330, baseEnd_750330] using wordTrace_append hprefix tailTrace_750330
  have hstable : (prefixWord ++ tailWord_750330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750330).length < 2 ^ (prefixWord ++ tailWord_750330).sum := by decide
  have hdescent : baseEnd_750330 < baseStart_750330 := by decide
  rcases family_descends (prefixWord ++ tailWord_750330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750340 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_750340 : Nat := 118140960795 + 750340 * 2 ^ 59
def prefixEnd_750340 : Nat := 4983230072969 + 3 ^ 40 * 750340 * 2
def baseEnd_750340 : Nat := 385285074294699524999255

theorem tailTrace_750340 : CollatzResearch.WordTrace tailWord_750340 prefixEnd_750340 385285074294699524999255 := by
  unfold tailWord_750340
  simp only [CollatzResearch.WordTrace]
  refine ⟨13683574050826901357368237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18244765401102535143157649 13683574050826901357368237)
  ·
    refine ⟨5131340269060088009013089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13683574050826901357368237 5131340269060088009013089)
    ·
      refine ⟨3848505201795066006759817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5131340269060088009013089 3848505201795066006759817)
      ·
        refine ⟨2886378901346299505069863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3848505201795066006759817 2886378901346299505069863)
        ·
          refine ⟨4329568352019449257604795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2886378901346299505069863 4329568352019449257604795)
          ·
            refine ⟨6494352528029173886407193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4329568352019449257604795 6494352528029173886407193)
            ·
              refine ⟨4870764396021880414805395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6494352528029173886407193 4870764396021880414805395)
              ·
                refine ⟨7306146594032820622208093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4870764396021880414805395 7306146594032820622208093)
                ·
                  refine ⟨2739804972762307733328035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7306146594032820622208093 2739804972762307733328035)
                  ·
                    refine ⟨4109707459143461599992053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2739804972762307733328035 4109707459143461599992053)
                    ·
                      refine ⟨385285074294699524999255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4109707459143461599992053 385285074294699524999255)
                      ·
                        rfl

theorem cell23_750340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_750340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750340 prefixEnd_750340 := by exact prefixLift 750340
  have htrace : WordTrace (prefixWord ++ tailWord_750340) baseStart_750340 baseEnd_750340 := by
    simpa [prefixWord, tailWord_750340, baseEnd_750340] using wordTrace_append hprefix tailTrace_750340
  have hstable : (prefixWord ++ tailWord_750340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750340).length < 2 ^ (prefixWord ++ tailWord_750340).sum := by decide
  have hdescent : baseEnd_750340 < baseStart_750340 := by decide
  rcases family_descends (prefixWord ++ tailWord_750340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750357 : List Nat := [1, 3, 2, 1, 2, 2, 2, 4, 1, 2, 3]
def baseStart_750357 : Nat := 118140960795 + 750357 * 2 ^ 59
def prefixEnd_750357 : Nat := 4983230072969 + 3 ^ 40 * 750357 * 2
def baseEnd_750357 : Nat := 385293803465825958486677

theorem tailTrace_750357 : CollatzResearch.WordTrace tailWord_750357 prefixEnd_750357 385293803465825958486677 := by
  unfold tailWord_750357
  simp only [CollatzResearch.WordTrace]
  refine ⟨27367768142592214618105325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18245178761728143078736883 27367768142592214618105325)
  ·
    refine ⟨10262913053472080481789497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27367768142592214618105325 10262913053472080481789497)
    ·
      refine ⟨7697184790104060361342123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10262913053472080481789497 7697184790104060361342123)
      ·
        refine ⟨11545777185156090542013185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7697184790104060361342123 11545777185156090542013185)
        ·
          refine ⟨8659332888867067906509889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11545777185156090542013185 8659332888867067906509889)
          ·
            refine ⟨6494499666650300929882417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8659332888867067906509889 6494499666650300929882417)
            ·
              refine ⟨4870874749987725697411813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6494499666650300929882417 4870874749987725697411813)
              ·
                refine ⟨913289015622698568264715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4870874749987725697411813 913289015622698568264715)
                ·
                  refine ⟨1369933523434047852397073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 913289015622698568264715 1369933523434047852397073)
                  ·
                    refine ⟨1027450142575535889297805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1369933523434047852397073 1027450142575535889297805)
                    ·
                      refine ⟨385293803465825958486677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1027450142575535889297805 385293803465825958486677)
                      ·
                        rfl

theorem cell23_750357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_750357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750357 prefixEnd_750357 := by exact prefixLift 750357
  have htrace : WordTrace (prefixWord ++ tailWord_750357) baseStart_750357 baseEnd_750357 := by
    simpa [prefixWord, tailWord_750357, baseEnd_750357] using wordTrace_append hprefix tailTrace_750357
  have hstable : (prefixWord ++ tailWord_750357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750357).length < 2 ^ (prefixWord ++ tailWord_750357).sum := by decide
  have hdescent : baseEnd_750357 < baseStart_750357 := by decide
  rcases family_descends (prefixWord ++ tailWord_750357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750381 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_750381 : Nat := 118140960795 + 750381 * 2 ^ 59
def prefixEnd_750381 : Nat := 4983230072969 + 3 ^ 40 * 750381 * 2
def baseEnd_750381 : Nat := 128435375667177954862189

theorem tailTrace_750381 : CollatzResearch.WordTrace tailWord_750381 prefixEnd_750381 128435375667177954862189 := by
  unfold tailWord_750381
  simp only [CollatzResearch.WordTrace]
  refine ⟨27368643494505266716978997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18245762329670177811319331 27368643494505266716978997)
  ·
    refine ⟨2565810327609868754716781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27368643494505266716978997 2565810327609868754716781)
    ·
      refine ⟨962178872853700783018793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2565810327609868754716781 962178872853700783018793)
      ·
        refine ⟨721634154640275587264095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 962178872853700783018793 721634154640275587264095)
        ·
          refine ⟨1082451231960413380896143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721634154640275587264095 1082451231960413380896143)
          ·
            refine ⟨1623676847940620071344215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082451231960413380896143 1623676847940620071344215)
            ·
              refine ⟨2435515271910930107016323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1623676847940620071344215 2435515271910930107016323)
              ·
                refine ⟨3653272907866395160524485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2435515271910930107016323 3653272907866395160524485)
                ·
                  refine ⟨684988670224949092598341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3653272907866395160524485 684988670224949092598341)
                  ·
                    refine ⟨128435375667177954862189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 684988670224949092598341 128435375667177954862189)
                    ·
                      rfl

theorem cell23_750381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_750381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750381 prefixEnd_750381 := by exact prefixLift 750381
  have htrace : WordTrace (prefixWord ++ tailWord_750381) baseStart_750381 baseEnd_750381 := by
    simpa [prefixWord, tailWord_750381, baseEnd_750381] using wordTrace_append hprefix tailTrace_750381
  have hstable : (prefixWord ++ tailWord_750381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750381).length < 2 ^ (prefixWord ++ tailWord_750381).sum := by decide
  have hdescent : baseEnd_750381 < baseStart_750381 := by decide
  rcases family_descends (prefixWord ++ tailWord_750381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750383 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 7]
def baseStart_750383 : Nat := 118140960795 + 750383 * 2 ^ 59
def prefixEnd_750383 : Nat := 4983230072969 + 3 ^ 40 * 750383 * 2
def baseEnd_750383 : Nat := 385307153962842856761557

theorem tailTrace_750383 : CollatzResearch.WordTrace tailWord_750383 prefixEnd_750383 385307153962842856761557 := by
  unfold tailWord_750383
  simp only [CollatzResearch.WordTrace]
  refine ⟨27368716440498021058551803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18245810960332014039034535 27368716440498021058551803)
  ·
    refine ⟨41053074660747031587827705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27368716440498021058551803 41053074660747031587827705)
    ·
      refine ⟨30789805995560273690870779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41053074660747031587827705 30789805995560273690870779)
      ·
        refine ⟨46184708993340410536306169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30789805995560273690870779 46184708993340410536306169)
        ·
          refine ⟨34638531745005307902229627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46184708993340410536306169 34638531745005307902229627)
          ·
            refine ⟨51957797617507961853344441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34638531745005307902229627 51957797617507961853344441)
            ·
              refine ⟨38968348213130971390008331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51957797617507961853344441 38968348213130971390008331)
              ·
                refine ⟨58452522319696457085012497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38968348213130971390008331 58452522319696457085012497)
                ·
                  refine ⟨43839391739772342813759373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58452522319696457085012497 43839391739772342813759373)
                  ·
                    refine ⟨16439771902414628555159765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43839391739772342813759373 16439771902414628555159765)
                    ·
                      refine ⟨385307153962842856761557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16439771902414628555159765 385307153962842856761557)
                      ·
                        rfl

theorem cell23_750383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_750383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750383 prefixEnd_750383 := by exact prefixLift 750383
  have htrace : WordTrace (prefixWord ++ tailWord_750383) baseStart_750383 baseEnd_750383 := by
    simpa [prefixWord, tailWord_750383, baseEnd_750383] using wordTrace_append hprefix tailTrace_750383
  have hstable : (prefixWord ++ tailWord_750383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750383).length < 2 ^ (prefixWord ++ tailWord_750383).sum := by decide
  have hdescent : baseEnd_750383 < baseStart_750383 := by decide
  rcases family_descends (prefixWord ++ tailWord_750383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750388 : List Nat := [2, 5, 1, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_750388 : Nat := 118140960795 + 750388 * 2 ^ 59
def prefixEnd_750388 : Nat := 4983230072969 + 3 ^ 40 * 750388 * 2
def baseEnd_750388 : Nat := 385309721366115337199035

theorem tailTrace_750388 : CollatzResearch.WordTrace tailWord_750388 prefixEnd_750388 385309721366115337199035 := by
  unfold tailWord_750388
  simp only [CollatzResearch.WordTrace]
  refine ⟨13684449402739953456241909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18245932536986604608322545 13684449402739953456241909)
  ·
    refine ⟨1282917131506870636522679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13684449402739953456241909 1282917131506870636522679)
    ·
      refine ⟨1924375697260305954784019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1282917131506870636522679 1924375697260305954784019)
      ·
        refine ⟨2886563545890458932176029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1924375697260305954784019 2886563545890458932176029)
        ·
          refine ⟨1082461329708922099566011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2886563545890458932176029 1082461329708922099566011)
          ·
            refine ⟨1623691994563383149349017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082461329708922099566011 1623691994563383149349017)
            ·
              refine ⟨1217768995922537362011763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1623691994563383149349017 1217768995922537362011763)
              ·
                refine ⟨1826653493883806043017645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1217768995922537362011763 1826653493883806043017645)
                ·
                  refine ⟨684995060206427266131617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1826653493883806043017645 684995060206427266131617)
                  ·
                    refine ⟨513746295154820449598713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 684995060206427266131617 513746295154820449598713)
                    ·
                      refine ⟨385309721366115337199035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 513746295154820449598713 385309721366115337199035)
                      ·
                        rfl

theorem cell23_750388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_750388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750388 prefixEnd_750388 := by exact prefixLift 750388
  have htrace : WordTrace (prefixWord ++ tailWord_750388) baseStart_750388 baseEnd_750388 := by
    simpa [prefixWord, tailWord_750388, baseEnd_750388] using wordTrace_append hprefix tailTrace_750388
  have hstable : (prefixWord ++ tailWord_750388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750388).length < 2 ^ (prefixWord ++ tailWord_750388).sum := by decide
  have hdescent : baseEnd_750388 < baseStart_750388 := by decide
  rcases family_descends (prefixWord ++ tailWord_750388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750401 : List Nat := [1, 2, 5, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_750401 : Nat := 118140960795 + 750401 * 2 ^ 59
def prefixEnd_750401 : Nat := 4983230072969 + 3 ^ 40 * 750401 * 2
def baseEnd_750401 : Nat := 385316396614623786336475

theorem tailTrace_750401 : CollatzResearch.WordTrace tailWord_750401 prefixEnd_750401 385316396614623786336475 := by
  unfold tailWord_750401
  simp only [CollatzResearch.WordTrace]
  refine ⟨27369372954432810132707057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18246248636288540088471371 27369372954432810132707057)
  ·
    refine ⟨20527029715824607599530293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27369372954432810132707057 20527029715824607599530293)
    ·
      refine ⟨1924409035858556962455965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20527029715824607599530293 1924409035858556962455965)
      ·
        refine ⟨721653388446958860920987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1924409035858556962455965 721653388446958860920987)
        ·
          refine ⟨1082480082670438291381481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721653388446958860920987 1082480082670438291381481)
          ·
            refine ⟨811860062002828718536111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1082480082670438291381481 811860062002828718536111)
            ·
              refine ⟨1217790093004243077804167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 811860062002828718536111 1217790093004243077804167)
              ·
                refine ⟨1826685139506364616706251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1217790093004243077804167 1826685139506364616706251)
                ·
                  refine ⟨2740027709259546925059377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1826685139506364616706251 2740027709259546925059377)
                  ·
                    refine ⟨2055020781944660193794533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2740027709259546925059377 2055020781944660193794533)
                    ·
                      refine ⟨385316396614623786336475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2055020781944660193794533 385316396614623786336475)
                      ·
                        rfl

theorem cell23_750401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_750401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750401 prefixEnd_750401 := by exact prefixLift 750401
  have htrace : WordTrace (prefixWord ++ tailWord_750401) baseStart_750401 baseEnd_750401 := by
    simpa [prefixWord, tailWord_750401, baseEnd_750401] using wordTrace_append hprefix tailTrace_750401
  have hstable : (prefixWord ++ tailWord_750401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750401).length < 2 ^ (prefixWord ++ tailWord_750401).sum := by decide
  have hdescent : baseEnd_750401 < baseStart_750401 := by decide
  rcases family_descends (prefixWord ++ tailWord_750401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750444 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 4, 2, 2]
def baseStart_750444 : Nat := 118140960795 + 750444 * 2 ^ 59
def prefixEnd_750444 : Nat := 4983230072969 + 3 ^ 40 * 750444 * 2
def baseEnd_750444 : Nat := 385338476282767118098777

theorem tailTrace_750444 : CollatzResearch.WordTrace tailWord_750444 prefixEnd_750444 385338476282767118098777 := by
  unfold tailWord_750444
  simp only [CollatzResearch.WordTrace]
  refine ⟨13685470646638514238261193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18247294195518018984348257 13685470646638514238261193)
  ·
    refine ⟨10264102984978885678695895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13685470646638514238261193 10264102984978885678695895)
    ·
      refine ⟨15396154477468328518043843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10264102984978885678695895 15396154477468328518043843)
      ·
        refine ⟨23094231716202492777065765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15396154477468328518043843 23094231716202492777065765)
        ·
          refine ⟨4330168446787967395699831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23094231716202492777065765 4330168446787967395699831)
          ·
            refine ⟨6495252670181951093549747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4330168446787967395699831 6495252670181951093549747)
            ·
              refine ⟨9742879005272926640324621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6495252670181951093549747 9742879005272926640324621)
              ·
                refine ⟨3653579626977347490121733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9742879005272926640324621 3653579626977347490121733)
                ·
                  refine ⟨685046180058252654397825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3653579626977347490121733 685046180058252654397825)
                  ·
                    refine ⟨513784635043689490798369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 685046180058252654397825 513784635043689490798369)
                    ·
                      refine ⟨385338476282767118098777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 513784635043689490798369 385338476282767118098777)
                      ·
                        rfl

theorem cell23_750444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 2, 2].length) (baseStart_750444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750444 prefixEnd_750444 := by exact prefixLift 750444
  have htrace : WordTrace (prefixWord ++ tailWord_750444) baseStart_750444 baseEnd_750444 := by
    simpa [prefixWord, tailWord_750444, baseEnd_750444] using wordTrace_append hprefix tailTrace_750444
  have hstable : (prefixWord ++ tailWord_750444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750444).length < 2 ^ (prefixWord ++ tailWord_750444).sum := by decide
  have hdescent : baseEnd_750444 < baseStart_750444 := by decide
  rcases family_descends (prefixWord ++ tailWord_750444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750484 : List Nat := [2, 4, 2, 1, 1, 1, 2, 5, 5]
def baseStart_750484 : Nat := 118140960795 + 750484 * 2 ^ 59
def prefixEnd_750484 : Nat := 4983230072969 + 3 ^ 40 * 750484 * 2
def baseEnd_750484 : Nat := 42817668389882995733177

theorem tailTrace_750484 : CollatzResearch.WordTrace tailWord_750484 prefixEnd_750484 42817668389882995733177 := by
  unfold tailWord_750484
  simp only [CollatzResearch.WordTrace]
  refine ⟨13686200106566057653989253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18248266808754743538652337 13686200106566057653989253)
  ·
    refine ⟨2566162519981135810122985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13686200106566057653989253 2566162519981135810122985)
    ·
      refine ⟨1924621889985851857592239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2566162519981135810122985 1924621889985851857592239)
      ·
        refine ⟨2886932834978777786388359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1924621889985851857592239 2886932834978777786388359)
        ·
          refine ⟨4330399252468166679582539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2886932834978777786388359 4330399252468166679582539)
          ·
            refine ⟨6495598878702250019373809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4330399252468166679582539 6495598878702250019373809)
            ·
              refine ⟨4871699159026687514530357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6495598878702250019373809 4871699159026687514530357)
              ·
                refine ⟨456721796158751954487221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4871699159026687514530357 456721796158751954487221)
                ·
                  refine ⟨42817668389882995733177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 456721796158751954487221 42817668389882995733177)
                  ·
                    rfl

theorem cell23_750484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_750484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750484 prefixEnd_750484 := by exact prefixLift 750484
  have htrace : WordTrace (prefixWord ++ tailWord_750484) baseStart_750484 baseEnd_750484 := by
    simpa [prefixWord, tailWord_750484, baseEnd_750484] using wordTrace_append hprefix tailTrace_750484
  have hstable : (prefixWord ++ tailWord_750484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750484).length < 2 ^ (prefixWord ++ tailWord_750484).sum := by decide
  have hdescent : baseEnd_750484 < baseStart_750484 := by decide
  rcases family_descends (prefixWord ++ tailWord_750484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750517 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_750517 : Nat := 118140960795 + 750517 * 2 ^ 59
def prefixEnd_750517 : Nat := 4983230072969 + 3 ^ 40 * 750517 * 2
def baseEnd_750517 : Nat := 385375960370545332485941

theorem tailTrace_750517 : CollatzResearch.WordTrace tailWord_750517 prefixEnd_750517 385375960370545332485941 := by
  unfold tailWord_750517
  simp only [CollatzResearch.WordTrace]
  refine ⟨27373603822012561943929805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18249069214675041295953203 27373603822012561943929805)
  ·
    refine ⟨10265101433254710728973677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27373603822012561943929805 10265101433254710728973677)
    ·
      refine ⟨3849413037470516523365129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10265101433254710728973677 3849413037470516523365129)
      ·
        refine ⟨2887059778102887392523847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3849413037470516523365129 2887059778102887392523847)
        ·
          refine ⟨4330589667154331088785771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2887059778102887392523847 4330589667154331088785771)
          ·
            refine ⟨6495884500731496633178657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4330589667154331088785771 6495884500731496633178657)
            ·
              refine ⟨4871913375548622474883993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6495884500731496633178657 4871913375548622474883993)
              ·
                refine ⟨3653935031661466856162995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4871913375548622474883993 3653935031661466856162995)
                ·
                  refine ⟨5480902547492200284244493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3653935031661466856162995 5480902547492200284244493)
                  ·
                    refine ⟨2055338455309575106591685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5480902547492200284244493 2055338455309575106591685)
                    ·
                      refine ⟨385375960370545332485941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2055338455309575106591685 385375960370545332485941)
                      ·
                        rfl

theorem cell23_750517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_750517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750517 prefixEnd_750517 := by exact prefixLift 750517
  have htrace : WordTrace (prefixWord ++ tailWord_750517) baseStart_750517 baseEnd_750517 := by
    simpa [prefixWord, tailWord_750517, baseEnd_750517] using wordTrace_append hprefix tailTrace_750517
  have hstable : (prefixWord ++ tailWord_750517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750517).length < 2 ^ (prefixWord ++ tailWord_750517).sum := by decide
  have hdescent : baseEnd_750517 < baseStart_750517 := by decide
  rcases family_descends (prefixWord ++ tailWord_750517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750518 : List Nat := [5, 1, 4, 1, 1, 1, 1, 2, 7]
def baseStart_750518 : Nat := 118140960795 + 750518 * 2 ^ 59
def prefixEnd_750518 : Nat := 4983230072969 + 3 ^ 40 * 750518 * 2
def baseEnd_750518 : Nat := 42819608205688869841493

theorem tailTrace_750518 : CollatzResearch.WordTrace tailWord_750518 prefixEnd_750518 42819608205688869841493 := by
  unfold tailWord_750518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1710852518438058694669763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18249093530005959409810805 1710852518438058694669763)
  ·
    refine ⟨2566278777657088042004645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1710852518438058694669763 2566278777657088042004645)
    ·
      refine ⟨481177270810704007875871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2566278777657088042004645 481177270810704007875871)
      ·
        refine ⟨721765906216056011813807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481177270810704007875871 721765906216056011813807)
        ·
          refine ⟨1082648859324084017720711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721765906216056011813807 1082648859324084017720711)
          ·
            refine ⟨1623973288986126026581067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082648859324084017720711 1623973288986126026581067)
            ·
              refine ⟨2435959933479189039871601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1623973288986126026581067 2435959933479189039871601)
              ·
                refine ⟨1826969950109391779903701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2435959933479189039871601 1826969950109391779903701)
                ·
                  refine ⟨42819608205688869841493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1826969950109391779903701 42819608205688869841493)
                  ·
                    rfl

theorem cell23_750518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_750518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750518 prefixEnd_750518 := by exact prefixLift 750518
  have htrace : WordTrace (prefixWord ++ tailWord_750518) baseStart_750518 baseEnd_750518 := by
    simpa [prefixWord, tailWord_750518, baseEnd_750518] using wordTrace_append hprefix tailTrace_750518
  have hstable : (prefixWord ++ tailWord_750518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750518).length < 2 ^ (prefixWord ++ tailWord_750518).sum := by decide
  have hdescent : baseEnd_750518 < baseStart_750518 := by decide
  rcases family_descends (prefixWord ++ tailWord_750518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750604 : List Nat := [2, 2, 1, 2, 3, 2, 2, 3, 1, 5]
def baseStart_750604 : Nat := 118140960795 + 750604 * 2 ^ 59
def prefixEnd_750604 : Nat := 4983230072969 + 3 ^ 40 * 750604 * 2
def baseEnd_750604 : Nat := 128473544395828830699347

theorem tailTrace_750604 : CollatzResearch.WordTrace tailWord_750604 prefixEnd_750604 128473544395828830699347 := by
  unfold tailWord_750604
  simp only [CollatzResearch.WordTrace]
  refine ⟨13688388486348687901173433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18251184648464917201564577 13688388486348687901173433)
  ·
    refine ⟨10266291364761515925880075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13688388486348687901173433 10266291364761515925880075)
    ·
      refine ⟨15399437047142273888820113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10266291364761515925880075 15399437047142273888820113)
      ·
        refine ⟨11549577785356705416615085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15399437047142273888820113 11549577785356705416615085)
        ·
          refine ⟨4331091669508764531230657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11549577785356705416615085 4331091669508764531230657)
          ·
            refine ⟨3248318752131573398422993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4331091669508764531230657 3248318752131573398422993)
            ·
              refine ⟨2436239064098680048817245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3248318752131573398422993 2436239064098680048817245)
              ·
                refine ⟨913589649037005018306467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2436239064098680048817245 913589649037005018306467)
                ·
                  refine ⟨1370384473555507527459701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 913589649037005018306467 1370384473555507527459701)
                  ·
                    refine ⟨128473544395828830699347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1370384473555507527459701 128473544395828830699347)
                    ·
                      rfl

theorem cell23_750604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 1, 5].length) (baseStart_750604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750604 prefixEnd_750604 := by exact prefixLift 750604
  have htrace : WordTrace (prefixWord ++ tailWord_750604) baseStart_750604 baseEnd_750604 := by
    simpa [prefixWord, tailWord_750604, baseEnd_750604] using wordTrace_append hprefix tailTrace_750604
  have hstable : (prefixWord ++ tailWord_750604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750604).length < 2 ^ (prefixWord ++ tailWord_750604).sum := by decide
  have hdescent : baseEnd_750604 < baseStart_750604 := by decide
  rcases family_descends (prefixWord ++ tailWord_750604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750641 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 5, 2, 2]
def baseStart_750641 : Nat := 118140960795 + 750641 * 2 ^ 59
def prefixEnd_750641 : Nat := 4983230072969 + 3 ^ 40 * 750641 * 2
def baseEnd_750641 : Nat := 385439631971702847335371

theorem tailTrace_750641 : CollatzResearch.WordTrace tailWord_750641 prefixEnd_750641 385439631971702847335371 := by
  unfold tailWord_750641
  simp only [CollatzResearch.WordTrace]
  refine ⟨27378126473563331121443777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18252084315708887414295851 27378126473563331121443777)
  ·
    refine ⟨20533594855172498341082833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27378126473563331121443777 20533594855172498341082833)
    ·
      refine ⟨15400196141379373755812125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20533594855172498341082833 15400196141379373755812125)
      ·
        refine ⟨5775073553017265158429547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15400196141379373755812125 5775073553017265158429547)
        ·
          refine ⟨8662610329525897737644321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5775073553017265158429547 8662610329525897737644321)
          ·
            refine ⟨6496957747144423303233241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8662610329525897737644321 6496957747144423303233241)
            ·
              refine ⟨4872718310358317477424931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6496957747144423303233241 4872718310358317477424931)
              ·
                refine ⟨7309077465537476216137397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4872718310358317477424931 7309077465537476216137397)
                ·
                  refine ⟨685226012394138395262881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7309077465537476216137397 685226012394138395262881)
                  ·
                    refine ⟨513919509295603796447161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 685226012394138395262881 513919509295603796447161)
                    ·
                      refine ⟨385439631971702847335371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 513919509295603796447161 385439631971702847335371)
                      ·
                        rfl

theorem cell23_750641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_750641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750641 prefixEnd_750641 := by exact prefixLift 750641
  have htrace : WordTrace (prefixWord ++ tailWord_750641) baseStart_750641 baseEnd_750641 := by
    simpa [prefixWord, tailWord_750641, baseEnd_750641] using wordTrace_append hprefix tailTrace_750641
  have hstable : (prefixWord ++ tailWord_750641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750641).length < 2 ^ (prefixWord ++ tailWord_750641).sum := by decide
  have hdescent : baseEnd_750641 < baseStart_750641 := by decide
  rcases family_descends (prefixWord ++ tailWord_750641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750677 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 1, 9]
def baseStart_750677 : Nat := 118140960795 + 750677 * 2 ^ 59
def prefixEnd_750677 : Nat := 4983230072969 + 3 ^ 40 * 750677 * 2
def baseEnd_750677 : Nat := 128486039091754902161735

theorem tailTrace_750677 : CollatzResearch.WordTrace tailWord_750677 prefixEnd_750677 128486039091754902161735 := by
  unfold tailWord_750677
  simp only [CollatzResearch.WordTrace]
  refine ⟨27379439501432909269754285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18252959667621939513169523 27379439501432909269754285)
  ·
    refine ⟨10267289813037340976157857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27379439501432909269754285 10267289813037340976157857)
    ·
      refine ⟨7700467359778005732118393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10267289813037340976157857 7700467359778005732118393)
      ·
        refine ⟨5775350519833504299088795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7700467359778005732118393 5775350519833504299088795)
        ·
          refine ⟨8663025779750256448633193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5775350519833504299088795 8663025779750256448633193)
          ·
            refine ⟨6497269334812692336474895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8663025779750256448633193 6497269334812692336474895)
            ·
              refine ⟨9745904002219038504712343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6497269334812692336474895 9745904002219038504712343)
              ·
                refine ⟨14618856003328557757068515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9745904002219038504712343 14618856003328557757068515)
                ·
                  refine ⟨21928284004992836635602773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14618856003328557757068515 21928284004992836635602773)
                  ·
                    refine ⟨128486039091754902161735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 21928284004992836635602773 128486039091754902161735)
                    ·
                      rfl

theorem cell23_750677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_750677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750677 prefixEnd_750677 := by exact prefixLift 750677
  have htrace : WordTrace (prefixWord ++ tailWord_750677) baseStart_750677 baseEnd_750677 := by
    simpa [prefixWord, tailWord_750677, baseEnd_750677] using wordTrace_append hprefix tailTrace_750677
  have hstable : (prefixWord ++ tailWord_750677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750677).length < 2 ^ (prefixWord ++ tailWord_750677).sum := by decide
  have hdescent : baseEnd_750677 < baseStart_750677 := by decide
  rcases family_descends (prefixWord ++ tailWord_750677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750709 : List Nat := [1, 3, 4, 3, 1, 1, 2, 3, 1, 2, 2]
def baseStart_750709 : Nat := 118140960795 + 750709 * 2 ^ 59
def prefixEnd_750709 : Nat := 4983230072969 + 3 ^ 40 * 750709 * 2
def baseEnd_750709 : Nat := 385474548656208581285059

theorem tailTrace_750709 : CollatzResearch.WordTrace tailWord_750709 prefixEnd_750709 385474548656208581285059 := by
  unfold tailWord_750709
  simp only [CollatzResearch.WordTrace]
  refine ⟨27380606637316978734919181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18253737758211319156612787 27380606637316978734919181)
  ·
    refine ⟨10267727488993867025594693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27380606637316978734919181 10267727488993867025594693)
    ·
      refine ⟨1925198904186350067299005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10267727488993867025594693 1925198904186350067299005)
      ·
        refine ⟨721949589069881275237127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1925198904186350067299005 721949589069881275237127)
        ·
          refine ⟨1082924383604821912855691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721949589069881275237127 1082924383604821912855691)
          ·
            refine ⟨1624386575407232869283537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082924383604821912855691 1624386575407232869283537)
            ·
              refine ⟨1218289931555424651962653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1624386575407232869283537 1218289931555424651962653)
              ·
                refine ⟨456858724333284244485995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1218289931555424651962653 456858724333284244485995)
                ·
                  refine ⟨685288086499926366728993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456858724333284244485995 685288086499926366728993)
                  ·
                    refine ⟨513966064874944775046745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 685288086499926366728993 513966064874944775046745)
                    ·
                      refine ⟨385474548656208581285059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 513966064874944775046745 385474548656208581285059)
                      ·
                        rfl

theorem cell23_750709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_750709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750709 prefixEnd_750709 := by exact prefixLift 750709
  have htrace : WordTrace (prefixWord ++ tailWord_750709) baseStart_750709 baseEnd_750709 := by
    simpa [prefixWord, tailWord_750709, baseEnd_750709] using wordTrace_append hprefix tailTrace_750709
  have hstable : (prefixWord ++ tailWord_750709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750709).length < 2 ^ (prefixWord ++ tailWord_750709).sum := by decide
  have hdescent : baseEnd_750709 < baseStart_750709 := by decide
  rcases family_descends (prefixWord ++ tailWord_750709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750724 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 2, 6]
def baseStart_750724 : Nat := 118140960795 + 750724 * 2 ^ 59
def prefixEnd_750724 : Nat := 4983230072969 + 3 ^ 40 * 750724 * 2
def baseEnd_750724 : Nat := 128494083622008674199163

theorem tailTrace_750724 : CollatzResearch.WordTrace tailWord_750724 prefixEnd_750724 128494083622008674199163 := by
  unfold tailWord_750724
  simp only [CollatzResearch.WordTrace]
  refine ⟨13690576866131318148357613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18254102488175090864476817 13690576866131318148357613)
  ·
    refine ⟨5133966324799244305634105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13690576866131318148357613 5133966324799244305634105)
    ·
      refine ⟨3850474743599433229225579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5133966324799244305634105 3850474743599433229225579)
      ·
        refine ⟨5775712115399149843838369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3850474743599433229225579 5775712115399149843838369)
        ·
          refine ⟨4331784086549362382878777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5775712115399149843838369 4331784086549362382878777)
          ·
            refine ⟨3248838064912021787159083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4331784086549362382878777 3248838064912021787159083)
            ·
              refine ⟨4873257097368032680738625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3248838064912021787159083 4873257097368032680738625)
              ·
                refine ⟨3654942823026024510553969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4873257097368032680738625 3654942823026024510553969)
                ·
                  refine ⟨2741207117269518382915477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3654942823026024510553969 2741207117269518382915477)
                  ·
                    refine ⟨128494083622008674199163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2741207117269518382915477 128494083622008674199163)
                    ·
                      rfl

theorem cell23_750724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_750724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750724 prefixEnd_750724 := by exact prefixLift 750724
  have htrace : WordTrace (prefixWord ++ tailWord_750724) baseStart_750724 baseEnd_750724 := by
    simpa [prefixWord, tailWord_750724, baseEnd_750724] using wordTrace_append hprefix tailTrace_750724
  have hstable : (prefixWord ++ tailWord_750724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750724).length < 2 ^ (prefixWord ++ tailWord_750724).sum := by decide
  have hdescent : baseEnd_750724 < baseStart_750724 := by decide
  rcases family_descends (prefixWord ++ tailWord_750724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750725 : List Nat := [1, 3, 1, 1, 6, 2, 1, 2, 2, 1, 3]
def baseStart_750725 : Nat := 118140960795 + 750725 * 2 ^ 59
def prefixEnd_750725 : Nat := 4983230072969 + 3 ^ 40 * 750725 * 2
def baseEnd_750725 : Nat := 385482764346680518684985

theorem tailTrace_750725 : CollatzResearch.WordTrace tailWord_750725 prefixEnd_750725 385482764346680518684985 := by
  unfold tailWord_750725
  simp only [CollatzResearch.WordTrace]
  refine ⟨27381190205259013467501629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18254126803506008978334419 27381190205259013467501629)
  ·
    refine ⟨10267946326972130050313111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27381190205259013467501629 10267946326972130050313111)
    ·
      refine ⟨15401919490458195075469667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10267946326972130050313111 15401919490458195075469667)
      ·
        refine ⟨23102879235687292613204501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15401919490458195075469667 23102879235687292613204501)
        ·
          refine ⟨1082947464172841841243961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23102879235687292613204501 1082947464172841841243961)
          ·
            refine ⟨812210598129631380932971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1082947464172841841243961 812210598129631380932971)
            ·
              refine ⟨1218315897194447071399457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812210598129631380932971 1218315897194447071399457)
              ·
                refine ⟨913736922895835303549593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1218315897194447071399457 913736922895835303549593)
                ·
                  refine ⟨685302692171876477662195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 913736922895835303549593 685302692171876477662195)
                  ·
                    refine ⟨1027954038257814716493293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 685302692171876477662195 1027954038257814716493293)
                    ·
                      refine ⟨385482764346680518684985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1027954038257814716493293 385482764346680518684985)
                      ·
                        rfl

theorem cell23_750725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 1, 3].length) (baseStart_750725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750725 prefixEnd_750725 := by exact prefixLift 750725
  have htrace : WordTrace (prefixWord ++ tailWord_750725) baseStart_750725 baseEnd_750725 := by
    simpa [prefixWord, tailWord_750725, baseEnd_750725] using wordTrace_append hprefix tailTrace_750725
  have hstable : (prefixWord ++ tailWord_750725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750725).length < 2 ^ (prefixWord ++ tailWord_750725).sum := by decide
  have hdescent : baseEnd_750725 < baseStart_750725 := by decide
  rcases family_descends (prefixWord ++ tailWord_750725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750748 : List Nat := [2, 2, 3, 2, 1, 2, 3, 1, 1, 4, 2]
def baseStart_750748 : Nat := 118140960795 + 750748 * 2 ^ 59
def prefixEnd_750748 : Nat := 4983230072969 + 3 ^ 40 * 750748 * 2
def baseEnd_750748 : Nat := 385494574401733928697379

theorem tailTrace_750748 : CollatzResearch.WordTrace tailWord_750748 prefixEnd_750748 385494574401733928697379 := by
  unfold tailWord_750748
  simp only [CollatzResearch.WordTrace]
  refine ⟨13691014542087844197794449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18254686056117125597059265 13691014542087844197794449)
  ·
    refine ⟨10268260906565883148345837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13691014542087844197794449 10268260906565883148345837)
    ·
      refine ⟨3850597839962206180629689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10268260906565883148345837 3850597839962206180629689)
      ·
        refine ⟨2887948379971654635472267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3850597839962206180629689 2887948379971654635472267)
        ·
          refine ⟨4331922569957481953208401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2887948379971654635472267 4331922569957481953208401)
          ·
            refine ⟨3248941927468111464906301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4331922569957481953208401 3248941927468111464906301)
            ·
              refine ⟨1218353222800541799339863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3248941927468111464906301 1218353222800541799339863)
              ·
                refine ⟨1827529834200812699009795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1218353222800541799339863 1827529834200812699009795)
                ·
                  refine ⟨2741294751301219048514693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1827529834200812699009795 2741294751301219048514693)
                  ·
                    refine ⟨513992765868978571596505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2741294751301219048514693 513992765868978571596505)
                    ·
                      refine ⟨385494574401733928697379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 513992765868978571596505 385494574401733928697379)
                      ·
                        rfl

theorem cell23_750748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_750748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750748 prefixEnd_750748 := by exact prefixLift 750748
  have htrace : WordTrace (prefixWord ++ tailWord_750748) baseStart_750748 baseEnd_750748 := by
    simpa [prefixWord, tailWord_750748, baseEnd_750748] using wordTrace_append hprefix tailTrace_750748
  have hstable : (prefixWord ++ tailWord_750748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750748).length < 2 ^ (prefixWord ++ tailWord_750748).sum := by decide
  have hdescent : baseEnd_750748 < baseStart_750748 := by decide
  rcases family_descends (prefixWord ++ tailWord_750748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750764 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 3]
def baseStart_750764 : Nat := 118140960795 + 750764 * 2 ^ 59
def prefixEnd_750764 : Nat := 4983230072969 + 3 ^ 40 * 750764 * 2
def baseEnd_750764 : Nat := 385502790092205866097305

theorem tailTrace_750764 : CollatzResearch.WordTrace tailWord_750764 prefixEnd_750764 385502790092205866097305 := by
  unfold tailWord_750764
  simp only [CollatzResearch.WordTrace]
  refine ⟨13691306326058861564085673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18255075101411815418780897 13691306326058861564085673)
  ·
    refine ⟨10268479744544146173064255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13691306326058861564085673 10268479744544146173064255)
    ·
      refine ⟨15402719616816219259596383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10268479744544146173064255 15402719616816219259596383)
      ·
        refine ⟨23104079425224328889394575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15402719616816219259596383 23104079425224328889394575)
        ·
          refine ⟨34656119137836493334091863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23104079425224328889394575 34656119137836493334091863)
          ·
            refine ⟨51984178706754740001137795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34656119137836493334091863 51984178706754740001137795)
            ·
              refine ⟨77976268060132110001706693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51984178706754740001137795 77976268060132110001706693)
              ·
                refine ⟨14620550261274770625320005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77976268060132110001706693 14620550261274770625320005)
                ·
                  refine ⟨2741353173989019492247501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14620550261274770625320005 2741353173989019492247501)
                  ·
                    refine ⟨1028007440245882309592813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2741353173989019492247501 1028007440245882309592813)
                    ·
                      refine ⟨385502790092205866097305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1028007440245882309592813 385502790092205866097305)
                      ·
                        rfl

theorem cell23_750764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_750764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750764 prefixEnd_750764 := by exact prefixLift 750764
  have htrace : WordTrace (prefixWord ++ tailWord_750764) baseStart_750764 baseEnd_750764 := by
    simpa [prefixWord, tailWord_750764, baseEnd_750764] using wordTrace_append hprefix tailTrace_750764
  have hstable : (prefixWord ++ tailWord_750764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750764).length < 2 ^ (prefixWord ++ tailWord_750764).sum := by decide
  have hdescent : baseEnd_750764 < baseStart_750764 := by decide
  rcases family_descends (prefixWord ++ tailWord_750764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750771 : List Nat := [1, 1, 1, 2, 3, 2, 5, 3, 5]
def baseStart_750771 : Nat := 118140960795 + 750771 * 2 ^ 59
def prefixEnd_750771 : Nat := 4983230072969 + 3 ^ 40 * 750771 * 2
def baseEnd_750771 : Nat := 42834042717420815412197

theorem tailTrace_750771 : CollatzResearch.WordTrace tailWord_750771 prefixEnd_750771 42834042717420815412197 := by
  unfold tailWord_750771
  simp only [CollatzResearch.WordTrace]
  refine ⟨27382867963092363323676167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18255245308728242215784111 27382867963092363323676167)
  ·
    refine ⟨41074301944638544985514251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27382867963092363323676167 41074301944638544985514251)
    ·
      refine ⟨61611452916957817478271377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41074301944638544985514251 61611452916957817478271377)
      ·
        refine ⟨46208589687718363108703533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61611452916957817478271377 46208589687718363108703533)
        ·
          refine ⟨17328221132894386165763825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46208589687718363108703533 17328221132894386165763825)
          ·
            refine ⟨12996165849670789624322869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17328221132894386165763825 12996165849670789624322869)
            ·
              refine ⟨1218390548406636527280269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12996165849670789624322869 1218390548406636527280269)
              ·
                refine ⟨456896455652488697730101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1218390548406636527280269 456896455652488697730101)
                ·
                  refine ⟨42834042717420815412197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 456896455652488697730101 42834042717420815412197)
                  ·
                    rfl

theorem cell23_750771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 5].length) (baseStart_750771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750771 prefixEnd_750771 := by exact prefixLift 750771
  have htrace : WordTrace (prefixWord ++ tailWord_750771) baseStart_750771 baseEnd_750771 := by
    simpa [prefixWord, tailWord_750771, baseEnd_750771] using wordTrace_append hprefix tailTrace_750771
  have hstable : (prefixWord ++ tailWord_750771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750771).length < 2 ^ (prefixWord ++ tailWord_750771).sum := by decide
  have hdescent : baseEnd_750771 < baseStart_750771 := by decide
  rcases family_descends (prefixWord ++ tailWord_750771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750788 : List Nat := [2, 3, 3, 1, 3, 2, 1, 1, 7]
def baseStart_750788 : Nat := 118140960795 + 750788 * 2 ^ 59
def prefixEnd_750788 : Nat := 4983230072969 + 3 ^ 40 * 750788 * 2
def baseEnd_750788 : Nat := 42835012625323752466355

theorem tailTrace_750788 : CollatzResearch.WordTrace tailWord_750788 prefixEnd_750788 42835012625323752466355 := by
  unfold tailWord_750788
  simp only [CollatzResearch.WordTrace]
  refine ⟨13691744002015387613522509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18255658669353850151363345 13691744002015387613522509)
  ·
    refine ⟨5134404000755770355070941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13691744002015387613522509 5134404000755770355070941)
    ·
      refine ⟨1925401500283413883151603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5134404000755770355070941 1925401500283413883151603)
      ·
        refine ⟨2888102250425120824727405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1925401500283413883151603 2888102250425120824727405)
        ·
          refine ⟨1083038343909420309272777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2888102250425120824727405 1083038343909420309272777)
          ·
            refine ⟨812278757932065231954583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1083038343909420309272777 812278757932065231954583)
            ·
              refine ⟨1218418136898097847931875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812278757932065231954583 1218418136898097847931875)
              ·
                refine ⟨1827627205347146771897813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1218418136898097847931875 1827627205347146771897813)
                ·
                  refine ⟨42835012625323752466355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1827627205347146771897813 42835012625323752466355)
                  ·
                    rfl

theorem cell23_750788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_750788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750788 prefixEnd_750788 := by exact prefixLift 750788
  have htrace : WordTrace (prefixWord ++ tailWord_750788) baseStart_750788 baseEnd_750788 := by
    simpa [prefixWord, tailWord_750788, baseEnd_750788] using wordTrace_append hprefix tailTrace_750788
  have hstable : (prefixWord ++ tailWord_750788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750788).length < 2 ^ (prefixWord ++ tailWord_750788).sum := by decide
  have hdescent : baseEnd_750788 < baseStart_750788 := by decide
  rcases family_descends (prefixWord ++ tailWord_750788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750794 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_750794 : Nat := 118140960795 + 750794 * 2 ^ 59
def prefixEnd_750794 : Nat := 4983230072969 + 3 ^ 40 * 750794 * 2
def baseEnd_750794 : Nat := 385518194511840748722167

theorem tailTrace_750794 : CollatzResearch.WordTrace tailWord_750794 prefixEnd_750794 385518194511840748722167 := by
  unfold tailWord_750794
  simp only [CollatzResearch.WordTrace]
  refine ⟨6845926710502259562940859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18255804561339358834508957 6845926710502259562940859)
  ·
    refine ⟨10268890065753389344411289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6845926710502259562940859 10268890065753389344411289)
    ·
      refine ⟨7701667549315042008308467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10268890065753389344411289 7701667549315042008308467)
      ·
        refine ⟨11552501323972563012462701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7701667549315042008308467 11552501323972563012462701)
        ·
          refine ⟨4332187996489711129673513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11552501323972563012462701 4332187996489711129673513)
          ·
            refine ⟨3249140997367283347255135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4332187996489711129673513 3249140997367283347255135)
            ·
              refine ⟨4873711496050925020882703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3249140997367283347255135 4873711496050925020882703)
              ·
                refine ⟨7310567244076387531324055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4873711496050925020882703 7310567244076387531324055)
                ·
                  refine ⟨10965850866114581296986083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7310567244076387531324055 10965850866114581296986083)
                  ·
                    refine ⟨16448776299171871945479125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10965850866114581296986083 16448776299171871945479125)
                    ·
                      refine ⟨385518194511840748722167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16448776299171871945479125 385518194511840748722167)
                      ·
                        rfl

theorem cell23_750794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_750794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750794 prefixEnd_750794 := by exact prefixLift 750794
  have htrace : WordTrace (prefixWord ++ tailWord_750794) baseStart_750794 baseEnd_750794 := by
    simpa [prefixWord, tailWord_750794, baseEnd_750794] using wordTrace_append hprefix tailTrace_750794
  have hstable : (prefixWord ++ tailWord_750794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750794).length < 2 ^ (prefixWord ++ tailWord_750794).sum := by decide
  have hdescent : baseEnd_750794 < baseStart_750794 := by decide
  rcases family_descends (prefixWord ++ tailWord_750794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750838 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2]
def baseStart_750838 : Nat := 118140960795 + 750838 * 2 ^ 59
def prefixEnd_750838 : Nat := 4983230072969 + 3 ^ 40 * 750838 * 2
def baseEnd_750838 : Nat := 385540787660638576571965

theorem tailTrace_750838 : CollatzResearch.WordTrace tailWord_750838 prefixEnd_750838 385540787660638576571965 := by
  unfold tailWord_750838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1711581978365602110397823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18256874435899755844243445 1711581978365602110397823)
  ·
    refine ⟨2567372967548403165596735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1711581978365602110397823 2567372967548403165596735)
    ·
      refine ⟨3851059451322604748395103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2567372967548403165596735 3851059451322604748395103)
      ·
        refine ⟨5776589176983907122592655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3851059451322604748395103 5776589176983907122592655)
        ·
          refine ⟨8664883765475860683888983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5776589176983907122592655 8664883765475860683888983)
          ·
            refine ⟨12997325648213791025833475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8664883765475860683888983 12997325648213791025833475)
            ·
              refine ⟨19495988472320686538750213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12997325648213791025833475 19495988472320686538750213)
              ·
                refine ⟨3655497838560128726015665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19495988472320686538750213 3655497838560128726015665)
                ·
                  refine ⟨2741623378920096544511749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3655497838560128726015665 2741623378920096544511749)
                  ·
                    refine ⟨514054383547518102095953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2741623378920096544511749 514054383547518102095953)
                    ·
                      refine ⟨385540787660638576571965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 514054383547518102095953 385540787660638576571965)
                      ·
                        rfl

theorem cell23_750838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_750838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750838 prefixEnd_750838 := by exact prefixLift 750838
  have htrace : WordTrace (prefixWord ++ tailWord_750838) baseStart_750838 baseEnd_750838 := by
    simpa [prefixWord, tailWord_750838, baseEnd_750838] using wordTrace_append hprefix tailTrace_750838
  have hstable : (prefixWord ++ tailWord_750838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750838).length < 2 ^ (prefixWord ++ tailWord_750838).sum := by decide
  have hdescent : baseEnd_750838 < baseStart_750838 := by decide
  rcases family_descends (prefixWord ++ tailWord_750838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750841 : List Nat := [1, 2, 1, 3, 1, 1, 3, 4, 2, 2, 3]
def baseStart_750841 : Nat := 118140960795 + 750841 * 2 ^ 59
def prefixEnd_750841 : Nat := 4983230072969 + 3 ^ 40 * 750841 * 2
def baseEnd_750841 : Nat := 385542328102602064834451

theorem tailTrace_750841 : CollatzResearch.WordTrace tailWord_750841 prefixEnd_750841 385542328102602064834451 := by
  unfold tailWord_750841
  simp only [CollatzResearch.WordTrace]
  refine ⟨27385421072838765278724377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18256947381892510185816251 27385421072838765278724377)
  ·
    refine ⟨20539065804629073959043283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27385421072838765278724377 20539065804629073959043283)
    ·
      refine ⟨30808598706943610938564925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20539065804629073959043283 30808598706943610938564925)
      ·
        refine ⟨11553224515103854101961847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30808598706943610938564925 11553224515103854101961847)
        ·
          refine ⟨17329836772655781152942771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11553224515103854101961847 17329836772655781152942771)
          ·
            refine ⟨25994755158983671729414157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17329836772655781152942771 25994755158983671729414157)
            ·
              refine ⟨9748033184618876898530309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25994755158983671729414157 9748033184618876898530309)
              ·
                refine ⟨1827756222116039418474433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9748033184618876898530309 1827756222116039418474433)
                ·
                  refine ⟨1370817166587029563855825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1827756222116039418474433 1370817166587029563855825)
                  ·
                    refine ⟨1028112874940272172891869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1370817166587029563855825 1028112874940272172891869)
                    ·
                      refine ⟨385542328102602064834451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1028112874940272172891869 385542328102602064834451)
                      ·
                        rfl

theorem cell23_750841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_750841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750841 prefixEnd_750841 := by exact prefixLift 750841
  have htrace : WordTrace (prefixWord ++ tailWord_750841) baseStart_750841 baseEnd_750841 := by
    simpa [prefixWord, tailWord_750841, baseEnd_750841] using wordTrace_append hprefix tailTrace_750841
  have hstable : (prefixWord ++ tailWord_750841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750841).length < 2 ^ (prefixWord ++ tailWord_750841).sum := by decide
  have hdescent : baseEnd_750841 < baseStart_750841 := by decide
  rcases family_descends (prefixWord ++ tailWord_750841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750882 : List Nat := [3, 3, 1, 1, 4, 1, 2, 3, 1, 4]
def baseStart_750882 : Nat := 118140960795 + 750882 * 2 ^ 59
def prefixEnd_750882 : Nat := 4983230072969 + 3 ^ 40 * 750882 * 2
def baseEnd_750882 : Nat := 128521126936478801473921

theorem tailTrace_750882 : CollatzResearch.WordTrace tailWord_750882 prefixEnd_750882 128521126936478801473921 := by
  unfold tailWord_750882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6846729116422557320241725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18257944310460152853977933 6846729116422557320241725)
  ·
    refine ⟨2567523418658458995090647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6846729116422557320241725 2567523418658458995090647)
    ·
      refine ⟨3851285127987688492635971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2567523418658458995090647 3851285127987688492635971)
      ·
        refine ⟨5776927691981532738953957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3851285127987688492635971 5776927691981532738953957)
        ·
          refine ⟨1083173942246537388553867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5776927691981532738953957 1083173942246537388553867)
          ·
            refine ⟨1624760913369806082830801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083173942246537388553867 1624760913369806082830801)
            ·
              refine ⟨1218570685027354562123101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1624760913369806082830801 1218570685027354562123101)
              ·
                refine ⟨456964006885257960796163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1218570685027354562123101 456964006885257960796163)
                ·
                  refine ⟨685446010327886941194245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456964006885257960796163 685446010327886941194245)
                  ·
                    refine ⟨128521126936478801473921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 685446010327886941194245 128521126936478801473921)
                    ·
                      rfl

theorem cell23_750882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_750882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750882 prefixEnd_750882 := by exact prefixLift 750882
  have htrace : WordTrace (prefixWord ++ tailWord_750882) baseStart_750882 baseEnd_750882 := by
    simpa [prefixWord, tailWord_750882, baseEnd_750882] using wordTrace_append hprefix tailTrace_750882
  have hstable : (prefixWord ++ tailWord_750882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750882).length < 2 ^ (prefixWord ++ tailWord_750882).sum := by decide
  have hdescent : baseEnd_750882 < baseStart_750882 := by decide
  rcases family_descends (prefixWord ++ tailWord_750882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750921 : List Nat := [1, 2, 1, 1, 2, 3, 5, 1, 1, 6]
def baseStart_750921 : Nat := 118140960795 + 750921 * 2 ^ 59
def prefixEnd_750921 : Nat := 4983230072969 + 3 ^ 40 * 750921 * 2
def baseEnd_750921 : Nat := 128527802184987250611361

theorem tailTrace_750921 : CollatzResearch.WordTrace tailWord_750921 prefixEnd_750921 128527802184987250611361 := by
  unfold tailWord_750921
  simp only [CollatzResearch.WordTrace]
  refine ⟨27388338912548938941636617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18258892608365959294424411 27388338912548938941636617)
  ·
    refine ⟨20541254184411704206227463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27388338912548938941636617 20541254184411704206227463)
    ·
      refine ⟨30811881276617556309341195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20541254184411704206227463 30811881276617556309341195)
      ·
        refine ⟨46217821914926334464011793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30811881276617556309341195 46217821914926334464011793)
        ·
          refine ⟨34663366436194750848008845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46217821914926334464011793 34663366436194750848008845)
          ·
            refine ⟨12998762413573031568003317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34663366436194750848008845 12998762413573031568003317)
            ·
              refine ⟨1218633976272471709500311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12998762413573031568003317 1218633976272471709500311)
              ·
                refine ⟨1827950964408707564250467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1218633976272471709500311 1827950964408707564250467)
                ·
                  refine ⟨2741926446613061346375701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1827950964408707564250467 2741926446613061346375701)
                  ·
                    refine ⟨128527802184987250611361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2741926446613061346375701 128527802184987250611361)
                    ·
                      rfl

theorem cell23_750921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 6].length) (baseStart_750921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750921 prefixEnd_750921 := by exact prefixLift 750921
  have htrace : WordTrace (prefixWord ++ tailWord_750921) baseStart_750921 baseEnd_750921 := by
    simpa [prefixWord, tailWord_750921, baseEnd_750921] using wordTrace_append hprefix tailTrace_750921
  have hstable : (prefixWord ++ tailWord_750921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750921).length < 2 ^ (prefixWord ++ tailWord_750921).sum := by decide
  have hdescent : baseEnd_750921 < baseStart_750921 := by decide
  rcases family_descends (prefixWord ++ tailWord_750921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750928 : List Nat := [2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 4]
def baseStart_750928 : Nat := 118140960795 + 750928 * 2 ^ 59
def prefixEnd_750928 : Nat := 4983230072969 + 3 ^ 40 * 750928 * 2
def baseEnd_750928 : Nat := 385587000919543224446551

theorem tailTrace_750928 : CollatzResearch.WordTrace tailWord_750928 prefixEnd_750928 385587000919543224446551 := by
  unfold tailWord_750928
  simp only [CollatzResearch.WordTrace]
  refine ⟨13694297111761789568570719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18259062815682386091427625 13694297111761789568570719)
  ·
    refine ⟨20541445667642684352856079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13694297111761789568570719 20541445667642684352856079)
    ·
      refine ⟨30812168501464026529284119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20541445667642684352856079 30812168501464026529284119)
      ·
        refine ⟨46218252752196039793926179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30812168501464026529284119 46218252752196039793926179)
        ·
          refine ⟨69327379128294059690889269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46218252752196039793926179 69327379128294059690889269)
          ·
            refine ⟨6499441793277568096020869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69327379128294059690889269 6499441793277568096020869)
            ·
              refine ⟨1218645336239544018003913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6499441793277568096020869 1218645336239544018003913)
              ·
                refine ⟨913984002179658013502935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1218645336239544018003913 913984002179658013502935)
                ·
                  refine ⟨1370976003269487020254403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 913984002179658013502935 1370976003269487020254403)
                  ·
                    refine ⟨2056464004904230530381605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1370976003269487020254403 2056464004904230530381605)
                    ·
                      refine ⟨385587000919543224446551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2056464004904230530381605 385587000919543224446551)
                      ·
                        rfl

theorem cell23_750928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 4].length) (baseStart_750928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750928 prefixEnd_750928 := by exact prefixLift 750928
  have htrace : WordTrace (prefixWord ++ tailWord_750928) baseStart_750928 baseEnd_750928 := by
    simpa [prefixWord, tailWord_750928, baseEnd_750928] using wordTrace_append hprefix tailTrace_750928
  have hstable : (prefixWord ++ tailWord_750928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750928).length < 2 ^ (prefixWord ++ tailWord_750928).sum := by decide
  have hdescent : baseEnd_750928 < baseStart_750928 := by decide
  rcases family_descends (prefixWord ++ tailWord_750928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750948 : List Nat := [2, 3, 1, 1, 3, 3, 2, 1, 1, 1, 5]
def baseStart_750948 : Nat := 118140960795 + 750948 * 2 ^ 59
def prefixEnd_750948 : Nat := 4983230072969 + 3 ^ 40 * 750948 * 2
def baseEnd_750948 : Nat := 385597270532633146196459

theorem tailTrace_750948 : CollatzResearch.WordTrace tailWord_750948 prefixEnd_750948 385597270532633146196459 := by
  unfold tailWord_750948
  simp only [CollatzResearch.WordTrace]
  refine ⟨13694661841725561276434749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18259549122300748368579665 13694661841725561276434749)
  ·
    refine ⟨5135498190647085478663031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13694661841725561276434749 5135498190647085478663031)
    ·
      refine ⟨7703247285970628217994547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5135498190647085478663031 7703247285970628217994547)
      ·
        refine ⟨11554870928955942326991821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7703247285970628217994547 11554870928955942326991821)
        ·
          refine ⟨4333076598358478372621933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11554870928955942326991821 4333076598358478372621933)
          ·
            refine ⟨1624903724384429389733225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4333076598358478372621933 1624903724384429389733225)
            ·
              refine ⟨1218677793288322042299919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1624903724384429389733225 1218677793288322042299919)
              ·
                refine ⟨1828016689932483063449879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1218677793288322042299919 1828016689932483063449879)
                ·
                  refine ⟨2742025034898724595174819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1828016689932483063449879 2742025034898724595174819)
                  ·
                    refine ⟨4113037552348086892762229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2742025034898724595174819 4113037552348086892762229)
                    ·
                      refine ⟨385597270532633146196459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4113037552348086892762229 385597270532633146196459)
                      ·
                        rfl

theorem cell23_750948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_750948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_750948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_750948 prefixEnd_750948 := by exact prefixLift 750948
  have htrace : WordTrace (prefixWord ++ tailWord_750948) baseStart_750948 baseEnd_750948 := by
    simpa [prefixWord, tailWord_750948, baseEnd_750948] using wordTrace_append hprefix tailTrace_750948
  have hstable : (prefixWord ++ tailWord_750948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750948).length < 2 ^ (prefixWord ++ tailWord_750948).sum := by decide
  have hdescent : baseEnd_750948 < baseStart_750948 := by decide
  rcases family_descends (prefixWord ++ tailWord_750948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751011 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 2, 6]
def baseStart_751011 : Nat := 118140960795 + 751011 * 2 ^ 59
def prefixEnd_751011 : Nat := 4983230072969 + 3 ^ 40 * 751011 * 2
def baseEnd_751011 : Nat := 128543206604622133236223

theorem tailTrace_751011 : CollatzResearch.WordTrace tailWord_751011 prefixEnd_751011 128543206604622133236223 := by
  unfold tailWord_751011
  simp only [CollatzResearch.WordTrace]
  refine ⟨27391621482222884312412887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18261080988148589541608591 27391621482222884312412887)
  ·
    refine ⟨41087432223334326468619331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27391621482222884312412887 41087432223334326468619331)
    ·
      refine ⟨61631148335001489702928997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41087432223334326468619331 61631148335001489702928997)
      ·
        refine ⟨11555840312812779319299187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61631148335001489702928997 11555840312812779319299187)
        ·
          refine ⟨17333760469219168978948781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11555840312812779319299187 17333760469219168978948781)
          ·
            refine ⟨6500160175957188367105793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17333760469219168978948781 6500160175957188367105793)
            ·
              refine ⟨4875120131967891275329345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6500160175957188367105793 4875120131967891275329345)
              ·
                refine ⟨3656340098975918456497009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4875120131967891275329345 3656340098975918456497009)
                ·
                  refine ⟨2742255074231938842372757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3656340098975918456497009 2742255074231938842372757)
                  ·
                    refine ⟨128543206604622133236223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2742255074231938842372757 128543206604622133236223)
                    ·
                      rfl

theorem cell23_751011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 6].length) (baseStart_751011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751011 prefixEnd_751011 := by exact prefixLift 751011
  have htrace : WordTrace (prefixWord ++ tailWord_751011) baseStart_751011 baseEnd_751011 := by
    simpa [prefixWord, tailWord_751011, baseEnd_751011] using wordTrace_append hprefix tailTrace_751011
  have hstable : (prefixWord ++ tailWord_751011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751011).length < 2 ^ (prefixWord ++ tailWord_751011).sum := by decide
  have hdescent : baseEnd_751011 < baseStart_751011 := by decide
  rcases family_descends (prefixWord ++ tailWord_751011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751038 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_751038 : Nat := 118140960795 + 751038 * 2 ^ 59
def prefixEnd_751038 : Nat := 4983230072969 + 3 ^ 40 * 751038 * 2
def baseEnd_751038 : Nat := 385643483791537794071045

theorem tailTrace_751038 : CollatzResearch.WordTrace tailWord_751038 prefixEnd_751038 385643483791537794071045 := by
  unfold tailWord_751038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3424075781640633490455721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18261737502083378615763845 3424075781640633490455721)
  ·
    refine ⟨2568056836230475117841791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3424075781640633490455721 2568056836230475117841791)
    ·
      refine ⟨3852085254345712676762687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2568056836230475117841791 3852085254345712676762687)
      ·
        refine ⟨5778127881518569015144031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3852085254345712676762687 5778127881518569015144031)
        ·
          refine ⟨8667191822277853522716047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5778127881518569015144031 8667191822277853522716047)
          ·
            refine ⟨13000787733416780284074071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8667191822277853522716047 13000787733416780284074071)
            ·
              refine ⟨19501181600125170426111107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13000787733416780284074071 19501181600125170426111107)
              ·
                refine ⟨29251772400187755639166661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19501181600125170426111107 29251772400187755639166661)
                ·
                  refine ⟨5484707325035204182343749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29251772400187755639166661 5484707325035204182343749)
                  ·
                    refine ⟨1028382623444100784189453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5484707325035204182343749 1028382623444100784189453)
                    ·
                      refine ⟨385643483791537794071045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1028382623444100784189453 385643483791537794071045)
                      ·
                        rfl

theorem cell23_751038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_751038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751038 prefixEnd_751038 := by exact prefixLift 751038
  have htrace : WordTrace (prefixWord ++ tailWord_751038) baseStart_751038 baseEnd_751038 := by
    simpa [prefixWord, tailWord_751038, baseEnd_751038] using wordTrace_append hprefix tailTrace_751038
  have hstable : (prefixWord ++ tailWord_751038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751038).length < 2 ^ (prefixWord ++ tailWord_751038).sum := by decide
  have hdescent : baseEnd_751038 < baseStart_751038 := by decide
  rcases family_descends (prefixWord ++ tailWord_751038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751069 : List Nat := [1, 4, 3, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_751069 : Nat := 118140960795 + 751069 * 2 ^ 59
def prefixEnd_751069 : Nat := 4983230072969 + 3 ^ 40 * 751069 * 2
def baseEnd_751069 : Nat := 385659401691827172783403

theorem tailTrace_751069 : CollatzResearch.WordTrace tailWord_751069 prefixEnd_751069 385659401691827172783403 := by
  unfold tailWord_751069
  simp only [CollatzResearch.WordTrace]
  refine ⟨27393736916012760218024261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18262491277341840145349507 27393736916012760218024261)
  ·
    refine ⟨5136325671752392540879549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27393736916012760218024261 5136325671752392540879549)
    ·
      refine ⟨1926122126907147202829831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5136325671752392540879549 1926122126907147202829831)
      ·
        refine ⟨2889183190360720804244747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1926122126907147202829831 2889183190360720804244747)
        ·
          refine ⟨4333774785541081206367121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2889183190360720804244747 4333774785541081206367121)
          ·
            refine ⟨3250331089155810904775341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4333774785541081206367121 3250331089155810904775341)
            ·
              refine ⟨1218874158433429089290753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3250331089155810904775341 1218874158433429089290753)
              ·
                refine ⟨914155618825071816968065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1218874158433429089290753 914155618825071816968065)
                ·
                  refine ⟨685616714118803862726049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 914155618825071816968065 685616714118803862726049)
                  ·
                    refine ⟨514212535589102897044537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 685616714118803862726049 514212535589102897044537)
                    ·
                      refine ⟨385659401691827172783403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 514212535589102897044537 385659401691827172783403)
                      ·
                        rfl

theorem cell23_751069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_751069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751069 prefixEnd_751069 := by exact prefixLift 751069
  have htrace : WordTrace (prefixWord ++ tailWord_751069) baseStart_751069 baseEnd_751069 := by
    simpa [prefixWord, tailWord_751069, baseEnd_751069] using wordTrace_append hprefix tailTrace_751069
  have hstable : (prefixWord ++ tailWord_751069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751069).length < 2 ^ (prefixWord ++ tailWord_751069).sum := by decide
  have hdescent : baseEnd_751069 < baseStart_751069 := by decide
  rcases family_descends (prefixWord ++ tailWord_751069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751075 : List Nat := [1, 1, 1, 6, 2, 1, 2, 4, 5]
def baseStart_751075 : Nat := 118140960795 + 751075 * 2 ^ 59
def prefixEnd_751075 : Nat := 4983230072969 + 3 ^ 40 * 751075 * 2
def baseEnd_751075 : Nat := 42851386952861572145375

theorem tailTrace_751075 : CollatzResearch.WordTrace tailWord_751075 prefixEnd_751075 42851386952861572145375 := by
  unfold tailWord_751075
  simp only [CollatzResearch.WordTrace]
  refine ⟨27393955753991023242742679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18262637169327348828495119 27393955753991023242742679)
  ·
    refine ⟨41090933630986534864114019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27393955753991023242742679 41090933630986534864114019)
    ·
      refine ⟨61636400446479802296171029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41090933630986534864114019 61636400446479802296171029)
      ·
        refine ⟨2889206270928740732633017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61636400446479802296171029 2889206270928740732633017)
        ·
          refine ⟨2166904703196555549474763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2889206270928740732633017 2166904703196555549474763)
          ·
            refine ⟨3250357054794833324212145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2166904703196555549474763 3250357054794833324212145)
            ·
              refine ⟨2437767791096124993159109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3250357054794833324212145 2437767791096124993159109)
              ·
                refine ⟨457081460830523436217333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2437767791096124993159109 457081460830523436217333)
                ·
                  refine ⟨42851386952861572145375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 457081460830523436217333 42851386952861572145375)
                  ·
                    rfl

theorem cell23_751075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 5].length) (baseStart_751075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751075 prefixEnd_751075 := by exact prefixLift 751075
  have htrace : WordTrace (prefixWord ++ tailWord_751075) baseStart_751075 baseEnd_751075 := by
    simpa [prefixWord, tailWord_751075, baseEnd_751075] using wordTrace_append hprefix tailTrace_751075
  have hstable : (prefixWord ++ tailWord_751075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751075).length < 2 ^ (prefixWord ++ tailWord_751075).sum := by decide
  have hdescent : baseEnd_751075 < baseStart_751075 := by decide
  rcases family_descends (prefixWord ++ tailWord_751075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751081 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 5, 2, 5]
def baseStart_751081 : Nat := 118140960795 + 751081 * 2 ^ 59
def prefixEnd_751081 : Nat := 4983230072969 + 3 ^ 40 * 751081 * 2
def baseEnd_751081 : Nat := 385665563459681125833347

theorem tailTrace_751081 : CollatzResearch.WordTrace tailWord_751081 prefixEnd_751081 385665563459681125833347 := by
  unfold tailWord_751081
  simp only [CollatzResearch.WordTrace]
  refine ⟨27394174591969286267461097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18262783061312857511640731 27394174591969286267461097)
  ·
    refine ⟨20545630943976964700595823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27394174591969286267461097 20545630943976964700595823)
    ·
      refine ⟨30818446415965447050893735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20545630943976964700595823 30818446415965447050893735)
      ·
        refine ⟨46227669623948170576340603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30818446415965447050893735 46227669623948170576340603)
        ·
          refine ⟨69341504435922255864510905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46227669623948170576340603 69341504435922255864510905)
          ·
            refine ⟨52006128326941691898383179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69341504435922255864510905 52006128326941691898383179)
            ·
              refine ⟨78009192490412537847574769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52006128326941691898383179 78009192490412537847574769)
              ·
                refine ⟨58506894367809403385681077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78009192490412537847574769 58506894367809403385681077)
                ·
                  refine ⟨5485021346982131567407601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58506894367809403385681077 5485021346982131567407601)
                  ·
                    refine ⟨4113766010236598675555701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5485021346982131567407601 4113766010236598675555701)
                    ·
                      refine ⟨385665563459681125833347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4113766010236598675555701 385665563459681125833347)
                      ·
                        rfl

theorem cell23_751081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_751081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751081 prefixEnd_751081 := by exact prefixLift 751081
  have htrace : WordTrace (prefixWord ++ tailWord_751081) baseStart_751081 baseEnd_751081 := by
    simpa [prefixWord, tailWord_751081, baseEnd_751081] using wordTrace_append hprefix tailTrace_751081
  have hstable : (prefixWord ++ tailWord_751081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751081).length < 2 ^ (prefixWord ++ tailWord_751081).sum := by decide
  have hdescent : baseEnd_751081 < baseStart_751081 := by decide
  rcases family_descends (prefixWord ++ tailWord_751081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751125 : List Nat := [1, 3, 2, 1, 3, 3, 1, 2, 2, 1, 4]
def baseStart_751125 : Nat := 118140960795 + 751125 * 2 ^ 59
def prefixEnd_751125 : Nat := 4983230072969 + 3 ^ 40 * 751125 * 2
def baseEnd_751125 : Nat := 385688156608478953683145

theorem tailTrace_751125 : CollatzResearch.WordTrace tailWord_751125 prefixEnd_751125 385688156608478953683145 := by
  unfold tailWord_751125
  simp only [CollatzResearch.WordTrace]
  refine ⟨27395779403809881782062829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18263852935873254521375219 27395779403809881782062829)
  ·
    refine ⟨10273417276428705668273561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27395779403809881782062829 10273417276428705668273561)
    ·
      refine ⟨7705062957321529251205171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10273417276428705668273561 7705062957321529251205171)
      ·
        refine ⟨11557594435982293876807757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7705062957321529251205171 11557594435982293876807757)
        ·
          refine ⟨4334097913493360203802909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11557594435982293876807757 4334097913493360203802909)
          ·
            refine ⟨1625286717560010076426091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4334097913493360203802909 1625286717560010076426091)
            ·
              refine ⟨2437930076340015114639137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1625286717560010076426091 2437930076340015114639137)
              ·
                refine ⟨1828447557255011335979353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2437930076340015114639137 1828447557255011335979353)
                ·
                  refine ⟨1371335667941258501984515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1828447557255011335979353 1371335667941258501984515)
                  ·
                    refine ⟨2057003501911887752976773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1371335667941258501984515 2057003501911887752976773)
                    ·
                      refine ⟨385688156608478953683145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2057003501911887752976773 385688156608478953683145)
                      ·
                        rfl

theorem cell23_751125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_751125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751125 prefixEnd_751125 := by exact prefixLift 751125
  have htrace : WordTrace (prefixWord ++ tailWord_751125) baseStart_751125 baseEnd_751125 := by
    simpa [prefixWord, tailWord_751125, baseEnd_751125] using wordTrace_append hprefix tailTrace_751125
  have hstable : (prefixWord ++ tailWord_751125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751125).length < 2 ^ (prefixWord ++ tailWord_751125).sum := by decide
  have hdescent : baseEnd_751125 < baseStart_751125 := by decide
  rcases family_descends (prefixWord ++ tailWord_751125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751135 : List Nat := [1, 1, 2, 4, 1, 1, 5, 1, 3, 4]
def baseStart_751135 : Nat := 118140960795 + 751135 * 2 ^ 59
def prefixEnd_751135 : Nat := 4983230072969 + 3 ^ 40 * 751135 * 2
def baseEnd_751135 : Nat := 128564430471674638186033

theorem tailTrace_751135 : CollatzResearch.WordTrace tailWord_751135 prefixEnd_751135 128564430471674638186033 := by
  unfold tailWord_751135
  simp only [CollatzResearch.WordTrace]
  refine ⟨27396144133773653489926859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18264096089182435659951239 27396144133773653489926859)
  ·
    refine ⟨41094216200660480234890289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27396144133773653489926859 41094216200660480234890289)
    ·
      refine ⟨30820662150495360176167717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41094216200660480234890289 30820662150495360176167717)
      ·
        refine ⟨5778874153217880033031447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30820662150495360176167717 5778874153217880033031447)
        ·
          refine ⟨8668311229826820049547171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5778874153217880033031447 8668311229826820049547171)
          ·
            refine ⟨13002466844740230074320757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8668311229826820049547171 13002466844740230074320757)
            ·
              refine ⟨1218981266694396569467571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13002466844740230074320757 1218981266694396569467571)
              ·
                refine ⟨1828471900041594854201357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1218981266694396569467571 1828471900041594854201357)
                ·
                  refine ⟨685676962515598070325509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1828471900041594854201357 685676962515598070325509)
                  ·
                    refine ⟨128564430471674638186033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 685676962515598070325509 128564430471674638186033)
                    ·
                      rfl

theorem cell23_751135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 4].length) (baseStart_751135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751135 prefixEnd_751135 := by exact prefixLift 751135
  have htrace : WordTrace (prefixWord ++ tailWord_751135) baseStart_751135 baseEnd_751135 := by
    simpa [prefixWord, tailWord_751135, baseEnd_751135] using wordTrace_append hprefix tailTrace_751135
  have hstable : (prefixWord ++ tailWord_751135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751135).length < 2 ^ (prefixWord ++ tailWord_751135).sum := by decide
  have hdescent : baseEnd_751135 < baseStart_751135 := by decide
  rcases family_descends (prefixWord ++ tailWord_751135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751138 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_751138 : Nat := 118140960795 + 751138 * 2 ^ 59
def prefixEnd_751138 : Nat := 4983230072969 + 3 ^ 40 * 751138 * 2
def baseEnd_751138 : Nat := 385694831856987402820585

theorem tailTrace_751138 : CollatzResearch.WordTrace tailWord_751138 prefixEnd_751138 385694831856987402820585 := by
  unfold tailWord_751138
  simp only [CollatzResearch.WordTrace]
  refine ⟨6849063388190696250571517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18264169035175190001524045 6849063388190696250571517)
  ·
    refine ⟨2568398770571511093964319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6849063388190696250571517 2568398770571511093964319)
    ·
      refine ⟨3852598155857266640946479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2568398770571511093964319 3852598155857266640946479)
      ·
        refine ⟨5778897233785899961419719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3852598155857266640946479 5778897233785899961419719)
        ·
          refine ⟨8668345850678849942129579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5778897233785899961419719 8668345850678849942129579)
          ·
            refine ⟨13002518776018274913194369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8668345850678849942129579 13002518776018274913194369)
            ·
              refine ⟨9751889082013706184895777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13002518776018274913194369 9751889082013706184895777)
              ·
                refine ⟨7313916811510279638671833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9751889082013706184895777 7313916811510279638671833)
                ·
                  refine ⟨5485437608632709729003875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7313916811510279638671833 5485437608632709729003875)
                  ·
                    refine ⟨8228156412949064593505813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5485437608632709729003875 8228156412949064593505813)
                    ·
                      refine ⟨385694831856987402820585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8228156412949064593505813 385694831856987402820585)
                      ·
                        rfl

theorem cell23_751138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_751138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751138 prefixEnd_751138 := by exact prefixLift 751138
  have htrace : WordTrace (prefixWord ++ tailWord_751138) baseStart_751138 baseEnd_751138 := by
    simpa [prefixWord, tailWord_751138, baseEnd_751138] using wordTrace_append hprefix tailTrace_751138
  have hstable : (prefixWord ++ tailWord_751138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751138).length < 2 ^ (prefixWord ++ tailWord_751138).sum := by decide
  have hdescent : baseEnd_751138 < baseStart_751138 := by decide
  rcases family_descends (prefixWord ++ tailWord_751138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751186 : List Nat := [3, 2, 2, 1, 2, 4, 2, 2, 1, 4]
def baseStart_751186 : Nat := 118140960795 + 751186 * 2 ^ 59
def prefixEnd_751186 : Nat := 4983230072969 + 3 ^ 40 * 751186 * 2
def baseEnd_751186 : Nat := 128573159642801071673455

theorem tailTrace_751186 : CollatzResearch.WordTrace tailWord_751186 prefixEnd_751186 128573159642801071673455 := by
  unfold tailWord_751186
  simp only [CollatzResearch.WordTrace]
  refine ⟨6849501064147222300008353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18265336171059259466688941 6849501064147222300008353)
  ·
    refine ⟨5137125798110416725006265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6849501064147222300008353 5137125798110416725006265)
    ·
      refine ⟨3852844348582812543754699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5137125798110416725006265 3852844348582812543754699)
      ·
        refine ⟨5779266522874218815632049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3852844348582812543754699 5779266522874218815632049)
        ·
          refine ⟨4334449892155664111724037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5779266522874218815632049 4334449892155664111724037)
          ·
            refine ⟨812709354779187020948257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4334449892155664111724037 812709354779187020948257)
            ·
              refine ⟨609532016084390265711193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 812709354779187020948257 609532016084390265711193)
              ·
                refine ⟨457149012063292699283395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 609532016084390265711193 457149012063292699283395)
                ·
                  refine ⟨685723518094939048925093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 457149012063292699283395 685723518094939048925093)
                  ·
                    refine ⟨128573159642801071673455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 685723518094939048925093 128573159642801071673455)
                    ·
                      rfl

theorem cell23_751186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_751186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751186 prefixEnd_751186 := by exact prefixLift 751186
  have htrace : WordTrace (prefixWord ++ tailWord_751186) baseStart_751186 baseEnd_751186 := by
    simpa [prefixWord, tailWord_751186, baseEnd_751186] using wordTrace_append hprefix tailTrace_751186
  have hstable : (prefixWord ++ tailWord_751186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751186).length < 2 ^ (prefixWord ++ tailWord_751186).sum := by decide
  have hdescent : baseEnd_751186 < baseStart_751186 := by decide
  rcases family_descends (prefixWord ++ tailWord_751186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751215 : List Nat := [1, 1, 2, 1, 3, 2, 1, 6, 1, 1, 4]
def baseStart_751215 : Nat := 118140960795 + 751215 * 2 ^ 59
def prefixEnd_751215 : Nat := 4983230072969 + 3 ^ 40 * 751215 * 2
def baseEnd_751215 : Nat := 385734369867383601557731

theorem tailTrace_751215 : CollatzResearch.WordTrace tailWord_751215 prefixEnd_751215 385734369867383601557731 := by
  unfold tailWord_751215
  simp only [CollatzResearch.WordTrace]
  refine ⟨27399061973483827152839099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18266041315655884768559399 27399061973483827152839099)
  ·
    refine ⟨41098592960225740729258649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27399061973483827152839099 41098592960225740729258649)
    ·
      refine ⟨30823944720169305546943987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41098592960225740729258649 30823944720169305546943987)
      ·
        refine ⟨46235917080253958320415981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30823944720169305546943987 46235917080253958320415981)
        ·
          refine ⟨17338468905095234370155993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46235917080253958320415981 17338468905095234370155993)
          ·
            refine ⟨13003851678821425777616995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17338468905095234370155993 13003851678821425777616995)
            ·
              refine ⟨19505777518232138666425493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13003851678821425777616995 19505777518232138666425493)
              ·
                refine ⟨914333321167131499988695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19505777518232138666425493 914333321167131499988695)
                ·
                  refine ⟨1371499981750697249983043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 914333321167131499988695 1371499981750697249983043)
                  ·
                    refine ⟨2057249972626045874974565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1371499981750697249983043 2057249972626045874974565)
                    ·
                      refine ⟨385734369867383601557731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2057249972626045874974565 385734369867383601557731)
                      ·
                        rfl

theorem cell23_751215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 1, 4].length) (baseStart_751215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751215 prefixEnd_751215 := by exact prefixLift 751215
  have htrace : WordTrace (prefixWord ++ tailWord_751215) baseStart_751215 baseEnd_751215 := by
    simpa [prefixWord, tailWord_751215, baseEnd_751215] using wordTrace_append hprefix tailTrace_751215
  have hstable : (prefixWord ++ tailWord_751215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751215).length < 2 ^ (prefixWord ++ tailWord_751215).sum := by decide
  have hdescent : baseEnd_751215 < baseStart_751215 := by decide
  rcases family_descends (prefixWord ++ tailWord_751215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751225 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 4, 4]
def baseStart_751225 : Nat := 118140960795 + 751225 * 2 ^ 59
def prefixEnd_751225 : Nat := 4983230072969 + 3 ^ 40 * 751225 * 2
def baseEnd_751225 : Nat := 128579834891309520810895

theorem tailTrace_751225 : CollatzResearch.WordTrace tailWord_751225 prefixEnd_751225 128579834891309520810895 := by
  unfold tailWord_751225
  simp only [CollatzResearch.WordTrace]
  refine ⟨27399426703447598860703129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18266284468965065907135419 27399426703447598860703129)
  ·
    refine ⟨20549570027585699145527347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27399426703447598860703129 20549570027585699145527347)
    ·
      refine ⟨30824355041378548718291021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20549570027585699145527347 30824355041378548718291021)
      ·
        refine ⟨11559133140516955769359133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30824355041378548718291021 11559133140516955769359133)
        ·
          refine ⟨4334674927693858413509675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11559133140516955769359133 4334674927693858413509675)
          ·
            refine ⟨6502012391540787620264513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4334674927693858413509675 6502012391540787620264513)
            ·
              refine ⟨4876509293655590715198385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6502012391540787620264513 4876509293655590715198385)
              ·
                refine ⟨3657381970241693036398789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4876509293655590715198385 3657381970241693036398789)
                ·
                  refine ⟨685759119420317444324773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3657381970241693036398789 685759119420317444324773)
                  ·
                    refine ⟨128579834891309520810895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 685759119420317444324773 128579834891309520810895)
                    ·
                      rfl

theorem cell23_751225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 4].length) (baseStart_751225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751225 prefixEnd_751225 := by exact prefixLift 751225
  have htrace : WordTrace (prefixWord ++ tailWord_751225) baseStart_751225 baseEnd_751225 := by
    simpa [prefixWord, tailWord_751225, baseEnd_751225] using wordTrace_append hprefix tailTrace_751225
  have hstable : (prefixWord ++ tailWord_751225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751225).length < 2 ^ (prefixWord ++ tailWord_751225).sum := by decide
  have hdescent : baseEnd_751225 < baseStart_751225 := by decide
  rcases family_descends (prefixWord ++ tailWord_751225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751228 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_751228 : Nat := 118140960795 + 751228 * 2 ^ 59
def prefixEnd_751228 : Nat := 4983230072969 + 3 ^ 40 * 751228 * 2
def baseEnd_751228 : Nat := 385741045115892050695171

theorem tailTrace_751228 : CollatzResearch.WordTrace tailWord_751228 prefixEnd_751228 385741045115892050695171 := by
  unfold tailWord_751228
  simp only [CollatzResearch.WordTrace]
  refine ⟨13699768061218365186531169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18266357414957820248708225 13699768061218365186531169)
  ·
    refine ⟨10274826045913773889898377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13699768061218365186531169 10274826045913773889898377)
    ·
      refine ⟨7706119534435330417423783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10274826045913773889898377 7706119534435330417423783)
      ·
        refine ⟨11559179301652995626135675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7706119534435330417423783 11559179301652995626135675)
        ·
          refine ⟨17338768952479493439203513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11559179301652995626135675 17338768952479493439203513)
          ·
            refine ⟨13004076714359620079402635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17338768952479493439203513 13004076714359620079402635)
            ·
              refine ⟨19506115071539430119103953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13004076714359620079402635 19506115071539430119103953)
              ·
                refine ⟨14629586303654572589327965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19506115071539430119103953 14629586303654572589327965)
                ·
                  refine ⟨5486094863870464720997987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14629586303654572589327965 5486094863870464720997987)
                  ·
                    refine ⟨8229142295805697081496981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5486094863870464720997987 8229142295805697081496981)
                    ·
                      refine ⟨385741045115892050695171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8229142295805697081496981 385741045115892050695171)
                      ·
                        rfl

theorem cell23_751228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_751228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751228 prefixEnd_751228 := by exact prefixLift 751228
  have htrace : WordTrace (prefixWord ++ tailWord_751228) baseStart_751228 baseEnd_751228 := by
    simpa [prefixWord, tailWord_751228, baseEnd_751228] using wordTrace_append hprefix tailTrace_751228
  have hstable : (prefixWord ++ tailWord_751228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751228).length < 2 ^ (prefixWord ++ tailWord_751228).sum := by decide
  have hdescent : baseEnd_751228 < baseStart_751228 := by decide
  rcases family_descends (prefixWord ++ tailWord_751228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751229 : List Nat := [1, 4, 1, 1, 4, 3, 2, 1, 1, 5]
def baseStart_751229 : Nat := 118140960795 + 751229 * 2 ^ 59
def prefixEnd_751229 : Nat := 4983230072969 + 3 ^ 40 * 751229 * 2
def baseEnd_751229 : Nat := 128580519532182182260889

theorem tailTrace_751229 : CollatzResearch.WordTrace tailWord_751229 prefixEnd_751229 128580519532182182260889 := by
  unfold tailWord_751229
  simp only [CollatzResearch.WordTrace]
  refine ⟨27399572595433107543848741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18266381730288738362565827 27399572595433107543848741)
  ·
    refine ⟨5137419861643707664471639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27399572595433107543848741 5137419861643707664471639)
    ·
      refine ⟨7706129792465561496707459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5137419861643707664471639 7706129792465561496707459)
      ·
        refine ⟨11559194688698342245061189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7706129792465561496707459 11559194688698342245061189)
        ·
          refine ⟨2167349004130939170948973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11559194688698342245061189 2167349004130939170948973)
          ·
            refine ⟨812755876549102189105865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2167349004130939170948973 812755876549102189105865)
            ·
              refine ⟨609566907411826641829399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 812755876549102189105865 609566907411826641829399)
              ·
                refine ⟨914350361117739962744099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 609566907411826641829399 914350361117739962744099)
                ·
                  refine ⟨1371525541676609944116149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 914350361117739962744099 1371525541676609944116149)
                  ·
                    refine ⟨128580519532182182260889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1371525541676609944116149 128580519532182182260889)
                    ·
                      rfl

theorem cell23_751229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_751229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751229 prefixEnd_751229 := by exact prefixLift 751229
  have htrace : WordTrace (prefixWord ++ tailWord_751229) baseStart_751229 baseEnd_751229 := by
    simpa [prefixWord, tailWord_751229, baseEnd_751229] using wordTrace_append hprefix tailTrace_751229
  have hstable : (prefixWord ++ tailWord_751229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751229).length < 2 ^ (prefixWord ++ tailWord_751229).sum := by decide
  have hdescent : baseEnd_751229 < baseStart_751229 := by decide
  rcases family_descends (prefixWord ++ tailWord_751229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751232 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 5, 2, 2]
def baseStart_751232 : Nat := 118140960795 + 751232 * 2 ^ 59
def prefixEnd_751232 : Nat := 4983230072969 + 3 ^ 40 * 751232 * 2
def baseEnd_751232 : Nat := 385743099038510035045153

theorem tailTrace_751232 : CollatzResearch.WordTrace tailWord_751232 prefixEnd_751232 385743099038510035045153 := by
  unfold tailWord_751232
  simp only [CollatzResearch.WordTrace]
  refine ⟨13699841007211119528103975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18266454676281492704138633 13699841007211119528103975)
  ·
    refine ⟨20549761510816679292155963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13699841007211119528103975 20549761510816679292155963)
    ·
      refine ⟨30824642266225018938233945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20549761510816679292155963 30824642266225018938233945)
      ·
        refine ⟨23118481699668764203675459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30824642266225018938233945 23118481699668764203675459)
        ·
          refine ⟨34677722549503146305513189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23118481699668764203675459 34677722549503146305513189)
          ·
            refine ⟨6502072978031839932283723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34677722549503146305513189 6502072978031839932283723)
            ·
              refine ⟨9753109467047759898425585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6502072978031839932283723 9753109467047759898425585)
              ·
                refine ⟨7314832100285819923819189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9753109467047759898425585 7314832100285819923819189)
                ·
                  refine ⟨685765509401795617858049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7314832100285819923819189 685765509401795617858049)
                  ·
                    refine ⟨514324132051346713393537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 685765509401795617858049 514324132051346713393537)
                    ·
                      refine ⟨385743099038510035045153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 514324132051346713393537 385743099038510035045153)
                      ·
                        rfl

theorem cell23_751232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 5, 2, 2].length) (baseStart_751232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751232 prefixEnd_751232 := by exact prefixLift 751232
  have htrace : WordTrace (prefixWord ++ tailWord_751232) baseStart_751232 baseEnd_751232 := by
    simpa [prefixWord, tailWord_751232, baseEnd_751232] using wordTrace_append hprefix tailTrace_751232
  have hstable : (prefixWord ++ tailWord_751232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751232).length < 2 ^ (prefixWord ++ tailWord_751232).sum := by decide
  have hdescent : baseEnd_751232 < baseStart_751232 := by decide
  rcases family_descends (prefixWord ++ tailWord_751232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751242 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 4, 4]
def baseStart_751242 : Nat := 118140960795 + 751242 * 2 ^ 59
def prefixEnd_751242 : Nat := 4983230072969 + 3 ^ 40 * 751242 * 2
def baseEnd_751242 : Nat := 128582744615018331973369

theorem tailTrace_751242 : CollatzResearch.WordTrace tailWord_751242 prefixEnd_751242 128582744615018331973369 := by
  unfold tailWord_751242
  simp only [CollatzResearch.WordTrace]
  refine ⟨6850011686096502691017995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18266697829590673842714653 6850011686096502691017995)
  ·
    refine ⟨10275017529144754036526993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6850011686096502691017995 10275017529144754036526993)
    ·
      refine ⟨7706263146858565527395245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10275017529144754036526993 7706263146858565527395245)
      ·
        refine ⟨2889848680071962072773217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7706263146858565527395245 2889848680071962072773217)
        ·
          refine ⟨2167386510053971554579913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2889848680071962072773217 2167386510053971554579913)
          ·
            refine ⟨1625539882540478665934935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2167386510053971554579913 1625539882540478665934935)
            ·
              refine ⟨2438309823810717998902403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1625539882540478665934935 2438309823810717998902403)
              ·
                refine ⟨3657464735716076998353605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2438309823810717998902403 3657464735716076998353605)
                ·
                  refine ⟨685774637946764437191301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3657464735716076998353605 685774637946764437191301)
                  ·
                    refine ⟨128582744615018331973369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 685774637946764437191301 128582744615018331973369)
                    ·
                      rfl

theorem cell23_751242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_751242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751242 prefixEnd_751242 := by exact prefixLift 751242
  have htrace : WordTrace (prefixWord ++ tailWord_751242) baseStart_751242 baseEnd_751242 := by
    simpa [prefixWord, tailWord_751242, baseEnd_751242] using wordTrace_append hprefix tailTrace_751242
  have hstable : (prefixWord ++ tailWord_751242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751242).length < 2 ^ (prefixWord ++ tailWord_751242).sum := by decide
  have hdescent : baseEnd_751242 < baseStart_751242 := by decide
  rcases family_descends (prefixWord ++ tailWord_751242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751262 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_751262 : Nat := 118140960795 + 751262 * 2 ^ 59
def prefixEnd_751262 : Nat := 4983230072969 + 3 ^ 40 * 751262 * 2
def baseEnd_751262 : Nat := 385758503458144917670015

theorem tailTrace_751262 : CollatzResearch.WordTrace tailWord_751262 prefixEnd_751262 385758503458144917670015 := by
  unfold tailWord_751262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3425097025539194272475005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18267184136209036119866693 3425097025539194272475005)
  ·
    refine ⟨1284411384577197852178127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3425097025539194272475005 1284411384577197852178127)
    ·
      refine ⟨1926617076865796778267191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1284411384577197852178127 1926617076865796778267191)
      ·
        refine ⟨2889925615298695167400787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1926617076865796778267191 2889925615298695167400787)
        ·
          refine ⟨4334888422948042751101181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2889925615298695167400787 4334888422948042751101181)
          ·
            refine ⟨1625583158605516031662943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4334888422948042751101181 1625583158605516031662943)
            ·
              refine ⟨2438374737908274047494415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1625583158605516031662943 2438374737908274047494415)
              ·
                refine ⟨3657562106862411071241623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2438374737908274047494415 3657562106862411071241623)
                ·
                  refine ⟨5486343160293616606862435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3657562106862411071241623 5486343160293616606862435)
                  ·
                    refine ⟨8229514740440424910293653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5486343160293616606862435 8229514740440424910293653)
                    ·
                      refine ⟨385758503458144917670015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8229514740440424910293653 385758503458144917670015)
                      ·
                        rfl

theorem cell23_751262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_751262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751262 prefixEnd_751262 := by exact prefixLift 751262
  have htrace : WordTrace (prefixWord ++ tailWord_751262) baseStart_751262 baseEnd_751262 := by
    simpa [prefixWord, tailWord_751262, baseEnd_751262] using wordTrace_append hprefix tailTrace_751262
  have hstable : (prefixWord ++ tailWord_751262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751262).length < 2 ^ (prefixWord ++ tailWord_751262).sum := by decide
  have hdescent : baseEnd_751262 < baseStart_751262 := by decide
  rcases family_descends (prefixWord ++ tailWord_751262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751266 : List Nat := [3, 3, 1, 4, 1, 1, 2, 2, 1, 1, 4]
def baseStart_751266 : Nat := 118140960795 + 751266 * 2 ^ 59
def prefixEnd_751266 : Nat := 4983230072969 + 3 ^ 40 * 751266 * 2
def baseEnd_751266 : Nat := 385760557380762902019997

theorem tailTrace_751266 : CollatzResearch.WordTrace tailWord_751266 prefixEnd_751266 385760557380762902019997 := by
  unfold tailWord_751266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6850230524074765715736413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18267281397532708575297101 6850230524074765715736413)
  ·
    refine ⟨2568836446528037143401155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6850230524074765715736413 2568836446528037143401155)
    ·
      refine ⟨3853254669792055715101733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2568836446528037143401155 3853254669792055715101733)
      ·
        refine ⟨722485250586010446581575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3853254669792055715101733 722485250586010446581575)
        ·
          refine ⟨1083727875879015669872363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722485250586010446581575 1083727875879015669872363)
          ·
            refine ⟨1625591813818523504808545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083727875879015669872363 1625591813818523504808545)
            ·
              refine ⟨1219193860363892628606409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1625591813818523504808545 1219193860363892628606409)
              ·
                refine ⟨914395395272919471454807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1219193860363892628606409 914395395272919471454807)
                ·
                  refine ⟨1371593092909379207182211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 914395395272919471454807 1371593092909379207182211)
                  ·
                    refine ⟨2057389639364068810773317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1371593092909379207182211 2057389639364068810773317)
                    ·
                      refine ⟨385760557380762902019997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2057389639364068810773317 385760557380762902019997)
                      ·
                        rfl

theorem cell23_751266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_751266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751266 prefixEnd_751266 := by exact prefixLift 751266
  have htrace : WordTrace (prefixWord ++ tailWord_751266) baseStart_751266 baseEnd_751266 := by
    simpa [prefixWord, tailWord_751266, baseEnd_751266] using wordTrace_append hprefix tailTrace_751266
  have hstable : (prefixWord ++ tailWord_751266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751266).length < 2 ^ (prefixWord ++ tailWord_751266).sum := by decide
  have hdescent : baseEnd_751266 < baseStart_751266 := by decide
  rcases family_descends (prefixWord ++ tailWord_751266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751282 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3]
def baseStart_751282 : Nat := 118140960795 + 751282 * 2 ^ 59
def prefixEnd_751282 : Nat := 4983230072969 + 3 ^ 40 * 751282 * 2
def baseEnd_751282 : Nat := 385768773071234839419923

theorem tailTrace_751282 : CollatzResearch.WordTrace tailWord_751282 prefixEnd_751282 385768773071234839419923 := by
  unfold tailWord_751282
  simp only [CollatzResearch.WordTrace]
  refine ⟨6850376416060274398882025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18267670442827398397018733 6850376416060274398882025)
  ·
    refine ⟨5137782312045205799161519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6850376416060274398882025 5137782312045205799161519)
    ·
      refine ⟨7706673468067808698742279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5137782312045205799161519 7706673468067808698742279)
      ·
        refine ⟨11560010202101713048113419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7706673468067808698742279 11560010202101713048113419)
        ·
          refine ⟨17340015303152569572170129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11560010202101713048113419 17340015303152569572170129)
          ·
            refine ⟨13005011477364427179127597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17340015303152569572170129 13005011477364427179127597)
            ·
              refine ⟨4876879304011660192172849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13005011477364427179127597 4876879304011660192172849)
              ·
                refine ⟨3657659478008745144129637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4876879304011660192172849 3657659478008745144129637)
                ·
                  refine ⟨685811152126639714524307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3657659478008745144129637 685811152126639714524307)
                  ·
                    refine ⟨1028716728189959571786461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 685811152126639714524307 1028716728189959571786461)
                    ·
                      refine ⟨385768773071234839419923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1028716728189959571786461 385768773071234839419923)
                      ·
                        rfl

theorem cell23_751282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_751282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751282 prefixEnd_751282 := by exact prefixLift 751282
  have htrace : WordTrace (prefixWord ++ tailWord_751282) baseStart_751282 baseEnd_751282 := by
    simpa [prefixWord, tailWord_751282, baseEnd_751282] using wordTrace_append hprefix tailTrace_751282
  have hstable : (prefixWord ++ tailWord_751282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751282).length < 2 ^ (prefixWord ++ tailWord_751282).sum := by decide
  have hdescent : baseEnd_751282 < baseStart_751282 := by decide
  rcases family_descends (prefixWord ++ tailWord_751282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751286 : List Nat := [5, 1, 3, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_751286 : Nat := 118140960795 + 751286 * 2 ^ 59
def prefixEnd_751286 : Nat := 4983230072969 + 3 ^ 40 * 751286 * 2
def baseEnd_751286 : Nat := 385770826993852823769905

theorem tailTrace_751286 : CollatzResearch.WordTrace tailWord_751286 prefixEnd_751286 385770826993852823769905 := by
  unfold tailWord_751286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1712603222264162892417107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18267767704151070852449141 1712603222264162892417107)
  ·
    refine ⟨2568904833396244338625661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1712603222264162892417107 2568904833396244338625661)
    ·
      refine ⟨963339312523591626984623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2568904833396244338625661 963339312523591626984623)
      ·
        refine ⟨1445008968785387440476935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 963339312523591626984623 1445008968785387440476935)
        ·
          refine ⟨2167513453178081160715403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1445008968785387440476935 2167513453178081160715403)
          ·
            refine ⟨3251270179767121741073105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2167513453178081160715403 3251270179767121741073105)
            ·
              refine ⟨2438452634825341305804829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3251270179767121741073105 2438452634825341305804829)
              ·
                refine ⟨914419738059502989676811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2438452634825341305804829 914419738059502989676811)
                ·
                  refine ⟨1371629607089254484515217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 914419738059502989676811 1371629607089254484515217)
                  ·
                    refine ⟨1028722205316940863386413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1371629607089254484515217 1028722205316940863386413)
                    ·
                      refine ⟨385770826993852823769905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1028722205316940863386413 385770826993852823769905)
                      ·
                        rfl

theorem cell23_751286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_751286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751286 prefixEnd_751286 := by exact prefixLift 751286
  have htrace : WordTrace (prefixWord ++ tailWord_751286) baseStart_751286 baseEnd_751286 := by
    simpa [prefixWord, tailWord_751286, baseEnd_751286] using wordTrace_append hprefix tailTrace_751286
  have hstable : (prefixWord ++ tailWord_751286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751286).length < 2 ^ (prefixWord ++ tailWord_751286).sum := by decide
  have hdescent : baseEnd_751286 < baseStart_751286 := by decide
  rcases family_descends (prefixWord ++ tailWord_751286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751288 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 8]
def baseStart_751288 : Nat := 118140960795 + 751288 * 2 ^ 59
def prefixEnd_751288 : Nat := 4983230072969 + 3 ^ 40 * 751288 * 2
def baseEnd_751288 : Nat := 385771853955161815944895

theorem tailTrace_751288 : CollatzResearch.WordTrace tailWord_751288 prefixEnd_751288 385771853955161815944895 := by
  unfold tailWord_751288
  simp only [CollatzResearch.WordTrace]
  refine ⟨13700862251109680310123259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18267816334812907080164345 13700862251109680310123259)
  ·
    refine ⟨20551293376664520465184889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13700862251109680310123259 20551293376664520465184889)
    ·
      refine ⟨15413470032498390348888667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20551293376664520465184889 15413470032498390348888667)
      ·
        refine ⟨23120205048747585523333001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15413470032498390348888667 23120205048747585523333001)
        ·
          refine ⟨17340153786560689142499751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23120205048747585523333001 17340153786560689142499751)
          ·
            refine ⟨26010230679841033713749627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17340153786560689142499751 26010230679841033713749627)
            ·
              refine ⟨39015346019761550570624441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26010230679841033713749627 39015346019761550570624441)
              ·
                refine ⟨29261509514821162927968331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39015346019761550570624441 29261509514821162927968331)
                ·
                  refine ⟨43892264272231744391952497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29261509514821162927968331 43892264272231744391952497)
                  ·
                    refine ⟨32919198204173808293964373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43892264272231744391952497 32919198204173808293964373)
                    ·
                      refine ⟨385771853955161815944895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 32919198204173808293964373 385771853955161815944895)
                      ·
                        rfl

theorem cell23_751288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_751288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751288 prefixEnd_751288 := by exact prefixLift 751288
  have htrace : WordTrace (prefixWord ++ tailWord_751288) baseStart_751288 baseEnd_751288 := by
    simpa [prefixWord, tailWord_751288, baseEnd_751288] using wordTrace_append hprefix tailTrace_751288
  have hstable : (prefixWord ++ tailWord_751288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751288).length < 2 ^ (prefixWord ++ tailWord_751288).sum := by decide
  have hdescent : baseEnd_751288 < baseStart_751288 := by decide
  rcases family_descends (prefixWord ++ tailWord_751288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751316 : List Nat := [2, 4, 1, 3, 1, 2, 1, 3, 2, 1, 3]
def baseStart_751316 : Nat := 118140960795 + 751316 * 2 ^ 59
def prefixEnd_751316 : Nat := 4983230072969 + 3 ^ 40 * 751316 * 2
def baseEnd_751316 : Nat := 385786231413487706394767

theorem tailTrace_751316 : CollatzResearch.WordTrace tailWord_751316 prefixEnd_751316 385786231413487706394767 := by
  unfold tailWord_751316
  simp only [CollatzResearch.WordTrace]
  refine ⟨13701372873058960701132901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18268497164078614268177201 13701372873058960701132901)
  ·
    refine ⟨2569007413698555131462419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13701372873058960701132901 2569007413698555131462419)
    ·
      refine ⟨3853511120547832697193629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2569007413698555131462419 3853511120547832697193629)
      ·
        refine ⟨1445066670205437261447611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3853511120547832697193629 1445066670205437261447611)
        ·
          refine ⟨2167600005308155892171417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1445066670205437261447611 2167600005308155892171417)
          ·
            refine ⟨1625700003981116919128563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2167600005308155892171417 1625700003981116919128563)
            ·
              refine ⟨2438550005971675378692845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1625700003981116919128563 2438550005971675378692845)
              ·
                refine ⟨914456252239378267009817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2438550005971675378692845 914456252239378267009817)
                ·
                  refine ⟨685842189179533700257363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 914456252239378267009817 685842189179533700257363)
                  ·
                    refine ⟨1028763283769300550386045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 685842189179533700257363 1028763283769300550386045)
                    ·
                      refine ⟨385786231413487706394767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1028763283769300550386045 385786231413487706394767)
                      ·
                        rfl

theorem cell23_751316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_751316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751316 prefixEnd_751316 := by exact prefixLift 751316
  have htrace : WordTrace (prefixWord ++ tailWord_751316) baseStart_751316 baseEnd_751316 := by
    simpa [prefixWord, tailWord_751316, baseEnd_751316] using wordTrace_append hprefix tailTrace_751316
  have hstable : (prefixWord ++ tailWord_751316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751316).length < 2 ^ (prefixWord ++ tailWord_751316).sum := by decide
  have hdescent : baseEnd_751316 < baseStart_751316 := by decide
  rcases family_descends (prefixWord ++ tailWord_751316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751356 : List Nat := [2, 2, 2, 1, 3, 1, 4, 2, 2, 2, 2]
def baseStart_751356 : Nat := 118140960795 + 751356 * 2 ^ 59
def prefixEnd_751356 : Nat := 4983230072969 + 3 ^ 40 * 751356 * 2
def baseEnd_751356 : Nat := 385806770639667549894583

theorem tailTrace_751356 : CollatzResearch.WordTrace tailWord_751356 prefixEnd_751356 385806770639667549894583 := by
  unfold tailWord_751356
  simp only [CollatzResearch.WordTrace]
  refine ⟨13702102332986504116860961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18269469777315338822481281 13702102332986504116860961)
  ·
    refine ⟨10276576749739878087645721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13702102332986504116860961 10276576749739878087645721)
    ·
      refine ⟨7707432562304908565734291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10276576749739878087645721 7707432562304908565734291)
      ·
        refine ⟨11561148843457362848601437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7707432562304908565734291 11561148843457362848601437)
        ·
          refine ⟨4335430816296511068225539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11561148843457362848601437 4335430816296511068225539)
          ·
            refine ⟨6503146224444766602338309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4335430816296511068225539 6503146224444766602338309)
            ·
              refine ⟨1219339917083393737938433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6503146224444766602338309 1219339917083393737938433)
              ·
                refine ⟨914504937812545303453825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1219339917083393737938433 914504937812545303453825)
                ·
                  refine ⟨685878703359408977590369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 914504937812545303453825 685878703359408977590369)
                  ·
                    refine ⟨514409027519556733192777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 685878703359408977590369 514409027519556733192777)
                    ·
                      refine ⟨385806770639667549894583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 514409027519556733192777 385806770639667549894583)
                      ·
                        rfl

theorem cell23_751356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_751356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751356 prefixEnd_751356 := by exact prefixLift 751356
  have htrace : WordTrace (prefixWord ++ tailWord_751356) baseStart_751356 baseEnd_751356 := by
    simpa [prefixWord, tailWord_751356, baseEnd_751356] using wordTrace_append hprefix tailTrace_751356
  have hstable : (prefixWord ++ tailWord_751356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751356).length < 2 ^ (prefixWord ++ tailWord_751356).sum := by decide
  have hdescent : baseEnd_751356 < baseStart_751356 := by decide
  rcases family_descends (prefixWord ++ tailWord_751356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751362 : List Nat := [3, 4, 1, 1, 1, 1, 2, 3, 7]
def baseStart_751362 : Nat := 118140960795 + 751362 * 2 ^ 59
def prefixEnd_751362 : Nat := 4983230072969 + 3 ^ 40 * 751362 * 2
def baseEnd_751362 : Nat := 42867761280399391824395

theorem tailTrace_751362 : CollatzResearch.WordTrace tailWord_751362 prefixEnd_751362 42867761280399391824395 := by
  unfold tailWord_751362
  simp only [CollatzResearch.WordTrace]
  refine ⟨6851105875987817814610085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18269615669300847505626893 6851105875987817814610085)
  ·
    refine ⟨1284582351747715840239391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6851105875987817814610085 1284582351747715840239391)
    ·
      refine ⟨1926873527621573760359087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1284582351747715840239391 1926873527621573760359087)
      ·
        refine ⟨2890310291432360640538631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1926873527621573760359087 2890310291432360640538631)
        ·
          refine ⟨4335465437148540960807947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2890310291432360640538631 4335465437148540960807947)
          ·
            refine ⟨6503198155722811441211921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4335465437148540960807947 6503198155722811441211921)
            ·
              refine ⟨4877398616792108580908941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6503198155722811441211921 4877398616792108580908941)
              ·
                refine ⟨1829024481297040717840853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4877398616792108580908941 1829024481297040717840853)
                ·
                  refine ⟨42867761280399391824395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1829024481297040717840853 42867761280399391824395)
                  ·
                    rfl

theorem cell23_751362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_751362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751362 prefixEnd_751362 := by exact prefixLift 751362
  have htrace : WordTrace (prefixWord ++ tailWord_751362) baseStart_751362 baseEnd_751362 := by
    simpa [prefixWord, tailWord_751362, baseEnd_751362] using wordTrace_append hprefix tailTrace_751362
  have hstable : (prefixWord ++ tailWord_751362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751362).length < 2 ^ (prefixWord ++ tailWord_751362).sum := by decide
  have hdescent : baseEnd_751362 < baseStart_751362 := by decide
  rcases family_descends (prefixWord ++ tailWord_751362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751432 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 1, 4, 3]
def baseStart_751432 : Nat := 118140960795 + 751432 * 2 ^ 59
def prefixEnd_751432 : Nat := 4983230072969 + 3 ^ 40 * 751432 * 2
def baseEnd_751432 : Nat := 385845795169409252544233

theorem tailTrace_751432 : CollatzResearch.WordTrace tailWord_751432 prefixEnd_751432 385845795169409252544233 := by
  unfold tailWord_751432
  simp only [CollatzResearch.WordTrace]
  refine ⟨13703488306848836606744275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18271317742465115475659033 13703488306848836606744275)
  ·
    refine ⟨20555232460273254910116413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13703488306848836606744275 20555232460273254910116413)
    ·
      refine ⟨7708212172602470591293655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20555232460273254910116413 7708212172602470591293655)
      ·
        refine ⟨11562318258903705886940483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7708212172602470591293655 11562318258903705886940483)
        ·
          refine ⟨17343477388355558830410725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11562318258903705886940483 17343477388355558830410725)
          ·
            refine ⟨3251902010316667280702011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17343477388355558830410725 3251902010316667280702011)
            ·
              refine ⟨4877853015475000921053017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3251902010316667280702011 4877853015475000921053017)
              ·
                refine ⟨3658389761606250690789763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4877853015475000921053017 3658389761606250690789763)
                ·
                  refine ⟨5487584642409376036184645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3658389761606250690789763 5487584642409376036184645)
                  ·
                    refine ⟨1028922120451758006784621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5487584642409376036184645 1028922120451758006784621)
                    ·
                      refine ⟨385845795169409252544233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1028922120451758006784621 385845795169409252544233)
                      ·
                        rfl

theorem cell23_751432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_751432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751432 prefixEnd_751432 := by exact prefixLift 751432
  have htrace : WordTrace (prefixWord ++ tailWord_751432) baseStart_751432 baseEnd_751432 := by
    simpa [prefixWord, tailWord_751432, baseEnd_751432] using wordTrace_append hprefix tailTrace_751432
  have hstable : (prefixWord ++ tailWord_751432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751432).length < 2 ^ (prefixWord ++ tailWord_751432).sum := by decide
  have hdescent : baseEnd_751432 < baseStart_751432 := by decide
  rcases family_descends (prefixWord ++ tailWord_751432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751456 : List Nat := [2, 1, 1, 3, 3, 2, 3, 3, 1, 4]
def baseStart_751456 : Nat := 118140960795 + 751456 * 2 ^ 59
def prefixEnd_751456 : Nat := 4983230072969 + 3 ^ 40 * 751456 * 2
def baseEnd_751456 : Nat := 128619372901705719548041

theorem tailTrace_751456 : CollatzResearch.WordTrace tailWord_751456 prefixEnd_751456 128619372901705719548041 := by
  unfold tailWord_751456
  simp only [CollatzResearch.WordTrace]
  refine ⟨13703925982805362656181111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18271901310407150208241481 13703925982805362656181111)
  ·
    refine ⟨20555888974208043984271667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13703925982805362656181111 20555888974208043984271667)
    ·
      refine ⟨30833833461312065976407501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20555888974208043984271667 30833833461312065976407501)
      ·
        refine ⟨11562687547992024741152813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30833833461312065976407501 11562687547992024741152813)
        ·
          refine ⟨4336007830497009277932305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11562687547992024741152813 4336007830497009277932305)
          ·
            refine ⟨3252005872872756958449229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4336007830497009277932305 3252005872872756958449229)
            ·
              refine ⟨1219502202327283859418461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3252005872872756958449229 1219502202327283859418461)
              ·
                refine ⟨457313325872731447281923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1219502202327283859418461 457313325872731447281923)
                ·
                  refine ⟨685969988809097170922885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 457313325872731447281923 685969988809097170922885)
                  ·
                    refine ⟨128619372901705719548041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 685969988809097170922885 128619372901705719548041)
                    ·
                      rfl

theorem cell23_751456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 1, 4].length) (baseStart_751456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751456 prefixEnd_751456 := by exact prefixLift 751456
  have htrace : WordTrace (prefixWord ++ tailWord_751456) baseStart_751456 baseEnd_751456 := by
    simpa [prefixWord, tailWord_751456, baseEnd_751456] using wordTrace_append hprefix tailTrace_751456
  have hstable : (prefixWord ++ tailWord_751456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751456).length < 2 ^ (prefixWord ++ tailWord_751456).sum := by decide
  have hdescent : baseEnd_751456 < baseStart_751456 := by decide
  rcases family_descends (prefixWord ++ tailWord_751456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751475 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 7]
def baseStart_751475 : Nat := 118140960795 + 751475 * 2 ^ 59
def prefixEnd_751475 : Nat := 4983230072969 + 3 ^ 40 * 751475 * 2
def baseEnd_751475 : Nat := 385867874837552584306535

theorem tailTrace_751475 : CollatzResearch.WordTrace tailWord_751475 prefixEnd_751475 385867874837552584306535 := by
  unfold tailWord_751475
  simp only [CollatzResearch.WordTrace]
  refine ⟨27408544952541891557303879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18272363301694594371535919 27408544952541891557303879)
  ·
    refine ⟨41112817428812837335955819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27408544952541891557303879 41112817428812837335955819)
    ·
      refine ⟨61669226143219256003933729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41112817428812837335955819 61669226143219256003933729)
      ·
        refine ⟨46251919607414442002950297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61669226143219256003933729 46251919607414442002950297)
        ·
          refine ⟨34688939705560831502212723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46251919607414442002950297 34688939705560831502212723)
          ·
            refine ⟨52033409558341247253319085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34688939705560831502212723 52033409558341247253319085)
            ·
              refine ⟨19512528584377967719994657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52033409558341247253319085 19512528584377967719994657)
              ·
                refine ⟨14634396438283475789995993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19512528584377967719994657 14634396438283475789995993)
                ·
                  refine ⟨10975797328712606842496995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14634396438283475789995993 10975797328712606842496995)
                  ·
                    refine ⟨16463695993068910263745493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10975797328712606842496995 16463695993068910263745493)
                    ·
                      refine ⟨385867874837552584306535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16463695993068910263745493 385867874837552584306535)
                      ·
                        rfl

theorem cell23_751475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_751475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751475 prefixEnd_751475 := by exact prefixLift 751475
  have htrace : WordTrace (prefixWord ++ tailWord_751475) baseStart_751475 baseEnd_751475 := by
    simpa [prefixWord, tailWord_751475, baseEnd_751475] using wordTrace_append hprefix tailTrace_751475
  have hstable : (prefixWord ++ tailWord_751475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751475).length < 2 ^ (prefixWord ++ tailWord_751475).sum := by decide
  have hdescent : baseEnd_751475 < baseStart_751475 := by decide
  rcases family_descends (prefixWord ++ tailWord_751475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751486 : List Nat := [4, 2, 3, 1, 1, 2, 1, 3, 6]
def baseStart_751486 : Nat := 118140960795 + 751486 * 2 ^ 59
def prefixEnd_751486 : Nat := 4983230072969 + 3 ^ 40 * 751486 * 2
def baseEnd_751486 : Nat := 42874835902750226807665

theorem tailTrace_751486 : CollatzResearch.WordTrace tailWord_751486 prefixEnd_751486 42874835902750226807665 := by
  unfold tailWord_751486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3426118269437755054494289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18272630770334693623969541 3426118269437755054494289)
  ·
    refine ⟨2569588702078316290870717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3426118269437755054494289 2569588702078316290870717)
    ·
      refine ⟨963595763279368609076519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2569588702078316290870717 963595763279368609076519)
      ·
        refine ⟨1445393644919052913614779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 963595763279368609076519 1445393644919052913614779)
        ·
          refine ⟨2168090467378579370422169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1445393644919052913614779 2168090467378579370422169)
          ·
            refine ⟨1626067850533934527816627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2168090467378579370422169 1626067850533934527816627)
            ·
              refine ⟨2439101775800901791724941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1626067850533934527816627 2439101775800901791724941)
              ·
                refine ⟨914663165925338171896853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2439101775800901791724941 914663165925338171896853)
                ·
                  refine ⟨42874835902750226807665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 914663165925338171896853 42874835902750226807665)
                  ·
                    rfl

theorem cell23_751486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_751486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751486 prefixEnd_751486 := by exact prefixLift 751486
  have htrace : WordTrace (prefixWord ++ tailWord_751486) baseStart_751486 baseEnd_751486 := by
    simpa [prefixWord, tailWord_751486, baseEnd_751486] using wordTrace_append hprefix tailTrace_751486
  have hstable : (prefixWord ++ tailWord_751486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751486).length < 2 ^ (prefixWord ++ tailWord_751486).sum := by decide
  have hdescent : baseEnd_751486 < baseStart_751486 := by decide
  rcases family_descends (prefixWord ++ tailWord_751486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751549 : List Nat := [1, 4, 1, 2, 3, 1, 1, 3, 1, 2, 4]
def baseStart_751549 : Nat := 118140960795 + 751549 * 2 ^ 59
def prefixEnd_751549 : Nat := 4983230072969 + 3 ^ 40 * 751549 * 2
def baseEnd_751549 : Nat := 385905872405985294781195

theorem tailTrace_751549 : CollatzResearch.WordTrace tailWord_751549 prefixEnd_751549 385905872405985294781195 := by
  unfold tailWord_751549
  simp only [CollatzResearch.WordTrace]
  refine ⟨27411243954273802195497701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18274162636182534796998467 27411243954273802195497701)
  ·
    refine ⟨5139608241426337911655819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27411243954273802195497701 5139608241426337911655819)
    ·
      refine ⟨7709412362139506867483729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5139608241426337911655819 7709412362139506867483729)
      ·
        refine ⟨5782059271604630150612797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7709412362139506867483729 5782059271604630150612797)
        ·
          refine ⟨2168272226851736306479799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5782059271604630150612797 2168272226851736306479799)
          ·
            refine ⟨3252408340277604459719699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2168272226851736306479799 3252408340277604459719699)
            ·
              refine ⟨4878612510416406689579549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3252408340277604459719699 4878612510416406689579549)
              ·
                refine ⟨1829479691406152508592331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4878612510416406689579549 1829479691406152508592331)
                ·
                  refine ⟨2744219537109228762888497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1829479691406152508592331 2744219537109228762888497)
                  ·
                    refine ⟨2058164652831921572166373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2744219537109228762888497 2058164652831921572166373)
                    ·
                      refine ⟨385905872405985294781195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2058164652831921572166373 385905872405985294781195)
                      ·
                        rfl

theorem cell23_751549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_751549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751549 prefixEnd_751549 := by exact prefixLift 751549
  have htrace : WordTrace (prefixWord ++ tailWord_751549) baseStart_751549 baseEnd_751549 := by
    simpa [prefixWord, tailWord_751549, baseEnd_751549] using wordTrace_append hprefix tailTrace_751549
  have hstable : (prefixWord ++ tailWord_751549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751549).length < 2 ^ (prefixWord ++ tailWord_751549).sum := by decide
  have hdescent : baseEnd_751549 < baseStart_751549 := by decide
  rcases family_descends (prefixWord ++ tailWord_751549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751570 : List Nat := [3, 2, 2, 3, 2, 2, 2, 1, 1, 1, 4]
def baseStart_751570 : Nat := 118140960795 + 751570 * 2 ^ 59
def prefixEnd_751570 : Nat := 4983230072969 + 3 ^ 40 * 751570 * 2
def baseEnd_751570 : Nat := 385916655499729712618599

theorem tailTrace_751570 : CollatzResearch.WordTrace tailWord_751570 prefixEnd_751570 385916655499729712618599 := by
  unfold tailWord_751570
  simp only [CollatzResearch.WordTrace]
  refine ⟨6853002471799430695503041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18274673258131815188008109 6853002471799430695503041)
  ·
    refine ⟨5139751853849573021627281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6853002471799430695503041 5139751853849573021627281)
    ·
      refine ⟨3854813890387179766220461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5139751853849573021627281 3854813890387179766220461)
      ·
        refine ⟨1445555208895192412332673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3854813890387179766220461 1445555208895192412332673)
        ·
          refine ⟨1084166406671394309249505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1445555208895192412332673 1084166406671394309249505)
          ·
            refine ⟨813124805003545731937129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1084166406671394309249505 813124805003545731937129)
            ·
              refine ⟨609843603752659298952847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 813124805003545731937129 609843603752659298952847)
              ·
                refine ⟨914765405628988948429271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 609843603752659298952847 914765405628988948429271)
                ·
                  refine ⟨1372148108443483422643907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 914765405628988948429271 1372148108443483422643907)
                  ·
                    refine ⟨2058222162665225133965861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1372148108443483422643907 2058222162665225133965861)
                    ·
                      refine ⟨385916655499729712618599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2058222162665225133965861 385916655499729712618599)
                      ·
                        rfl

theorem cell23_751570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_751570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751570 prefixEnd_751570 := by exact prefixLift 751570
  have htrace : WordTrace (prefixWord ++ tailWord_751570) baseStart_751570 baseEnd_751570 := by
    simpa [prefixWord, tailWord_751570, baseEnd_751570] using wordTrace_append hprefix tailTrace_751570
  have hstable : (prefixWord ++ tailWord_751570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751570).length < 2 ^ (prefixWord ++ tailWord_751570).sum := by decide
  have hdescent : baseEnd_751570 < baseStart_751570 := by decide
  rcases family_descends (prefixWord ++ tailWord_751570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751573 : List Nat := [1, 3, 2, 3, 2, 1, 4, 1, 1, 2, 3]
def baseStart_751573 : Nat := 118140960795 + 751573 * 2 ^ 59
def prefixEnd_751573 : Nat := 4983230072969 + 3 ^ 40 * 751573 * 2
def baseEnd_751573 : Nat := 385918195941693200881085

theorem tailTrace_751573 : CollatzResearch.WordTrace tailWord_751573 prefixEnd_751573 385918195941693200881085 := by
  unfold tailWord_751573
  simp only [CollatzResearch.WordTrace]
  refine ⟨27412119306186854294371373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18274746204124569529580915 27412119306186854294371373)
  ·
    refine ⟨10279544739820070360389265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27412119306186854294371373 10279544739820070360389265)
    ·
      refine ⟨7709658554865052770291949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10279544739820070360389265 7709658554865052770291949)
      ·
        refine ⟨2891121958074394788859481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7709658554865052770291949 2891121958074394788859481)
        ·
          refine ⟨2168341468555796091644611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2891121958074394788859481 2168341468555796091644611)
          ·
            refine ⟨3252512202833694137466917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2168341468555796091644611 3252512202833694137466917)
            ·
              refine ⟨609846038031317650775047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3252512202833694137466917 609846038031317650775047)
              ·
                refine ⟨914769057046976476162571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 609846038031317650775047 914769057046976476162571)
                ·
                  refine ⟨1372153585570464714243857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 914769057046976476162571 1372153585570464714243857)
                  ·
                    refine ⟨1029115189177848535682893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1372153585570464714243857 1029115189177848535682893)
                    ·
                      refine ⟨385918195941693200881085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1029115189177848535682893 385918195941693200881085)
                      ·
                        rfl

theorem cell23_751573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_751573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751573 prefixEnd_751573 := by exact prefixLift 751573
  have htrace : WordTrace (prefixWord ++ tailWord_751573) baseStart_751573 baseEnd_751573 := by
    simpa [prefixWord, tailWord_751573, baseEnd_751573] using wordTrace_append hprefix tailTrace_751573
  have hstable : (prefixWord ++ tailWord_751573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751573).length < 2 ^ (prefixWord ++ tailWord_751573).sum := by decide
  have hdescent : baseEnd_751573 < baseStart_751573 := by decide
  rcases family_descends (prefixWord ++ tailWord_751573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751580 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 4, 4]
def baseStart_751580 : Nat := 118140960795 + 751580 * 2 ^ 59
def prefixEnd_751580 : Nat := 4983230072969 + 3 ^ 40 * 751580 * 2
def baseEnd_751580 : Nat := 128640596768758224497851

theorem tailTrace_751580 : CollatzResearch.WordTrace tailWord_751580 prefixEnd_751580 128640596768758224497851 := by
  unfold tailWord_751580
  simp only [CollatzResearch.WordTrace]
  refine ⟨13706187308580747244938097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18274916411440996326584129 13706187308580747244938097)
  ·
    refine ⟨10279640481435560433703573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13706187308580747244938097 10279640481435560433703573)
    ·
      refine ⟨481858147567291895329855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10279640481435560433703573 481858147567291895329855)
      ·
        refine ⟨722787221350937842994783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481858147567291895329855 722787221350937842994783)
        ·
          refine ⟨1084180832026406764492175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722787221350937842994783 1084180832026406764492175)
          ·
            refine ⟨1626271248039610146738263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1084180832026406764492175 1626271248039610146738263)
            ·
              refine ⟨2439406872059415220107395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1626271248039610146738263 2439406872059415220107395)
              ·
                refine ⟨3659110308089122830161093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2439406872059415220107395 3659110308089122830161093)
                ·
                  refine ⟨686083182766710530655205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3659110308089122830161093 686083182766710530655205)
                  ·
                    refine ⟨128640596768758224497851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 686083182766710530655205 128640596768758224497851)
                    ·
                      rfl

theorem cell23_751580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_751580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751580 prefixEnd_751580 := by exact prefixLift 751580
  have htrace : WordTrace (prefixWord ++ tailWord_751580) baseStart_751580 baseEnd_751580 := by
    simpa [prefixWord, tailWord_751580, baseEnd_751580] using wordTrace_append hprefix tailTrace_751580
  have hstable : (prefixWord ++ tailWord_751580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751580).length < 2 ^ (prefixWord ++ tailWord_751580).sum := by decide
  have hdescent : baseEnd_751580 < baseStart_751580 := by decide
  rcases family_descends (prefixWord ++ tailWord_751580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751679 : List Nat := [1, 1, 2, 2, 3, 1, 3, 3, 2, 5]
def baseStart_751679 : Nat := 118140960795 + 751679 * 2 ^ 59
def prefixEnd_751679 : Nat := 4983230072969 + 3 ^ 40 * 751679 * 2
def baseEnd_751679 : Nat := 128657541630356595385199

theorem tailTrace_751679 : CollatzResearch.WordTrace tailWord_751679 prefixEnd_751679 128657541630356595385199 := by
  unfold tailWord_751679
  simp only [CollatzResearch.WordTrace]
  refine ⟨27415985443802834397730091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18277323629201889598486727 27415985443802834397730091)
  ·
    refine ⟨41123978165704251596595137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27415985443802834397730091 41123978165704251596595137)
    ·
      refine ⟨30842983624278188697446353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41123978165704251596595137 30842983624278188697446353)
      ·
        refine ⟨23132237718208641523084765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30842983624278188697446353 23132237718208641523084765)
        ·
          refine ⟨8674589144328240571156787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23132237718208641523084765 8674589144328240571156787)
          ·
            refine ⟨13011883716492360856735181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8674589144328240571156787 13011883716492360856735181)
            ·
              refine ⟨4879456393684635321275693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13011883716492360856735181 4879456393684635321275693)
              ·
                refine ⟨1829796147631738245478385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4879456393684635321275693 1829796147631738245478385)
                ·
                  refine ⟨1372347110723803684108789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1829796147631738245478385 1372347110723803684108789)
                  ·
                    refine ⟨128657541630356595385199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1372347110723803684108789 128657541630356595385199)
                    ·
                      rfl

theorem cell23_751679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 5].length) (baseStart_751679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751679 prefixEnd_751679 := by exact prefixLift 751679
  have htrace : WordTrace (prefixWord ++ tailWord_751679) baseStart_751679 baseEnd_751679 := by
    simpa [prefixWord, tailWord_751679, baseEnd_751679] using wordTrace_append hprefix tailTrace_751679
  have hstable : (prefixWord ++ tailWord_751679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751679).length < 2 ^ (prefixWord ++ tailWord_751679).sum := by decide
  have hdescent : baseEnd_751679 < baseStart_751679 := by decide
  rcases family_descends (prefixWord ++ tailWord_751679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751716 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 1, 6, 2]
def baseStart_751716 : Nat := 118140960795 + 751716 * 2 ^ 59
def prefixEnd_751716 : Nat := 4983230072969 + 3 ^ 40 * 751716 * 2
def baseEnd_751716 : Nat := 385991623675286141392927

theorem tailTrace_751716 : CollatzResearch.WordTrace tailWord_751716 prefixEnd_751716 385991623675286141392927 := by
  unfold tailWord_751716
  simp only [CollatzResearch.WordTrace]
  refine ⟨13708667472334394858413501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18278223296445859811218001 13708667472334394858413501)
  ·
    refine ⟨5140750302125398071905063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13708667472334394858413501 5140750302125398071905063)
    ·
      refine ⟨7711125453188097107857595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5140750302125398071905063 7711125453188097107857595)
      ·
        refine ⟨11566688179782145661786393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7711125453188097107857595 11566688179782145661786393)
        ·
          refine ⟨8675016134836609246339795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11566688179782145661786393 8675016134836609246339795)
          ·
            refine ⟨13012524202254913869509693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8675016134836609246339795 13012524202254913869509693)
            ·
              refine ⟨4879696575845592701066135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13012524202254913869509693 4879696575845592701066135)
              ·
                refine ⟨7319544863768389051599203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4879696575845592701066135 7319544863768389051599203)
                ·
                  refine ⟨10979317295652583577398805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7319544863768389051599203 10979317295652583577398805)
                  ·
                    refine ⟨514655498233714855190569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10979317295652583577398805 514655498233714855190569)
                    ·
                      refine ⟨385991623675286141392927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 514655498233714855190569 385991623675286141392927)
                      ·
                        rfl

theorem cell23_751716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_751716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751716 prefixEnd_751716 := by exact prefixLift 751716
  have htrace : WordTrace (prefixWord ++ tailWord_751716) baseStart_751716 baseEnd_751716 := by
    simpa [prefixWord, tailWord_751716, baseEnd_751716] using wordTrace_append hprefix tailTrace_751716
  have hstable : (prefixWord ++ tailWord_751716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751716).length < 2 ^ (prefixWord ++ tailWord_751716).sum := by decide
  have hdescent : baseEnd_751716 < baseStart_751716 := by decide
  rcases family_descends (prefixWord ++ tailWord_751716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751769 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 5, 5]
def baseStart_751769 : Nat := 118140960795 + 751769 * 2 ^ 59
def prefixEnd_751769 : Nat := 4983230072969 + 3 ^ 40 * 751769 * 2
def baseEnd_751769 : Nat := 128672946049991478010061

theorem tailTrace_751769 : CollatzResearch.WordTrace tailWord_751769 prefixEnd_751769 128672946049991478010061 := by
  unfold tailWord_751769
  simp only [CollatzResearch.WordTrace]
  refine ⟨27419268013476779768506361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18279512008984519845670907 27419268013476779768506361)
  ·
    refine ⟨20564451010107584826379771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27419268013476779768506361 20564451010107584826379771)
    ·
      refine ⟨30846676515161377239569657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20564451010107584826379771 30846676515161377239569657)
      ·
        refine ⟨23135007386371032929677243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30846676515161377239569657 23135007386371032929677243)
        ·
          refine ⟨34702511079556549394515865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23135007386371032929677243 34702511079556549394515865)
          ·
            refine ⟨26026883309667412045886899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34702511079556549394515865 26026883309667412045886899)
            ·
              refine ⟨39040324964501118068830349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26026883309667412045886899 39040324964501118068830349)
              ·
                refine ⟨14640121861687919275811381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39040324964501118068830349 14640121861687919275811381)
                ·
                  refine ⟨1372511424533242432107317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14640121861687919275811381 1372511424533242432107317)
                  ·
                    refine ⟨128672946049991478010061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1372511424533242432107317 128672946049991478010061)
                    ·
                      rfl

theorem cell23_751769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 5].length) (baseStart_751769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751769 prefixEnd_751769 := by exact prefixLift 751769
  have htrace : WordTrace (prefixWord ++ tailWord_751769) baseStart_751769 baseEnd_751769 := by
    simpa [prefixWord, tailWord_751769, baseEnd_751769] using wordTrace_append hprefix tailTrace_751769
  have hstable : (prefixWord ++ tailWord_751769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751769).length < 2 ^ (prefixWord ++ tailWord_751769).sum := by decide
  have hdescent : baseEnd_751769 < baseStart_751769 := by decide
  rcases family_descends (prefixWord ++ tailWord_751769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751773 : List Nat := [1, 4, 2, 1, 1, 4, 3, 1, 6]
def baseStart_751773 : Nat := 118140960795 + 751773 * 2 ^ 59
def prefixEnd_751773 : Nat := 4983230072969 + 3 ^ 40 * 751773 * 2
def baseEnd_751773 : Nat := 42891210230288046486685

theorem tailTrace_751773 : CollatzResearch.WordTrace tailWord_751773 prefixEnd_751773 42891210230288046486685 := by
  unfold tailWord_751773
  simp only [CollatzResearch.WordTrace]
  refine ⟨27419413905462288451651973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18279609270308192301101315 27419413905462288451651973)
  ·
    refine ⟨5141140107274179084684745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27419413905462288451651973 5141140107274179084684745)
    ·
      refine ⟨3855855080455634313513559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5141140107274179084684745 3855855080455634313513559)
      ·
        refine ⟨5783782620683451470270339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3855855080455634313513559 5783782620683451470270339)
        ·
          refine ⟨8675673931025177205405509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5783782620683451470270339 8675673931025177205405509)
          ·
            refine ⟨1626688862067220726013533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8675673931025177205405509 1626688862067220726013533)
            ·
              refine ⟨610008323275207772255075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1626688862067220726013533 610008323275207772255075)
              ·
                refine ⟨915012484912811658382613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 610008323275207772255075 915012484912811658382613)
                ·
                  refine ⟨42891210230288046486685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 915012484912811658382613 42891210230288046486685)
                  ·
                    rfl

theorem cell23_751773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_751773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751773 prefixEnd_751773 := by exact prefixLift 751773
  have htrace : WordTrace (prefixWord ++ tailWord_751773) baseStart_751773 baseEnd_751773 := by
    simpa [prefixWord, tailWord_751773, baseEnd_751773] using wordTrace_append hprefix tailTrace_751773
  have hstable : (prefixWord ++ tailWord_751773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751773).length < 2 ^ (prefixWord ++ tailWord_751773).sum := by decide
  have hdescent : baseEnd_751773 < baseStart_751773 := by decide
  rcases family_descends (prefixWord ++ tailWord_751773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751819 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 6]
def baseStart_751819 : Nat := 118140960795 + 751819 * 2 ^ 59
def prefixEnd_751819 : Nat := 4983230072969 + 3 ^ 40 * 751819 * 2
def baseEnd_751819 : Nat := 386044512182699238404953

theorem tailTrace_751819 : CollatzResearch.WordTrace tailWord_751819 prefixEnd_751819 386044512182699238404953 := by
  unfold tailWord_751819
  simp only [CollatzResearch.WordTrace]
  refine ⟨27421091663295638307826511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18280727775530425538551007 27421091663295638307826511)
  ·
    refine ⟨41131637494943457461739767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27421091663295638307826511 41131637494943457461739767)
    ·
      refine ⟨61697456242415186192609651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41131637494943457461739767 61697456242415186192609651)
      ·
        refine ⟨92546184363622779288914477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61697456242415186192609651 92546184363622779288914477)
        ·
          refine ⟨34704819136358542233342929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92546184363622779288914477 34704819136358542233342929)
          ·
            refine ⟨26028614352268906675007197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34704819136358542233342929 26028614352268906675007197)
            ·
              refine ⟨9760730382100840003127699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26028614352268906675007197 9760730382100840003127699)
              ·
                refine ⟨14641095573151260004691549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9760730382100840003127699 14641095573151260004691549)
                ·
                  refine ⟨5490410839931722501759331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14641095573151260004691549 5490410839931722501759331)
                  ·
                    refine ⟨8235616259897583752638997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5490410839931722501759331 8235616259897583752638997)
                    ·
                      refine ⟨386044512182699238404953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8235616259897583752638997 386044512182699238404953)
                      ·
                        rfl

theorem cell23_751819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 6].length) (baseStart_751819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751819 prefixEnd_751819 := by exact prefixLift 751819
  have htrace : WordTrace (prefixWord ++ tailWord_751819) baseStart_751819 baseEnd_751819 := by
    simpa [prefixWord, tailWord_751819, baseEnd_751819] using wordTrace_append hprefix tailTrace_751819
  have hstable : (prefixWord ++ tailWord_751819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751819).length < 2 ^ (prefixWord ++ tailWord_751819).sum := by decide
  have hdescent : baseEnd_751819 < baseStart_751819 := by decide
  rcases family_descends (prefixWord ++ tailWord_751819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751849 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 1, 4, 6]
def baseStart_751849 : Nat := 118140960795 + 751849 * 2 ^ 59
def prefixEnd_751849 : Nat := 4983230072969 + 3 ^ 40 * 751849 * 2
def baseEnd_751849 : Nat := 386059916602334121029815

theorem tailTrace_751849 : CollatzResearch.WordTrace tailWord_751849 prefixEnd_751849 386059916602334121029815 := by
  unfold tailWord_751849
  simp only [CollatzResearch.WordTrace]
  refine ⟨27422185853186953431418601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18281457235457968954279067 27422185853186953431418601)
  ·
    refine ⟨20566639389890215073563951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27422185853186953431418601 20566639389890215073563951)
    ·
      refine ⟨30849959084835322610345927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20566639389890215073563951 30849959084835322610345927)
      ·
        refine ⟨46274938627252983915518891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30849959084835322610345927 46274938627252983915518891)
        ·
          refine ⟨69412407940879475873278337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46274938627252983915518891 69412407940879475873278337)
          ·
            refine ⟨52059305955659606904958753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69412407940879475873278337 52059305955659606904958753)
            ·
              refine ⟨39044479466744705178719065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52059305955659606904958753 39044479466744705178719065)
              ·
                refine ⟨29283359600058528884039299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39044479466744705178719065 29283359600058528884039299)
                ·
                  refine ⟨43925039400087793326058949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29283359600058528884039299 43925039400087793326058949)
                  ·
                    refine ⟨8235944887516461248636053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43925039400087793326058949 8235944887516461248636053)
                    ·
                      refine ⟨386059916602334121029815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8235944887516461248636053 386059916602334121029815)
                      ·
                        rfl

theorem cell23_751849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_751849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751849 prefixEnd_751849 := by exact prefixLift 751849
  have htrace : WordTrace (prefixWord ++ tailWord_751849) baseStart_751849 baseEnd_751849 := by
    simpa [prefixWord, tailWord_751849, baseEnd_751849] using wordTrace_append hprefix tailTrace_751849
  have hstable : (prefixWord ++ tailWord_751849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751849).length < 2 ^ (prefixWord ++ tailWord_751849).sum := by decide
  have hdescent : baseEnd_751849 < baseStart_751849 := by decide
  rcases family_descends (prefixWord ++ tailWord_751849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751883 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 5, 3, 2]
def baseStart_751883 : Nat := 118140960795 + 751883 * 2 ^ 59
def prefixEnd_751883 : Nat := 4983230072969 + 3 ^ 40 * 751883 * 2
def baseEnd_751883 : Nat := 386077374944586988004659

theorem tailTrace_751883 : CollatzResearch.WordTrace tailWord_751883 prefixEnd_751883 386077374944586988004659 := by
  unfold tailWord_751883
  simp only [CollatzResearch.WordTrace]
  refine ⟨27423425935063777238156303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18282283956709184825437535 27423425935063777238156303)
  ·
    refine ⟨41135138902595665857234455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27423425935063777238156303 41135138902595665857234455)
    ·
      refine ⟨61702708353893498785851683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41135138902595665857234455 61702708353893498785851683)
      ·
        refine ⟨92554062530840248178777525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61702708353893498785851683 92554062530840248178777525)
        ·
          refine ⟨8676943362266273266760393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92554062530840248178777525 8676943362266273266760393)
          ·
            refine ⟨6507707521699704950070295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8676943362266273266760393 6507707521699704950070295)
            ·
              refine ⟨9761561282549557425105443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6507707521699704950070295 9761561282549557425105443)
              ·
                refine ⟨14642341923824336137658165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9761561282549557425105443 14642341923824336137658165)
                ·
                  refine ⟨1372719555358531512905453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14642341923824336137658165 1372719555358531512905453)
                  ·
                    refine ⟨514769833259449317339545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1372719555358531512905453 514769833259449317339545)
                    ·
                      refine ⟨386077374944586988004659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 514769833259449317339545 386077374944586988004659)
                      ·
                        rfl

theorem cell23_751883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 3, 2].length) (baseStart_751883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751883 prefixEnd_751883 := by exact prefixLift 751883
  have htrace : WordTrace (prefixWord ++ tailWord_751883) baseStart_751883 baseEnd_751883 := by
    simpa [prefixWord, tailWord_751883, baseEnd_751883] using wordTrace_append hprefix tailTrace_751883
  have hstable : (prefixWord ++ tailWord_751883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751883).length < 2 ^ (prefixWord ++ tailWord_751883).sum := by decide
  have hdescent : baseEnd_751883 < baseStart_751883 := by decide
  rcases family_descends (prefixWord ++ tailWord_751883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751896 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 2, 3, 4]
def baseStart_751896 : Nat := 118140960795 + 751896 * 2 ^ 59
def prefixEnd_751896 : Nat := 4983230072969 + 3 ^ 40 * 751896 * 2
def baseEnd_751896 : Nat := 386084050193095437142099

theorem tailTrace_751896 : CollatzResearch.WordTrace tailWord_751896 prefixEnd_751896 386084050193095437142099 := by
  unfold tailWord_751896
  simp only [CollatzResearch.WordTrace]
  refine ⟨13711950042008340229189771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18282600056011120305586361 13711950042008340229189771)
  ·
    refine ⟨20567925063012510343784657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13711950042008340229189771 20567925063012510343784657)
    ·
      refine ⟨15425943797259382757838493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20567925063012510343784657 15425943797259382757838493)
      ·
        refine ⟨5784728923972268534189435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15425943797259382757838493 5784728923972268534189435)
        ·
          refine ⟨8677093385958402801284153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5784728923972268534189435 8677093385958402801284153)
          ·
            refine ⟨6507820039468802100963115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8677093385958402801284153 6507820039468802100963115)
            ·
              refine ⟨9761730059203203151444673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6507820039468802100963115 9761730059203203151444673)
              ·
                refine ⟨7321297544402402363583505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9761730059203203151444673 7321297544402402363583505)
                ·
                  refine ⟨5490973158301801772687629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7321297544402402363583505 5490973158301801772687629)
                  ·
                    refine ⟨2059114934363175664757861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5490973158301801772687629 2059114934363175664757861)
                    ·
                      refine ⟨386084050193095437142099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2059114934363175664757861 386084050193095437142099)
                      ·
                        rfl

theorem cell23_751896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_751896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751896 prefixEnd_751896 := by exact prefixLift 751896
  have htrace : WordTrace (prefixWord ++ tailWord_751896) baseStart_751896 baseEnd_751896 := by
    simpa [prefixWord, tailWord_751896, baseEnd_751896] using wordTrace_append hprefix tailTrace_751896
  have hstable : (prefixWord ++ tailWord_751896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751896).length < 2 ^ (prefixWord ++ tailWord_751896).sum := by decide
  have hdescent : baseEnd_751896 < baseStart_751896 := by decide
  rcases family_descends (prefixWord ++ tailWord_751896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751900 : List Nat := [2, 2, 3, 1, 1, 1, 1, 6, 1, 3, 2]
def baseStart_751900 : Nat := 118140960795 + 751900 * 2 ^ 59
def prefixEnd_751900 : Nat := 4983230072969 + 3 ^ 40 * 751900 * 2
def baseEnd_751900 : Nat := 386086104115713421492081

theorem tailTrace_751900 : CollatzResearch.WordTrace tailWord_751900 prefixEnd_751900 386086104115713421492081 := by
  unfold tailWord_751900
  simp only [CollatzResearch.WordTrace]
  refine ⟨13712022988001094570762577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18282697317334792761016769 13712022988001094570762577)
  ·
    refine ⟨10284017241000820928071933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13712022988001094570762577 10284017241000820928071933)
    ·
      refine ⟨3856506465375307848026975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10284017241000820928071933 3856506465375307848026975)
      ·
        refine ⟨5784759698062961772040463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3856506465375307848026975 5784759698062961772040463)
        ·
          refine ⟨8677139547094442658060695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5784759698062961772040463 8677139547094442658060695)
          ·
            refine ⟨13015709320641663987091043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8677139547094442658060695 13015709320641663987091043)
            ·
              refine ⟨19523563980962495980636565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13015709320641663987091043 19523563980962495980636565)
              ·
                refine ⟨915167061607616999092339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19523563980962495980636565 915167061607616999092339)
                ·
                  refine ⟨1372750592411425498638509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 915167061607616999092339 1372750592411425498638509)
                  ·
                    refine ⟨514781472154284561989441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1372750592411425498638509 514781472154284561989441)
                    ·
                      refine ⟨386086104115713421492081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 514781472154284561989441 386086104115713421492081)
                      ·
                        rfl

theorem cell23_751900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_751900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751900 prefixEnd_751900 := by exact prefixLift 751900
  have htrace : WordTrace (prefixWord ++ tailWord_751900) baseStart_751900 baseEnd_751900 := by
    simpa [prefixWord, tailWord_751900, baseEnd_751900] using wordTrace_append hprefix tailTrace_751900
  have hstable : (prefixWord ++ tailWord_751900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751900).length < 2 ^ (prefixWord ++ tailWord_751900).sum := by decide
  have hdescent : baseEnd_751900 < baseStart_751900 := by decide
  rcases family_descends (prefixWord ++ tailWord_751900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751916 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 5]
def baseStart_751916 : Nat := 118140960795 + 751916 * 2 ^ 59
def prefixEnd_751916 : Nat := 4983230072969 + 3 ^ 40 * 751916 * 2
def baseEnd_751916 : Nat := 386094319806185358892007

theorem tailTrace_751916 : CollatzResearch.WordTrace tailWord_751916 prefixEnd_751916 386094319806185358892007 := by
  unfold tailWord_751916
  simp only [CollatzResearch.WordTrace]
  refine ⟨13712314771972111937053801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18283086362629482582738401 13712314771972111937053801)
  ·
    refine ⟨10284236078979083952790351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13712314771972111937053801 10284236078979083952790351)
    ·
      refine ⟨15426354118468625929185527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10284236078979083952790351 15426354118468625929185527)
      ·
        refine ⟨23139531177702938893778291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15426354118468625929185527 23139531177702938893778291)
        ·
          refine ⟨34709296766554408340667437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23139531177702938893778291 34709296766554408340667437)
          ·
            refine ⟨13015986287457903127750289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34709296766554408340667437 13015986287457903127750289)
            ·
              refine ⟨9761989715593427345812717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13015986287457903127750289 9761989715593427345812717)
              ·
                refine ⟨3660746143347535254679769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9761989715593427345812717 3660746143347535254679769)
                ·
                  refine ⟨2745559607510651441009827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3660746143347535254679769 2745559607510651441009827)
                  ·
                    refine ⟨4118339411265977161514741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2745559607510651441009827 4118339411265977161514741)
                    ·
                      refine ⟨386094319806185358892007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4118339411265977161514741 386094319806185358892007)
                      ·
                        rfl

theorem cell23_751916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_751916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751916 prefixEnd_751916 := by exact prefixLift 751916
  have htrace : WordTrace (prefixWord ++ tailWord_751916) baseStart_751916 baseEnd_751916 := by
    simpa [prefixWord, tailWord_751916, baseEnd_751916] using wordTrace_append hprefix tailTrace_751916
  have hstable : (prefixWord ++ tailWord_751916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751916).length < 2 ^ (prefixWord ++ tailWord_751916).sum := by decide
  have hdescent : baseEnd_751916 < baseStart_751916 := by decide
  rcases family_descends (prefixWord ++ tailWord_751916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751924 : List Nat := [2, 5, 1, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_751924 : Nat := 118140960795 + 751924 * 2 ^ 59
def prefixEnd_751924 : Nat := 4983230072969 + 3 ^ 40 * 751924 * 2
def baseEnd_751924 : Nat := 386098427651421327591971

theorem tailTrace_751924 : CollatzResearch.WordTrace tailWord_751924 prefixEnd_751924 386098427651421327591971 := by
  unfold tailWord_751924
  simp only [CollatzResearch.WordTrace]
  refine ⟨13712460663957620620199413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18283280885276827493599217 13712460663957620620199413)
  ·
    refine ⟨1285543187246026933143695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13712460663957620620199413 1285543187246026933143695)
    ·
      refine ⟨1928314780869040399715543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1285543187246026933143695 1928314780869040399715543)
      ·
        refine ⟨2892472171303560599573315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1928314780869040399715543 2892472171303560599573315)
        ·
          refine ⟨4338708256955340899359973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2892472171303560599573315 4338708256955340899359973)
          ·
            refine ⟨813507798179126418629995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4338708256955340899359973 813507798179126418629995)
            ·
              refine ⟨1220261697268689627944993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813507798179126418629995 1220261697268689627944993)
              ·
                refine ⟨915196272951517220958745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1220261697268689627944993 915196272951517220958745)
                ·
                  refine ⟨686397204713637915719059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 915196272951517220958745 686397204713637915719059)
                  ·
                    refine ⟨1029595807070456873578589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 686397204713637915719059 1029595807070456873578589)
                    ·
                      refine ⟨386098427651421327591971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1029595807070456873578589 386098427651421327591971)
                      ·
                        rfl

theorem cell23_751924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_751924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751924 prefixEnd_751924 := by exact prefixLift 751924
  have htrace : WordTrace (prefixWord ++ tailWord_751924) baseStart_751924 baseEnd_751924 := by
    simpa [prefixWord, tailWord_751924, baseEnd_751924] using wordTrace_append hprefix tailTrace_751924
  have hstable : (prefixWord ++ tailWord_751924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751924).length < 2 ^ (prefixWord ++ tailWord_751924).sum := by decide
  have hdescent : baseEnd_751924 < baseStart_751924 := by decide
  rcases family_descends (prefixWord ++ tailWord_751924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_751996 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 2, 8]
def baseStart_751996 : Nat := 118140960795 + 751996 * 2 ^ 59
def prefixEnd_751996 : Nat := 4983230072969 + 3 ^ 40 * 751996 * 2
def baseEnd_751996 : Nat := 128711799419515015297213

theorem tailTrace_751996 : CollatzResearch.WordTrace tailWord_751996 prefixEnd_751996 128711799419515015297213 := by
  unfold tailWord_751996
  simp only [CollatzResearch.WordTrace]
  refine ⟨13713773691827198768509921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18285031589102931691346561 13713773691827198768509921)
  ·
    refine ⟨10285330268870399076382441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13713773691827198768509921 10285330268870399076382441)
    ·
      refine ⟨7713997701652799307286831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10285330268870399076382441 7713997701652799307286831)
      ·
        refine ⟨11570996552479198960930247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7713997701652799307286831 11570996552479198960930247)
        ·
          refine ⟨17356494828718798441395371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11570996552479198960930247 17356494828718798441395371)
          ·
            refine ⟨26034742243078197662093057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17356494828718798441395371 26034742243078197662093057)
            ·
              refine ⟨19526056682308648246569793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26034742243078197662093057 19526056682308648246569793)
              ·
                refine ⟨14644542511731486184927345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19526056682308648246569793 14644542511731486184927345)
                ·
                  refine ⟨10983406883798614638695509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14644542511731486184927345 10983406883798614638695509)
                  ·
                    refine ⟨128711799419515015297213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10983406883798614638695509 128711799419515015297213)
                    ·
                      rfl

theorem cell23_751996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_751996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_751996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_751996 prefixEnd_751996 := by exact prefixLift 751996
  have htrace : WordTrace (prefixWord ++ tailWord_751996) baseStart_751996 baseEnd_751996 := by
    simpa [prefixWord, tailWord_751996, baseEnd_751996] using wordTrace_append hprefix tailTrace_751996
  have hstable : (prefixWord ++ tailWord_751996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_751996).length < 2 ^ (prefixWord ++ tailWord_751996).sum := by decide
  have hdescent : baseEnd_751996 < baseStart_751996 := by decide
  rcases family_descends (prefixWord ++ tailWord_751996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752016 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 6]
def baseStart_752016 : Nat := 118140960795 + 752016 * 2 ^ 59
def prefixEnd_752016 : Nat := 4983230072969 + 3 ^ 40 * 752016 * 2
def baseEnd_752016 : Nat := 386145667871634967641547

theorem tailTrace_752016 : CollatzResearch.WordTrace tailWord_752016 prefixEnd_752016 386145667871634967641547 := by
  unfold tailWord_752016
  simp only [CollatzResearch.WordTrace]
  refine ⟨13714138421790970476373951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18285517895721293968498601 13714138421790970476373951)
  ·
    refine ⟨20571207632686455714560927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13714138421790970476373951 20571207632686455714560927)
    ·
      refine ⟨30856811449029683571841391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20571207632686455714560927 30856811449029683571841391)
      ·
        refine ⟨46285217173544525357762087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30856811449029683571841391 46285217173544525357762087)
        ·
          refine ⟨69427825760316788036643131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46285217173544525357762087 69427825760316788036643131)
          ·
            refine ⟨104141738640475182054964697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69427825760316788036643131 104141738640475182054964697)
            ·
              refine ⟨78106303980356386541223523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104141738640475182054964697 78106303980356386541223523)
              ·
                refine ⟨117159455970534579811835285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78106303980356386541223523 117159455970534579811835285)
                ·
                  refine ⟨5491849498618808428679779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117159455970534579811835285 5491849498618808428679779)
                  ·
                    refine ⟨8237774247928212643019669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5491849498618808428679779 8237774247928212643019669)
                    ·
                      refine ⟨386145667871634967641547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8237774247928212643019669 386145667871634967641547)
                      ·
                        rfl

theorem cell23_752016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_752016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752016 prefixEnd_752016 := by exact prefixLift 752016
  have htrace : WordTrace (prefixWord ++ tailWord_752016) baseStart_752016 baseEnd_752016 := by
    simpa [prefixWord, tailWord_752016, baseEnd_752016] using wordTrace_append hprefix tailTrace_752016
  have hstable : (prefixWord ++ tailWord_752016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752016).length < 2 ^ (prefixWord ++ tailWord_752016).sum := by decide
  have hdescent : baseEnd_752016 < baseStart_752016 := by decide
  rcases family_descends (prefixWord ++ tailWord_752016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752023 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 3]
def baseStart_752023 : Nat := 118140960795 + 752023 * 2 ^ 59
def prefixEnd_752023 : Nat := 4983230072969 + 3 ^ 40 * 752023 * 2
def baseEnd_752023 : Nat := 386149262236216440254015

theorem tailTrace_752023 : CollatzResearch.WordTrace tailWord_752023 prefixEnd_752023 386149262236216440254015 := by
  unfold tailWord_752023
  simp only [CollatzResearch.WordTrace]
  refine ⟨27428532154556581148252723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18285688103037720765501815 27428532154556581148252723)
  ·
    refine ⟨41142798231834871722379085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27428532154556581148252723 41142798231834871722379085)
    ·
      refine ⟨15428549336938076895892157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41142798231834871722379085 15428549336938076895892157)
      ·
        refine ⟨5785706001351778835959559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15428549336938076895892157 5785706001351778835959559)
        ·
          refine ⟨8678559002027668253939339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5785706001351778835959559 8678559002027668253939339)
          ·
            refine ⟨13017838503041502380909009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8678559002027668253939339 13017838503041502380909009)
            ·
              refine ⟨9763378877281126785681757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13017838503041502380909009 9763378877281126785681757)
              ·
                refine ⟨3661267078980422544630659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9763378877281126785681757 3661267078980422544630659)
                ·
                  refine ⟨5491900618470633816945989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3661267078980422544630659 5491900618470633816945989)
                  ·
                    refine ⟨1029731365963243840677373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5491900618470633816945989 1029731365963243840677373)
                    ·
                      refine ⟨386149262236216440254015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1029731365963243840677373 386149262236216440254015)
                      ·
                        rfl

theorem cell23_752023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_752023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752023 prefixEnd_752023 := by exact prefixLift 752023
  have htrace : WordTrace (prefixWord ++ tailWord_752023) baseStart_752023 baseEnd_752023 := by
    simpa [prefixWord, tailWord_752023, baseEnd_752023] using wordTrace_append hprefix tailTrace_752023
  have hstable : (prefixWord ++ tailWord_752023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752023).length < 2 ^ (prefixWord ++ tailWord_752023).sum := by decide
  have hdescent : baseEnd_752023 < baseStart_752023 := by decide
  rcases family_descends (prefixWord ++ tailWord_752023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752060 : List Nat := [2, 2, 2, 4, 1, 1, 2, 3, 6]
def baseStart_752060 : Nat := 118140960795 + 752060 * 2 ^ 59
def prefixEnd_752060 : Nat := 4983230072969 + 3 ^ 40 * 752060 * 2
def baseEnd_752060 : Nat := 42907584557825866165705

theorem tailTrace_752060 : CollatzResearch.WordTrace tailWord_752060 prefixEnd_752060 42907584557825866165705 := by
  unfold tailWord_752060
  simp only [CollatzResearch.WordTrace]
  refine ⟨13714940827711268233674817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18286587770281690978233089 13714940827711268233674817)
  ·
    refine ⟨10286205620783451175256113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13714940827711268233674817 10286205620783451175256113)
    ·
      refine ⟨7714654215587588381442085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10286205620783451175256113 7714654215587588381442085)
      ·
        refine ⟨1446497665422672821520391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7714654215587588381442085 1446497665422672821520391)
        ·
          refine ⟨2169746498134009232280587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1446497665422672821520391 2169746498134009232280587)
          ·
            refine ⟨3254619747201013848420881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2169746498134009232280587 3254619747201013848420881)
            ·
              refine ⟨2440964810400760386315661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3254619747201013848420881 2440964810400760386315661)
              ·
                refine ⟨915361803900285144868373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2440964810400760386315661 915361803900285144868373)
                ·
                  refine ⟨42907584557825866165705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 915361803900285144868373 42907584557825866165705)
                  ·
                    rfl

theorem cell23_752060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 6].length) (baseStart_752060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752060 prefixEnd_752060 := by exact prefixLift 752060
  have htrace : WordTrace (prefixWord ++ tailWord_752060) baseStart_752060 baseEnd_752060 := by
    simpa [prefixWord, tailWord_752060, baseEnd_752060] using wordTrace_append hprefix tailTrace_752060
  have hstable : (prefixWord ++ tailWord_752060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752060).length < 2 ^ (prefixWord ++ tailWord_752060).sum := by decide
  have hdescent : baseEnd_752060 < baseStart_752060 := by decide
  rcases family_descends (prefixWord ++ tailWord_752060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752073 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 3, 5]
def baseStart_752073 : Nat := 118140960795 + 752073 * 2 ^ 59
def prefixEnd_752073 : Nat := 4983230072969 + 3 ^ 40 * 752073 * 2
def baseEnd_752073 : Nat := 128724978756313748209595

theorem tailTrace_752073 : CollatzResearch.WordTrace tailWord_752073 prefixEnd_752073 128724978756313748209595 := by
  unfold tailWord_752073
  simp only [CollatzResearch.WordTrace]
  refine ⟨27430355804375439687572873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18286903869583626458381915 27430355804375439687572873)
  ·
    refine ⟨20572766853281579765679655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27430355804375439687572873 20572766853281579765679655)
    ·
      refine ⟨30859150279922369648519483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20572766853281579765679655 30859150279922369648519483)
      ·
        refine ⟨46288725419883554472779225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30859150279922369648519483 46288725419883554472779225)
        ·
          refine ⟨34716544064912665854584419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46288725419883554472779225 34716544064912665854584419)
          ·
            refine ⟨52074816097368998781876629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34716544064912665854584419 52074816097368998781876629)
            ·
              refine ⟨2441007004564171817900467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52074816097368998781876629 2441007004564171817900467)
              ·
                refine ⟨3661510506846257726850701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2441007004564171817900467 3661510506846257726850701)
                ·
                  refine ⟨1373066440067346647569013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3661510506846257726850701 1373066440067346647569013)
                  ·
                    refine ⟨128724978756313748209595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1373066440067346647569013 128724978756313748209595)
                    ·
                      rfl

theorem cell23_752073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 5].length) (baseStart_752073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752073 prefixEnd_752073 := by exact prefixLift 752073
  have htrace : WordTrace (prefixWord ++ tailWord_752073) baseStart_752073 baseEnd_752073 := by
    simpa [prefixWord, tailWord_752073, baseEnd_752073] using wordTrace_append hprefix tailTrace_752073
  have hstable : (prefixWord ++ tailWord_752073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752073).length < 2 ^ (prefixWord ++ tailWord_752073).sum := by decide
  have hdescent : baseEnd_752073 < baseStart_752073 := by decide
  rcases family_descends (prefixWord ++ tailWord_752073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752090 : List Nat := [3, 1, 1, 2, 3, 1, 3, 3, 1, 5]
def baseStart_752090 : Nat := 118140960795 + 752090 * 2 ^ 59
def prefixEnd_752090 : Nat := 4983230072969 + 3 ^ 40 * 752090 * 2
def baseEnd_752090 : Nat := 128727888480022559372069

theorem tailTrace_752090 : CollatzResearch.WordTrace tailWord_752090 prefixEnd_752090 128727888480022559372069 := by
  unfold tailWord_752090
  simp only [CollatzResearch.WordTrace]
  refine ⟨6857743961328462897735431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18287317230209234393961149 6857743961328462897735431)
  ·
    refine ⟨10286615941992694346603147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6857743961328462897735431 10286615941992694346603147)
    ·
      refine ⟨15429923912989041519904721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10286615941992694346603147 15429923912989041519904721)
      ·
        refine ⟨11572442934741781139928541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15429923912989041519904721 11572442934741781139928541)
        ·
          refine ⟨4339666100528167927473203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11572442934741781139928541 4339666100528167927473203)
          ·
            refine ⟨6509499150792251891209805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4339666100528167927473203 6509499150792251891209805)
            ·
              refine ⟨2441062181547094459203677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6509499150792251891209805 2441062181547094459203677)
              ·
                refine ⟨915398318080160422201379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2441062181547094459203677 915398318080160422201379)
                ·
                  refine ⟨1373097477120240633302069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 915398318080160422201379 1373097477120240633302069)
                  ·
                    refine ⟨128727888480022559372069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1373097477120240633302069 128727888480022559372069)
                    ·
                      rfl

theorem cell23_752090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 1, 5].length) (baseStart_752090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752090 prefixEnd_752090 := by exact prefixLift 752090
  have htrace : WordTrace (prefixWord ++ tailWord_752090) baseStart_752090 baseEnd_752090 := by
    simpa [prefixWord, tailWord_752090, baseEnd_752090] using wordTrace_append hprefix tailTrace_752090
  have hstable : (prefixWord ++ tailWord_752090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752090).length < 2 ^ (prefixWord ++ tailWord_752090).sum := by decide
  have hdescent : baseEnd_752090 < baseStart_752090 := by decide
  rcases family_descends (prefixWord ++ tailWord_752090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752104 : List Nat := [2, 1, 4, 1, 1, 3, 2, 4, 1, 1, 3]
def baseStart_752104 : Nat := 118140960795 + 752104 * 2 ^ 59
def prefixEnd_752104 : Nat := 4983230072969 + 3 ^ 40 * 752104 * 2
def baseEnd_752104 : Nat := 386190854169230623341143

theorem tailTrace_752104 : CollatzResearch.WordTrace tailWord_752104 prefixEnd_752104 386190854169230623341143 := by
  unfold tailWord_752104
  simp only [CollatzResearch.WordTrace]
  refine ⟨13715743233631565990975683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18287657644842087987967577 13715743233631565990975683)
  ·
    refine ⟨20573614850447348986463525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13715743233631565990975683 20573614850447348986463525)
    ·
      refine ⟨3857552784458877934961911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20573614850447348986463525 3857552784458877934961911)
      ·
        refine ⟨5786329176688316902442867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3857552784458877934961911 5786329176688316902442867)
        ·
          refine ⟨8679493765032475353664301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5786329176688316902442867 8679493765032475353664301)
          ·
            refine ⟨3254810161887178257624113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8679493765032475353664301 3254810161887178257624113)
            ·
              refine ⟨2441107621415383693218085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3254810161887178257624113 2441107621415383693218085)
              ·
                refine ⟨457707679015384442478391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2441107621415383693218085 457707679015384442478391)
                ·
                  refine ⟨686561518523076663717587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 457707679015384442478391 686561518523076663717587)
                  ·
                    refine ⟨1029842277784614995576381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 686561518523076663717587 1029842277784614995576381)
                    ·
                      refine ⟨386190854169230623341143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1029842277784614995576381 386190854169230623341143)
                      ·
                        rfl

theorem cell23_752104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_752104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752104 prefixEnd_752104 := by exact prefixLift 752104
  have htrace : WordTrace (prefixWord ++ tailWord_752104) baseStart_752104 baseEnd_752104 := by
    simpa [prefixWord, tailWord_752104, baseEnd_752104] using wordTrace_append hprefix tailTrace_752104
  have hstable : (prefixWord ++ tailWord_752104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752104).length < 2 ^ (prefixWord ++ tailWord_752104).sum := by decide
  have hdescent : baseEnd_752104 < baseStart_752104 := by decide
  rcases family_descends (prefixWord ++ tailWord_752104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752127 : List Nat := [1, 1, 2, 2, 1, 2, 3, 4, 3, 2, 2]
def baseStart_752127 : Nat := 118140960795 + 752127 * 2 ^ 59
def prefixEnd_752127 : Nat := 4983230072969 + 3 ^ 40 * 752127 * 2
def baseEnd_752127 : Nat := 386202664224284033353537

theorem tailTrace_752127 : CollatzResearch.WordTrace tailWord_752127 prefixEnd_752127 386202664224284033353537 := by
  unfold tailWord_752127
  simp only [CollatzResearch.WordTrace]
  refine ⟨27432325346179806910038635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18288216897453204606692423 27432325346179806910038635)
  ·
    refine ⟨41148488019269710365057953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27432325346179806910038635 41148488019269710365057953)
    ·
      refine ⟨30861366014452282773793465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41148488019269710365057953 30861366014452282773793465)
      ·
        refine ⟨23146024510839212080345099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30861366014452282773793465 23146024510839212080345099)
        ·
          refine ⟨34719036766258818120517649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23146024510839212080345099 34719036766258818120517649)
          ·
            refine ⟨26039277574694113590388237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34719036766258818120517649 26039277574694113590388237)
            ·
              refine ⟨9764729090510292596395589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26039277574694113590388237 9764729090510292596395589)
              ·
                refine ⟨1830886704470679861824173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9764729090510292596395589 1830886704470679861824173)
                ·
                  refine ⟨686582514176504948184065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1830886704470679861824173 686582514176504948184065)
                  ·
                    refine ⟨514936885632378711138049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 686582514176504948184065 514936885632378711138049)
                    ·
                      refine ⟨386202664224284033353537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 514936885632378711138049 386202664224284033353537)
                      ·
                        rfl

theorem cell23_752127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 2, 2].length) (baseStart_752127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752127 prefixEnd_752127 := by exact prefixLift 752127
  have htrace : WordTrace (prefixWord ++ tailWord_752127) baseStart_752127 baseEnd_752127 := by
    simpa [prefixWord, tailWord_752127, baseEnd_752127] using wordTrace_append hprefix tailTrace_752127
  have hstable : (prefixWord ++ tailWord_752127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752127).length < 2 ^ (prefixWord ++ tailWord_752127).sum := by decide
  have hdescent : baseEnd_752127 < baseStart_752127 := by decide
  rcases family_descends (prefixWord ++ tailWord_752127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752198 : List Nat := [6, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_752198 : Nat := 118140960795 + 752198 * 2 ^ 59
def prefixEnd_752198 : Nat := 4983230072969 + 3 ^ 40 * 752198 * 2
def baseEnd_752198 : Nat := 386239121350753255565711

theorem tailTrace_752198 : CollatzResearch.WordTrace tailWord_752198 prefixEnd_752198 386239121350753255565711 := by
  unfold tailWord_752198
  simp only [CollatzResearch.WordTrace]
  refine ⟨857341091528830813621039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18289943285948390690582165 857341091528830813621039)
  ·
    refine ⟨1286011637293246220431559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 857341091528830813621039 1286011637293246220431559)
    ·
      refine ⟨1929017455939869330647339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1286011637293246220431559 1929017455939869330647339)
      ·
        refine ⟨2893526183909803995971009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1929017455939869330647339 2893526183909803995971009)
        ·
          refine ⟨2170144637932352996978257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2893526183909803995971009 2170144637932352996978257)
          ·
            refine ⟨1627608478449264747733693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2170144637932352996978257 1627608478449264747733693)
            ·
              refine ⟨610353179418474280400135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1627608478449264747733693 610353179418474280400135)
              ·
                refine ⟨915529769127711420600203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 610353179418474280400135 915529769127711420600203)
                ·
                  refine ⟨1373294653691567130900305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 915529769127711420600203 1373294653691567130900305)
                  ·
                    refine ⟨1029970990268675348175229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1373294653691567130900305 1029970990268675348175229)
                    ·
                      refine ⟨386239121350753255565711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1029970990268675348175229 386239121350753255565711)
                      ·
                        rfl

theorem cell23_752198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_752198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752198 prefixEnd_752198 := by exact prefixLift 752198
  have htrace : WordTrace (prefixWord ++ tailWord_752198) baseStart_752198 baseEnd_752198 := by
    simpa [prefixWord, tailWord_752198, baseEnd_752198] using wordTrace_append hprefix tailTrace_752198
  have hstable : (prefixWord ++ tailWord_752198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752198).length < 2 ^ (prefixWord ++ tailWord_752198).sum := by decide
  have hdescent : baseEnd_752198 < baseStart_752198 := by decide
  rcases family_descends (prefixWord ++ tailWord_752198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752210 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 2, 6]
def baseStart_752210 : Nat := 118140960795 + 752210 * 2 ^ 59
def prefixEnd_752210 : Nat := 4983230072969 + 3 ^ 40 * 752210 * 2
def baseEnd_752210 : Nat := 128748427706202402871885

theorem tailTrace_752210 : CollatzResearch.WordTrace tailWord_752210 prefixEnd_752210 128748427706202402871885 := by
  unfold tailWord_752210
  simp only [CollatzResearch.WordTrace]
  refine ⟨6858838151219778021327521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18290235069919408056873389 6858838151219778021327521)
  ·
    refine ⟨5144128613414833515995641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6858838151219778021327521 5144128613414833515995641)
    ·
      refine ⟨3858096460061125136996731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5144128613414833515995641 3858096460061125136996731)
      ·
        refine ⟨5787144690091687705495097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3858096460061125136996731 5787144690091687705495097)
        ·
          refine ⟨4340358517568765779121323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5787144690091687705495097 4340358517568765779121323)
          ·
            refine ⟨6510537776353148668681985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4340358517568765779121323 6510537776353148668681985)
            ·
              refine ⟨4882903332264861501511489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6510537776353148668681985 4882903332264861501511489)
              ·
                refine ⟨3662177499198646126133617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4882903332264861501511489 3662177499198646126133617)
                ·
                  refine ⟨2746633124398984594600213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3662177499198646126133617 2746633124398984594600213)
                  ·
                    refine ⟨128748427706202402871885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2746633124398984594600213 128748427706202402871885)
                    ·
                      rfl

theorem cell23_752210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_752210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752210 prefixEnd_752210 := by exact prefixLift 752210
  have htrace : WordTrace (prefixWord ++ tailWord_752210) baseStart_752210 baseEnd_752210 := by
    simpa [prefixWord, tailWord_752210, baseEnd_752210] using wordTrace_append hprefix tailTrace_752210
  have hstable : (prefixWord ++ tailWord_752210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752210).length < 2 ^ (prefixWord ++ tailWord_752210).sum := by decide
  have hdescent : baseEnd_752210 < baseStart_752210 := by decide
  rcases family_descends (prefixWord ++ tailWord_752210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752223 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 11]
def baseStart_752223 : Nat := 118140960795 + 752223 * 2 ^ 59
def prefixEnd_752223 : Nat := 4983230072969 + 3 ^ 40 * 752223 * 2
def baseEnd_752223 : Nat := 42916884263012850861455

theorem tailTrace_752223 : CollatzResearch.WordTrace tailWord_752223 prefixEnd_752223 42916884263012850861455 := by
  unfold tailWord_752223
  simp only [CollatzResearch.WordTrace]
  refine ⟨27435826753832015305533323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18290551169221343537022215 27435826753832015305533323)
  ·
    refine ⟨41153740130748022958299985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27435826753832015305533323 41153740130748022958299985)
    ·
      refine ⟨30865305098061017218724989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41153740130748022958299985 30865305098061017218724989)
      ·
        refine ⟨11574489411772881457021871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30865305098061017218724989 11574489411772881457021871)
        ·
          refine ⟨17361734117659322185532807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11574489411772881457021871 17361734117659322185532807)
          ·
            refine ⟨26042601176488983278299211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17361734117659322185532807 26042601176488983278299211)
            ·
              refine ⟨39063901764733474917448817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26042601176488983278299211 39063901764733474917448817)
              ·
                refine ⟨29297926323550106188086613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39063901764733474917448817 29297926323550106188086613)
                ·
                  refine ⟨42916884263012850861455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 29297926323550106188086613 42916884263012850861455)
                  ·
                    rfl

theorem cell23_752223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 11].length) (baseStart_752223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752223 prefixEnd_752223 := by exact prefixLift 752223
  have htrace : WordTrace (prefixWord ++ tailWord_752223) baseStart_752223 baseEnd_752223 := by
    simpa [prefixWord, tailWord_752223, baseEnd_752223] using wordTrace_append hprefix tailTrace_752223
  have hstable : (prefixWord ++ tailWord_752223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752223).length < 2 ^ (prefixWord ++ tailWord_752223).sum := by decide
  have hdescent : baseEnd_752223 < baseStart_752223 := by decide
  rcases family_descends (prefixWord ++ tailWord_752223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752234 : List Nat := [3, 1, 3, 2, 1, 1, 4, 1, 1, 4, 2]
def baseStart_752234 : Nat := 118140960795 + 752234 * 2 ^ 59
def prefixEnd_752234 : Nat := 4983230072969 + 3 ^ 40 * 752234 * 2
def baseEnd_752234 : Nat := 386257606654315114715545

theorem tailTrace_752234 : CollatzResearch.WordTrace tailWord_752234 prefixEnd_752234 386257606654315114715545 := by
  unfold tailWord_752234
  simp only [CollatzResearch.WordTrace]
  refine ⟨6859056989198041046045939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18290818637861442789455837 6859056989198041046045939)
  ·
    refine ⟨10288585483797061569068909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6859056989198041046045939 10288585483797061569068909)
    ·
      refine ⟨3858219556423898088400841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10288585483797061569068909 3858219556423898088400841)
      ·
        refine ⟨2893664667317923566300631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3858219556423898088400841 2893664667317923566300631)
        ·
          refine ⟨4340497000976885349450947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2893664667317923566300631 4340497000976885349450947)
          ·
            refine ⟨6510745501465328024176421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4340497000976885349450947 6510745501465328024176421)
            ·
              refine ⟨1220764781524749004533079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6510745501465328024176421 1220764781524749004533079)
              ·
                refine ⟨1831147172287123506799619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1220764781524749004533079 1831147172287123506799619)
                ·
                  refine ⟨2746720758430685260199429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1831147172287123506799619 2746720758430685260199429)
                  ·
                    refine ⟨515010142205753486287393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2746720758430685260199429 515010142205753486287393)
                    ·
                      refine ⟨386257606654315114715545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 515010142205753486287393 386257606654315114715545)
                      ·
                        rfl

theorem cell23_752234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_752234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752234 prefixEnd_752234 := by exact prefixLift 752234
  have htrace : WordTrace (prefixWord ++ tailWord_752234) baseStart_752234 baseEnd_752234 := by
    simpa [prefixWord, tailWord_752234, baseEnd_752234] using wordTrace_append hprefix tailTrace_752234
  have hstable : (prefixWord ++ tailWord_752234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752234).length < 2 ^ (prefixWord ++ tailWord_752234).sum := by decide
  have hdescent : baseEnd_752234 < baseStart_752234 := by decide
  rcases family_descends (prefixWord ++ tailWord_752234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752274 : List Nat := [3, 2, 3, 1, 2, 1, 2, 4, 5]
def baseStart_752274 : Nat := 118140960795 + 752274 * 2 ^ 59
def prefixEnd_752274 : Nat := 4983230072969 + 3 ^ 40 * 752274 * 2
def baseEnd_752274 : Nat := 42919793986721662023929

theorem tailTrace_752274 : CollatzResearch.WordTrace tailWord_752274 prefixEnd_752274 42919793986721662023929 := by
  unfold tailWord_752274
  simp only [CollatzResearch.WordTrace]
  refine ⟨6859421719161812753909969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18291791251098167343759917 6859421719161812753909969)
  ·
    refine ⟨5144566289371359565432477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6859421719161812753909969 5144566289371359565432477)
    ·
      refine ⟨1929212358514259837037179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5144566289371359565432477 1929212358514259837037179)
      ·
        refine ⟨2893818537771389755555769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1929212358514259837037179 2893818537771389755555769)
        ·
          refine ⟨2170363903328542316666827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2893818537771389755555769 2170363903328542316666827)
          ·
            refine ⟨3255545854992813475000241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2170363903328542316666827 3255545854992813475000241)
            ·
              refine ⟨2441659391244610106250181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3255545854992813475000241 2441659391244610106250181)
              ·
                refine ⟨457811135858364394921909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2441659391244610106250181 457811135858364394921909)
                ·
                  refine ⟨42919793986721662023929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 457811135858364394921909 42919793986721662023929)
                  ·
                    rfl

theorem cell23_752274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_752274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752274 prefixEnd_752274 := by exact prefixLift 752274
  have htrace : WordTrace (prefixWord ++ tailWord_752274) baseStart_752274 baseEnd_752274 := by
    simpa [prefixWord, tailWord_752274, baseEnd_752274] using wordTrace_append hprefix tailTrace_752274
  have hstable : (prefixWord ++ tailWord_752274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752274).length < 2 ^ (prefixWord ++ tailWord_752274).sum := by decide
  have hdescent : baseEnd_752274 < baseStart_752274 := by decide
  rcases family_descends (prefixWord ++ tailWord_752274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752280 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 1, 1, 7]
def baseStart_752280 : Nat := 118140960795 + 752280 * 2 ^ 59
def prefixEnd_752280 : Nat := 4983230072969 + 3 ^ 40 * 752280 * 2
def baseEnd_752280 : Nat := 386281226764421934740333

theorem tailTrace_752280 : CollatzResearch.WordTrace tailWord_752280 prefixEnd_752280 386281226764421934740333 := by
  unfold tailWord_752280
  simp only [CollatzResearch.WordTrace]
  refine ⟨13718952857312757020179147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18291937143083676026905529 13718952857312757020179147)
  ·
    refine ⟨20578429285969135530268721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13718952857312757020179147 20578429285969135530268721)
    ·
      refine ⟨15433821964476851647701541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20578429285969135530268721 15433821964476851647701541)
      ·
        refine ⟨2893841618339409683944039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15433821964476851647701541 2893841618339409683944039)
        ·
          refine ⟨4340762427509114525916059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2893841618339409683944039 4340762427509114525916059)
          ·
            refine ⟨6511143641263671788874089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4340762427509114525916059 6511143641263671788874089)
            ·
              refine ⟨4883357730947753841655567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6511143641263671788874089 4883357730947753841655567)
              ·
                refine ⟨7325036596421630762483351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4883357730947753841655567 7325036596421630762483351)
                ·
                  refine ⟨10987554894632446143725027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7325036596421630762483351 10987554894632446143725027)
                  ·
                    refine ⟨16481332341948669215587541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10987554894632446143725027 16481332341948669215587541)
                    ·
                      refine ⟨386281226764421934740333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16481332341948669215587541 386281226764421934740333)
                      ·
                        rfl

theorem cell23_752280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_752280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752280 prefixEnd_752280 := by exact prefixLift 752280
  have htrace : WordTrace (prefixWord ++ tailWord_752280) baseStart_752280 baseEnd_752280 := by
    simpa [prefixWord, tailWord_752280, baseEnd_752280] using wordTrace_append hprefix tailTrace_752280
  have hstable : (prefixWord ++ tailWord_752280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752280).length < 2 ^ (prefixWord ++ tailWord_752280).sum := by decide
  have hdescent : baseEnd_752280 < baseStart_752280 := by decide
  rcases family_descends (prefixWord ++ tailWord_752280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752321 : List Nat := [1, 2, 6, 2, 1, 1, 1, 2, 2, 5]
def baseStart_752321 : Nat := 118140960795 + 752321 * 2 ^ 59
def prefixEnd_752321 : Nat := 4983230072969 + 3 ^ 40 * 752321 * 2
def baseEnd_752321 : Nat := 128767426490418758109215

theorem tailTrace_752321 : CollatzResearch.WordTrace tailWord_752321 prefixEnd_752321 128767426490418758109215 := by
  unfold tailWord_752321
  simp only [CollatzResearch.WordTrace]
  refine ⟨27439401107476978042600817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18292934071651318695067211 27439401107476978042600817)
  ·
    refine ⟨20579550830607733531950613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27439401107476978042600817 20579550830607733531950613)
    ·
      refine ⟨964666445184737509310185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20579550830607733531950613 964666445184737509310185)
      ·
        refine ⟨723499833888553131982639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 964666445184737509310185 723499833888553131982639)
        ·
          refine ⟨1085249750832829697973959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 723499833888553131982639 1085249750832829697973959)
          ·
            refine ⟨1627874626249244546960939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085249750832829697973959 1627874626249244546960939)
            ·
              refine ⟨2441811939373866820441409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1627874626249244546960939 2441811939373866820441409)
              ·
                refine ⟨1831358954530400115331057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2441811939373866820441409 1831358954530400115331057)
                ·
                  refine ⟨1373519215897800086498293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1831358954530400115331057 1373519215897800086498293)
                  ·
                    refine ⟨128767426490418758109215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1373519215897800086498293 128767426490418758109215)
                    ·
                      rfl

theorem cell23_752321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_752321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752321 prefixEnd_752321 := by exact prefixLift 752321
  have htrace : WordTrace (prefixWord ++ tailWord_752321) baseStart_752321 baseEnd_752321 := by
    simpa [prefixWord, tailWord_752321, baseEnd_752321] using wordTrace_append hprefix tailTrace_752321
  have hstable : (prefixWord ++ tailWord_752321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752321).length < 2 ^ (prefixWord ++ tailWord_752321).sum := by decide
  have hdescent : baseEnd_752321 < baseStart_752321 := by decide
  rcases family_descends (prefixWord ++ tailWord_752321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752324 : List Nat := [2, 3, 3, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_752324 : Nat := 118140960795 + 752324 * 2 ^ 59
def prefixEnd_752324 : Nat := 4983230072969 + 3 ^ 40 * 752324 * 2
def baseEnd_752324 : Nat := 386303819913219762590131

theorem tailTrace_752324 : CollatzResearch.WordTrace tailWord_752324 prefixEnd_752324 386303819913219762590131 := by
  unfold tailWord_752324
  simp only [CollatzResearch.WordTrace]
  refine ⟨13719755263233054777480013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18293007017644073036640017 13719755263233054777480013)
  ·
    refine ⟨5144908223712395541555005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13719755263233054777480013 5144908223712395541555005)
    ·
      refine ⟨1929340583892148328083127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5144908223712395541555005 1929340583892148328083127)
      ·
        refine ⟨2894010875838222492124691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1929340583892148328083127 2894010875838222492124691)
        ·
          refine ⟨4341016313757333738187037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2894010875838222492124691 4341016313757333738187037)
          ·
            refine ⟨1627881117659000151820139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4341016313757333738187037 1627881117659000151820139)
            ·
              refine ⟨2441821676488500227730209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1627881117659000151820139 2441821676488500227730209)
              ·
                refine ⟨1831366257366375170797657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2441821676488500227730209 1831366257366375170797657)
                ·
                  refine ⟨1373524693024781378098243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1831366257366375170797657 1373524693024781378098243)
                  ·
                    refine ⟨2060287039537172067147365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1373524693024781378098243 2060287039537172067147365)
                    ·
                      refine ⟨386303819913219762590131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2060287039537172067147365 386303819913219762590131)
                      ·
                        rfl

theorem cell23_752324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_752324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752324 prefixEnd_752324 := by exact prefixLift 752324
  have htrace : WordTrace (prefixWord ++ tailWord_752324) baseStart_752324 baseEnd_752324 := by
    simpa [prefixWord, tailWord_752324, baseEnd_752324] using wordTrace_append hprefix tailTrace_752324
  have hstable : (prefixWord ++ tailWord_752324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752324).length < 2 ^ (prefixWord ++ tailWord_752324).sum := by decide
  have hdescent : baseEnd_752324 < baseStart_752324 := by decide
  rcases family_descends (prefixWord ++ tailWord_752324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752334 : List Nat := [4, 1, 1, 1, 3, 2, 3, 1, 3, 4]
def baseStart_752334 : Nat := 118140960795 + 752334 * 2 ^ 59
def prefixEnd_752334 : Nat := 4983230072969 + 3 ^ 40 * 752334 * 2
def baseEnd_752334 : Nat := 128769651573254907821695

theorem tailTrace_752334 : CollatzResearch.WordTrace tailWord_752334 prefixEnd_752334 128769651573254907821695 := by
  unfold tailWord_752334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3429984407053735157853007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18293250170953254175216037 3429984407053735157853007)
  ·
    refine ⟨5144976610580602736779511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3429984407053735157853007 5144976610580602736779511)
    ·
      refine ⟨7717464915870904105169267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5144976610580602736779511 7717464915870904105169267)
      ·
        refine ⟨11576197373806356157753901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7717464915870904105169267 11576197373806356157753901)
        ·
          refine ⟨4341074015177383559157713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11576197373806356157753901 4341074015177383559157713)
          ·
            refine ⟨3255805511383037669368285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4341074015177383559157713 3255805511383037669368285)
            ·
              refine ⟨1220927066768639126013107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3255805511383037669368285 1220927066768639126013107)
              ·
                refine ⟨1831390600152958689019661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1220927066768639126013107 1831390600152958689019661)
                ·
                  refine ⟨686771475057359508382373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1831390600152958689019661 686771475057359508382373)
                  ·
                    refine ⟨128769651573254907821695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 686771475057359508382373 128769651573254907821695)
                    ·
                      rfl

theorem cell23_752334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_752334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752334 prefixEnd_752334 := by exact prefixLift 752334
  have htrace : WordTrace (prefixWord ++ tailWord_752334) baseStart_752334 baseEnd_752334 := by
    simpa [prefixWord, tailWord_752334, baseEnd_752334] using wordTrace_append hprefix tailTrace_752334
  have hstable : (prefixWord ++ tailWord_752334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752334).length < 2 ^ (prefixWord ++ tailWord_752334).sum := by decide
  have hdescent : baseEnd_752334 < baseStart_752334 := by decide
  rcases family_descends (prefixWord ++ tailWord_752334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752377 : List Nat := [1, 2, 1, 3, 1, 1, 1, 7, 1, 5]
def baseStart_752377 : Nat := 118140960795 + 752377 * 2 ^ 59
def prefixEnd_752377 : Nat := 4983230072969 + 3 ^ 40 * 752377 * 2
def baseEnd_752377 : Nat := 128777011462636018409129

theorem tailTrace_752377 : CollatzResearch.WordTrace tailWord_752377 prefixEnd_752377 128777011462636018409129 := by
  unfold tailWord_752377
  simp only [CollatzResearch.WordTrace]
  refine ⟨27441443595274099606639385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18294295730182733071092923 27441443595274099606639385)
  ·
    refine ⟨20581082696455574704979539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27441443595274099606639385 20581082696455574704979539)
    ·
      refine ⟨30871624044683362057469309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20581082696455574704979539 30871624044683362057469309)
      ·
        refine ⟨11576859016756260771550991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30871624044683362057469309 11576859016756260771550991)
        ·
          refine ⟨17365288525134391157326487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11576859016756260771550991 17365288525134391157326487)
          ·
            refine ⟨26047932787701586735989731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17365288525134391157326487 26047932787701586735989731)
            ·
              refine ⟨39071899181552380103984597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26047932787701586735989731 39071899181552380103984597)
              ·
                refine ⟨915747637067633908687139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 39071899181552380103984597 915747637067633908687139)
                ·
                  refine ⟨1373621455601450863030709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 915747637067633908687139 1373621455601450863030709)
                  ·
                    refine ⟨128777011462636018409129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1373621455601450863030709 128777011462636018409129)
                    ·
                      rfl

theorem cell23_752377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 5].length) (baseStart_752377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752377 prefixEnd_752377 := by exact prefixLift 752377
  have htrace : WordTrace (prefixWord ++ tailWord_752377) baseStart_752377 baseEnd_752377 := by
    simpa [prefixWord, tailWord_752377, baseEnd_752377] using wordTrace_append hprefix tailTrace_752377
  have hstable : (prefixWord ++ tailWord_752377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752377).length < 2 ^ (prefixWord ++ tailWord_752377).sum := by decide
  have hdescent : baseEnd_752377 < baseStart_752377 := by decide
  rcases family_descends (prefixWord ++ tailWord_752377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_752418 : List Nat := [3, 3, 1, 1, 2, 4, 1, 1, 2, 3, 2]
def baseStart_752418 : Nat := 118140960795 + 752418 * 2 ^ 59
def prefixEnd_752418 : Nat := 4983230072969 + 3 ^ 40 * 752418 * 2
def baseEnd_752418 : Nat := 386352087094742394814699

theorem tailTrace_752418 : CollatzResearch.WordTrace tailWord_752418 prefixEnd_752418 386352087094742394814699 := by
  unfold tailWord_752418
  simp only [CollatzResearch.WordTrace]
  refine ⟨6860734747031390902220477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18295292658750375739254605 6860734747031390902220477)
  ·
    refine ⟨2572775530136771588332679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6860734747031390902220477 2572775530136771588332679)
    ·
      refine ⟨3859163295205157382499019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2572775530136771588332679 3859163295205157382499019)
      ·
        refine ⟨5788744942807736073748529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3859163295205157382499019 5788744942807736073748529)
        ·
          refine ⟨4341558707105802055311397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5788744942807736073748529 4341558707105802055311397)
          ·
            refine ⟨814042257582337885370887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4341558707105802055311397 814042257582337885370887)
            ·
              refine ⟨1221063386373506828056331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814042257582337885370887 1221063386373506828056331)
              ·
                refine ⟨1831595079560260242084497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1221063386373506828056331 1831595079560260242084497)
                ·
                  refine ⟨1373696309670195181563373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1831595079560260242084497 1373696309670195181563373)
                  ·
                    refine ⟨515136116126323193086265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1373696309670195181563373 515136116126323193086265)
                    ·
                      refine ⟨386352087094742394814699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 515136116126323193086265 386352087094742394814699)
                      ·
                        rfl

theorem cell23_752418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_752418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_752418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_752418 prefixEnd_752418 := by exact prefixLift 752418
  have htrace : WordTrace (prefixWord ++ tailWord_752418) baseStart_752418 baseEnd_752418 := by
    simpa [prefixWord, tailWord_752418, baseEnd_752418] using wordTrace_append hprefix tailTrace_752418
  have hstable : (prefixWord ++ tailWord_752418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_752418).length < 2 ^ (prefixWord ++ tailWord_752418).sum := by decide
  have hdescent : baseEnd_752418 < baseStart_752418 := by decide
  rcases family_descends (prefixWord ++ tailWord_752418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
