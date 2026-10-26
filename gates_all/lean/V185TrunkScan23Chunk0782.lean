import V185TrunkScan23Chunk0781

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4625082 : List Nat := [3, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4]
def baseStart_4625082 : Nat := 118140960795 + 4625082 * 2 ^ 59
def prefixEnd_4625082 : Nat := 4983230072969 + 3 ^ 40 * 4625082 * 2
def baseEnd_4625082 : Nat := 2374890132458178579104641

theorem tailTrace_4625082 : CollatzResearch.WordTrace tailWord_4625082 prefixEnd_4625082 2374890132458178579104641 := by
  unfold tailWord_4625082
  simp only [CollatzResearch.WordTrace]
  refine ⟨42172649757531322490867375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112460399353416859975646333 42172649757531322490867375)
  ·
    refine ⟨63258974636296983736301063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42172649757531322490867375 63258974636296983736301063)
    ·
      refine ⟨94888461954445475604451595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63258974636296983736301063 94888461954445475604451595)
      ·
        refine ⟨142332692931668213406677393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94888461954445475604451595 142332692931668213406677393)
        ·
          refine ⟨106749519698751160055008045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142332692931668213406677393 106749519698751160055008045)
          ·
            refine ⟨40031069887031685020628017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106749519698751160055008045 40031069887031685020628017)
            ·
              refine ⟨30023302415273763765471013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40031069887031685020628017 30023302415273763765471013)
              ·
                refine ⟨5629369202863830706025815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30023302415273763765471013 5629369202863830706025815)
                ·
                  refine ⟨8444053804295746059038723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5629369202863830706025815 8444053804295746059038723)
                  ·
                    refine ⟨12666080706443619088558085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8444053804295746059038723 12666080706443619088558085)
                    ·
                      refine ⟨2374890132458178579104641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12666080706443619088558085 2374890132458178579104641)
                      ·
                        rfl

theorem cell23_4625082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4].length) (baseStart_4625082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625082 prefixEnd_4625082 := by exact prefixLift 4625082
  have htrace : WordTrace (prefixWord ++ tailWord_4625082) baseStart_4625082 baseEnd_4625082 := by
    simpa [prefixWord, tailWord_4625082, baseEnd_4625082] using wordTrace_append hprefix tailTrace_4625082
  have hstable : (prefixWord ++ tailWord_4625082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625082).length < 2 ^ (prefixWord ++ tailWord_4625082).sum := by decide
  have hdescent : baseEnd_4625082 < baseStart_4625082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625092 : List Nat := [2, 3, 3, 1, 1, 2, 2, 2, 1, 6]
def baseStart_4625092 : Nat := 118140960795 + 4625092 * 2 ^ 59
def prefixEnd_4625092 : Nat := 4983230072969 + 3 ^ 40 * 4625092 * 2
def baseEnd_4625092 : Nat := 791631755754907846659865

theorem tailTrace_4625092 : CollatzResearch.WordTrace tailWord_4625092 prefixEnd_4625092 791631755754907846659865 := by
  unfold tailWord_4625092
  simp only [CollatzResearch.WordTrace]
  refine ⟨84345481880044530835666765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112460642506726041114222353 84345481880044530835666765)
  ·
    refine ⟨31629555705016699063375037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84345481880044530835666765 31629555705016699063375037)
    ·
      refine ⟨11861083389381262148765639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31629555705016699063375037 11861083389381262148765639)
      ·
        refine ⟨17791625084071893223148459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11861083389381262148765639 17791625084071893223148459)
        ·
          refine ⟨26687437626107839834722689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17791625084071893223148459 26687437626107839834722689)
          ·
            refine ⟨20015578219580879876042017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26687437626107839834722689 20015578219580879876042017)
            ·
              refine ⟨15011683664685659907031513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20015578219580879876042017 15011683664685659907031513)
              ·
                refine ⟨11258762748514244930273635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15011683664685659907031513 11258762748514244930273635)
                ·
                  refine ⟨16888144122771367395410453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11258762748514244930273635 16888144122771367395410453)
                  ·
                    refine ⟨791631755754907846659865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16888144122771367395410453 791631755754907846659865)
                    ·
                      rfl

theorem cell23_4625092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_4625092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625092 prefixEnd_4625092 := by exact prefixLift 4625092
  have htrace : WordTrace (prefixWord ++ tailWord_4625092) baseStart_4625092 baseEnd_4625092 := by
    simpa [prefixWord, tailWord_4625092, baseEnd_4625092] using wordTrace_append hprefix tailTrace_4625092
  have hstable : (prefixWord ++ tailWord_4625092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625092).length < 2 ^ (prefixWord ++ tailWord_4625092).sum := by decide
  have hdescent : baseEnd_4625092 < baseStart_4625092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625095 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_4625095 : Nat := 118140960795 + 4625095 * 2 ^ 59
def prefixEnd_4625095 : Nat := 4983230072969 + 3 ^ 40 * 4625095 * 2
def baseEnd_4625095 : Nat := 2374896807706687028242081

theorem tailTrace_4625095 : CollatzResearch.WordTrace tailWord_4625095 prefixEnd_4625095 2374896807706687028242081 := by
  unfold tailWord_4625095
  simp only [CollatzResearch.WordTrace]
  refine ⟨168691073179078193183692739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112460715452718795455795159 168691073179078193183692739)
  ·
    refine ⟨253036609768617289775539109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168691073179078193183692739 253036609768617289775539109)
    ·
      refine ⟨47444364331615741832913583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 253036609768617289775539109 47444364331615741832913583)
      ·
        refine ⟨71166546497423612749370375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47444364331615741832913583 71166546497423612749370375)
        ·
          refine ⟨106749819746135419124055563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71166546497423612749370375 106749819746135419124055563)
          ·
            refine ⟨160124729619203128686083345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106749819746135419124055563 160124729619203128686083345)
            ·
              refine ⟨120093547214402346514562509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160124729619203128686083345 120093547214402346514562509)
              ·
                refine ⟨45035080205400879942960941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120093547214402346514562509 45035080205400879942960941)
                ·
                  refine ⟨16888155077025329978610353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45035080205400879942960941 16888155077025329978610353)
                  ·
                    refine ⟨12666116307768997483957765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16888155077025329978610353 12666116307768997483957765)
                    ·
                      refine ⟨2374896807706687028242081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12666116307768997483957765 2374896807706687028242081)
                      ·
                        rfl

theorem cell23_4625095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_4625095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625095 prefixEnd_4625095 := by exact prefixLift 4625095
  have htrace : WordTrace (prefixWord ++ tailWord_4625095) baseStart_4625095 baseEnd_4625095 := by
    simpa [prefixWord, tailWord_4625095, baseEnd_4625095] using wordTrace_append hprefix tailTrace_4625095
  have hstable : (prefixWord ++ tailWord_4625095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625095).length < 2 ^ (prefixWord ++ tailWord_4625095).sum := by decide
  have hdescent : baseEnd_4625095 < baseStart_4625095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625150 : List Nat := [4, 2, 2, 1, 2, 1, 3, 3, 1, 2, 2]
def baseStart_4625150 : Nat := 118140960795 + 4625150 * 2 ^ 59
def prefixEnd_4625150 : Nat := 4983230072969 + 3 ^ 40 * 4625150 * 2
def baseEnd_4625150 : Nat := 2374925049142684313054329

theorem tailTrace_4625150 : CollatzResearch.WordTrace tailWord_4625150 prefixEnd_4625150 2374925049142684313054329 := by
  unfold tailWord_4625150
  simp only [CollatzResearch.WordTrace]
  refine ⟨21086634899234867197118113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112462052795919291717963269 21086634899234867197118113)
  ·
    refine ⟨15814976174426150397838585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21086634899234867197118113 15814976174426150397838585)
    ·
      refine ⟨11861232130819612798378939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15814976174426150397838585 11861232130819612798378939)
      ·
        refine ⟨17791848196229419197568409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11861232130819612798378939 17791848196229419197568409)
        ·
          refine ⟨13343886147172064398176307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17791848196229419197568409 13343886147172064398176307)
          ·
            refine ⟨20015829220758096597264461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13343886147172064398176307 20015829220758096597264461)
            ·
              refine ⟨7505935957784286223974173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20015829220758096597264461 7505935957784286223974173)
              ·
                refine ⟨2814725984169107333990315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7505935957784286223974173 2814725984169107333990315)
                ·
                  refine ⟨4222088976253661000985473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2814725984169107333990315 4222088976253661000985473)
                  ·
                    refine ⟨3166566732190245750739105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4222088976253661000985473 3166566732190245750739105)
                    ·
                      refine ⟨2374925049142684313054329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3166566732190245750739105 2374925049142684313054329)
                      ·
                        rfl

theorem cell23_4625150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_4625150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625150 prefixEnd_4625150 := by exact prefixLift 4625150
  have htrace : WordTrace (prefixWord ++ tailWord_4625150) baseStart_4625150 baseEnd_4625150 := by
    simpa [prefixWord, tailWord_4625150, baseEnd_4625150] using wordTrace_append hprefix tailTrace_4625150
  have hstable : (prefixWord ++ tailWord_4625150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625150).length < 2 ^ (prefixWord ++ tailWord_4625150).sum := by decide
  have hdescent : baseEnd_4625150 < baseStart_4625150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625155 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 4]
def baseStart_4625155 : Nat := 118140960795 + 4625155 * 2 ^ 59
def prefixEnd_4625155 : Nat := 4983230072969 + 3 ^ 40 * 4625155 * 2
def baseEnd_4625155 : Nat := 2374927616545956793491805

theorem tailTrace_4625155 : CollatzResearch.WordTrace tailWord_4625155 prefixEnd_4625155 2374927616545956793491805 := by
  unfold tailWord_4625155
  simp only [CollatzResearch.WordTrace]
  refine ⟨168693261558860823430876919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112462174372573882287251279 168693261558860823430876919)
  ·
    refine ⟨253039892338291235146315379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168693261558860823430876919 253039892338291235146315379)
    ·
      refine ⟨379559838507436852719473069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253039892338291235146315379 379559838507436852719473069)
      ·
        refine ⟨142334939440288819769802401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 379559838507436852719473069 142334939440288819769802401)
        ·
          refine ⟨106751204580216614827351801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142334939440288819769802401 106751204580216614827351801)
          ·
            refine ⟨80063403435162461120513851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106751204580216614827351801 80063403435162461120513851)
            ·
              refine ⟨120095105152743691680770777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80063403435162461120513851 120095105152743691680770777)
              ·
                refine ⟨90071328864557768760578083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120095105152743691680770777 90071328864557768760578083)
                ·
                  refine ⟨135106993296836653140867125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90071328864557768760578083 135106993296836653140867125)
                  ·
                    refine ⟨12666280621578436231956293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 135106993296836653140867125 12666280621578436231956293)
                    ·
                      refine ⟨2374927616545956793491805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12666280621578436231956293 2374927616545956793491805)
                      ·
                        rfl

theorem cell23_4625155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_4625155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625155 prefixEnd_4625155 := by exact prefixLift 4625155
  have htrace : WordTrace (prefixWord ++ tailWord_4625155) baseStart_4625155 baseEnd_4625155 := by
    simpa [prefixWord, tailWord_4625155, baseEnd_4625155] using wordTrace_append hprefix tailTrace_4625155
  have hstable : (prefixWord ++ tailWord_4625155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625155).length < 2 ^ (prefixWord ++ tailWord_4625155).sum := by decide
  have hdescent : baseEnd_4625155 < baseStart_4625155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625183 : List Nat := [1, 1, 2, 4, 2, 4, 2, 1, 2, 1, 3]
def baseStart_4625183 : Nat := 118140960795 + 4625183 * 2 ^ 59
def prefixEnd_4625183 : Nat := 4983230072969 + 3 ^ 40 * 4625183 * 2
def baseEnd_4625183 : Nat := 2374941994004282683941677

theorem tailTrace_4625183 : CollatzResearch.WordTrace tailWord_4625183 prefixEnd_4625183 2374941994004282683941677 := by
  unfold tailWord_4625183
  simp only [CollatzResearch.WordTrace]
  refine ⟨168694282802759384212896203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112462855201839589475264135 168694282802759384212896203)
  ·
    refine ⟨253041424204139076319344305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168694282802759384212896203 253041424204139076319344305)
    ·
      refine ⟨189781068153104307239508229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253041424204139076319344305 189781068153104307239508229)
      ·
        refine ⟨35583950278707057607407793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189781068153104307239508229 35583950278707057607407793)
        ·
          refine ⟨26687962709030293205555845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35583950278707057607407793 26687962709030293205555845)
          ·
            refine ⟨5003993007943179976041721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26687962709030293205555845 5003993007943179976041721)
            ·
              refine ⟨3752994755957384982031291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5003993007943179976041721 3752994755957384982031291)
              ·
                refine ⟨5629492133936077473046937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3752994755957384982031291 5629492133936077473046937)
                ·
                  refine ⟨4222119100452058104785203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5629492133936077473046937 4222119100452058104785203)
                  ·
                    refine ⟨6333178650678087157177805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4222119100452058104785203 6333178650678087157177805)
                    ·
                      refine ⟨2374941994004282683941677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6333178650678087157177805 2374941994004282683941677)
                      ·
                        rfl

theorem cell23_4625183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_4625183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625183 prefixEnd_4625183 := by exact prefixLift 4625183
  have htrace : WordTrace (prefixWord ++ tailWord_4625183) baseStart_4625183 baseEnd_4625183 := by
    simpa [prefixWord, tailWord_4625183, baseEnd_4625183] using wordTrace_append hprefix tailTrace_4625183
  have hstable : (prefixWord ++ tailWord_4625183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625183).length < 2 ^ (prefixWord ++ tailWord_4625183).sum := by decide
  have hdescent : baseEnd_4625183 < baseStart_4625183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625189 : List Nat := [1, 3, 1, 2, 3, 1, 2, 3, 1, 4, 2]
def baseStart_4625189 : Nat := 118140960795 + 4625189 * 2 ^ 59
def prefixEnd_4625189 : Nat := 4983230072969 + 3 ^ 40 * 4625189 * 2
def baseEnd_4625189 : Nat := 2374945074888209660466649

theorem tailTrace_4625189 : CollatzResearch.WordTrace tailWord_4625189 prefixEnd_4625189 2374945074888209660466649 := by
  unfold tailWord_4625189
  simp only [CollatzResearch.WordTrace]
  refine ⟨168694501640737647237614621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112463001093825098158409747 168694501640737647237614621)
  ·
    refine ⟨63260438115276617714105483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168694501640737647237614621 63260438115276617714105483)
    ·
      refine ⟨94890657172914926571158225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63260438115276617714105483 94890657172914926571158225)
      ·
        refine ⟨71167992879686194928368669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94890657172914926571158225 71167992879686194928368669)
        ·
          refine ⟨26687997329882323098138251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71167992879686194928368669 26687997329882323098138251)
          ·
            refine ⟨40031995994823484647207377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26687997329882323098138251 40031995994823484647207377)
            ·
              refine ⟨30023996996117613485405533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40031995994823484647207377 30023996996117613485405533)
              ·
                refine ⟨11258998873544105057027075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30023996996117613485405533 11258998873544105057027075)
                ·
                  refine ⟨16888498310316157585540613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11258998873544105057027075 16888498310316157585540613)
                  ·
                    refine ⟨3166593433184279547288865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16888498310316157585540613 3166593433184279547288865)
                    ·
                      refine ⟨2374945074888209660466649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3166593433184279547288865 2374945074888209660466649)
                      ·
                        rfl

theorem cell23_4625189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_4625189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625189 prefixEnd_4625189 := by exact prefixLift 4625189
  have htrace : WordTrace (prefixWord ++ tailWord_4625189) baseStart_4625189 baseEnd_4625189 := by
    simpa [prefixWord, tailWord_4625189, baseEnd_4625189] using wordTrace_append hprefix tailTrace_4625189
  have hstable : (prefixWord ++ tailWord_4625189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625189).length < 2 ^ (prefixWord ++ tailWord_4625189).sum := by decide
  have hdescent : baseEnd_4625189 < baseStart_4625189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625192 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_4625192 : Nat := 118140960795 + 4625192 * 2 ^ 59
def prefixEnd_4625192 : Nat := 4983230072969 + 3 ^ 40 * 4625192 * 2
def baseEnd_4625192 : Nat := 2374946615330173148729135

theorem tailTrace_4625192 : CollatzResearch.WordTrace tailWord_4625192 prefixEnd_4625192 2374946615330173148729135 := by
  unfold tailWord_4625192
  simp only [CollatzResearch.WordTrace]
  refine ⟨84347305529863389374986915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112463074039817852499982553 84347305529863389374986915)
  ·
    refine ⟨126520958294795084062480373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84347305529863389374986915 126520958294795084062480373)
    ·
      refine ⟨11861339840137039130857535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126520958294795084062480373 11861339840137039130857535)
      ·
        refine ⟨17792009760205558696286303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11861339840137039130857535 17792009760205558696286303)
        ·
          refine ⟨26688014640308338044429455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17792009760205558696286303 26688014640308338044429455)
          ·
            refine ⟨40032021960462507066644183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26688014640308338044429455 40032021960462507066644183)
            ·
              refine ⟨60048032940693760599966275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40032021960462507066644183 60048032940693760599966275)
              ·
                refine ⟨90072049411040640899949413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60048032940693760599966275 90072049411040640899949413)
                ·
                  refine ⟨16888509264570120168740515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90072049411040640899949413 16888509264570120168740515)
                  ·
                    refine ⟨25332763896855180253110773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16888509264570120168740515 25332763896855180253110773)
                    ·
                      refine ⟨2374946615330173148729135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25332763896855180253110773 2374946615330173148729135)
                      ·
                        rfl

theorem cell23_4625192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_4625192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625192 prefixEnd_4625192 := by exact prefixLift 4625192
  have htrace : WordTrace (prefixWord ++ tailWord_4625192) baseStart_4625192 baseEnd_4625192 := by
    simpa [prefixWord, tailWord_4625192, baseEnd_4625192] using wordTrace_append hprefix tailTrace_4625192
  have hstable : (prefixWord ++ tailWord_4625192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625192).length < 2 ^ (prefixWord ++ tailWord_4625192).sum := by decide
  have hdescent : baseEnd_4625192 < baseStart_4625192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625239 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 3]
def baseStart_4625239 : Nat := 118140960795 + 4625239 * 2 ^ 59
def prefixEnd_4625239 : Nat := 4983230072969 + 3 ^ 40 * 4625239 * 2
def baseEnd_4625239 : Nat := 2374970748920934464841419

theorem tailTrace_4625239 : CollatzResearch.WordTrace tailWord_4625239 prefixEnd_4625239 2374970748920934464841419 := by
  unfold tailWord_4625239
  simp only [CollatzResearch.WordTrace]
  refine ⟨168696325290556505776934771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112464216860371003851289847 168696325290556505776934771)
  ·
    refine ⟨253044487935834758665402157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168696325290556505776934771 253044487935834758665402157)
    ·
      refine ⟨94891682975938034499525809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253044487935834758665402157 94891682975938034499525809)
      ·
        refine ⟨71168762231953525874644357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94891682975938034499525809 71168762231953525874644357)
        ·
          refine ⟨13344142918491286101495817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71168762231953525874644357 13344142918491286101495817)
          ·
            refine ⟨10008107188868464576121863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13344142918491286101495817 10008107188868464576121863)
            ·
              refine ⟨15012160783302696864182795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10008107188868464576121863 15012160783302696864182795)
              ·
                refine ⟨22518241174954045296274193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15012160783302696864182795 22518241174954045296274193)
                ·
                  refine ⟨16888680881215533972205645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22518241174954045296274193 16888680881215533972205645)
                  ·
                    refine ⟨6333255330455825239577117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16888680881215533972205645 6333255330455825239577117)
                    ·
                      refine ⟨2374970748920934464841419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6333255330455825239577117 2374970748920934464841419)
                      ·
                        rfl

theorem cell23_4625239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_4625239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625239 prefixEnd_4625239 := by exact prefixLift 4625239
  have htrace : WordTrace (prefixWord ++ tailWord_4625239) baseStart_4625239 baseEnd_4625239 := by
    simpa [prefixWord, tailWord_4625239, baseEnd_4625239] using wordTrace_append hprefix tailTrace_4625239
  have hstable : (prefixWord ++ tailWord_4625239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625239).length < 2 ^ (prefixWord ++ tailWord_4625239).sum := by decide
  have hdescent : baseEnd_4625239 < baseStart_4625239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625279 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 2, 4, 2]
def baseStart_4625279 : Nat := 118140960795 + 4625279 * 2 ^ 59
def prefixEnd_4625279 : Nat := 4983230072969 + 3 ^ 40 * 4625279 * 2
def baseEnd_4625279 : Nat := 2374991288147114308341235

theorem tailTrace_4625279 : CollatzResearch.WordTrace tailWord_4625279 prefixEnd_4625279 2374991288147114308341235 := by
  unfold tailWord_4625279
  simp only [CollatzResearch.WordTrace]
  refine ⟨168697784210411592608390891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112465189473607728405593927 168697784210411592608390891)
  ·
    refine ⟨253046676315617388912586337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168697784210411592608390891 253046676315617388912586337)
    ·
      refine ⟨189785007236713041684439753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253046676315617388912586337 189785007236713041684439753)
      ·
        refine ⟨142338755427534781263329815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189785007236713041684439753 142338755427534781263329815)
        ·
          refine ⟨213508133141302171894994723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142338755427534781263329815 213508133141302171894994723)
          ·
            refine ⟨320262199711953257842492085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213508133141302171894994723 320262199711953257842492085)
            ·
              refine ⟨30024581222995617922733633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 320262199711953257842492085 30024581222995617922733633)
              ·
                refine ⟨22518435917246713442050225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30024581222995617922733633 22518435917246713442050225)
                ·
                  refine ⟨16888826937935035081537669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22518435917246713442050225 16888826937935035081537669)
                  ·
                    refine ⟨3166655050862819077788313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16888826937935035081537669 3166655050862819077788313)
                    ·
                      refine ⟨2374991288147114308341235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3166655050862819077788313 2374991288147114308341235)
                      ·
                        rfl

theorem cell23_4625279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 4, 2].length) (baseStart_4625279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625279 prefixEnd_4625279 := by exact prefixLift 4625279
  have htrace : WordTrace (prefixWord ++ tailWord_4625279) baseStart_4625279 baseEnd_4625279 := by
    simpa [prefixWord, tailWord_4625279, baseEnd_4625279] using wordTrace_append hprefix tailTrace_4625279
  have hstable : (prefixWord ++ tailWord_4625279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625279).length < 2 ^ (prefixWord ++ tailWord_4625279).sum := by decide
  have hdescent : baseEnd_4625279 < baseStart_4625279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625289 : List Nat := [1, 2, 1, 1, 5, 2, 1, 3, 3, 4]
def baseStart_4625289 : Nat := 118140960795 + 4625289 * 2 ^ 59
def prefixEnd_4625289 : Nat := 4983230072969 + 3 ^ 40 * 4625289 * 2
def baseEnd_4625289 : Nat := 791665474317886423072063

theorem tailTrace_4625289 : CollatzResearch.WordTrace tailWord_4625289 prefixEnd_4625289 791665474317886423072063 := by
  unfold tailWord_4625289
  simp only [CollatzResearch.WordTrace]
  refine ⟨168698148940375364316254921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112465432626916909544169947 168698148940375364316254921)
  ·
    refine ⟨126523611705281523237191191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168698148940375364316254921 126523611705281523237191191)
    ·
      refine ⟨189785417557922284855786787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126523611705281523237191191 189785417557922284855786787)
      ·
        refine ⟨284678126336883427283680181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189785417557922284855786787 284678126336883427283680181)
        ·
          refine ⟨26688574344082821307845017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 284678126336883427283680181 26688574344082821307845017)
          ·
            refine ⟨20016430758062115980883763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26688574344082821307845017 20016430758062115980883763)
            ·
              refine ⟨30024646137093173971325645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20016430758062115980883763 30024646137093173971325645)
              ·
                refine ⟨11259242301409940239247117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30024646137093173971325645 11259242301409940239247117)
                ·
                  refine ⟨4222215863028727589717669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11259242301409940239247117 4222215863028727589717669)
                  ·
                    refine ⟨791665474317886423072063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4222215863028727589717669 791665474317886423072063)
                    ·
                      rfl

theorem cell23_4625289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 4].length) (baseStart_4625289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625289 prefixEnd_4625289 := by exact prefixLift 4625289
  have htrace : WordTrace (prefixWord ++ tailWord_4625289) baseStart_4625289 baseEnd_4625289 := by
    simpa [prefixWord, tailWord_4625289, baseEnd_4625289] using wordTrace_append hprefix tailTrace_4625289
  have hstable : (prefixWord ++ tailWord_4625289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625289).length < 2 ^ (prefixWord ++ tailWord_4625289).sum := by decide
  have hdescent : baseEnd_4625289 < baseStart_4625289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625356 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 4, 3, 2]
def baseStart_4625356 : Nat := 118140960795 + 4625356 * 2 ^ 59
def prefixEnd_4625356 : Nat := 4983230072969 + 3 ^ 40 * 4625356 * 2
def baseEnd_4625356 : Nat := 2375030826157510507078381

theorem tailTrace_4625356 : CollatzResearch.WordTrace tailWord_4625356 prefixEnd_4625356 2375030826157510507078381 := by
  unfold tailWord_4625356
  simp only [CollatzResearch.WordTrace]
  refine ⟨84350296315566317379471961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112467061754088423172629281 84350296315566317379471961)
  ·
    refine ⟨63262722236674738034603971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84350296315566317379471961 63262722236674738034603971)
    ·
      refine ⟨94894083355012107051905957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63262722236674738034603971 94894083355012107051905957)
      ·
        refine ⟨17792640629064770072232367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94894083355012107051905957 17792640629064770072232367)
        ·
          refine ⟨26688960943597155108348551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17792640629064770072232367 26688960943597155108348551)
          ·
            refine ⟨40033441415395732662522827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26688960943597155108348551 40033441415395732662522827)
            ·
              refine ⟨60050162123093598993784241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40033441415395732662522827 60050162123093598993784241)
              ·
                refine ⟨45037621592320199245338181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60050162123093598993784241 45037621592320199245338181)
                ·
                  refine ⟨8444554048560037358500909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45037621592320199245338181 8444554048560037358500909)
                  ·
                    refine ⟨3166707768210014009437841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8444554048560037358500909 3166707768210014009437841)
                    ·
                      refine ⟨2375030826157510507078381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3166707768210014009437841 2375030826157510507078381)
                      ·
                        rfl

theorem cell23_4625356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_4625356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625356 prefixEnd_4625356 := by exact prefixLift 4625356
  have htrace : WordTrace (prefixWord ++ tailWord_4625356) baseStart_4625356 baseEnd_4625356 := by
    simpa [prefixWord, tailWord_4625356, baseEnd_4625356] using wordTrace_append hprefix tailTrace_4625356
  have hstable : (prefixWord ++ tailWord_4625356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625356).length < 2 ^ (prefixWord ++ tailWord_4625356).sum := by decide
  have hdescent : baseEnd_4625356 < baseStart_4625356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625373 : List Nat := [1, 4, 3, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_4625373 : Nat := 118140960795 + 4625373 * 2 ^ 59
def prefixEnd_4625373 : Nat := 4983230072969 + 3 ^ 40 * 4625373 * 2
def baseEnd_4625373 : Nat := 2375039555328636940565803

theorem tailTrace_4625373 : CollatzResearch.WordTrace tailWord_4625373 prefixEnd_4625373 2375039555328636940565803 := by
  unfold tailWord_4625373
  simp only [CollatzResearch.WordTrace]
  refine ⟨168701212672071046662312773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112467475114714031108208515 168701212672071046662312773)
  ·
    refine ⟨31631477376013321249183645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168701212672071046662312773 31631477376013321249183645)
    ·
      refine ⟨11861804016004995468443867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31631477376013321249183645 11861804016004995468443867)
      ·
        refine ⟨17792706024007493202665801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11861804016004995468443867 17792706024007493202665801)
        ·
          refine ⟨13344529518005619901999351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17792706024007493202665801 13344529518005619901999351)
          ·
            refine ⟨20016794277008429852999027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13344529518005619901999351 20016794277008429852999027)
            ·
              refine ⟨30025191415512644779498541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20016794277008429852999027 30025191415512644779498541)
              ·
                refine ⟨11259446780817241792311953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30025191415512644779498541 11259446780817241792311953)
                ·
                  refine ⟨8444585085612931344233965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11259446780817241792311953 8444585085612931344233965)
                  ·
                    refine ⟨3166719407104849254087737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8444585085612931344233965 3166719407104849254087737)
                    ·
                      refine ⟨2375039555328636940565803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3166719407104849254087737 2375039555328636940565803)
                      ·
                        rfl

theorem cell23_4625373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_4625373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625373 prefixEnd_4625373 := by exact prefixLift 4625373
  have htrace : WordTrace (prefixWord ++ tailWord_4625373) baseStart_4625373 baseEnd_4625373 := by
    simpa [prefixWord, tailWord_4625373, baseEnd_4625373] using wordTrace_append hprefix tailTrace_4625373
  have hstable : (prefixWord ++ tailWord_4625373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625373).length < 2 ^ (prefixWord ++ tailWord_4625373).sum := by decide
  have hdescent : baseEnd_4625373 < baseStart_4625373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625379 : List Nat := [1, 1, 1, 6, 1, 1, 3, 2, 1, 6]
def baseStart_4625379 : Nat := 118140960795 + 4625379 * 2 ^ 59
def prefixEnd_4625379 : Nat := 4983230072969 + 3 ^ 40 * 4625379 * 2
def baseEnd_4625379 : Nat := 791680878737521305696925

theorem tailTrace_4625379 : CollatzResearch.WordTrace tailWord_4625379 prefixEnd_4625379 791680878737521305696925 := by
  unfold tailWord_4625379
  simp only [CollatzResearch.WordTrace]
  refine ⟨168701431510049309687031191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112467621006699539791354127 168701431510049309687031191)
  ·
    refine ⟨253052147265073964530546787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168701431510049309687031191 253052147265073964530546787)
    ·
      refine ⟨379578220897610946795820181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253052147265073964530546787 379578220897610946795820181)
      ·
        refine ⟨17792729104575513131054071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 379578220897610946795820181 17792729104575513131054071)
        ·
          refine ⟨26689093656863269696581107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17792729104575513131054071 26689093656863269696581107)
          ·
            refine ⟨40033640485294904544871661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26689093656863269696581107 40033640485294904544871661)
            ·
              refine ⟨15012615181985589204326873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40033640485294904544871661 15012615181985589204326873)
              ·
                refine ⟨11259461386489191903245155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15012615181985589204326873 11259461386489191903245155)
                ·
                  refine ⟨16889192079733787854867733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11259461386489191903245155 16889192079733787854867733)
                  ·
                    refine ⟨791680878737521305696925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16889192079733787854867733 791680878737521305696925)
                    ·
                      rfl

theorem cell23_4625379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 6].length) (baseStart_4625379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625379 prefixEnd_4625379 := by exact prefixLift 4625379
  have htrace : WordTrace (prefixWord ++ tailWord_4625379) baseStart_4625379 baseEnd_4625379 := by
    simpa [prefixWord, tailWord_4625379, baseEnd_4625379] using wordTrace_append hprefix tailTrace_4625379
  have hstable : (prefixWord ++ tailWord_4625379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625379).length < 2 ^ (prefixWord ++ tailWord_4625379).sum := by decide
  have hdescent : baseEnd_4625379 < baseStart_4625379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625383 : List Nat := [1, 1, 5, 2, 2, 2, 3, 1, 1, 5]
def baseStart_4625383 : Nat := 118140960795 + 4625383 * 2 ^ 59
def prefixEnd_4625383 : Nat := 4983230072969 + 3 ^ 40 * 4625383 * 2
def baseEnd_4625383 : Nat := 791681563378393967146919

theorem tailTrace_4625383 : CollatzResearch.WordTrace tailWord_4625383 prefixEnd_4625383 791681563378393967146919 := by
  unfold tailWord_4625383
  simp only [CollatzResearch.WordTrace]
  refine ⟨168701577402034818370176803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112467718268023212246784535 168701577402034818370176803)
  ·
    refine ⟨253052366103052227555265205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168701577402034818370176803 253052366103052227555265205)
    ·
      refine ⟨23723659322161146333306113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 253052366103052227555265205 23723659322161146333306113)
      ·
        refine ⟨17792744491620859749979585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23723659322161146333306113 17792744491620859749979585)
        ·
          refine ⟨13344558368715644812484689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17792744491620859749979585 13344558368715644812484689)
          ·
            refine ⟨10008418776536733609363517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13344558368715644812484689 10008418776536733609363517)
            ·
              refine ⟨3753157041201275103511319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10008418776536733609363517 3753157041201275103511319)
              ·
                refine ⟨5629735561801912655266979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3753157041201275103511319 5629735561801912655266979)
                ·
                  refine ⟨8444603342702868982900469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5629735561801912655266979 8444603342702868982900469)
                  ·
                    refine ⟨791681563378393967146919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8444603342702868982900469 791681563378393967146919)
                    ·
                      rfl

theorem cell23_4625383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_4625383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625383 prefixEnd_4625383 := by exact prefixLift 4625383
  have htrace : WordTrace (prefixWord ++ tailWord_4625383) baseStart_4625383 baseEnd_4625383 := by
    simpa [prefixWord, tailWord_4625383, baseEnd_4625383] using wordTrace_append hprefix tailTrace_4625383
  have hstable : (prefixWord ++ tailWord_4625383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625383).length < 2 ^ (prefixWord ++ tailWord_4625383).sum := by decide
  have hdescent : baseEnd_4625383 < baseStart_4625383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625409 : List Nat := [1, 2, 4, 1, 2, 2, 3, 8]
def baseStart_4625409 : Nat := 118140960795 + 4625409 * 2 ^ 59
def prefixEnd_4625409 : Nat := 4983230072969 + 3 ^ 40 * 4625409 * 2
def baseEnd_4625409 : Nat := 87965112616007362952431

theorem tailTrace_4625409 : CollatzResearch.WordTrace tailWord_4625409 prefixEnd_4625409 87965112616007362952431 := by
  unfold tailWord_4625409
  simp only [CollatzResearch.WordTrace]
  refine ⟨168702525699940624810623281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112468350466627083207082187 168702525699940624810623281)
  ·
    refine ⟨126526894274955468607967461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168702525699940624810623281 126526894274955468607967461)
    ·
      refine ⟨23723792676554150363993899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126526894274955468607967461 23723792676554150363993899)
      ·
        refine ⟨35585689014831225545990849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23723792676554150363993899 35585689014831225545990849)
        ·
          refine ⟨26689266761123419159493137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35585689014831225545990849 26689266761123419159493137)
          ·
            refine ⟨20016950070842564369619853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26689266761123419159493137 20016950070842564369619853)
            ·
              refine ⟨7506356276565961638607445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20016950070842564369619853 7506356276565961638607445)
              ·
                refine ⟨87965112616007362952431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7506356276565961638607445 87965112616007362952431)
                ·
                  rfl

theorem cell23_4625409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 8].length) (baseStart_4625409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625409 prefixEnd_4625409 := by exact prefixLift 4625409
  have htrace : WordTrace (prefixWord ++ tailWord_4625409) baseStart_4625409 baseEnd_4625409 := by
    simpa [prefixWord, tailWord_4625409, baseEnd_4625409] using wordTrace_append hprefix tailTrace_4625409
  have hstable : (prefixWord ++ tailWord_4625409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625409).length < 2 ^ (prefixWord ++ tailWord_4625409).sum := by decide
  have hdescent : baseEnd_4625409 < baseStart_4625409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625416 : List Nat := [2, 1, 3, 2, 1, 4, 2, 1, 1, 2, 4]
def baseStart_4625416 : Nat := 118140960795 + 4625416 * 2 ^ 59
def prefixEnd_4625416 : Nat := 4983230072969 + 3 ^ 40 * 4625416 * 2
def baseEnd_4625416 : Nat := 2375061634996780272328105

theorem tailTrace_4625416 : CollatzResearch.WordTrace tailWord_4625416 prefixEnd_4625416 2375061634996780272328105 := by
  unfold tailWord_4625416
  simp only [CollatzResearch.WordTrace]
  refine ⟨84351390505457632503064051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112468520673943510004085401 84351390505457632503064051)
  ·
    refine ⟨126527085758186448754596077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84351390505457632503064051 126527085758186448754596077)
    ·
      refine ⟨47447657159319918282973529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126527085758186448754596077 47447657159319918282973529)
      ·
        refine ⟨35585742869489938712230147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47447657159319918282973529 35585742869489938712230147)
        ·
          refine ⟨53378614304234908068345221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35585742869489938712230147 53378614304234908068345221)
          ·
            refine ⟨10008490182044045262814729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53378614304234908068345221 10008490182044045262814729)
            ·
              refine ⟨7506367636533033947111047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10008490182044045262814729 7506367636533033947111047)
              ·
                refine ⟨11259551454799550920666571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7506367636533033947111047 11259551454799550920666571)
                ·
                  refine ⟨16889327182199326380999857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11259551454799550920666571 16889327182199326380999857)
                  ·
                    refine ⟨12666995386649494785749893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16889327182199326380999857 12666995386649494785749893)
                    ·
                      refine ⟨2375061634996780272328105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12666995386649494785749893 2375061634996780272328105)
                      ·
                        rfl

theorem cell23_4625416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_4625416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625416 prefixEnd_4625416 := by exact prefixLift 4625416
  have htrace : WordTrace (prefixWord ++ tailWord_4625416) baseStart_4625416 baseEnd_4625416 := by
    simpa [prefixWord, tailWord_4625416, baseEnd_4625416] using wordTrace_append hprefix tailTrace_4625416
  have hstable : (prefixWord ++ tailWord_4625416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625416).length < 2 ^ (prefixWord ++ tailWord_4625416).sum := by decide
  have hdescent : baseEnd_4625416 < baseStart_4625416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625437 : List Nat := [1, 4, 2, 2, 4, 1, 2, 1, 1, 1, 4]
def baseStart_4625437 : Nat := 118140960795 + 4625437 * 2 ^ 59
def prefixEnd_4625437 : Nat := 4983230072969 + 3 ^ 40 * 4625437 * 2
def baseEnd_4625437 : Nat := 2375072418090524690165509

theorem tailTrace_4625437 : CollatzResearch.WordTrace tailWord_4625437 prefixEnd_4625437 2375072418090524690165509 := by
  unfold tailWord_4625437
  simp only [CollatzResearch.WordTrace]
  refine ⟨168703546943839185592642565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112469031295892790395095043 168703546943839185592642565)
  ·
    refine ⟨31631915051969847298620481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168703546943839185592642565 31631915051969847298620481)
    ·
      refine ⟨23723936288977385473965361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31631915051969847298620481 23723936288977385473965361)
      ·
        refine ⟨17792952216733039105474021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23723936288977385473965361 17792952216733039105474021)
        ·
          refine ⟨3336178540637444832276379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17792952216733039105474021 3336178540637444832276379)
          ·
            refine ⟨5004267810956167248414569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3336178540637444832276379 5004267810956167248414569)
            ·
              refine ⟨3753200858217125436310927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5004267810956167248414569 3753200858217125436310927)
              ·
                refine ⟨5629801287325688154466391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3753200858217125436310927 5629801287325688154466391)
                ·
                  refine ⟨8444701930988532231699587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5629801287325688154466391 8444701930988532231699587)
                  ·
                    refine ⟨12667052896482798347549381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8444701930988532231699587 12667052896482798347549381)
                    ·
                      refine ⟨2375072418090524690165509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12667052896482798347549381 2375072418090524690165509)
                      ·
                        rfl

theorem cell23_4625437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_4625437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625437 prefixEnd_4625437 := by exact prefixLift 4625437
  have htrace : WordTrace (prefixWord ++ tailWord_4625437) baseStart_4625437 baseEnd_4625437 := by
    simpa [prefixWord, tailWord_4625437, baseEnd_4625437] using wordTrace_append hprefix tailTrace_4625437
  have hstable : (prefixWord ++ tailWord_4625437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625437).length < 2 ^ (prefixWord ++ tailWord_4625437).sum := by decide
  have hdescent : baseEnd_4625437 < baseStart_4625437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625440 : List Nat := [2, 1, 1, 7, 1, 1, 1, 3, 1, 2, 3]
def baseStart_4625440 : Nat := 118140960795 + 4625440 * 2 ^ 59
def prefixEnd_4625440 : Nat := 4983230072969 + 3 ^ 40 * 4625440 * 2
def baseEnd_4625440 : Nat := 2375073958532488178427995

theorem tailTrace_4625440 : CollatzResearch.WordTrace tailWord_4625440 prefixEnd_4625440 2375073958532488178427995 := by
  unfold tailWord_4625440
  simp only [CollatzResearch.WordTrace]
  refine ⟨84351828181414158552500887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112469104241885544736667849 84351828181414158552500887)
  ·
    refine ⟨126527742272121237828751331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84351828181414158552500887 126527742272121237828751331)
    ·
      refine ⟨189791613408181856743126997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126527742272121237828751331 189791613408181856743126997)
      ·
        refine ⟨4448240939254262267417039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 189791613408181856743126997 4448240939254262267417039)
        ·
          refine ⟨6672361408881393401125559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4448240939254262267417039 6672361408881393401125559)
          ·
            refine ⟨10008542113322090101688339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6672361408881393401125559 10008542113322090101688339)
            ·
              refine ⟨15012813169983135152532509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10008542113322090101688339 15012813169983135152532509)
              ·
                refine ⟨5629804938743675682199691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15012813169983135152532509 5629804938743675682199691)
                ·
                  refine ⟨8444707408115513523299537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5629804938743675682199691 8444707408115513523299537)
                  ·
                    refine ⟨6333530556086635142474653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8444707408115513523299537 6333530556086635142474653)
                    ·
                      refine ⟨2375073958532488178427995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6333530556086635142474653 2375073958532488178427995)
                      ·
                        rfl

theorem cell23_4625440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_4625440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625440 prefixEnd_4625440 := by exact prefixLift 4625440
  have htrace : WordTrace (prefixWord ++ tailWord_4625440) baseStart_4625440 baseEnd_4625440 := by
    simpa [prefixWord, tailWord_4625440, baseEnd_4625440] using wordTrace_append hprefix tailTrace_4625440
  have hstable : (prefixWord ++ tailWord_4625440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625440).length < 2 ^ (prefixWord ++ tailWord_4625440).sum := by decide
  have hdescent : baseEnd_4625440 < baseStart_4625440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625470 : List Nat := [4, 2, 1, 3, 1, 3, 1, 1, 1, 3, 3]
def baseStart_4625470 : Nat := 118140960795 + 4625470 * 2 ^ 59
def prefixEnd_4625470 : Nat := 4983230072969 + 3 ^ 40 * 4625470 * 2
def baseEnd_4625470 : Nat := 2375089362952123061052857

theorem tailTrace_4625470 : CollatzResearch.WordTrace tailWord_4625470 prefixEnd_4625470 2375089362952123061052857 := by
  unfold tailWord_4625470
  simp only [CollatzResearch.WordTrace]
  refine ⟨21088093819089954028574233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112469833701813088152395909 21088093819089954028574233)
  ·
    refine ⟨15816070364317465521430675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21088093819089954028574233 15816070364317465521430675)
    ·
      refine ⟨23724105546476198282146013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15816070364317465521430675 23724105546476198282146013)
      ·
        refine ⟨8896539579928574355804755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23724105546476198282146013 8896539579928574355804755)
        ·
          refine ⟨13344809369892861533707133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8896539579928574355804755 13344809369892861533707133)
          ·
            refine ⟨5004303513709823075140175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13344809369892861533707133 5004303513709823075140175)
            ·
              refine ⟨7506455270564734612710263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5004303513709823075140175 7506455270564734612710263)
              ·
                refine ⟨11259682905847101919065395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7506455270564734612710263 11259682905847101919065395)
                ·
                  refine ⟨16889524358770652878598093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11259682905847101919065395 16889524358770652878598093)
                  ·
                    refine ⟨6333571634538994829474285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16889524358770652878598093 6333571634538994829474285)
                    ·
                      refine ⟨2375089362952123061052857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6333571634538994829474285 2375089362952123061052857)
                      ·
                        rfl

theorem cell23_4625470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_4625470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625470 prefixEnd_4625470 := by exact prefixLift 4625470
  have htrace : WordTrace (prefixWord ++ tailWord_4625470) baseStart_4625470 baseEnd_4625470 := by
    simpa [prefixWord, tailWord_4625470, baseEnd_4625470] using wordTrace_append hprefix tailTrace_4625470
  have hstable : (prefixWord ++ tailWord_4625470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625470).length < 2 ^ (prefixWord ++ tailWord_4625470).sum := by decide
  have hdescent : baseEnd_4625470 < baseStart_4625470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625489 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 1, 4, 4]
def baseStart_4625489 : Nat := 118140960795 + 4625489 * 2 ^ 59
def prefixEnd_4625489 : Nat := 4983230072969 + 3 ^ 40 * 4625489 * 2
def baseEnd_4625489 : Nat := 2375099119084558486715269

theorem tailTrace_4625489 : CollatzResearch.WordTrace tailWord_4625489 prefixEnd_4625489 2375099119084558486715269 := by
  unfold tailWord_4625489
  simp only [CollatzResearch.WordTrace]
  refine ⟨168705443539650798473535521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112470295693100532315690347 168705443539650798473535521)
  ·
    refine ⟨126529082654738098855151641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168705443539650798473535521 126529082654738098855151641)
    ·
      refine ⟨94896811991053574141363731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126529082654738098855151641 94896811991053574141363731)
      ·
        refine ⟨142345217986580361212045597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94896811991053574141363731 142345217986580361212045597)
        ·
          refine ⟨53379456744967635454517099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142345217986580361212045597 53379456744967635454517099)
          ·
            refine ⟨80069185117451453181775649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53379456744967635454517099 80069185117451453181775649)
            ·
              refine ⟨60051888838088589886331737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80069185117451453181775649 60051888838088589886331737)
              ·
                refine ⟨45038916628566442414748803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60051888838088589886331737 45038916628566442414748803)
                ·
                  refine ⟨67558374942849663622123205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45038916628566442414748803 67558374942849663622123205)
                  ·
                    refine ⟨12667195301784311929148101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67558374942849663622123205 12667195301784311929148101)
                    ·
                      refine ⟨2375099119084558486715269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12667195301784311929148101 2375099119084558486715269)
                      ·
                        rfl

theorem cell23_4625489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_4625489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625489 prefixEnd_4625489 := by exact prefixLift 4625489
  have htrace : WordTrace (prefixWord ++ tailWord_4625489) baseStart_4625489 baseEnd_4625489 := by
    simpa [prefixWord, tailWord_4625489, baseEnd_4625489] using wordTrace_append hprefix tailTrace_4625489
  have hstable : (prefixWord ++ tailWord_4625489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625489).length < 2 ^ (prefixWord ++ tailWord_4625489).sum := by decide
  have hdescent : baseEnd_4625489 < baseStart_4625489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625493 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 6, 2, 2]
def baseStart_4625493 : Nat := 118140960795 + 4625493 * 2 ^ 59
def prefixEnd_4625493 : Nat := 4983230072969 + 3 ^ 40 * 4625493 * 2
def baseEnd_4625493 : Nat := 2375101173007176471065251

theorem tailTrace_4625493 : CollatzResearch.WordTrace tailWord_4625493 prefixEnd_4625493 2375101173007176471065251 := by
  unfold tailWord_4625493
  simp only [CollatzResearch.WordTrace]
  refine ⟨168705589431636307156681133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112470392954424204771120755 168705589431636307156681133)
  ·
    refine ⟨63264596036863615183755425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168705589431636307156681133 63264596036863615183755425)
    ·
      refine ⟨47448447027647711387816569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63264596036863615183755425 47448447027647711387816569)
      ·
        refine ⟨35586335270735783540862427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47448447027647711387816569 35586335270735783540862427)
        ·
          refine ⟨53379502906103675311293641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35586335270735783540862427 53379502906103675311293641)
          ·
            refine ⟨40034627179577756483470231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53379502906103675311293641 40034627179577756483470231)
            ·
              refine ⟨60051940769366634725205347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40034627179577756483470231 60051940769366634725205347)
              ·
                refine ⟨90077911154049952087808021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60051940769366634725205347 90077911154049952087808021)
                ·
                  refine ⟨4222402085346091504116001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90077911154049952087808021 4222402085346091504116001)
                  ·
                    refine ⟨3166801564009568628087001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4222402085346091504116001 3166801564009568628087001)
                    ·
                      refine ⟨2375101173007176471065251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3166801564009568628087001 2375101173007176471065251)
                      ·
                        rfl

theorem cell23_4625493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_4625493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625493 prefixEnd_4625493 := by exact prefixLift 4625493
  have htrace : WordTrace (prefixWord ++ tailWord_4625493) baseStart_4625493 baseEnd_4625493 := by
    simpa [prefixWord, tailWord_4625493, baseEnd_4625493] using wordTrace_append hprefix tailTrace_4625493
  have hstable : (prefixWord ++ tailWord_4625493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625493).length < 2 ^ (prefixWord ++ tailWord_4625493).sum := by decide
  have hdescent : baseEnd_4625493 < baseStart_4625493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625509 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 1, 2, 7]
def baseStart_4625509 : Nat := 118140960795 + 4625509 * 2 ^ 59
def prefixEnd_4625509 : Nat := 4983230072969 + 3 ^ 40 * 4625509 * 2
def baseEnd_4625509 : Nat := 2375109388697648408465177

theorem tailTrace_4625509 : CollatzResearch.WordTrace tailWord_4625509 prefixEnd_4625509 2375109388697648408465177 := by
  unfold tailWord_4625509
  simp only [CollatzResearch.WordTrace]
  refine ⟨168706172999578341889263581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112470781999718894592842387 168706172999578341889263581)
  ·
    refine ⟨63264814874841878208473843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168706172999578341889263581 63264814874841878208473843)
    ·
      refine ⟨94897222312262817312710765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63264814874841878208473843 94897222312262817312710765)
      ·
        refine ⟨35586458367098556492266537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94897222312262817312710765 35586458367098556492266537)
        ·
          refine ⟨26689843775323917369199903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35586458367098556492266537 26689843775323917369199903)
          ·
            refine ⟨40034765662985876053799855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26689843775323917369199903 40034765662985876053799855)
            ·
              refine ⟨60052148494478814080699783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40034765662985876053799855 60052148494478814080699783)
              ·
                refine ⟨90078222741718221121049675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60052148494478814080699783 90078222741718221121049675)
                ·
                  refine ⟨135117334112577331681574513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90078222741718221121049675 135117334112577331681574513)
                  ·
                    refine ⟨101338000584432998761180885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 135117334112577331681574513 101338000584432998761180885)
                    ·
                      refine ⟨2375109388697648408465177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101338000584432998761180885 2375109388697648408465177)
                      ·
                        rfl

theorem cell23_4625509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_4625509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625509 prefixEnd_4625509 := by exact prefixLift 4625509
  have htrace : WordTrace (prefixWord ++ tailWord_4625509) baseStart_4625509 baseEnd_4625509 := by
    simpa [prefixWord, tailWord_4625509, baseEnd_4625509] using wordTrace_append hprefix tailTrace_4625509
  have hstable : (prefixWord ++ tailWord_4625509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625509).length < 2 ^ (prefixWord ++ tailWord_4625509).sum := by decide
  have hdescent : baseEnd_4625509 < baseStart_4625509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625539 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 7]
def baseStart_4625539 : Nat := 118140960795 + 4625539 * 2 ^ 59
def prefixEnd_4625539 : Nat := 4983230072969 + 3 ^ 40 * 4625539 * 2
def baseEnd_4625539 : Nat := 2375124793117283291090039

theorem tailTrace_4625539 : CollatzResearch.WordTrace tailWord_4625539 prefixEnd_4625539 2375124793117283291090039 := by
  unfold tailWord_4625539
  simp only [CollatzResearch.WordTrace]
  refine ⟨168707267189469657012855671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112471511459646438008570447 168707267189469657012855671)
  ·
    refine ⟨253060900784204485519283507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168707267189469657012855671 253060900784204485519283507)
    ·
      refine ⟨379591351176306728278925261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253060900784204485519283507 379591351176306728278925261)
      ·
        refine ⟨142346756691115023104596973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 379591351176306728278925261 142346756691115023104596973)
        ·
          refine ⟨53380033759168133664223865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142346756691115023104596973 53380033759168133664223865)
          ·
            refine ⟨40035025319376100248167899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53380033759168133664223865 40035025319376100248167899)
            ·
              refine ⟨60052537979064150372251849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40035025319376100248167899 60052537979064150372251849)
              ·
                refine ⟨45039403484298112779188887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60052537979064150372251849 45039403484298112779188887)
                ·
                  refine ⟨67559105226447169168783331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45039403484298112779188887 67559105226447169168783331)
                  ·
                    refine ⟨101338657839670753753174997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67559105226447169168783331 101338657839670753753174997)
                    ·
                      refine ⟨2375124793117283291090039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101338657839670753753174997 2375124793117283291090039)
                      ·
                        rfl

theorem cell23_4625539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_4625539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625539 prefixEnd_4625539 := by exact prefixLift 4625539
  have htrace : WordTrace (prefixWord ++ tailWord_4625539) baseStart_4625539 baseEnd_4625539 := by
    simpa [prefixWord, tailWord_4625539, baseEnd_4625539] using wordTrace_append hprefix tailTrace_4625539
  have hstable : (prefixWord ++ tailWord_4625539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625539).length < 2 ^ (prefixWord ++ tailWord_4625539).sum := by decide
  have hdescent : baseEnd_4625539 < baseStart_4625539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625567 : List Nat := [1, 1, 2, 6, 2, 2, 2, 2, 5]
def baseStart_4625567 : Nat := 118140960795 + 4625567 * 2 ^ 59
def prefixEnd_4625567 : Nat := 4983230072969 + 3 ^ 40 * 4625567 * 2
def baseEnd_4625567 : Nat := 263904352286178797948879

theorem tailTrace_4625567 : CollatzResearch.WordTrace tailWord_4625567 prefixEnd_4625567 263904352286178797948879 := by
  unfold tailWord_4625567
  simp only [CollatzResearch.WordTrace]
  refine ⟨168708288433368217794874955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112472192288912145196583303 168708288433368217794874955)
  ·
    refine ⟨253062432650052326692312433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168708288433368217794874955 253062432650052326692312433)
    ·
      refine ⟨189796824487539245019234325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253062432650052326692312433 189796824487539245019234325)
      ·
        refine ⟨8896726147853402110276609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 189796824487539245019234325 8896726147853402110276609)
        ·
          refine ⟨6672544610890051582707457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8896726147853402110276609 6672544610890051582707457)
          ·
            refine ⟨5004408458167538687030593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6672544610890051582707457 5004408458167538687030593)
            ·
              refine ⟨3753306343625654015272945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5004408458167538687030593 3753306343625654015272945)
              ·
                refine ⟨2814979757719240511454709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3753306343625654015272945 2814979757719240511454709)
                ·
                  refine ⟨263904352286178797948879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2814979757719240511454709 263904352286178797948879)
                  ·
                    rfl

theorem cell23_4625567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 5].length) (baseStart_4625567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625567 prefixEnd_4625567 := by exact prefixLift 4625567
  have htrace : WordTrace (prefixWord ++ tailWord_4625567) baseStart_4625567 baseEnd_4625567 := by
    simpa [prefixWord, tailWord_4625567, baseEnd_4625567] using wordTrace_append hprefix tailTrace_4625567
  have hstable : (prefixWord ++ tailWord_4625567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625567).length < 2 ^ (prefixWord ++ tailWord_4625567).sum := by decide
  have hdescent : baseEnd_4625567 < baseStart_4625567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625593 : List Nat := [1, 2, 1, 4, 1, 4, 1, 2, 3, 4]
def baseStart_4625593 : Nat := 118140960795 + 4625593 * 2 ^ 59
def prefixEnd_4625593 : Nat := 4983230072969 + 3 ^ 40 * 4625593 * 2
def baseEnd_4625593 : Nat := 791717507024208693271597

theorem tailTrace_4625593 : CollatzResearch.WordTrace tailWord_4625593 prefixEnd_4625593 791717507024208693271597 := by
  unfold tailWord_4625593
  simp only [CollatzResearch.WordTrace]
  refine ⟨168709236731274024235321433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112472824487516016156880955 168709236731274024235321433)
  ·
    refine ⟨126531927548455518176491075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168709236731274024235321433 126531927548455518176491075)
    ·
      refine ⟨189797891322683277264736613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126531927548455518176491075 189797891322683277264736613)
      ·
        refine ⟨35587104623003114487138115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189797891322683277264736613 35587104623003114487138115)
        ·
          refine ⟨53380656934504671730707173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35587104623003114487138115 53380656934504671730707173)
          ·
            refine ⟨10008873175219625949507595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53380656934504671730707173 10008873175219625949507595)
            ·
              refine ⟨15013309762829438924261393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10008873175219625949507595 15013309762829438924261393)
              ·
                refine ⟨11259982322122079193196045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15013309762829438924261393 11259982322122079193196045)
                ·
                  refine ⟨4222493370795779697448517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11259982322122079193196045 4222493370795779697448517)
                  ·
                    refine ⟨791717507024208693271597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4222493370795779697448517 791717507024208693271597)
                    ·
                      rfl

theorem cell23_4625593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 4].length) (baseStart_4625593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625593 prefixEnd_4625593 := by exact prefixLift 4625593
  have htrace : WordTrace (prefixWord ++ tailWord_4625593) baseStart_4625593 baseEnd_4625593 := by
    simpa [prefixWord, tailWord_4625593, baseEnd_4625593] using wordTrace_append hprefix tailTrace_4625593
  have hstable : (prefixWord ++ tailWord_4625593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625593).length < 2 ^ (prefixWord ++ tailWord_4625593).sum := by decide
  have hdescent : baseEnd_4625593 < baseStart_4625593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625600 : List Nat := [2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 4]
def baseStart_4625600 : Nat := 118140960795 + 4625600 * 2 ^ 59
def prefixEnd_4625600 : Nat := 4983230072969 + 3 ^ 40 * 4625600 * 2
def baseEnd_4625600 : Nat := 2375156115437207552427259

theorem tailTrace_4625600 : CollatzResearch.WordTrace tailWord_4625600 prefixEnd_4625600 2375156115437207552427259 := by
  unfold tailWord_4625600
  simp only [CollatzResearch.WordTrace]
  refine ⟨84354746021124332215413127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112472994694832442953884169 84354746021124332215413127)
  ·
    refine ⟨126532119031686498323119691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84354746021124332215413127 126532119031686498323119691)
    ·
      refine ⟨189798178547529747484679537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126532119031686498323119691 189798178547529747484679537)
      ·
        refine ⟨142348633910647310613509653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189798178547529747484679537 142348633910647310613509653)
        ·
          refine ⟨6672592214561592685008265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 142348633910647310613509653 6672592214561592685008265)
          ·
            refine ⟨5004444160921194513756199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6672592214561592685008265 5004444160921194513756199)
            ·
              refine ⟨7506666241381791770634299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5004444160921194513756199 7506666241381791770634299)
              ·
                refine ⟨11259999362072687655951449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7506666241381791770634299 11259999362072687655951449)
                ·
                  refine ⟨8444999521554515741963587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11259999362072687655951449 8444999521554515741963587)
                  ·
                    refine ⟨12667499282331773612945381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8444999521554515741963587 12667499282331773612945381)
                    ·
                      refine ⟨2375156115437207552427259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12667499282331773612945381 2375156115437207552427259)
                      ·
                        rfl

theorem cell23_4625600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 4].length) (baseStart_4625600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625600 prefixEnd_4625600 := by exact prefixLift 4625600
  have htrace : WordTrace (prefixWord ++ tailWord_4625600) baseStart_4625600 baseEnd_4625600 := by
    simpa [prefixWord, tailWord_4625600, baseEnd_4625600] using wordTrace_append hprefix tailTrace_4625600
  have hstable : (prefixWord ++ tailWord_4625600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625600).length < 2 ^ (prefixWord ++ tailWord_4625600).sum := by decide
  have hdescent : baseEnd_4625600 < baseStart_4625600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625610 : List Nat := [3, 1, 2, 1, 3, 2, 1, 5, 1, 4]
def baseStart_4625610 : Nat := 118140960795 + 4625610 * 2 ^ 59
def prefixEnd_4625610 : Nat := 4983230072969 + 3 ^ 40 * 4625610 * 2
def baseEnd_4625610 : Nat := 791720416747917504434071

theorem tailTrace_4625610 : CollatzResearch.WordTrace tailWord_4625610 prefixEnd_4625610 791720416747917504434071 := by
  unfold tailWord_4625610
  simp only [CollatzResearch.WordTrace]
  refine ⟨42177464193053109034672571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112473237848141624092460189 42177464193053109034672571)
  ·
    refine ⟨63266196289579663552008857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42177464193053109034672571 63266196289579663552008857)
    ·
      refine ⟨47449647217184747664006643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63266196289579663552008857 47449647217184747664006643)
      ·
        refine ⟨71174470825777121496009965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47449647217184747664006643 71174470825777121496009965)
        ·
          refine ⟨26690426559666420561003737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71174470825777121496009965 26690426559666420561003737)
          ·
            refine ⟨20017819919749815420752803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26690426559666420561003737 20017819919749815420752803)
            ·
              refine ⟨30026729879624723131129205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20017819919749815420752803 30026729879624723131129205)
              ·
                refine ⟨2815005926214817793543363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30026729879624723131129205 2815005926214817793543363)
                ·
                  refine ⟨4222508889322226690315045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2815005926214817793543363 4222508889322226690315045)
                  ·
                    refine ⟨791720416747917504434071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4222508889322226690315045 791720416747917504434071)
                    ·
                      rfl

theorem cell23_4625610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_4625610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625610 prefixEnd_4625610 := by exact prefixLift 4625610
  have htrace : WordTrace (prefixWord ++ tailWord_4625610) baseStart_4625610 baseEnd_4625610 := by
    simpa [prefixWord, tailWord_4625610, baseEnd_4625610] using wordTrace_append hprefix tailTrace_4625610
  have hstable : (prefixWord ++ tailWord_4625610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625610).length < 2 ^ (prefixWord ++ tailWord_4625610).sum := by decide
  have hdescent : baseEnd_4625610 < baseStart_4625610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625636 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 5, 5]
def baseStart_4625636 : Nat := 118140960795 + 4625636 * 2 ^ 59
def prefixEnd_4625636 : Nat := 4983230072969 + 3 ^ 40 * 4625636 * 2
def baseEnd_4625636 : Nat := 791724866913589803859031

theorem tailTrace_4625636 : CollatzResearch.WordTrace tailWord_4625636 prefixEnd_4625636 791724866913589803859031 := by
  unfold tailWord_4625636
  simp only [CollatzResearch.WordTrace]
  refine ⟨84355402535059121289568381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112473870046745495052757841 84355402535059121289568381)
  ·
    refine ⟨31633275950647170483588143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84355402535059121289568381 31633275950647170483588143)
    ·
      refine ⟨47449913925970755725382215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31633275950647170483588143 47449913925970755725382215)
      ·
        refine ⟨71174870888956133588073323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47449913925970755725382215 71174870888956133588073323)
        ·
          refine ⟨106762306333434200382109985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71174870888956133588073323 106762306333434200382109985)
          ·
            refine ⟨80071729750075650286582489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106762306333434200382109985 80071729750075650286582489)
            ·
              refine ⟨60053797312556737714936867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80071729750075650286582489 60053797312556737714936867)
              ·
                refine ⟨90080695968835106572405301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60053797312556737714936867 90080695968835106572405301)
                ·
                  refine ⟨8445065247078291241162997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90080695968835106572405301 8445065247078291241162997)
                  ·
                    refine ⟨791724866913589803859031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8445065247078291241162997 791724866913589803859031)
                    ·
                      rfl

theorem cell23_4625636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_4625636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625636 prefixEnd_4625636 := by exact prefixLift 4625636
  have htrace : WordTrace (prefixWord ++ tailWord_4625636) baseStart_4625636 baseEnd_4625636 := by
    simpa [prefixWord, tailWord_4625636, baseEnd_4625636] using wordTrace_append hprefix tailTrace_4625636
  have hstable : (prefixWord ++ tailWord_4625636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625636).length < 2 ^ (prefixWord ++ tailWord_4625636).sum := by decide
  have hdescent : baseEnd_4625636 < baseStart_4625636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625643 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 1, 5, 2]
def baseStart_4625643 : Nat := 118140960795 + 4625643 * 2 ^ 59
def prefixEnd_4625643 : Nat := 4983230072969 + 3 ^ 40 * 4625643 * 2
def baseEnd_4625643 : Nat := 2375178195105350884189561

theorem tailTrace_4625643 : CollatzResearch.WordTrace tailWord_4625643 prefixEnd_4625643 2375178195105350884189561 := by
  unfold tailWord_4625643
  simp only [CollatzResearch.WordTrace]
  refine ⟨168711060381092882774641583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112474040254061921849761055 168711060381092882774641583)
  ·
    refine ⟨253066590571639324161962375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168711060381092882774641583 253066590571639324161962375)
    ·
      refine ⟨379599885857458986242943563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253066590571639324161962375 379599885857458986242943563)
      ·
        refine ⟨569399828786188479364415345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379599885857458986242943563 569399828786188479364415345)
        ·
          refine ⟨427049871589641359523311509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 569399828786188479364415345 427049871589641359523311509)
          ·
            refine ⟨20017962730764438727655227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 427049871589641359523311509 20017962730764438727655227)
            ·
              refine ⟨30026944096146658091482841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20017962730764438727655227 30026944096146658091482841)
              ·
                refine ⟨22520208072109993568612131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30026944096146658091482841 22520208072109993568612131)
                ·
                  refine ⟨33780312108164990352918197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22520208072109993568612131 33780312108164990352918197)
                  ·
                    refine ⟨3166904260140467845586081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33780312108164990352918197 3166904260140467845586081)
                    ·
                      refine ⟨2375178195105350884189561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3166904260140467845586081 2375178195105350884189561)
                      ·
                        rfl

theorem cell23_4625643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 5, 2].length) (baseStart_4625643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625643 prefixEnd_4625643 := by exact prefixLift 4625643
  have htrace : WordTrace (prefixWord ++ tailWord_4625643) baseStart_4625643 baseEnd_4625643 := by
    simpa [prefixWord, tailWord_4625643, baseEnd_4625643] using wordTrace_append hprefix tailTrace_4625643
  have hstable : (prefixWord ++ tailWord_4625643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625643).length < 2 ^ (prefixWord ++ tailWord_4625643).sum := by decide
  have hdescent : baseEnd_4625643 < baseStart_4625643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625646 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_4625646 : Nat := 118140960795 + 4625646 * 2 ^ 59
def prefixEnd_4625646 : Nat := 4983230072969 + 3 ^ 40 * 4625646 * 2
def baseEnd_4625646 : Nat := 2375179735547314372452047

theorem tailTrace_4625646 : CollatzResearch.WordTrace tailWord_4625646 prefixEnd_4625646 2375179735547314372452047 := by
  unfold tailWord_4625646
  simp only [CollatzResearch.WordTrace]
  refine ⟨21088896225010251785875099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112474113200054676191333861 21088896225010251785875099)
  ·
    refine ⟨31633344337515377678812649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21088896225010251785875099 31633344337515377678812649)
    ·
      refine ⟨23725008253136533259109487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31633344337515377678812649 23725008253136533259109487)
      ·
        refine ⟨35587512379704799888664231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23725008253136533259109487 35587512379704799888664231)
        ·
          refine ⟨53381268569557199832996347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35587512379704799888664231 53381268569557199832996347)
          ·
            refine ⟨80071902854335799749494521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53381268569557199832996347 80071902854335799749494521)
            ·
              refine ⟨60053927140751849812120891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80071902854335799749494521 60053927140751849812120891)
              ·
                refine ⟨90080890711127774718181337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60053927140751849812120891 90080890711127774718181337)
                ·
                  refine ⟨67560668033345831038636003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90080890711127774718181337 67560668033345831038636003)
                  ·
                    refine ⟨101341002050018746557954005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67560668033345831038636003 101341002050018746557954005)
                    ·
                      refine ⟨2375179735547314372452047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101341002050018746557954005 2375179735547314372452047)
                      ·
                        rfl

theorem cell23_4625646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_4625646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625646 prefixEnd_4625646 := by exact prefixLift 4625646
  have htrace : WordTrace (prefixWord ++ tailWord_4625646) baseStart_4625646 baseEnd_4625646 := by
    simpa [prefixWord, tailWord_4625646, baseEnd_4625646] using wordTrace_append hprefix tailTrace_4625646
  have hstable : (prefixWord ++ tailWord_4625646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625646).length < 2 ^ (prefixWord ++ tailWord_4625646).sum := by decide
  have hdescent : baseEnd_4625646 < baseStart_4625646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625667 : List Nat := [1, 1, 1, 3, 2, 4, 3, 3, 1, 1, 3]
def baseStart_4625667 : Nat := 118140960795 + 4625667 * 2 ^ 59
def prefixEnd_4625667 : Nat := 4983230072969 + 3 ^ 40 * 4625667 * 2
def baseEnd_4625667 : Nat := 2375190518641058790289451

theorem tailTrace_4625667 : CollatzResearch.WordTrace tailWord_4625667 prefixEnd_4625667 2375190518641058790289451 := by
  unfold tailWord_4625667
  simp only [CollatzResearch.WordTrace]
  refine ⟨168711935733005934873515255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112474623822003956582343503 168711935733005934873515255)
  ·
    refine ⟨253067903599508902310272883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168711935733005934873515255 253067903599508902310272883)
    ·
      refine ⟨379601855399263353465409325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253067903599508902310272883 379601855399263353465409325)
      ·
        refine ⟨142350695774723757549528497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 379601855399263353465409325 142350695774723757549528497)
        ·
          refine ⟨106763021831042818162146373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142350695774723757549528497 106763021831042818162146373)
          ·
            refine ⟨20018066593320528405402445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106763021831042818162146373 20018066593320528405402445)
            ·
              refine ⟨7506774972495198152025917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20018066593320528405402445 7506774972495198152025917)
              ·
                refine ⟨2815040614685699307009719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7506774972495198152025917 2815040614685699307009719)
                ·
                  refine ⟨4222560922028548960514579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2815040614685699307009719 4222560922028548960514579)
                  ·
                    refine ⟨6333841383042823440771869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4222560922028548960514579 6333841383042823440771869)
                    ·
                      refine ⟨2375190518641058790289451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6333841383042823440771869 2375190518641058790289451)
                      ·
                        rfl

theorem cell23_4625667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 1, 1, 3].length) (baseStart_4625667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625667 prefixEnd_4625667 := by exact prefixLift 4625667
  have htrace : WordTrace (prefixWord ++ tailWord_4625667) baseStart_4625667 baseEnd_4625667 := by
    simpa [prefixWord, tailWord_4625667, baseEnd_4625667] using wordTrace_append hprefix tailTrace_4625667
  have hstable : (prefixWord ++ tailWord_4625667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625667).length < 2 ^ (prefixWord ++ tailWord_4625667).sum := by decide
  have hdescent : baseEnd_4625667 < baseStart_4625667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625673 : List Nat := [1, 2, 1, 1, 3, 3, 1, 5, 1, 1, 4]
def baseStart_4625673 : Nat := 118140960795 + 4625673 * 2 ^ 59
def prefixEnd_4625673 : Nat := 4983230072969 + 3 ^ 40 * 4625673 * 2
def baseEnd_4625673 : Nat := 2375193599524985766814423

theorem tailTrace_4625673 : CollatzResearch.WordTrace tailWord_4625673 prefixEnd_4625673 2375193599524985766814423 := by
  unfold tailWord_4625673
  simp only [CollatzResearch.WordTrace]
  refine ⟨168712154570984197898233673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112474769713989465265489115 168712154570984197898233673)
  ·
    refine ⟨126534115928238148423675255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168712154570984197898233673 126534115928238148423675255)
    ·
      refine ⟨189801173892357222635512883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126534115928238148423675255 189801173892357222635512883)
      ·
        refine ⟨284701760838535833953269325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189801173892357222635512883 284701760838535833953269325)
        ·
          refine ⟨106763160314450937732475997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 284701760838535833953269325 106763160314450937732475997)
          ·
            refine ⟨40036185117919101649678499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106763160314450937732475997 40036185117919101649678499)
            ·
              refine ⟨60054277676878652474517749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40036185117919101649678499 60054277676878652474517749)
              ·
                refine ⟨5630088532207373669486039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60054277676878652474517749 5630088532207373669486039)
                ·
                  refine ⟨8445132798311060504229059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5630088532207373669486039 8445132798311060504229059)
                  ·
                    refine ⟨12667699197466590756343589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8445132798311060504229059 12667699197466590756343589)
                    ·
                      refine ⟨2375193599524985766814423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12667699197466590756343589 2375193599524985766814423)
                      ·
                        rfl

theorem cell23_4625673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 1, 4].length) (baseStart_4625673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625673 prefixEnd_4625673 := by exact prefixLift 4625673
  have htrace : WordTrace (prefixWord ++ tailWord_4625673) baseStart_4625673 baseEnd_4625673 := by
    simpa [prefixWord, tailWord_4625673, baseEnd_4625673] using wordTrace_append hprefix tailTrace_4625673
  have hstable : (prefixWord ++ tailWord_4625673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625673).length < 2 ^ (prefixWord ++ tailWord_4625673).sum := by decide
  have hdescent : baseEnd_4625673 < baseStart_4625673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625700 : List Nat := [2, 3, 1, 3, 1, 1, 3, 3, 2, 4]
def baseStart_4625700 : Nat := 118140960795 + 4625700 * 2 ^ 59
def prefixEnd_4625700 : Nat := 4983230072969 + 3 ^ 40 * 4625700 * 2
def baseEnd_4625700 : Nat := 791735821167552387058933

theorem tailTrace_4625700 : CollatzResearch.WordTrace tailWord_4625700 prefixEnd_4625700 791735821167552387058933 := by
  unfold tailWord_4625700
  simp only [CollatzResearch.WordTrace]
  refine ⟨84356569670943190754733277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112475426227924254339644369 84356569670943190754733277)
  ·
    refine ⟨31633713626603696533024979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84356569670943190754733277 31633713626603696533024979)
    ·
      refine ⟨47450570439905544799537469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31633713626603696533024979 47450570439905544799537469)
      ·
        refine ⟨17793963914964579299826551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47450570439905544799537469 17793963914964579299826551)
        ·
          refine ⟨26690945872446868949739827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17793963914964579299826551 26690945872446868949739827)
          ·
            refine ⟨40036418808670303424609741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26690945872446868949739827 40036418808670303424609741)
            ·
              refine ⟨15013657053251363784228653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40036418808670303424609741 15013657053251363784228653)
              ·
                refine ⟨5630121394969261419085745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15013657053251363784228653 5630121394969261419085745)
                ·
                  refine ⟨4222591046226946064314309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5630121394969261419085745 4222591046226946064314309)
                  ·
                    refine ⟨791735821167552387058933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4222591046226946064314309 791735821167552387058933)
                    ·
                      rfl

theorem cell23_4625700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_4625700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625700 prefixEnd_4625700 := by exact prefixLift 4625700
  have htrace : WordTrace (prefixWord ++ tailWord_4625700) baseStart_4625700 baseEnd_4625700 := by
    simpa [prefixWord, tailWord_4625700, baseEnd_4625700] using wordTrace_append hprefix tailTrace_4625700
  have hstable : (prefixWord ++ tailWord_4625700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625700).length < 2 ^ (prefixWord ++ tailWord_4625700).sum := by decide
  have hdescent : baseEnd_4625700 < baseStart_4625700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625727 : List Nat := [1, 1, 2, 2, 4, 3, 3, 1, 1, 2, 3]
def baseStart_4625727 : Nat := 118140960795 + 4625727 * 2 ^ 59
def prefixEnd_4625727 : Nat := 4983230072969 + 3 ^ 40 * 4625727 * 2
def baseEnd_4625727 : Nat := 2375221327480328555539175

theorem tailTrace_4625727 : CollatzResearch.WordTrace tailWord_4625727 prefixEnd_4625727 2375221327480328555539175 := by
  unfold tailWord_4625727
  simp only [CollatzResearch.WordTrace]
  refine ⟨168714124112788565120699435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112476082741859043413799623 168714124112788565120699435)
  ·
    refine ⟨253071186169182847681049153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168714124112788565120699435 253071186169182847681049153)
    ·
      refine ⟨189803389626887135760786865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253071186169182847681049153 189803389626887135760786865)
      ·
        refine ⟨142352542220165351820590149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189803389626887135760786865 142352542220165351820590149)
        ·
          refine ⟨26691101666281003466360653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142352542220165351820590149 26691101666281003466360653)
          ·
            refine ⟨10009163124855376299885245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26691101666281003466360653 10009163124855376299885245)
            ·
              refine ⟨3753436171820766112456967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10009163124855376299885245 3753436171820766112456967)
              ·
                refine ⟨5630154257731149168685451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3753436171820766112456967 5630154257731149168685451)
                ·
                  refine ⟨8445231386596723753028177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5630154257731149168685451 8445231386596723753028177)
                  ·
                    refine ⟨6333923539947542814771133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8445231386596723753028177 6333923539947542814771133)
                    ·
                      refine ⟨2375221327480328555539175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6333923539947542814771133 2375221327480328555539175)
                      ·
                        rfl

theorem cell23_4625727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 1, 2, 3].length) (baseStart_4625727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625727 prefixEnd_4625727 := by exact prefixLift 4625727
  have htrace : WordTrace (prefixWord ++ tailWord_4625727) baseStart_4625727 baseEnd_4625727 := by
    simpa [prefixWord, tailWord_4625727, baseEnd_4625727] using wordTrace_append hprefix tailTrace_4625727
  have hstable : (prefixWord ++ tailWord_4625727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625727).length < 2 ^ (prefixWord ++ tailWord_4625727).sum := by decide
  have hdescent : baseEnd_4625727 < baseStart_4625727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625803 : List Nat := [1, 1, 1, 1, 4, 3, 4, 1, 7]
def baseStart_4625803 : Nat := 118140960795 + 4625803 * 2 ^ 59
def prefixEnd_4625803 : Nat := 4983230072969 + 3 ^ 40 * 4625803 * 2
def baseEnd_4625803 : Nat := 263917816890007806465425

theorem tailTrace_4625803 : CollatzResearch.WordTrace tailWord_4625803 prefixEnd_4625803 263917816890007806465425 := by
  unfold tailWord_4625803
  simp only [CollatzResearch.WordTrace]
  refine ⟨168716896060513230100466063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112477930707008820066977375 168716896060513230100466063)
  ·
    refine ⟨253075344090769845150699095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168716896060513230100466063 253075344090769845150699095)
    ·
      refine ⟨379613016136154767726048643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253075344090769845150699095 379613016136154767726048643)
      ·
        refine ⟨569419524204232151589072965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379613016136154767726048643 569419524204232151589072965)
        ·
          refine ⟨106766160788293528422951181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 569419524204232151589072965 106766160788293528422951181)
          ·
            refine ⟨40037310295610073158606693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106766160788293528422951181 40037310295610073158606693)
            ·
              refine ⟨7506995680426888717238755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40037310295610073158606693 7506995680426888717238755)
              ·
                refine ⟨11260493520640333075858133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7506995680426888717238755 11260493520640333075858133)
                ·
                  refine ⟨263917816890007806465425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11260493520640333075858133 263917816890007806465425)
                  ·
                    rfl

theorem cell23_4625803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 7].length) (baseStart_4625803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625803 prefixEnd_4625803 := by exact prefixLift 4625803
  have htrace : WordTrace (prefixWord ++ tailWord_4625803) baseStart_4625803 baseEnd_4625803 := by
    simpa [prefixWord, tailWord_4625803, baseEnd_4625803] using wordTrace_append hprefix tailTrace_4625803
  have hstable : (prefixWord ++ tailWord_4625803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625803).length < 2 ^ (prefixWord ++ tailWord_4625803).sum := by decide
  have hdescent : baseEnd_4625803 < baseStart_4625803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625860 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_4625860 : Nat := 118140960795 + 4625860 * 2 ^ 59
def prefixEnd_4625860 : Nat := 4983230072969 + 3 ^ 40 * 4625860 * 2
def baseEnd_4625860 : Nat := 2375289620407376535176063

theorem tailTrace_4625860 : CollatzResearch.WordTrace tailWord_4625860 prefixEnd_4625860 2375289620407376535176063 := by
  unfold tailWord_4625860
  simp only [CollatzResearch.WordTrace]
  refine ⟨84359487510653364417645517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112479316680871152556860689 84359487510653364417645517)
  ·
    refine ⟨31634807816495011656617069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84359487510653364417645517 31634807816495011656617069)
    ·
      refine ⟨11863052931185629371231401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31634807816495011656617069 11863052931185629371231401)
      ·
        refine ⟨8897289698389222028423551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11863052931185629371231401 8897289698389222028423551)
        ·
          refine ⟨13345934547583833042635327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8897289698389222028423551 13345934547583833042635327)
          ·
            refine ⟨20018901821375749563952991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13345934547583833042635327 20018901821375749563952991)
            ·
              refine ⟨30028352732063624345929487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20018901821375749563952991 30028352732063624345929487)
              ·
                refine ⟨45042529098095436518894231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30028352732063624345929487 45042529098095436518894231)
                ·
                  refine ⟨67563793647143154778341347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45042529098095436518894231 67563793647143154778341347)
                  ·
                    refine ⟨101345690470714732167512021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67563793647143154778341347 101345690470714732167512021)
                    ·
                      refine ⟨2375289620407376535176063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101345690470714732167512021 2375289620407376535176063)
                      ·
                        rfl

theorem cell23_4625860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_4625860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625860 prefixEnd_4625860 := by exact prefixLift 4625860
  have htrace : WordTrace (prefixWord ++ tailWord_4625860) baseStart_4625860 baseEnd_4625860 := by
    simpa [prefixWord, tailWord_4625860, baseEnd_4625860] using wordTrace_append hprefix tailTrace_4625860
  have hstable : (prefixWord ++ tailWord_4625860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625860).length < 2 ^ (prefixWord ++ tailWord_4625860).sum := by decide
  have hdescent : baseEnd_4625860 < baseStart_4625860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625880 : List Nat := [2, 1, 2, 2, 2, 1, 2, 4, 3, 4]
def baseStart_4625880 : Nat := 118140960795 + 4625880 * 2 ^ 59
def prefixEnd_4625880 : Nat := 4983230072969 + 3 ^ 40 * 4625880 * 2
def baseEnd_4625880 : Nat := 791766630006822152308657

theorem tailTrace_4625880 : CollatzResearch.WordTrace tailWord_4625880 prefixEnd_4625880 791766630006822152308657 := by
  unfold tailWord_4625880
  simp only [CollatzResearch.WordTrace]
  refine ⟨84359852240617136125509547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112479802987489514834012729 84359852240617136125509547)
  ·
    refine ⟨126539778360925704188264321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84359852240617136125509547 126539778360925704188264321)
    ·
      refine ⟨94904833770694278141198241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126539778360925704188264321 94904833770694278141198241)
      ·
        refine ⟨71178625328020708605898681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94904833770694278141198241 71178625328020708605898681)
        ·
          refine ⟨53383968996015531454424011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71178625328020708605898681 53383968996015531454424011)
          ·
            refine ⟨80075953494023297181636017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53383968996015531454424011 80075953494023297181636017)
            ·
              refine ⟨60056965120517472886227013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80075953494023297181636017 60056965120517472886227013)
              ·
                refine ⟨11260680960097026166167565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60056965120517472886227013 11260680960097026166167565)
                ·
                  refine ⟨4222755360036384812312837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11260680960097026166167565 4222755360036384812312837)
                  ·
                    refine ⟨791766630006822152308657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4222755360036384812312837 791766630006822152308657)
                    ·
                      rfl

theorem cell23_4625880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 3, 4].length) (baseStart_4625880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625880 prefixEnd_4625880 := by exact prefixLift 4625880
  have htrace : WordTrace (prefixWord ++ tailWord_4625880) baseStart_4625880 baseEnd_4625880 := by
    simpa [prefixWord, tailWord_4625880, baseEnd_4625880] using wordTrace_append hprefix tailTrace_4625880
  have hstable : (prefixWord ++ tailWord_4625880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625880).length < 2 ^ (prefixWord ++ tailWord_4625880).sum := by decide
  have hdescent : baseEnd_4625880 < baseStart_4625880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625913 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 6]
def baseStart_4625913 : Nat := 118140960795 + 4625913 * 2 ^ 59
def prefixEnd_4625913 : Nat := 4983230072969 + 3 ^ 40 * 4625913 * 2
def baseEnd_4625913 : Nat := 2375316834882064827813319

theorem tailTrace_4625913 : CollatzResearch.WordTrace tailWord_4625913 prefixEnd_4625913 2375316834882064827813319 := by
  unfold tailWord_4625913
  simp only [CollatzResearch.WordTrace]
  refine ⟨168720908090114718886970393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112480605393409812591313595 168720908090114718886970393)
  ·
    refine ⟨126540681067586039165227795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168720908090114718886970393 126540681067586039165227795)
    ·
      refine ⟨189811021601379058747841693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126540681067586039165227795 189811021601379058747841693)
      ·
        refine ⟨71179133100517147030440635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189811021601379058747841693 71179133100517147030440635)
        ·
          refine ⟨106768699650775720545660953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71179133100517147030440635 106768699650775720545660953)
          ·
            refine ⟨80076524738081790409245715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106768699650775720545660953 80076524738081790409245715)
            ·
              refine ⟨120114787107122685613868573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80076524738081790409245715 120114787107122685613868573)
              ·
                refine ⟨45043045165171007105200715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120114787107122685613868573 45043045165171007105200715)
                ·
                  refine ⟨67564567747756510657801073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45043045165171007105200715 67564567747756510657801073)
                  ·
                    refine ⟨50673425810817382993350805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67564567747756510657801073 50673425810817382993350805)
                    ·
                      refine ⟨2375316834882064827813319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50673425810817382993350805 2375316834882064827813319)
                      ·
                        rfl

theorem cell23_4625913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_4625913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625913 prefixEnd_4625913 := by exact prefixLift 4625913
  have htrace : WordTrace (prefixWord ++ tailWord_4625913) baseStart_4625913 baseEnd_4625913 := by
    simpa [prefixWord, tailWord_4625913, baseEnd_4625913] using wordTrace_append hprefix tailTrace_4625913
  have hstable : (prefixWord ++ tailWord_4625913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625913).length < 2 ^ (prefixWord ++ tailWord_4625913).sum := by decide
  have hdescent : baseEnd_4625913 < baseStart_4625913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625937 : List Nat := [1, 2, 2, 1, 1, 2, 5, 2, 3, 1, 3]
def baseStart_4625937 : Nat := 118140960795 + 4625937 * 2 ^ 59
def prefixEnd_4625937 : Nat := 4983230072969 + 3 ^ 40 * 4625937 * 2
def baseEnd_4625937 : Nat := 2375329158417772733913209

theorem tailTrace_4625937 : CollatzResearch.WordTrace tailWord_4625937 prefixEnd_4625937 2375329158417772733913209 := by
  unfold tailWord_4625937
  simp only [CollatzResearch.WordTrace]
  refine ⟨168721783442027770985844065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112481188961351847323896043 168721783442027770985844065)
  ·
    refine ⟨126541337581520828239383049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168721783442027770985844065 126541337581520828239383049)
    ·
      refine ⟨94906003186140621179537287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126541337581520828239383049 94906003186140621179537287)
      ·
        refine ⟨142359004779210931769305931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94906003186140621179537287 142359004779210931769305931)
        ·
          refine ⟨213538507168816397653958897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142359004779210931769305931 213538507168816397653958897)
          ·
            refine ⟨160153880376612298240469173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213538507168816397653958897 160153880376612298240469173)
            ·
              refine ⟨15014426285307402960043985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 160153880376612298240469173 15014426285307402960043985)
              ·
                refine ⟨11260819713980552220032989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15014426285307402960043985 11260819713980552220032989)
                ·
                  refine ⟨4222807392742707082512371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11260819713980552220032989 4222807392742707082512371)
                  ·
                    refine ⟨6334211089114060623768557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4222807392742707082512371 6334211089114060623768557)
                    ·
                      refine ⟨2375329158417772733913209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6334211089114060623768557 2375329158417772733913209)
                      ·
                        rfl

theorem cell23_4625937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 1, 3].length) (baseStart_4625937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625937 prefixEnd_4625937 := by exact prefixLift 4625937
  have htrace : WordTrace (prefixWord ++ tailWord_4625937) baseStart_4625937 baseEnd_4625937 := by
    simpa [prefixWord, tailWord_4625937, baseEnd_4625937] using wordTrace_append hprefix tailTrace_4625937
  have hstable : (prefixWord ++ tailWord_4625937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625937).length < 2 ^ (prefixWord ++ tailWord_4625937).sum := by decide
  have hdescent : baseEnd_4625937 < baseStart_4625937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4625994 : List Nat := [3, 1, 2, 1, 1, 3, 1, 4, 3, 2, 2]
def baseStart_4625994 : Nat := 118140960795 + 4625994 * 2 ^ 59
def prefixEnd_4625994 : Nat := 4983230072969 + 3 ^ 40 * 4625994 * 2
def baseEnd_4625994 : Nat := 2375358426815079010900447

theorem tailTrace_4625994 : CollatzResearch.WordTrace tailWord_4625994 prefixEnd_4625994 2375358426815079010900447 := by
  unfold tailWord_4625994
  simp only [CollatzResearch.WordTrace]
  refine ⟨42180965600705317430167259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112482574935214179813779357 42180965600705317430167259)
  ·
    refine ⟨63271448401057976145250889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42180965600705317430167259 63271448401057976145250889)
    ·
      refine ⟨47453586300793482108938167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63271448401057976145250889 47453586300793482108938167)
      ·
        refine ⟨71180379451190223163407251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47453586300793482108938167 71180379451190223163407251)
        ·
          refine ⟨106770569176785334745110877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71180379451190223163407251 106770569176785334745110877)
          ·
            refine ⟨40038963441294500529416579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106770569176785334745110877 40038963441294500529416579)
            ·
              refine ⟨60058445161941750794124869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40038963441294500529416579 60058445161941750794124869)
              ·
                refine ⟨11260958467864078273898413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60058445161941750794124869 11260958467864078273898413)
                ·
                  refine ⟨4222859425449029352711905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11260958467864078273898413 4222859425449029352711905)
                  ·
                    refine ⟨3167144569086772014533929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4222859425449029352711905 3167144569086772014533929)
                    ·
                      refine ⟨2375358426815079010900447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3167144569086772014533929 2375358426815079010900447)
                      ·
                        rfl

theorem cell23_4625994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_4625994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4625994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4625994 prefixEnd_4625994 := by exact prefixLift 4625994
  have htrace : WordTrace (prefixWord ++ tailWord_4625994) baseStart_4625994 baseEnd_4625994 := by
    simpa [prefixWord, tailWord_4625994, baseEnd_4625994] using wordTrace_append hprefix tailTrace_4625994
  have hstable : (prefixWord ++ tailWord_4625994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4625994).length < 2 ^ (prefixWord ++ tailWord_4625994).sum := by decide
  have hdescent : baseEnd_4625994 < baseStart_4625994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4625994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626038 : List Nat := [5, 1, 1, 2, 2, 3, 2, 1, 2, 4]
def baseStart_4626038 : Nat := 118140960795 + 4626038 * 2 ^ 59
def prefixEnd_4626038 : Nat := 4983230072969 + 3 ^ 40 * 4626038 * 2
def baseEnd_4626038 : Nat := 791793673321292279583415

theorem tailTrace_4626038 : CollatzResearch.WordTrace tailWord_4626038 prefixEnd_4626038 791793673321292279583415 := by
  unfold tailWord_4626038
  simp only [CollatzResearch.WordTrace]
  refine ⟨10545341700916366577204423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112483644809774576823513845 10545341700916366577204423)
  ·
    refine ⟨15818012551374549865806635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10545341700916366577204423 15818012551374549865806635)
    ·
      refine ⟨23727018827061824798709953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15818012551374549865806635 23727018827061824798709953)
      ·
        refine ⟨17795264120296368599032465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23727018827061824798709953 17795264120296368599032465)
        ·
          refine ⟨13346448090222276449274349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17795264120296368599032465 13346448090222276449274349)
          ·
            refine ⟨5004918033833353668477881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13346448090222276449274349 5004918033833353668477881)
            ·
              refine ⟨3753688525375015251358411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5004918033833353668477881 3753688525375015251358411)
              ·
                refine ⟨5630532788062522877037617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3753688525375015251358411 5630532788062522877037617)
                ·
                  refine ⟨4222899591046892157778213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5630532788062522877037617 4222899591046892157778213)
                  ·
                    refine ⟨791793673321292279583415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4222899591046892157778213 791793673321292279583415)
                    ·
                      rfl

theorem cell23_4626038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_4626038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626038 prefixEnd_4626038 := by exact prefixLift 4626038
  have htrace : WordTrace (prefixWord ++ tailWord_4626038) baseStart_4626038 baseEnd_4626038 := by
    simpa [prefixWord, tailWord_4626038, baseEnd_4626038] using wordTrace_append hprefix tailTrace_4626038
  have hstable : (prefixWord ++ tailWord_4626038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626038).length < 2 ^ (prefixWord ++ tailWord_4626038).sum := by decide
  have hdescent : baseEnd_4626038 < baseStart_4626038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626078 : List Nat := [4, 3, 1, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_4626078 : Nat := 118140960795 + 4626078 * 2 ^ 59
def prefixEnd_4626078 : Nat := 4983230072969 + 3 ^ 40 * 4626078 * 2
def baseEnd_4626078 : Nat := 2375401559190056682250061

theorem tailTrace_4626078 : CollatzResearch.WordTrace tailWord_4626078 prefixEnd_4626078 2375401559190056682250061 := by
  unfold tailWord_4626078
  simp only [CollatzResearch.WordTrace]
  refine ⟨21090865766814619008340861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112484617423011301377817925 21090865766814619008340861)
  ·
    refine ⟨7909074662555482128127823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21090865766814619008340861 7909074662555482128127823)
    ·
      refine ⟨11863611993833223192191735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7909074662555482128127823 11863611993833223192191735)
      ·
        refine ⟨17795417990749834788287603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11863611993833223192191735 17795417990749834788287603)
        ·
          refine ⟨26693126986124752182431405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17795417990749834788287603 26693126986124752182431405)
          ·
            refine ⟨10009922619796782068411777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26693126986124752182431405 10009922619796782068411777)
            ·
              refine ⟨7507441964847586551308833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10009922619796782068411777 7507441964847586551308833)
              ·
                refine ⟨5630581473635689913481625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7507441964847586551308833 5630581473635689913481625)
                ·
                  refine ⟨4222936105226767435111219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5630581473635689913481625 4222936105226767435111219)
                  ·
                    refine ⟨6334404157840151152666829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4222936105226767435111219 6334404157840151152666829)
                    ·
                      refine ⟨2375401559190056682250061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6334404157840151152666829 2375401559190056682250061)
                      ·
                        rfl

theorem cell23_4626078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_4626078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626078 prefixEnd_4626078 := by exact prefixLift 4626078
  have htrace : WordTrace (prefixWord ++ tailWord_4626078) baseStart_4626078 baseEnd_4626078 := by
    simpa [prefixWord, tailWord_4626078, baseEnd_4626078] using wordTrace_append hprefix tailTrace_4626078
  have hstable : (prefixWord ++ tailWord_4626078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626078).length < 2 ^ (prefixWord ++ tailWord_4626078).sum := by decide
  have hdescent : baseEnd_4626078 < baseStart_4626078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626079 : List Nat := [1, 1, 2, 7, 2, 1, 2, 2, 1, 2, 2]
def baseStart_4626079 : Nat := 118140960795 + 4626079 * 2 ^ 59
def prefixEnd_4626079 : Nat := 4983230072969 + 3 ^ 40 * 4626079 * 2
def baseEnd_4626079 : Nat := 2375402072670711178337557

theorem tailTrace_4626079 : CollatzResearch.WordTrace tailWord_4626079 prefixEnd_4626079 2375402072670711178337557 := by
  unfold tailWord_4626079
  simp only [CollatzResearch.WordTrace]
  refine ⟨168726962607513329237513291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112484641738342219491675527 168726962607513329237513291)
  ·
    refine ⟨253090443911269993856269937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168726962607513329237513291 253090443911269993856269937)
    ·
      refine ⟨189817832933452495392202453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253090443911269993856269937 189817832933452495392202453)
      ·
        refine ⟨4448855459377792860754745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 189817832933452495392202453 4448855459377792860754745)
        ·
          refine ⟨3336641594533344645566059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4448855459377792860754745 3336641594533344645566059)
          ·
            refine ⟨5004962391800016968349089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3336641594533344645566059 5004962391800016968349089)
            ·
              refine ⟨3753721793850012726261817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5004962391800016968349089 3753721793850012726261817)
              ·
                refine ⟨2815291345387509544696363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3753721793850012726261817 2815291345387509544696363)
                ·
                  refine ⟨4222937018081264317044545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2815291345387509544696363 4222937018081264317044545)
                  ·
                    refine ⟨3167202763560948237783409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4222937018081264317044545 3167202763560948237783409)
                    ·
                      refine ⟨2375402072670711178337557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3167202763560948237783409 2375402072670711178337557)
                      ·
                        rfl

theorem cell23_4626079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_4626079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626079 prefixEnd_4626079 := by exact prefixLift 4626079
  have htrace : WordTrace (prefixWord ++ tailWord_4626079) baseStart_4626079 baseEnd_4626079 := by
    simpa [prefixWord, tailWord_4626079, baseEnd_4626079] using wordTrace_append hprefix tailTrace_4626079
  have hstable : (prefixWord ++ tailWord_4626079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626079).length < 2 ^ (prefixWord ++ tailWord_4626079).sum := by decide
  have hdescent : baseEnd_4626079 < baseStart_4626079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626141 : List Nat := [1, 4, 3, 3, 1, 1, 2, 1, 7]
def baseStart_4626141 : Nat := 118140960795 + 4626141 * 2 ^ 59
def prefixEnd_4626141 : Nat := 4983230072969 + 3 ^ 40 * 4626141 * 2
def baseEnd_4626141 : Nat := 263937100941254437306919

theorem tailTrace_4626141 : CollatzResearch.WordTrace tailWord_4626141 prefixEnd_4626141 263937100941254437306919 := by
  unfold tailWord_4626141
  simp only [CollatzResearch.WordTrace]
  refine ⟨168729223933288713826270277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112486149288859142550846851 168729223933288713826270277)
  ·
    refine ⟨31636729487491633842425677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168729223933288713826270277 31636729487491633842425677)
    ·
      refine ⟨11863773557809362690909629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31636729487491633842425677 11863773557809362690909629)
      ·
        refine ⟨4448915084178511009091111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11863773557809362690909629 4448915084178511009091111)
        ·
          refine ⟨6673372626267766513636667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4448915084178511009091111 6673372626267766513636667)
          ·
            refine ⟨10010058939401649770455001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6673372626267766513636667 10010058939401649770455001)
            ·
              refine ⟨7507544204551237327841251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10010058939401649770455001 7507544204551237327841251)
              ·
                refine ⟨11261316306826855991761877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7507544204551237327841251 11261316306826855991761877)
                ·
                  refine ⟨263937100941254437306919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11261316306826855991761877 263937100941254437306919)
                  ·
                    rfl

theorem cell23_4626141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_4626141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626141 prefixEnd_4626141 := by exact prefixLift 4626141
  have htrace : WordTrace (prefixWord ++ tailWord_4626141) baseStart_4626141 baseEnd_4626141 := by
    simpa [prefixWord, tailWord_4626141, baseEnd_4626141] using wordTrace_append hprefix tailTrace_4626141
  have hstable : (prefixWord ++ tailWord_4626141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626141).length < 2 ^ (prefixWord ++ tailWord_4626141).sum := by decide
  have hdescent : baseEnd_4626141 < baseStart_4626141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626197 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 8]
def baseStart_4626197 : Nat := 118140960795 + 4626197 * 2 ^ 59
def prefixEnd_4626197 : Nat := 4983230072969 + 3 ^ 40 * 4626197 * 2
def baseEnd_4626197 : Nat := 263940295931993524073557

theorem tailTrace_4626197 : CollatzResearch.WordTrace tailWord_4626197 prefixEnd_4626197 263940295931993524073557 := by
  unfold tailWord_4626197
  simp only [CollatzResearch.WordTrace]
  refine ⟨168731266421085835390308845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112487510947390556926872563 168731266421085835390308845)
  ·
    refine ⟨63274224907907188271365817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168731266421085835390308845 63274224907907188271365817)
    ·
      refine ⟨47455668680930391203524363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63274224907907188271365817 47455668680930391203524363)
      ·
        refine ⟨71183503021395586805286545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47455668680930391203524363 71183503021395586805286545)
        ·
          refine ⟨53387627266046690103964909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71183503021395586805286545 53387627266046690103964909)
          ·
            refine ⟨20020360224767508788986841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53387627266046690103964909 20020360224767508788986841)
            ·
              refine ⟨15015270168575631591740131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20020360224767508788986841 15015270168575631591740131)
              ·
                refine ⟨22522905252863447387610197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15015270168575631591740131 22522905252863447387610197)
                ·
                  refine ⟨263940295931993524073557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22522905252863447387610197 263940295931993524073557)
                  ·
                    rfl

theorem cell23_4626197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 8].length) (baseStart_4626197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626197 prefixEnd_4626197 := by exact prefixLift 4626197
  have htrace : WordTrace (prefixWord ++ tailWord_4626197) baseStart_4626197 baseEnd_4626197 := by
    simpa [prefixWord, tailWord_4626197, baseEnd_4626197] using wordTrace_append hprefix tailTrace_4626197
  have hstable : (prefixWord ++ tailWord_4626197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626197).length < 2 ^ (prefixWord ++ tailWord_4626197).sum := by decide
  have hdescent : baseEnd_4626197 < baseStart_4626197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626228 : List Nat := [2, 5, 1, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_4626228 : Nat := 118140960795 + 4626228 * 2 ^ 59
def prefixEnd_4626228 : Nat := 4983230072969 + 3 ^ 40 * 4626228 * 2
def baseEnd_4626228 : Nat := 2375478581288231095374371

theorem tailTrace_4626228 : CollatzResearch.WordTrace tailWord_4626228 prefixEnd_4626228 2375478581288231095374371 := by
  unfold tailWord_4626228
  simp only [CollatzResearch.WordTrace]
  refine ⟨84366198541986763842343669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112488264722649018456458225 84366198541986763842343669)
  ·
    refine ⟨7909331113311259110219719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84366198541986763842343669 7909331113311259110219719)
    ·
      refine ⟨11863996669966888665329579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7909331113311259110219719 11863996669966888665329579)
      ·
        refine ⟨17795995004950332997994369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11863996669966888665329579 17795995004950332997994369)
        ·
          refine ⟨13346996253712749748495777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17795995004950332997994369 13346996253712749748495777)
          ·
            refine ⟨10010247190284562311371833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13346996253712749748495777 10010247190284562311371833)
            ·
              refine ⟨7507685392713421733528875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10010247190284562311371833 7507685392713421733528875)
              ·
                refine ⟨11261528089070132600293313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7507685392713421733528875 11261528089070132600293313)
                ·
                  refine ⟨8446146066802599450219985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11261528089070132600293313 8446146066802599450219985)
                  ·
                    refine ⟨6334609550101949587664989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8446146066802599450219985 6334609550101949587664989)
                    ·
                      refine ⟨2375478581288231095374371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6334609550101949587664989 2375478581288231095374371)
                      ·
                        rfl

theorem cell23_4626228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_4626228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626228 prefixEnd_4626228 := by exact prefixLift 4626228
  have htrace : WordTrace (prefixWord ++ tailWord_4626228) baseStart_4626228 baseEnd_4626228 := by
    simpa [prefixWord, tailWord_4626228, baseEnd_4626228] using wordTrace_append hprefix tailTrace_4626228
  have hstable : (prefixWord ++ tailWord_4626228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626228).length < 2 ^ (prefixWord ++ tailWord_4626228).sum := by decide
  have hdescent : baseEnd_4626228 < baseStart_4626228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626252 : List Nat := [2, 2, 1, 3, 5, 1, 2, 2, 1, 4]
def baseStart_4626252 : Nat := 118140960795 + 4626252 * 2 ^ 59
def prefixEnd_4626252 : Nat := 4983230072969 + 3 ^ 40 * 4626252 * 2
def baseEnd_4626252 : Nat := 791830301607979667158087

theorem tailTrace_4626252 : CollatzResearch.WordTrace tailWord_4626252 prefixEnd_4626252 791830301607979667158087 := by
  unfold tailWord_4626252
  simp only [CollatzResearch.WordTrace]
  refine ⟨84366636217943289891780505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112488848290591053189040673 84366636217943289891780505)
  ·
    refine ⟨63274977163457467418835379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84366636217943289891780505 63274977163457467418835379)
    ·
      refine ⟨94912465745186201128253069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63274977163457467418835379 94912465745186201128253069)
      ·
        refine ⟨35592174654444825423094901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94912465745186201128253069 35592174654444825423094901)
        ·
          refine ⟨3336766373854202383415147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35592174654444825423094901 3336766373854202383415147)
          ·
            refine ⟨5005149560781303575122721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3336766373854202383415147 5005149560781303575122721)
            ·
              refine ⟨3753862170585977681342041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5005149560781303575122721 3753862170585977681342041)
              ·
                refine ⟨2815396627939483261006531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3753862170585977681342041 2815396627939483261006531)
                ·
                  refine ⟨4223094941909224891509797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2815396627939483261006531 4223094941909224891509797)
                  ·
                    refine ⟨791830301607979667158087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4223094941909224891509797 791830301607979667158087)
                    ·
                      rfl

theorem cell23_4626252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 1, 4].length) (baseStart_4626252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626252 prefixEnd_4626252 := by exact prefixLift 4626252
  have htrace : WordTrace (prefixWord ++ tailWord_4626252) baseStart_4626252 baseEnd_4626252 := by
    simpa [prefixWord, tailWord_4626252, baseEnd_4626252] using wordTrace_append hprefix tailTrace_4626252
  have hstable : (prefixWord ++ tailWord_4626252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626252).length < 2 ^ (prefixWord ++ tailWord_4626252).sum := by decide
  have hdescent : baseEnd_4626252 < baseStart_4626252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626264 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 4, 6, 2]
def baseStart_4626264 : Nat := 118140960795 + 4626264 * 2 ^ 59
def prefixEnd_4626264 : Nat := 4983230072969 + 3 ^ 40 * 4626264 * 2
def baseEnd_4626264 : Nat := 2375497066591792954524205

theorem tailTrace_4626264 : CollatzResearch.WordTrace tailWord_4626264 prefixEnd_4626264 2375497066591792954524205 := by
  unfold tailWord_4626264
  simp only [CollatzResearch.WordTrace]
  refine ⟨84366855055921552916498923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112489140074562070555331897 84366855055921552916498923)
  ·
    refine ⟨126550282583882329374748385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84366855055921552916498923 126550282583882329374748385)
    ·
      refine ⟨94912711937911747031061289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126550282583882329374748385 94912711937911747031061289)
      ·
        refine ⟨71184533953433810273295967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94912711937911747031061289 71184533953433810273295967)
        ·
          refine ⟨106776800930150715409943951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71184533953433810273295967 106776800930150715409943951)
          ·
            refine ⟨160165201395226073114915927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106776800930150715409943951 160165201395226073114915927)
            ·
              refine ⟨240247802092839109672373891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160165201395226073114915927 240247802092839109672373891)
              ·
                refine ⟨360371703139258664508560837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240247802092839109672373891 360371703139258664508560837)
                ·
                  refine ⟨67569694338610999595355157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 360371703139258664508560837 67569694338610999595355157)
                  ·
                    refine ⟨3167329422122390606032273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67569694338610999595355157 3167329422122390606032273)
                    ·
                      refine ⟨2375497066591792954524205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3167329422122390606032273 2375497066591792954524205)
                      ·
                        rfl

theorem cell23_4626264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_4626264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626264 prefixEnd_4626264 := by exact prefixLift 4626264
  have htrace : WordTrace (prefixWord ++ tailWord_4626264) baseStart_4626264 baseEnd_4626264 := by
    simpa [prefixWord, tailWord_4626264, baseEnd_4626264] using wordTrace_append hprefix tailTrace_4626264
  have hstable : (prefixWord ++ tailWord_4626264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626264).length < 2 ^ (prefixWord ++ tailWord_4626264).sum := by decide
  have hdescent : baseEnd_4626264 < baseStart_4626264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626318 : List Nat := [4, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5]
def baseStart_4626318 : Nat := 118140960795 + 4626318 * 2 ^ 59
def prefixEnd_4626318 : Nat := 4983230072969 + 3 ^ 40 * 4626318 * 2
def baseEnd_4626318 : Nat := 2375524794547135743248957

theorem tailTrace_4626318 : CollatzResearch.WordTrace tailWord_4626318 prefixEnd_4626318 2375524794547135743248957 := by
  unfold tailWord_4626318
  simp only [CollatzResearch.WordTrace]
  refine ⟨21091959956705934131932951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112490453102431648703642405 21091959956705934131932951)
  ·
    refine ⟨31637939935058901197899427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21091959956705934131932951 31637939935058901197899427)
    ·
      refine ⟨47456909902588351796849141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31637939935058901197899427 47456909902588351796849141)
      ·
        refine ⟨4449085303367657980954607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47456909902588351796849141 4449085303367657980954607)
        ·
          refine ⟨6673627955051486971431911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4449085303367657980954607 6673627955051486971431911)
          ·
            refine ⟨10010441932577230457147867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6673627955051486971431911 10010441932577230457147867)
            ·
              refine ⟨15015662898865845685721801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10010441932577230457147867 15015662898865845685721801)
              ·
                refine ⟨11261747174149384264291351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15015662898865845685721801 11261747174149384264291351)
                ·
                  refine ⟨16892620761224076396437027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11261747174149384264291351 16892620761224076396437027)
                  ·
                    refine ⟨25338931141836114594655541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16892620761224076396437027 25338931141836114594655541)
                    ·
                      refine ⟨2375524794547135743248957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25338931141836114594655541 2375524794547135743248957)
                      ·
                        rfl

theorem cell23_4626318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_4626318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626318 prefixEnd_4626318 := by exact prefixLift 4626318
  have htrace : WordTrace (prefixWord ++ tailWord_4626318) baseStart_4626318 baseEnd_4626318 := by
    simpa [prefixWord, tailWord_4626318, baseEnd_4626318] using wordTrace_append hprefix tailTrace_4626318
  have hstable : (prefixWord ++ tailWord_4626318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626318).length < 2 ^ (prefixWord ++ tailWord_4626318).sum := by decide
  have hdescent : baseEnd_4626318 < baseStart_4626318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626338 : List Nat := [3, 3, 1, 2, 3, 2, 2, 7]
def baseStart_4626338 : Nat := 118140960795 + 4626338 * 2 ^ 59
def prefixEnd_4626338 : Nat := 4983230072969 + 3 ^ 40 * 4626338 * 2
def baseEnd_4626338 : Nat := 87982780154082432036995

theorem tailTrace_4626338 : CollatzResearch.WordTrace tailWord_4626338 prefixEnd_4626338 87982780154082432036995 := by
  unfold tailWord_4626338
  simp only [CollatzResearch.WordTrace]
  refine ⟨42184102278393754117797917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112490939409050010980794445 42184102278393754117797917)
  ·
    refine ⟨15819038354397657794174219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42184102278393754117797917 15819038354397657794174219)
    ·
      refine ⟨23728557531596486691261329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15819038354397657794174219 23728557531596486691261329)
      ·
        refine ⟨17796418148697365018445997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23728557531596486691261329 17796418148697365018445997)
        ·
          refine ⟨6673656805761511881917249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17796418148697365018445997 6673656805761511881917249)
          ·
            refine ⟨5005242604321133911437937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6673656805761511881917249 5005242604321133911437937)
            ·
              refine ⟨3753931953240850433578453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5005242604321133911437937 3753931953240850433578453)
              ·
                refine ⟨87982780154082432036995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3753931953240850433578453 87982780154082432036995)
                ·
                  rfl

theorem cell23_4626338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 7].length) (baseStart_4626338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626338 prefixEnd_4626338 := by exact prefixLift 4626338
  have htrace : WordTrace (prefixWord ++ tailWord_4626338) baseStart_4626338 baseEnd_4626338 := by
    simpa [prefixWord, tailWord_4626338, baseEnd_4626338] using wordTrace_append hprefix tailTrace_4626338
  have hstable : (prefixWord ++ tailWord_4626338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626338).length < 2 ^ (prefixWord ++ tailWord_4626338).sum := by decide
  have hdescent : baseEnd_4626338 < baseStart_4626338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626341 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 3, 3, 2]
def baseStart_4626341 : Nat := 118140960795 + 4626341 * 2 ^ 59
def prefixEnd_4626341 : Nat := 4983230072969 + 3 ^ 40 * 4626341 * 2
def baseEnd_4626341 : Nat := 2375536604602189153261351

theorem tailTrace_4626341 : CollatzResearch.WordTrace tailWord_4626341 prefixEnd_4626341 2375536604602189153261351 := by
  unfold tailWord_4626341
  simp only [CollatzResearch.WordTrace]
  refine ⟨168736518532564147983550877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112491012355042765322367251 168736518532564147983550877)
  ·
    refine ⟨63276194449711555493831579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168736518532564147983550877 63276194449711555493831579)
    ·
      refine ⟨94914291674567333240747369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63276194449711555493831579 94914291674567333240747369)
      ·
        refine ⟨71185718755925499930560527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94914291674567333240747369 71185718755925499930560527)
        ·
          refine ⟨106778578133888249895840791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71185718755925499930560527 106778578133888249895840791)
          ·
            refine ⟨160167867200832374843761187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106778578133888249895840791 160167867200832374843761187)
            ·
              refine ⟨240251800801248562265641781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160167867200832374843761187 240251800801248562265641781)
              ·
                refine ⟨22523606325117052712403917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 240251800801248562265641781 22523606325117052712403917)
                ·
                  refine ⟨8446352371918894767151469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22523606325117052712403917 8446352371918894767151469)
                  ·
                    refine ⟨3167382139469585537681801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8446352371918894767151469 3167382139469585537681801)
                    ·
                      refine ⟨2375536604602189153261351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3167382139469585537681801 2375536604602189153261351)
                      ·
                        rfl

theorem cell23_4626341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_4626341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626341 prefixEnd_4626341 := by exact prefixLift 4626341
  have htrace : WordTrace (prefixWord ++ tailWord_4626341) baseStart_4626341 baseEnd_4626341 := by
    simpa [prefixWord, tailWord_4626341, baseEnd_4626341] using wordTrace_append hprefix tailTrace_4626341
  have hstable : (prefixWord ++ tailWord_4626341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626341).length < 2 ^ (prefixWord ++ tailWord_4626341).sum := by decide
  have hdescent : baseEnd_4626341 < baseStart_4626341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626384 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 4]
def baseStart_4626384 : Nat := 118140960795 + 4626384 * 2 ^ 59
def prefixEnd_4626384 : Nat := 4983230072969 + 3 ^ 40 * 4626384 * 2
def baseEnd_4626384 : Nat := 2375558684270332485023653

theorem tailTrace_4626384 : CollatzResearch.WordTrace tailWord_4626384 prefixEnd_4626384 2375558684270332485023653 := by
  unfold tailWord_4626384
  simp only [CollatzResearch.WordTrace]
  refine ⟨84369043435704183163683103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112492057914272244218244137 84369043435704183163683103)
  ·
    refine ⟨126553565153556274745524655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84369043435704183163683103 126553565153556274745524655)
    ·
      refine ⟨189830347730334412118286983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126553565153556274745524655 189830347730334412118286983)
      ·
        refine ⟨284745521595501618177430475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189830347730334412118286983 284745521595501618177430475)
        ·
          refine ⟨427118282393252427266145713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284745521595501618177430475 427118282393252427266145713)
          ·
            refine ⟨320338711794939320449609285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 427118282393252427266145713 320338711794939320449609285)
            ·
              refine ⟨60063508461551122584301741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 320338711794939320449609285 60063508461551122584301741)
              ·
                refine ⟨22523815673081670969113153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60063508461551122584301741 22523815673081670969113153)
                ·
                  refine ⟨16892861754811253226834865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22523815673081670969113153 16892861754811253226834865)
                  ·
                    refine ⟨12669646316108439920126149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16892861754811253226834865 12669646316108439920126149)
                    ·
                      refine ⟨2375558684270332485023653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12669646316108439920126149 2375558684270332485023653)
                      ·
                        rfl

theorem cell23_4626384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 4].length) (baseStart_4626384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626384 prefixEnd_4626384 := by exact prefixLift 4626384
  have htrace : WordTrace (prefixWord ++ tailWord_4626384) baseStart_4626384 baseEnd_4626384 := by
    simpa [prefixWord, tailWord_4626384, baseEnd_4626384] using wordTrace_append hprefix tailTrace_4626384
  have hstable : (prefixWord ++ tailWord_4626384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626384).length < 2 ^ (prefixWord ++ tailWord_4626384).sum := by decide
  have hdescent : baseEnd_4626384 < baseStart_4626384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626388 : List Nat := [2, 4, 1, 2, 1, 1, 2, 3, 1, 4, 2]
def baseStart_4626388 : Nat := 118140960795 + 4626388 * 2 ^ 59
def prefixEnd_4626388 : Nat := 4983230072969 + 3 ^ 40 * 4626388 * 2
def baseEnd_4626388 : Nat := 2375560738192950469373635

theorem tailTrace_4626388 : CollatzResearch.WordTrace tailWord_4626388 prefixEnd_4626388 2375560738192950469373635 := by
  unfold tailWord_4626388
  simp only [CollatzResearch.WordTrace]
  refine ⟨84369116381696937505255909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112492155175595916673674545 84369116381696937505255909)
  ·
    refine ⟨15819209321568175782235483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84369116381696937505255909 15819209321568175782235483)
    ·
      refine ⟨23728813982352263673353225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15819209321568175782235483 23728813982352263673353225)
      ·
        refine ⟨17796610486764197755014919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23728813982352263673353225 17796610486764197755014919)
        ·
          refine ⟨26694915730146296632522379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17796610486764197755014919 26694915730146296632522379)
          ·
            refine ⟨40042373595219444948783569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26694915730146296632522379 40042373595219444948783569)
            ·
              refine ⟨30031780196414583711587677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40042373595219444948783569 30031780196414583711587677)
              ·
                refine ⟨11261917573655468891845379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30031780196414583711587677 11261917573655468891845379)
                ·
                  refine ⟨16892876360483203337768069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11261917573655468891845379 16892876360483203337768069)
                  ·
                    refine ⟨3167414317590600625831513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16892876360483203337768069 3167414317590600625831513)
                    ·
                      refine ⟨2375560738192950469373635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3167414317590600625831513 2375560738192950469373635)
                      ·
                        rfl

theorem cell23_4626388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_4626388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626388 prefixEnd_4626388 := by exact prefixLift 4626388
  have htrace : WordTrace (prefixWord ++ tailWord_4626388) baseStart_4626388 baseEnd_4626388 := by
    simpa [prefixWord, tailWord_4626388, baseEnd_4626388] using wordTrace_append hprefix tailTrace_4626388
  have hstable : (prefixWord ++ tailWord_4626388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626388).length < 2 ^ (prefixWord ++ tailWord_4626388).sum := by decide
  have hdescent : baseEnd_4626388 < baseStart_4626388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626458 : List Nat := [3, 1, 1, 3, 1, 5, 1, 1, 2, 5]
def baseStart_4626458 : Nat := 118140960795 + 4626458 * 2 ^ 59
def prefixEnd_4626458 : Nat := 4983230072969 + 3 ^ 40 * 4626458 * 2
def baseEnd_4626458 : Nat := 791865560612921731832771

theorem tailTrace_4626458 : CollatzResearch.WordTrace tailWord_4626458 prefixEnd_4626458 791865560612921731832771 := by
  unfold tailWord_4626458
  simp only [CollatzResearch.WordTrace]
  refine ⟨42185196468285069241390007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112493857248760184643706685 42185196468285069241390007)
  ·
    refine ⟨63277794702427603862085011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42185196468285069241390007 63277794702427603862085011)
    ·
      refine ⟨94916692053641405793127517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63277794702427603862085011 94916692053641405793127517)
      ·
        refine ⟨35593759520115527172422819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94916692053641405793127517 35593759520115527172422819)
        ·
          refine ⟨53390639280173290758634229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35593759520115527172422819 53390639280173290758634229)
          ·
            refine ⟨5005372432516246008621959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53390639280173290758634229 5005372432516246008621959)
            ·
              refine ⟨7508058648774369012932939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5005372432516246008621959 7508058648774369012932939)
              ·
                refine ⟨11262087973161553519399409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7508058648774369012932939 11262087973161553519399409)
                ·
                  refine ⟨8446565979871165139549557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11262087973161553519399409 8446565979871165139549557)
                  ·
                    refine ⟨791865560612921731832771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8446565979871165139549557 791865560612921731832771)
                    ·
                      rfl

theorem cell23_4626458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 2, 5].length) (baseStart_4626458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626458 prefixEnd_4626458 := by exact prefixLift 4626458
  have htrace : WordTrace (prefixWord ++ tailWord_4626458) baseStart_4626458 baseEnd_4626458 := by
    simpa [prefixWord, tailWord_4626458, baseEnd_4626458] using wordTrace_append hprefix tailTrace_4626458
  have hstable : (prefixWord ++ tailWord_4626458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626458).length < 2 ^ (prefixWord ++ tailWord_4626458).sum := by decide
  have hdescent : baseEnd_4626458 < baseStart_4626458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626565 : List Nat := [1, 3, 1, 1, 5, 3, 1, 2, 1, 5]
def baseStart_4626565 : Nat := 118140960795 + 4626565 * 2 ^ 59
def prefixEnd_4626565 : Nat := 4983230072969 + 3 ^ 40 * 4626565 * 2
def baseEnd_4626565 : Nat := 791883874756265425620107

theorem tailTrace_4626565 : CollatzResearch.WordTrace tailWord_4626565 prefixEnd_4626565 791883874756265425620107 := by
  unfold tailWord_4626565
  simp only [CollatzResearch.WordTrace]
  refine ⟨168744688483752634239705149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112496458989168422826470099 168744688483752634239705149)
  ·
    refine ⟨63279258181407237839889431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168744688483752634239705149 63279258181407237839889431)
    ·
      refine ⟨94918887272110856759834147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63279258181407237839889431 94918887272110856759834147)
      ·
        refine ⟨142378330908166285139751221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94918887272110856759834147 142378330908166285139751221)
        ·
          refine ⟨13347968522640589231851677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 142378330908166285139751221 13347968522640589231851677)
          ·
            refine ⟨5005488195990220961944379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13347968522640589231851677 5005488195990220961944379)
            ·
              refine ⟨7508232293985331442916569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5005488195990220961944379 7508232293985331442916569)
              ·
                refine ⟨5631174220488998582187427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7508232293985331442916569 5631174220488998582187427)
                ·
                  refine ⟨8446761330733497873281141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5631174220488998582187427 8446761330733497873281141)
                  ·
                    refine ⟨791883874756265425620107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8446761330733497873281141 791883874756265425620107)
                    ·
                      rfl

theorem cell23_4626565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 5].length) (baseStart_4626565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626565 prefixEnd_4626565 := by exact prefixLift 4626565
  have htrace : WordTrace (prefixWord ++ tailWord_4626565) baseStart_4626565 baseEnd_4626565 := by
    simpa [prefixWord, tailWord_4626565, baseEnd_4626565] using wordTrace_append hprefix tailTrace_4626565
  have hstable : (prefixWord ++ tailWord_4626565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626565).length < 2 ^ (prefixWord ++ tailWord_4626565).sum := by decide
  have hdescent : baseEnd_4626565 < baseStart_4626565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626578 : List Nat := [3, 2, 3, 1, 1, 1, 3, 2, 1, 6]
def baseStart_4626578 : Nat := 118140960795 + 4626578 * 2 ^ 59
def prefixEnd_4626578 : Nat := 4983230072969 + 3 ^ 40 * 4626578 * 2
def baseEnd_4626578 : Nat := 791886099839101575332587

theorem tailTrace_4626578 : CollatzResearch.WordTrace tailWord_4626578 prefixEnd_4626578 791886099839101575332587 := by
  unfold tailWord_4626578
  simp only [CollatzResearch.WordTrace]
  refine ⟨42186290658176384364982097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112496775088470358306618925 42186290658176384364982097)
  ·
    refine ⟨31639717993632288273736573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42186290658176384364982097 31639717993632288273736573)
    ·
      refine ⟨11864894247612108102651215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31639717993632288273736573 11864894247612108102651215)
      ·
        refine ⟨17797341371418162153976823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11864894247612108102651215 17797341371418162153976823)
        ·
          refine ⟨26696012057127243230965235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17797341371418162153976823 26696012057127243230965235)
          ·
            refine ⟨40044018085690864846447853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26696012057127243230965235 40044018085690864846447853)
            ·
              refine ⟨15016506782134074317417945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40044018085690864846447853 15016506782134074317417945)
              ·
                refine ⟨11262380086600555738063459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15016506782134074317417945 11262380086600555738063459)
                ·
                  refine ⟨16893570129900833607095189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11262380086600555738063459 16893570129900833607095189)
                  ·
                    refine ⟨791886099839101575332587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16893570129900833607095189 791886099839101575332587)
                    ·
                      rfl

theorem cell23_4626578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_4626578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626578 prefixEnd_4626578 := by exact prefixLift 4626578
  have htrace : WordTrace (prefixWord ++ tailWord_4626578) baseStart_4626578 baseEnd_4626578 := by
    simpa [prefixWord, tailWord_4626578, baseEnd_4626578] using wordTrace_append hprefix tailTrace_4626578
  have hstable : (prefixWord ++ tailWord_4626578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626578).length < 2 ^ (prefixWord ++ tailWord_4626578).sum := by decide
  have hdescent : baseEnd_4626578 < baseStart_4626578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626591 : List Nat := [1, 1, 2, 6, 1, 12]
def baseStart_4626591 : Nat := 118140960795 + 4626591 * 2 ^ 59
def prefixEnd_4626591 : Nat := 4983230072969 + 3 ^ 40 * 4626591 * 2
def baseEnd_4626591 : Nat := 9776399073110342284507

theorem tailTrace_4626591 : CollatzResearch.WordTrace tailWord_4626591 prefixEnd_4626591 9776399073110342284507 := by
  unfold tailWord_4626591
  simp only [CollatzResearch.WordTrace]
  refine ⟨168745636781658440680151627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112497091187772293786767751 168745636781658440680151627)
  ·
    refine ⟨253118455172487661020227441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168745636781658440680151627 253118455172487661020227441)
    ·
      refine ⟨189838841379365745765170581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253118455172487661020227441 189838841379365745765170581)
      ·
        refine ⟨8898695689657769332742371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 189838841379365745765170581 8898695689657769332742371)
        ·
          refine ⟨13348043534486653999113557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8898695689657769332742371 13348043534486653999113557)
          ·
            refine ⟨9776399073110342284507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 13348043534486653999113557 9776399073110342284507)
            ·
              rfl

theorem cell23_4626591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 12].length) (baseStart_4626591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626591 prefixEnd_4626591 := by exact prefixLift 4626591
  have htrace : WordTrace (prefixWord ++ tailWord_4626591) baseStart_4626591 baseEnd_4626591 := by
    simpa [prefixWord, tailWord_4626591, baseEnd_4626591] using wordTrace_append hprefix tailTrace_4626591
  have hstable : (prefixWord ++ tailWord_4626591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626591).length < 2 ^ (prefixWord ++ tailWord_4626591).sum := by decide
  have hdescent : baseEnd_4626591 < baseStart_4626591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626596 : List Nat := [2, 3, 1, 2, 4, 2, 2, 2, 1, 1, 3]
def baseStart_4626596 : Nat := 118140960795 + 4626596 * 2 ^ 59
def prefixEnd_4626596 : Nat := 4983230072969 + 3 ^ 40 * 4626596 * 2
def baseEnd_4626596 : Nat := 2375667542169085655572679

theorem tailTrace_4626596 : CollatzResearch.WordTrace tailWord_4626596 prefixEnd_4626596 2375667542169085655572679 := by
  unfold tailWord_4626596
  simp only [CollatzResearch.WordTrace]
  refine ⟨84372909573320163267041821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112497212764426884356055761 84372909573320163267041821)
  ·
    refine ⟨31639841089995061225140683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84372909573320163267041821 31639841089995061225140683)
    ·
      refine ⟨47459761634992591837711025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31639841089995061225140683 47459761634992591837711025)
      ·
        refine ⟨35594821226244443878283269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47459761634992591837711025 35594821226244443878283269)
        ·
          refine ⟨6674028979920833227178113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35594821226244443878283269 6674028979920833227178113)
          ·
            refine ⟨5005521734940624920383585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6674028979920833227178113 5005521734940624920383585)
            ·
              refine ⟨3754141301205468690287689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5005521734940624920383585 3754141301205468690287689)
              ·
                refine ⟨2815605975904101517715767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3754141301205468690287689 2815605975904101517715767)
                ·
                  refine ⟨4223408963856152276573651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2815605975904101517715767 4223408963856152276573651)
                  ·
                    refine ⟨6335113445784228414860477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4223408963856152276573651 6335113445784228414860477)
                    ·
                      refine ⟨2375667542169085655572679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6335113445784228414860477 2375667542169085655572679)
                      ·
                        rfl

theorem cell23_4626596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_4626596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626596 prefixEnd_4626596 := by exact prefixLift 4626596
  have htrace : WordTrace (prefixWord ++ tailWord_4626596) baseStart_4626596 baseEnd_4626596 := by
    simpa [prefixWord, tailWord_4626596, baseEnd_4626596] using wordTrace_append hprefix tailTrace_4626596
  have hstable : (prefixWord ++ tailWord_4626596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626596).length < 2 ^ (prefixWord ++ tailWord_4626596).sum := by decide
  have hdescent : baseEnd_4626596 < baseStart_4626596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626601 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 1, 9, 3]
def baseStart_4626601 : Nat := 118140960795 + 4626601 * 2 ^ 59
def prefixEnd_4626601 : Nat := 4983230072969 + 3 ^ 40 * 4626601 * 2
def baseEnd_4626601 : Nat := 2375670109572358136010155

theorem tailTrace_4626601 : CollatzResearch.WordTrace tailWord_4626601 prefixEnd_4626601 2375670109572358136010155 := by
  unfold tailWord_4626601
  simp only [CollatzResearch.WordTrace]
  refine ⟨168746001511622212388015657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112497334341081474925343771 168746001511622212388015657)
  ·
    refine ⟨126559501133716659291011743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168746001511622212388015657 126559501133716659291011743)
    ·
      refine ⟨189839251700574988936517615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126559501133716659291011743 189839251700574988936517615)
      ·
        refine ⟨284758877550862483404776423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189839251700574988936517615 284758877550862483404776423)
        ·
          refine ⟨427138316326293725107164635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284758877550862483404776423 427138316326293725107164635)
          ·
            refine ⟨640707474489440587660746953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427138316326293725107164635 640707474489440587660746953)
            ·
              refine ⟨480530605867080440745560215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 640707474489440587660746953 480530605867080440745560215)
              ·
                refine ⟨720795908800620661118340323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 480530605867080440745560215 720795908800620661118340323)
                ·
                  refine ⟨1081193863200930991677510485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 720795908800620661118340323 1081193863200930991677510485)
                  ·
                    refine ⟨6335120292192955029360413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1081193863200930991677510485 6335120292192955029360413)
                    ·
                      refine ⟨2375670109572358136010155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6335120292192955029360413 2375670109572358136010155)
                      ·
                        rfl

theorem cell23_4626601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 9, 3].length) (baseStart_4626601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626601 prefixEnd_4626601 := by exact prefixLift 4626601
  have htrace : WordTrace (prefixWord ++ tailWord_4626601) baseStart_4626601 baseEnd_4626601 := by
    simpa [prefixWord, tailWord_4626601, baseEnd_4626601] using wordTrace_append hprefix tailTrace_4626601
  have hstable : (prefixWord ++ tailWord_4626601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626601).length < 2 ^ (prefixWord ++ tailWord_4626601).sum := by decide
  have hdescent : baseEnd_4626601 < baseStart_4626601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626605 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_4626605 : Nat := 118140960795 + 4626605 * 2 ^ 59
def prefixEnd_4626605 : Nat := 4983230072969 + 3 ^ 40 * 4626605 * 2
def baseEnd_4626605 : Nat := 2375672163494976120360137

theorem tailTrace_4626605 : CollatzResearch.WordTrace tailWord_4626605 prefixEnd_4626605 2375672163494976120360137 := by
  unfold tailWord_4626605
  simp only [CollatzResearch.WordTrace]
  refine ⟨168746147403607721071161269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112497431602405147380774179 168746147403607721071161269)
  ·
    refine ⟨15819951319088223850421369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 168746147403607721071161269 15819951319088223850421369)
    ·
      refine ⟨11864963489316167887816027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15819951319088223850421369 11864963489316167887816027)
      ·
        refine ⟨17797445233974251831724041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11864963489316167887816027 17797445233974251831724041)
        ·
          refine ⟨13348083925480688873793031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17797445233974251831724041 13348083925480688873793031)
          ·
            refine ⟨20022125888221033310689547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13348083925480688873793031 20022125888221033310689547)
            ·
              refine ⟨30033188832331549966034321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20022125888221033310689547 30033188832331549966034321)
              ·
                refine ⟨22524891624248662474525741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30033188832331549966034321 22524891624248662474525741)
                ·
                  refine ⟨8446834359093248427947153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22524891624248662474525741 8446834359093248427947153)
                  ·
                    refine ⟨6335125769319936320960365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8446834359093248427947153 6335125769319936320960365)
                    ·
                      refine ⟨2375672163494976120360137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6335125769319936320960365 2375672163494976120360137)
                      ·
                        rfl

theorem cell23_4626605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_4626605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626605 prefixEnd_4626605 := by exact prefixLift 4626605
  have htrace : WordTrace (prefixWord ++ tailWord_4626605) baseStart_4626605 baseEnd_4626605 := by
    simpa [prefixWord, tailWord_4626605, baseEnd_4626605] using wordTrace_append hprefix tailTrace_4626605
  have hstable : (prefixWord ++ tailWord_4626605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626605).length < 2 ^ (prefixWord ++ tailWord_4626605).sum := by decide
  have hdescent : baseEnd_4626605 < baseStart_4626605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626618 : List Nat := [3, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3]
def baseStart_4626618 : Nat := 118140960795 + 4626618 * 2 ^ 59
def prefixEnd_4626618 : Nat := 4983230072969 + 3 ^ 40 * 4626618 * 2
def baseEnd_4626618 : Nat := 2375678838743484569497577

theorem tailTrace_4626618 : CollatzResearch.WordTrace tailWord_4626618 prefixEnd_4626618 2375678838743484569497577 := by
  unfold tailWord_4626618
  simp only [CollatzResearch.WordTrace]
  refine ⟨42186655388140156072846127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112497747701707082860923005 42186655388140156072846127)
  ·
    refine ⟨63279983082210234109269191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42186655388140156072846127 63279983082210234109269191)
    ·
      refine ⟨94919974623315351163903787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63279983082210234109269191 94919974623315351163903787)
      ·
        refine ⟨142379961934973026745855681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94919974623315351163903787 142379961934973026745855681)
        ·
          refine ⟨106784971451229770059391761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142379961934973026745855681 106784971451229770059391761)
          ·
            refine ⟨80088728588422327544543821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106784971451229770059391761 80088728588422327544543821)
            ·
              refine ⟨30033273220658372829203933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80088728588422327544543821 30033273220658372829203933)
              ·
                refine ⟨11262477457746889810951475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30033273220658372829203933 11262477457746889810951475)
                ·
                  refine ⟨16893716186620334716427213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11262477457746889810951475 16893716186620334716427213)
                  ·
                    refine ⟨6335143569982625518660205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16893716186620334716427213 6335143569982625518660205)
                    ·
                      refine ⟨2375678838743484569497577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6335143569982625518660205 2375678838743484569497577)
                      ·
                        rfl

theorem cell23_4626618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_4626618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626618 prefixEnd_4626618 := by exact prefixLift 4626618
  have htrace : WordTrace (prefixWord ++ tailWord_4626618) baseStart_4626618 baseEnd_4626618 := by
    simpa [prefixWord, tailWord_4626618, baseEnd_4626618] using wordTrace_append hprefix tailTrace_4626618
  have hstable : (prefixWord ++ tailWord_4626618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626618).length < 2 ^ (prefixWord ++ tailWord_4626618).sum := by decide
  have hdescent : baseEnd_4626618 < baseStart_4626618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626621 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 4, 7]
def baseStart_4626621 : Nat := 118140960795 + 4626621 * 2 ^ 59
def prefixEnd_4626621 : Nat := 4983230072969 + 3 ^ 40 * 4626621 * 2
def baseEnd_4626621 : Nat := 791893459728482685920021

theorem tailTrace_4626621 : CollatzResearch.WordTrace tailWord_4626621 prefixEnd_4626621 791893459728482685920021 := by
  unfold tailWord_4626621
  simp only [CollatzResearch.WordTrace]
  refine ⟨168746730971549755803743717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112497820647699837202495811 168746730971549755803743717)
  ·
    refine ⟨31640012057165579213201947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168746730971549755803743717 31640012057165579213201947)
    ·
      refine ⟨47460018085748368819802921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31640012057165579213201947 47460018085748368819802921)
      ·
        refine ⟨35595013564311276614852191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47460018085748368819802921 35595013564311276614852191)
        ·
          refine ⟨53392520346466914922278287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35595013564311276614852191 53392520346466914922278287)
          ·
            refine ⟨80088780519700372383417431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53392520346466914922278287 80088780519700372383417431)
            ·
              refine ⟨120133170779550558575126147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80088780519700372383417431 120133170779550558575126147)
              ·
                refine ⟨180199756169325837862689221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120133170779550558575126147 180199756169325837862689221)
                ·
                  refine ⟨33787454281748594599254229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 180199756169325837862689221 33787454281748594599254229)
                  ·
                    refine ⟨791893459728482685920021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33787454281748594599254229 791893459728482685920021)
                    ·
                      rfl

theorem cell23_4626621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_4626621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626621 prefixEnd_4626621 := by exact prefixLift 4626621
  have htrace : WordTrace (prefixWord ++ tailWord_4626621) baseStart_4626621 baseEnd_4626621 := by
    simpa [prefixWord, tailWord_4626621, baseEnd_4626621] using wordTrace_append hprefix tailTrace_4626621
  have hstable : (prefixWord ++ tailWord_4626621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626621).length < 2 ^ (prefixWord ++ tailWord_4626621).sum := by decide
  have hdescent : baseEnd_4626621 < baseStart_4626621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626636 : List Nat := [2, 2, 1, 6, 2, 1, 2, 1, 1, 1, 4]
def baseStart_4626636 : Nat := 118140960795 + 4626636 * 2 ^ 59
def prefixEnd_4626636 : Nat := 4983230072969 + 3 ^ 40 * 4626636 * 2
def baseEnd_4626636 : Nat := 2375688081395265499072495

theorem tailTrace_4626636 : CollatzResearch.WordTrace tailWord_4626636 prefixEnd_4626636 2375688081395265499072495 := by
  unfold tailWord_4626636
  simp only [CollatzResearch.WordTrace]
  refine ⟨84373639033247706682769881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112498185377663608910359841 84373639033247706682769881)
  ·
    refine ⟨63280229274935780012077411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84373639033247706682769881 63280229274935780012077411)
    ·
      refine ⟨94920343912403670018116117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63280229274935780012077411 94920343912403670018116117)
      ·
        refine ⟨4449391120893922032099193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 94920343912403670018116117 4449391120893922032099193)
        ·
          refine ⟨3337043340670441524074395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4449391120893922032099193 3337043340670441524074395)
          ·
            refine ⟨5005565011005662286111593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3337043340670441524074395 5005565011005662286111593)
            ·
              refine ⟨3754173758254246714583695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5005565011005662286111593 3754173758254246714583695)
              ·
                refine ⟨5631260637381370071875543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3754173758254246714583695 5631260637381370071875543)
                ·
                  refine ⟨8446890956072055107813315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5631260637381370071875543 8446890956072055107813315)
                  ·
                    refine ⟨12670336434108082661719973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8446890956072055107813315 12670336434108082661719973)
                    ·
                      refine ⟨2375688081395265499072495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12670336434108082661719973 2375688081395265499072495)
                      ·
                        rfl

theorem cell23_4626636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_4626636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626636 prefixEnd_4626636 := by exact prefixLift 4626636
  have htrace : WordTrace (prefixWord ++ tailWord_4626636) baseStart_4626636 baseEnd_4626636 := by
    simpa [prefixWord, tailWord_4626636, baseEnd_4626636] using wordTrace_append hprefix tailTrace_4626636
  have hstable : (prefixWord ++ tailWord_4626636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626636).length < 2 ^ (prefixWord ++ tailWord_4626636).sum := by decide
  have hdescent : baseEnd_4626636 < baseStart_4626636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626651 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 2, 6]
def baseStart_4626651 : Nat := 118140960795 + 4626651 * 2 ^ 59
def prefixEnd_4626651 : Nat := 4983230072969 + 3 ^ 40 * 4626651 * 2
def baseEnd_4626651 : Nat := 791898594535027646794975

theorem tailTrace_4626651 : CollatzResearch.WordTrace tailWord_4626651 prefixEnd_4626651 791898594535027646794975 := by
  unfold tailWord_4626651
  simp only [CollatzResearch.WordTrace]
  refine ⟨168747825161441070927335807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112498550107627380618223871 168747825161441070927335807)
  ·
    refine ⟨253121737742161606391003711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168747825161441070927335807 253121737742161606391003711)
    ·
      refine ⟨379682606613242409586505567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253121737742161606391003711 379682606613242409586505567)
      ·
        refine ⟨569523909919863614379758351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379682606613242409586505567 569523909919863614379758351)
        ·
          refine ⟨854285864879795421569637527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569523909919863614379758351 854285864879795421569637527)
          ·
            refine ⟨1281428797319693132354456291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854285864879795421569637527 1281428797319693132354456291)
            ·
              refine ⟨1922143195979539698531684437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281428797319693132354456291 1922143195979539698531684437)
              ·
                refine ⟨22525115577885230842168177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1922143195979539698531684437 22525115577885230842168177)
                ·
                  refine ⟨16893836683413923131626133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22525115577885230842168177 16893836683413923131626133)
                  ·
                    refine ⟨791898594535027646794975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16893836683413923131626133 791898594535027646794975)
                    ·
                      rfl

theorem cell23_4626651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 6].length) (baseStart_4626651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626651 prefixEnd_4626651 := by exact prefixLift 4626651
  have htrace : WordTrace (prefixWord ++ tailWord_4626651) baseStart_4626651 baseEnd_4626651 := by
    simpa [prefixWord, tailWord_4626651, baseEnd_4626651] using wordTrace_append hprefix tailTrace_4626651
  have hstable : (prefixWord ++ tailWord_4626651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626651).length < 2 ^ (prefixWord ++ tailWord_4626651).sum := by decide
  have hdescent : baseEnd_4626651 < baseStart_4626651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626669 : List Nat := [1, 5, 1, 2, 4, 1, 1, 1, 1, 3, 3]
def baseStart_4626669 : Nat := 118140960795 + 4626669 * 2 ^ 59
def prefixEnd_4626669 : Nat := 4983230072969 + 3 ^ 40 * 4626669 * 2
def baseEnd_4626669 : Nat := 2375705026256863869959843

theorem tailTrace_4626669 : CollatzResearch.WordTrace tailWord_4626669 prefixEnd_4626669 2375705026256863869959843 := by
  unfold tailWord_4626669
  simp only [CollatzResearch.WordTrace]
  refine ⟨168748481675375860001491061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112498987783583906667660707 168748481675375860001491061)
  ·
    refine ⟨15820170157066486875139787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 168748481675375860001491061 15820170157066486875139787)
    ·
      refine ⟨23730255235599730312709681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15820170157066486875139787 23730255235599730312709681)
      ·
        refine ⟨17797691426699797734532261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23730255235599730312709681 17797691426699797734532261)
        ·
          refine ⟨3337067142506212075224799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17797691426699797734532261 3337067142506212075224799)
          ·
            refine ⟨5005600713759318112837199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3337067142506212075224799 5005600713759318112837199)
            ·
              refine ⟨7508401070638977169255799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5005600713759318112837199 7508401070638977169255799)
              ·
                refine ⟨11262601605958465753883699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7508401070638977169255799 11262601605958465753883699)
                ·
                  refine ⟨16893902408937698630825549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11262601605958465753883699 16893902408937698630825549)
                  ·
                    refine ⟨6335213403351636986559581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16893902408937698630825549 6335213403351636986559581)
                    ·
                      refine ⟨2375705026256863869959843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6335213403351636986559581 2375705026256863869959843)
                      ·
                        rfl

theorem cell23_4626669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_4626669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626669 prefixEnd_4626669 := by exact prefixLift 4626669
  have htrace : WordTrace (prefixWord ++ tailWord_4626669) baseStart_4626669 baseEnd_4626669 := by
    simpa [prefixWord, tailWord_4626669, baseEnd_4626669] using wordTrace_append hprefix tailTrace_4626669
  have hstable : (prefixWord ++ tailWord_4626669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626669).length < 2 ^ (prefixWord ++ tailWord_4626669).sum := by decide
  have hdescent : baseEnd_4626669 < baseStart_4626669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626681 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 9]
def baseStart_4626681 : Nat := 118140960795 + 4626681 * 2 ^ 59
def prefixEnd_4626681 : Nat := 4983230072969 + 3 ^ 40 * 4626681 * 2
def baseEnd_4626681 : Nat := 263967909780524202556643

theorem tailTrace_4626681 : CollatzResearch.WordTrace tailWord_4626681 prefixEnd_4626681 263967909780524202556643 := by
  unfold tailWord_4626681
  simp only [CollatzResearch.WordTrace]
  refine ⟨168748919351332386050927897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112499279567554924033951931 168748919351332386050927897)
  ·
    refine ⟨126561689513499289538195923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168748919351332386050927897 126561689513499289538195923)
    ·
      refine ⟨189842534270248934307293885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126561689513499289538195923 189842534270248934307293885)
      ·
        refine ⟨71190950351343350365235207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189842534270248934307293885 71190950351343350365235207)
        ·
          refine ⟨106786425527015025547852811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71190950351343350365235207 106786425527015025547852811)
          ·
            refine ⟨160179638290522538321779217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106786425527015025547852811 160179638290522538321779217)
            ·
              refine ⟨120134728717891903741334413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160179638290522538321779217 120134728717891903741334413)
              ·
                refine ⟨45050523269209463903000405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120134728717891903741334413 45050523269209463903000405)
                ·
                  refine ⟨263967909780524202556643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45050523269209463903000405 263967909780524202556643)
                  ·
                    rfl

theorem cell23_4626681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 9].length) (baseStart_4626681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626681 prefixEnd_4626681 := by exact prefixLift 4626681
  have htrace : WordTrace (prefixWord ++ tailWord_4626681) baseStart_4626681 baseEnd_4626681 := by
    simpa [prefixWord, tailWord_4626681, baseEnd_4626681] using wordTrace_append hprefix tailTrace_4626681
  have hstable : (prefixWord ++ tailWord_4626681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626681).length < 2 ^ (prefixWord ++ tailWord_4626681).sum := by decide
  have hdescent : baseEnd_4626681 < baseStart_4626681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626745 : List Nat := [1, 2, 1, 6, 1, 1, 1, 3, 2, 5]
def baseStart_4626745 : Nat := 118140960795 + 4626745 * 2 ^ 59
def prefixEnd_4626745 : Nat := 4983230072969 + 3 ^ 40 * 4626745 * 2
def baseEnd_4626745 : Nat := 791914683595535190869831

theorem tailTrace_4626745 : CollatzResearch.WordTrace tailWord_4626745 prefixEnd_4626745 791914683595535190869831 := by
  unfold tailWord_4626745
  simp only [CollatzResearch.WordTrace]
  refine ⟨168751253623100524981257689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112500835748733683320838459 168751253623100524981257689)
  ·
    refine ⟨126563440217325393735943267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168751253623100524981257689 126563440217325393735943267)
    ·
      refine ⟨189845160325988090603914901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126563440217325393735943267 189845160325988090603914901)
      ·
        refine ⟨8898991890280691747058511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 189845160325988090603914901 8898991890280691747058511)
        ·
          refine ⟨13348487835421037620587767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8898991890280691747058511 13348487835421037620587767)
          ·
            refine ⟨20022731753131556430881651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13348487835421037620587767 20022731753131556430881651)
            ·
              refine ⟨30034097629697334646322477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20022731753131556430881651 30034097629697334646322477)
              ·
                refine ⟨11262786611136500492370929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30034097629697334646322477 11262786611136500492370929)
                ·
                  refine ⟨8447089958352375369278197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11262786611136500492370929 8447089958352375369278197)
                  ·
                    refine ⟨791914683595535190869831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8447089958352375369278197 791914683595535190869831)
                    ·
                      rfl

theorem cell23_4626745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 5].length) (baseStart_4626745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626745 prefixEnd_4626745 := by exact prefixLift 4626745
  have htrace : WordTrace (prefixWord ++ tailWord_4626745) baseStart_4626745 baseEnd_4626745 := by
    simpa [prefixWord, tailWord_4626745, baseEnd_4626745] using wordTrace_append hprefix tailTrace_4626745
  have hstable : (prefixWord ++ tailWord_4626745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626745).length < 2 ^ (prefixWord ++ tailWord_4626745).sum := by decide
  have hdescent : baseEnd_4626745 < baseStart_4626745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626775 : List Nat := [1, 1, 3, 2, 3, 1, 2, 3, 3, 4]
def baseStart_4626775 : Nat := 118140960795 + 4626775 * 2 ^ 59
def prefixEnd_4626775 : Nat := 4983230072969 + 3 ^ 40 * 4626775 * 2
def baseEnd_4626775 : Nat := 791919818402080151744785

theorem tailTrace_4626775 : CollatzResearch.WordTrace tailWord_4626775 prefixEnd_4626775 791919818402080151744785 := by
  unfold tailWord_4626775
  simp only [CollatzResearch.WordTrace]
  refine ⟨168752347812991840104849779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112501565208661226736566519 168752347812991840104849779)
  ·
    refine ⟨253128521719487760157274669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168752347812991840104849779 253128521719487760157274669)
    ·
      refine ⟨94923195644807910058978001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253128521719487760157274669 94923195644807910058978001)
      ·
        refine ⟨71192396733605932544233501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94923195644807910058978001 71192396733605932544233501)
        ·
          refine ⟨26697148775102224704087563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71192396733605932544233501 26697148775102224704087563)
          ·
            refine ⟨40045723162653337056131345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26697148775102224704087563 40045723162653337056131345)
            ·
              refine ⟨30034292371990002792098509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40045723162653337056131345 30034292371990002792098509)
              ·
                refine ⟨11262859639496251047036941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30034292371990002792098509 11262859639496251047036941)
                ·
                  refine ⟨4223572364811094142638853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11262859639496251047036941 4223572364811094142638853)
                  ·
                    refine ⟨791919818402080151744785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4223572364811094142638853 791919818402080151744785)
                    ·
                      rfl

theorem cell23_4626775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 4].length) (baseStart_4626775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626775 prefixEnd_4626775 := by exact prefixLift 4626775
  have htrace : WordTrace (prefixWord ++ tailWord_4626775) baseStart_4626775 baseEnd_4626775 := by
    simpa [prefixWord, tailWord_4626775, baseEnd_4626775] using wordTrace_append hprefix tailTrace_4626775
  have hstable : (prefixWord ++ tailWord_4626775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626775).length < 2 ^ (prefixWord ++ tailWord_4626775).sum := by decide
  have hdescent : baseEnd_4626775 < baseStart_4626775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626778 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4]
def baseStart_4626778 : Nat := 118140960795 + 4626778 * 2 ^ 59
def prefixEnd_4626778 : Nat := 4983230072969 + 3 ^ 40 * 4626778 * 2
def baseEnd_4626778 : Nat := 2375760995648203943496841

theorem tailTrace_4626778 : CollatzResearch.WordTrace tailWord_4626778 prefixEnd_4626778 2375760995648203943496841 := by
  unfold tailWord_4626778
  simp only [CollatzResearch.WordTrace]
  refine ⟨42188114307995242904302247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112501638154653981078139325 42188114307995242904302247)
  ·
    refine ⟨63282171461992864356453371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42188114307995242904302247 63282171461992864356453371)
    ·
      refine ⟨94923257192989296534680057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63282171461992864356453371 94923257192989296534680057)
      ·
        refine ⟨71192442894741972401010043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94923257192989296534680057 71192442894741972401010043)
        ·
          refine ⟨106788664342112958601515065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71192442894741972401010043 106788664342112958601515065)
          ·
            refine ⟨80091498256584718951136299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106788664342112958601515065 80091498256584718951136299)
            ·
              refine ⟨120137247384877078426704449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80091498256584718951136299 120137247384877078426704449)
              ·
                refine ⟨90102935538657808820028337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120137247384877078426704449 90102935538657808820028337)
                ·
                  refine ⟨67577201653993356615021253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90102935538657808820028337 67577201653993356615021253)
                  ·
                    refine ⟨12670725310123754365316485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67577201653993356615021253 12670725310123754365316485)
                    ·
                      refine ⟨2375760995648203943496841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12670725310123754365316485 2375760995648203943496841)
                      ·
                        rfl

theorem cell23_4626778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_4626778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626778 prefixEnd_4626778 := by exact prefixLift 4626778
  have htrace : WordTrace (prefixWord ++ tailWord_4626778) baseStart_4626778 baseEnd_4626778 := by
    simpa [prefixWord, tailWord_4626778, baseEnd_4626778] using wordTrace_append hprefix tailTrace_4626778
  have hstable : (prefixWord ++ tailWord_4626778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626778).length < 2 ^ (prefixWord ++ tailWord_4626778).sum := by decide
  have hdescent : baseEnd_4626778 < baseStart_4626778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626792 : List Nat := [2, 1, 4, 2, 2, 2, 1, 2, 3, 4]
def baseStart_4626792 : Nat := 118140960795 + 4626792 * 2 ^ 59
def prefixEnd_4626792 : Nat := 4983230072969 + 3 ^ 40 * 4626792 * 2
def baseEnd_4626792 : Nat := 791922728125788962907259

theorem tailTrace_4626792 : CollatzResearch.WordTrace tailWord_4626792 prefixEnd_4626792 791922728125788962907259 := by
  unfold tailWord_4626792
  simp only [CollatzResearch.WordTrace]
  refine ⟨84376483926965126004109315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112501978569286834672145753 84376483926965126004109315)
  ·
    refine ⟨126564725890447689006163973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84376483926965126004109315 126564725890447689006163973)
    ·
      refine ⟨23730886104458941688655745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126564725890447689006163973 23730886104458941688655745)
      ·
        refine ⟨17798164578344206266491809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23730886104458941688655745 17798164578344206266491809)
        ·
          refine ⟨13348623433758154699868857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17798164578344206266491809 13348623433758154699868857)
          ·
            refine ⟨10011467575318616024901643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13348623433758154699868857 10011467575318616024901643)
            ·
              refine ⟨15017201362977924037352465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10011467575318616024901643 15017201362977924037352465)
              ·
                refine ⟨11262901022233443028014349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15017201362977924037352465 11262901022233443028014349)
                ·
                  refine ⟨4223587883337541135505381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11262901022233443028014349 4223587883337541135505381)
                  ·
                    refine ⟨791922728125788962907259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4223587883337541135505381 791922728125788962907259)
                    ·
                      rfl

theorem cell23_4626792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_4626792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626792 prefixEnd_4626792 := by exact prefixLift 4626792
  have htrace : WordTrace (prefixWord ++ tailWord_4626792) baseStart_4626792 baseEnd_4626792 := by
    simpa [prefixWord, tailWord_4626792, baseEnd_4626792] using wordTrace_append hprefix tailTrace_4626792
  have hstable : (prefixWord ++ tailWord_4626792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626792).length < 2 ^ (prefixWord ++ tailWord_4626792).sum := by decide
  have hdescent : baseEnd_4626792 < baseStart_4626792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626802 : List Nat := [3, 2, 1, 2, 1, 3, 3, 1, 2, 2, 3]
def baseStart_4626802 : Nat := 118140960795 + 4626802 * 2 ^ 59
def prefixEnd_4626802 : Nat := 4983230072969 + 3 ^ 40 * 4626802 * 2
def baseEnd_4626802 : Nat := 2375773319183911849596731

theorem tailTrace_4626802 : CollatzResearch.WordTrace tailWord_4626802 prefixEnd_4626802 2375773319183911849596731 := by
  unfold tailWord_4626802
  simp only [CollatzResearch.WordTrace]
  refine ⟨42188333145973505929020665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112502221722596015810721773 42188333145973505929020665)
  ·
    refine ⟨31641249859480129446765499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42188333145973505929020665 31641249859480129446765499)
    ·
      refine ⟨47461874789220194170148249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31641249859480129446765499 47461874789220194170148249)
      ·
        refine ⟨35596406091915145627611187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47461874789220194170148249 35596406091915145627611187)
        ·
          refine ⟨53394609137872718441416781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35596406091915145627611187 53394609137872718441416781)
          ·
            refine ⟨20022978426702269415531293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53394609137872718441416781 20022978426702269415531293)
            ·
              refine ⟨7508616910013351030824235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20022978426702269415531293 7508616910013351030824235)
              ·
                refine ⟨11262925365020026546236353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7508616910013351030824235 11262925365020026546236353)
                ·
                  refine ⟨8447194023765019909677265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11262925365020026546236353 8447194023765019909677265)
                  ·
                    refine ⟨6335395517823764932257949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8447194023765019909677265 6335395517823764932257949)
                    ·
                      refine ⟨2375773319183911849596731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6335395517823764932257949 2375773319183911849596731)
                      ·
                        rfl

theorem cell23_4626802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_4626802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626802 prefixEnd_4626802 := by exact prefixLift 4626802
  have htrace : WordTrace (prefixWord ++ tailWord_4626802) baseStart_4626802 baseEnd_4626802 := by
    simpa [prefixWord, tailWord_4626802, baseEnd_4626802] using wordTrace_append hprefix tailTrace_4626802
  have hstable : (prefixWord ++ tailWord_4626802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626802).length < 2 ^ (prefixWord ++ tailWord_4626802).sum := by decide
  have hdescent : baseEnd_4626802 < baseStart_4626802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626842 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2]
def baseStart_4626842 : Nat := 118140960795 + 4626842 * 2 ^ 59
def prefixEnd_4626842 : Nat := 4983230072969 + 3 ^ 40 * 4626842 * 2
def baseEnd_4626842 : Nat := 2375793858410091693096547

theorem tailTrace_4626842 : CollatzResearch.WordTrace tailWord_4626842 prefixEnd_4626842 2375793858410091693096547 := by
  unfold tailWord_4626842
  simp only [CollatzResearch.WordTrace]
  refine ⟨42188697875937277636884695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112503194335832740365025853 42188697875937277636884695)
  ·
    refine ⟨63283046813905916455327043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42188697875937277636884695 63283046813905916455327043)
    ·
      refine ⟨94924570220858874682990565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63283046813905916455327043 94924570220858874682990565)
      ·
        refine ⟨17798356916411039003060731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94924570220858874682990565 17798356916411039003060731)
        ·
          refine ⟨26697535374616558504591097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17798356916411039003060731 26697535374616558504591097)
          ·
            refine ⟨20023151530962418878443323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26697535374616558504591097 20023151530962418878443323)
            ·
              refine ⟨30034727296443628317664985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20023151530962418878443323 30034727296443628317664985)
              ·
                refine ⟨22526045472332721238248739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30034727296443628317664985 22526045472332721238248739)
                ·
                  refine ⟨33789068208499081857373109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22526045472332721238248739 33789068208499081857373109)
                  ·
                    refine ⟨3167725144546788924128729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33789068208499081857373109 3167725144546788924128729)
                    ·
                      refine ⟨2375793858410091693096547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3167725144546788924128729 2375793858410091693096547)
                      ·
                        rfl

theorem cell23_4626842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_4626842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626842 prefixEnd_4626842 := by exact prefixLift 4626842
  have htrace : WordTrace (prefixWord ++ tailWord_4626842) baseStart_4626842 baseEnd_4626842 := by
    simpa [prefixWord, tailWord_4626842, baseEnd_4626842] using wordTrace_append hprefix tailTrace_4626842
  have hstable : (prefixWord ++ tailWord_4626842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626842).length < 2 ^ (prefixWord ++ tailWord_4626842).sum := by decide
  have hdescent : baseEnd_4626842 < baseStart_4626842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626889 : List Nat := [1, 2, 1, 1, 2, 1, 7, 1, 3, 2, 2]
def baseStart_4626889 : Nat := 118140960795 + 4626889 * 2 ^ 59
def prefixEnd_4626889 : Nat := 4983230072969 + 3 ^ 40 * 4626889 * 2
def baseEnd_4626889 : Nat := 2375817992000853009208831

theorem tailTrace_4626889 : CollatzResearch.WordTrace tailWord_4626889 prefixEnd_4626889 2375817992000853009208831 := by
  unfold tailWord_4626889
  simp only [CollatzResearch.WordTrace]
  refine ⟨168756505734578837574499721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112504337156385891716333147 168756505734578837574499721)
  ·
    refine ⟨126567379300934128180874791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168756505734578837574499721 126567379300934128180874791)
    ·
      refine ⟨189851068951401192271312187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126567379300934128180874791 189851068951401192271312187)
      ·
        refine ⟨284776603427101788406968281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189851068951401192271312187 284776603427101788406968281)
        ·
          refine ⟨213582452570326341305226211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284776603427101788406968281 213582452570326341305226211)
          ·
            refine ⟨320373678855489511957839317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213582452570326341305226211 320373678855489511957839317)
            ·
              refine ⟨7508758098175535436511859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 320373678855489511957839317 7508758098175535436511859)
              ·
                refine ⟨11263137147263303154767789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7508758098175535436511859 11263137147263303154767789)
                ·
                  refine ⟨4223676430223738683037921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11263137147263303154767789 4223676430223738683037921)
                  ·
                    refine ⟨3167757322667804012278441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4223676430223738683037921 3167757322667804012278441)
                    ·
                      refine ⟨2375817992000853009208831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3167757322667804012278441 2375817992000853009208831)
                      ·
                        rfl

theorem cell23_4626889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 2, 2].length) (baseStart_4626889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626889 prefixEnd_4626889 := by exact prefixLift 4626889
  have htrace : WordTrace (prefixWord ++ tailWord_4626889) baseStart_4626889 baseEnd_4626889 := by
    simpa [prefixWord, tailWord_4626889, baseEnd_4626889] using wordTrace_append hprefix tailTrace_4626889
  have hstable : (prefixWord ++ tailWord_4626889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626889).length < 2 ^ (prefixWord ++ tailWord_4626889).sum := by decide
  have hdescent : baseEnd_4626889 < baseStart_4626889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626902 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_4626902 : Nat := 118140960795 + 4626902 * 2 ^ 59
def prefixEnd_4626902 : Nat := 4983230072969 + 3 ^ 40 * 4626902 * 2
def baseEnd_4626902 : Nat := 2375824667249361458346271

theorem tailTrace_4626902 : CollatzResearch.WordTrace tailWord_4626902 prefixEnd_4626902 2375824667249361458346271 := by
  unfold tailWord_4626902
  simp only [CollatzResearch.WordTrace]
  refine ⟨10547311242720733799670185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112504653255687827196481973 10547311242720733799670185)
  ·
    refine ⟨7910483432040550349752639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10547311242720733799670185 7910483432040550349752639)
    ·
      refine ⟨11865725148060825524628959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7910483432040550349752639 11865725148060825524628959)
      ·
        refine ⟨17798587722091238286943439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11865725148060825524628959 17798587722091238286943439)
        ·
          refine ⟨26697881583136857430415159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17798587722091238286943439 26697881583136857430415159)
          ·
            refine ⟨40046822374705286145622739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26697881583136857430415159 40046822374705286145622739)
            ·
              refine ⟨60070233562057929218434109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40046822374705286145622739 60070233562057929218434109)
              ·
                refine ⟨22526337585771723456912791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60070233562057929218434109 22526337585771723456912791)
                ·
                  refine ⟨33789506378657585185369187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22526337585771723456912791 33789506378657585185369187)
                  ·
                    refine ⟨50684259567986377778053781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33789506378657585185369187 50684259567986377778053781)
                    ·
                      refine ⟨2375824667249361458346271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50684259567986377778053781 2375824667249361458346271)
                      ·
                        rfl

theorem cell23_4626902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_4626902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626902 prefixEnd_4626902 := by exact prefixLift 4626902
  have htrace : WordTrace (prefixWord ++ tailWord_4626902) baseStart_4626902 baseEnd_4626902 := by
    simpa [prefixWord, tailWord_4626902, baseEnd_4626902] using wordTrace_append hprefix tailTrace_4626902
  have hstable : (prefixWord ++ tailWord_4626902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626902).length < 2 ^ (prefixWord ++ tailWord_4626902).sum := by decide
  have hdescent : baseEnd_4626902 < baseStart_4626902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626922 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_4626922 : Nat := 118140960795 + 4626922 * 2 ^ 59
def prefixEnd_4626922 : Nat := 4983230072969 + 3 ^ 40 * 4626922 * 2
def baseEnd_4626922 : Nat := 2375834936862451380096179

theorem tailTrace_4626922 : CollatzResearch.WordTrace tailWord_4626922 prefixEnd_4626922 2375834936862451380096179 := by
  unfold tailWord_4626922
  simp only [CollatzResearch.WordTrace]
  refine ⟨42189427335864821052612755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112505139562306189473634013 42189427335864821052612755)
  ·
    refine ⟨63284141003797231578919133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42189427335864821052612755 63284141003797231578919133)
    ·
      refine ⟨23731552876423961842094675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63284141003797231578919133 23731552876423961842094675)
      ·
        refine ⟨35597329314635942763142013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23731552876423961842094675 35597329314635942763142013)
        ·
          refine ⟨13348998492988478536178255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35597329314635942763142013 13348998492988478536178255)
          ·
            refine ⟨20023497739482717804267383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13348998492988478536178255 20023497739482717804267383)
            ·
              refine ⟨30035246609224076706401075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20023497739482717804267383 30035246609224076706401075)
              ·
                refine ⟨45052869913836115059601613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30035246609224076706401075 45052869913836115059601613)
                ·
                  refine ⟨16894826217688543147350605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45052869913836115059601613 16894826217688543147350605)
                  ·
                    refine ⟨6335559831633203680256477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16894826217688543147350605 6335559831633203680256477)
                    ·
                      refine ⟨2375834936862451380096179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6335559831633203680256477 2375834936862451380096179)
                      ·
                        rfl

theorem cell23_4626922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_4626922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626922 prefixEnd_4626922 := by exact prefixLift 4626922
  have htrace : WordTrace (prefixWord ++ tailWord_4626922) baseStart_4626922 baseEnd_4626922 := by
    simpa [prefixWord, tailWord_4626922, baseEnd_4626922] using wordTrace_append hprefix tailTrace_4626922
  have hstable : (prefixWord ++ tailWord_4626922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626922).length < 2 ^ (prefixWord ++ tailWord_4626922).sum := by decide
  have hdescent : baseEnd_4626922 < baseStart_4626922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626926 : List Nat := [4, 1, 2, 1, 2, 3, 3, 1, 1, 2, 3]
def baseStart_4626926 : Nat := 118140960795 + 4626926 * 2 ^ 59
def prefixEnd_4626926 : Nat := 4983230072969 + 3 ^ 40 * 4626926 * 2
def baseEnd_4626926 : Nat := 2375836990785069364446161

theorem tailTrace_4626926 : CollatzResearch.WordTrace tailWord_4626926 prefixEnd_4626926 2375836990785069364446161 := by
  unfold tailWord_4626926
  simp only [CollatzResearch.WordTrace]
  refine ⟨21094731904430599111699579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112505236823629861929064421 21094731904430599111699579)
  ·
    refine ⟨31642097856645898667549369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21094731904430599111699579 31642097856645898667549369)
    ·
      refine ⟨23731573392484424000662027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31642097856645898667549369 23731573392484424000662027)
      ·
        refine ⟨35597360088726636000993041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23731573392484424000662027 35597360088726636000993041)
        ·
          refine ⟨26698020066544977000744781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35597360088726636000993041 26698020066544977000744781)
          ·
            refine ⟨10011757524954366375279293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26698020066544977000744781 10011757524954366375279293)
            ·
              refine ⟨3754409071857887390729735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10011757524954366375279293 3754409071857887390729735)
              ·
                refine ⟨5631613607786831086094603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3754409071857887390729735 5631613607786831086094603)
                ·
                  refine ⟨8447420411680246629141905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5631613607786831086094603 8447420411680246629141905)
                  ·
                    refine ⟨6335565308760184971856429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8447420411680246629141905 6335565308760184971856429)
                    ·
                      refine ⟨2375836990785069364446161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6335565308760184971856429 2375836990785069364446161)
                      ·
                        rfl

theorem cell23_4626926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_4626926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626926 prefixEnd_4626926 := by exact prefixLift 4626926
  have htrace : WordTrace (prefixWord ++ tailWord_4626926) baseStart_4626926 baseEnd_4626926 := by
    simpa [prefixWord, tailWord_4626926, baseEnd_4626926] using wordTrace_append hprefix tailTrace_4626926
  have hstable : (prefixWord ++ tailWord_4626926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626926).length < 2 ^ (prefixWord ++ tailWord_4626926).sum := by decide
  have hdescent : baseEnd_4626926 < baseStart_4626926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626946 : List Nat := [3, 4, 1, 2, 3, 1, 1, 8]
def baseStart_4626946 : Nat := 118140960795 + 4626946 * 2 ^ 59
def prefixEnd_4626946 : Nat := 4983230072969 + 3 ^ 40 * 4626946 * 2
def baseEnd_4626946 : Nat := 87994342977709603192447

theorem tailTrace_4626946 : CollatzResearch.WordTrace tailWord_4626946 prefixEnd_4626946 87994342977709603192447 := by
  unfold tailWord_4626946
  simp only [CollatzResearch.WordTrace]
  refine ⟨42189646173843084077331173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112505723130248224206216461 42189646173843084077331173)
  ·
    refine ⟨7910558657595578264499595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42189646173843084077331173 7910558657595578264499595)
    ·
      refine ⟨11865837986393367396749393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7910558657595578264499595 11865837986393367396749393)
      ·
        refine ⟨8899378489795025547562045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11865837986393367396749393 8899378489795025547562045)
        ·
          refine ⟨3337266933673134580335767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8899378489795025547562045 3337266933673134580335767)
          ·
            refine ⟨5005900400509701870503651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3337266933673134580335767 5005900400509701870503651)
            ·
              refine ⟨7508850600764552805755477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5005900400509701870503651 7508850600764552805755477)
              ·
                refine ⟨87994342977709603192447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7508850600764552805755477 87994342977709603192447)
                ·
                  rfl

theorem cell23_4626946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 8].length) (baseStart_4626946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626946 prefixEnd_4626946 := by exact prefixLift 4626946
  have htrace : WordTrace (prefixWord ++ tailWord_4626946) baseStart_4626946 baseEnd_4626946 := by
    simpa [prefixWord, tailWord_4626946, baseEnd_4626946] using wordTrace_append hprefix tailTrace_4626946
  have hstable : (prefixWord ++ tailWord_4626946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626946).length < 2 ^ (prefixWord ++ tailWord_4626946).sum := by decide
  have hdescent : baseEnd_4626946 < baseStart_4626946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626955 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 1, 8]
def baseStart_4626955 : Nat := 118140960795 + 4626955 * 2 ^ 59
def prefixEnd_4626955 : Nat := 4983230072969 + 3 ^ 40 * 4626955 * 2
def baseEnd_4626955 : Nat := 791950627241349916994509

theorem tailTrace_4626955 : CollatzResearch.WordTrace tailWord_4626955 prefixEnd_4626955 791950627241349916994509 := by
  unfold tailWord_4626955
  simp only [CollatzResearch.WordTrace]
  refine ⟨168758912952339730846402319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112505941968226487230934879 168758912952339730846402319)
  ·
    refine ⟨253138369428509596269603479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168758912952339730846402319 253138369428509596269603479)
    ·
      refine ⟨379707554142764394404405219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253138369428509596269603479 379707554142764394404405219)
      ·
        refine ⟨569561331214146591606607829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379707554142764394404405219 569561331214146591606607829)
        ·
          refine ⟨13349093700331560740779871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 569561331214146591606607829 13349093700331560740779871)
          ·
            refine ⟨20023640550497341111169807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13349093700331560740779871 20023640550497341111169807)
            ·
              refine ⟨30035460825746011666754711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20023640550497341111169807 30035460825746011666754711)
              ·
                refine ⟨45053191238619017500132067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30035460825746011666754711 45053191238619017500132067)
                ·
                  refine ⟨67579786857928526250198101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45053191238619017500132067 67579786857928526250198101)
                  ·
                    refine ⟨791950627241349916994509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67579786857928526250198101 791950627241349916994509)
                    ·
                      rfl

theorem cell23_4626955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 8].length) (baseStart_4626955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626955 prefixEnd_4626955 := by exact prefixLift 4626955
  have htrace : WordTrace (prefixWord ++ tailWord_4626955) baseStart_4626955 baseEnd_4626955 := by
    simpa [prefixWord, tailWord_4626955, baseEnd_4626955] using wordTrace_append hprefix tailTrace_4626955
  have hstable : (prefixWord ++ tailWord_4626955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626955).length < 2 ^ (prefixWord ++ tailWord_4626955).sum := by decide
  have hdescent : baseEnd_4626955 < baseStart_4626955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626975 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 4]
def baseStart_4626975 : Nat := 118140960795 + 4626975 * 2 ^ 59
def prefixEnd_4626975 : Nat := 4983230072969 + 3 ^ 40 * 4626975 * 2
def baseEnd_4626975 : Nat := 2375862151337139672733435

theorem tailTrace_4626975 : CollatzResearch.WordTrace tailWord_4626975 prefixEnd_4626975 2375862151337139672733435 := by
  unfold tailWord_4626975
  simp only [CollatzResearch.WordTrace]
  refine ⟨168759642412267274262130379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112506428274844849508086919 168759642412267274262130379)
  ·
    refine ⟨253139463618400911393195569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168759642412267274262130379 253139463618400911393195569)
    ·
      refine ⟨189854597713800683544896677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253139463618400911393195569 189854597713800683544896677)
      ·
        refine ⟨35597737071337628164668127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189854597713800683544896677 35597737071337628164668127)
        ·
          refine ⟨53396605607006442247002191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35597737071337628164668127 53396605607006442247002191)
          ·
            refine ⟨80094908410509663370503287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53396605607006442247002191 80094908410509663370503287)
            ·
              refine ⟨120142362615764495055754931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80094908410509663370503287 120142362615764495055754931)
              ·
                refine ⟨180213543923646742583632397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120142362615764495055754931 180213543923646742583632397)
                ·
                  refine ⟨67580078971367528468862149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180213543923646742583632397 67580078971367528468862149)
                  ·
                    refine ⟨12671264807131411587911653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67580078971367528468862149 12671264807131411587911653)
                    ·
                      refine ⟨2375862151337139672733435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12671264807131411587911653 2375862151337139672733435)
                      ·
                        rfl

theorem cell23_4626975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_4626975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626975 prefixEnd_4626975 := by exact prefixLift 4626975
  have htrace : WordTrace (prefixWord ++ tailWord_4626975) baseStart_4626975 baseEnd_4626975 := by
    simpa [prefixWord, tailWord_4626975, baseEnd_4626975] using wordTrace_append hprefix tailTrace_4626975
  have hstable : (prefixWord ++ tailWord_4626975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626975).length < 2 ^ (prefixWord ++ tailWord_4626975).sum := by decide
  have hdescent : baseEnd_4626975 < baseStart_4626975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626979 : List Nat := [1, 1, 1, 4, 4, 1, 2, 2, 1, 4, 2]
def baseStart_4626979 : Nat := 118140960795 + 4626979 * 2 ^ 59
def prefixEnd_4626979 : Nat := 4983230072969 + 3 ^ 40 * 4626979 * 2
def baseEnd_4626979 : Nat := 2375864205259757657083417

theorem tailTrace_4626979 : CollatzResearch.WordTrace tailWord_4626979 prefixEnd_4626979 2375864205259757657083417 := by
  unfold tailWord_4626979
  simp only [CollatzResearch.WordTrace]
  refine ⟨168759788304252782945275991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112506525536168521963517327 168759788304252782945275991)
  ·
    refine ⟨253139682456379174417913987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168759788304252782945275991 253139682456379174417913987)
    ·
      refine ⟨379709523684568761626870981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253139682456379174417913987 379709523684568761626870981)
      ·
        refine ⟨71195535690856642805038309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 379709523684568761626870981 71195535690856642805038309)
        ·
          refine ⟨13349162942035620525944683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71195535690856642805038309 13349162942035620525944683)
          ·
            refine ⟨20023744413053430788917025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13349162942035620525944683 20023744413053430788917025)
            ·
              refine ⟨15017808309790073091687769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20023744413053430788917025 15017808309790073091687769)
              ·
                refine ⟨11263356232342554818765827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15017808309790073091687769 11263356232342554818765827)
                ·
                  refine ⟨16895034348513832228148741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11263356232342554818765827 16895034348513832228148741)
                  ·
                    refine ⟨3167818940346343542777889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16895034348513832228148741 3167818940346343542777889)
                    ·
                      refine ⟨2375864205259757657083417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3167818940346343542777889 2375864205259757657083417)
                      ·
                        rfl

theorem cell23_4626979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_4626979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626979 prefixEnd_4626979 := by exact prefixLift 4626979
  have htrace : WordTrace (prefixWord ++ tailWord_4626979) baseStart_4626979 baseEnd_4626979 := by
    simpa [prefixWord, tailWord_4626979, baseEnd_4626979] using wordTrace_append hprefix tailTrace_4626979
  have hstable : (prefixWord ++ tailWord_4626979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626979).length < 2 ^ (prefixWord ++ tailWord_4626979).sum := by decide
  have hdescent : baseEnd_4626979 < baseStart_4626979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4626990 : List Nat := [4, 1, 3, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_4626990 : Nat := 118140960795 + 4626990 * 2 ^ 59
def prefixEnd_4626990 : Nat := 4983230072969 + 3 ^ 40 * 4626990 * 2
def baseEnd_4626990 : Nat := 2375869853546957114045867

theorem tailTrace_4626990 : CollatzResearch.WordTrace tailWord_4626990 prefixEnd_4626990 2375869853546957114045867 := by
  unfold tailWord_4626990
  simp only [CollatzResearch.WordTrace]
  refine ⟨21095023688401616477990803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112506793004808621215950949 21095023688401616477990803)
  ·
    refine ⟨31642535532602424716986205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21095023688401616477990803 31642535532602424716986205)
    ·
      refine ⟨11865950824725909268869827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31642535532602424716986205 11865950824725909268869827)
      ·
        refine ⟨17798926237088863903304741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11865950824725909268869827 17798926237088863903304741)
        ·
          refine ⟨3337298669454161981869639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17798926237088863903304741 3337298669454161981869639)
          ·
            refine ⟨5005948004181242972804459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3337298669454161981869639 5005948004181242972804459)
            ·
              refine ⟨7508922006271864459206689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5005948004181242972804459 7508922006271864459206689)
              ·
                refine ⟨5631691504703898344405017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7508922006271864459206689 5631691504703898344405017)
                ·
                  refine ⟨4223768628527923758303763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5631691504703898344405017 4223768628527923758303763)
                  ·
                    refine ⟨6335652942791885637455645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4223768628527923758303763 6335652942791885637455645)
                    ·
                      refine ⟨2375869853546957114045867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6335652942791885637455645 2375869853546957114045867)
                      ·
                        rfl

theorem cell23_4626990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_4626990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4626990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4626990 prefixEnd_4626990 := by exact prefixLift 4626990
  have htrace : WordTrace (prefixWord ++ tailWord_4626990) baseStart_4626990 baseEnd_4626990 := by
    simpa [prefixWord, tailWord_4626990, baseEnd_4626990] using wordTrace_append hprefix tailTrace_4626990
  have hstable : (prefixWord ++ tailWord_4626990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4626990).length < 2 ^ (prefixWord ++ tailWord_4626990).sum := by decide
  have hdescent : baseEnd_4626990 < baseStart_4626990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4626990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627002 : List Nat := [3, 1, 1, 1, 3, 4, 2, 1, 7]
def baseStart_4627002 : Nat := 118140960795 + 4627002 * 2 ^ 59
def prefixEnd_4627002 : Nat := 4983230072969 + 3 ^ 40 * 4627002 * 2
def baseEnd_4627002 : Nat := 263986223923867896343979

theorem tailTrace_4627002 : CollatzResearch.WordTrace tailWord_4627002 prefixEnd_4627002 263986223923867896343979 := by
  unfold tailWord_4627002
  simp only [CollatzResearch.WordTrace]
  refine ⟨42190156795792364468340815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112507084788779638582242173 42190156795792364468340815)
  ·
    refine ⟨63285235193688546702511223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42190156795792364468340815 63285235193688546702511223)
    ·
      refine ⟨94927852790532820053766835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63285235193688546702511223 94927852790532820053766835)
      ·
        refine ⟨142391779185799230080650253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94927852790532820053766835 142391779185799230080650253)
        ·
          refine ⟨53396917194674711280243845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142391779185799230080650253 53396917194674711280243845)
          ·
            refine ⟨10011921974001508365045721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53396917194674711280243845 10011921974001508365045721)
            ·
              refine ⟨7508941480501131273784291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10011921974001508365045721 7508941480501131273784291)
              ·
                refine ⟨11263412220751696910676437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7508941480501131273784291 11263412220751696910676437)
                ·
                  refine ⟨263986223923867896343979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11263412220751696910676437 263986223923867896343979)
                  ·
                    rfl

theorem cell23_4627002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 7].length) (baseStart_4627002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627002 prefixEnd_4627002 := by exact prefixLift 4627002
  have htrace : WordTrace (prefixWord ++ tailWord_4627002) baseStart_4627002 baseEnd_4627002 := by
    simpa [prefixWord, tailWord_4627002, baseEnd_4627002] using wordTrace_append hprefix tailTrace_4627002
  have hstable : (prefixWord ++ tailWord_4627002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627002).length < 2 ^ (prefixWord ++ tailWord_4627002).sum := by decide
  have hdescent : baseEnd_4627002 < baseStart_4627002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627013 : List Nat := [1, 3, 1, 1, 1, 6, 3, 1, 2, 2, 2]
def baseStart_4627013 : Nat := 118140960795 + 4627013 * 2 ^ 59
def prefixEnd_4627013 : Nat := 4983230072969 + 3 ^ 40 * 4627013 * 2
def baseEnd_4627013 : Nat := 2375881663602010524058261

theorem tailTrace_4627013 : CollatzResearch.WordTrace tailWord_4627013 prefixEnd_4627013 2375881663602010524058261 := by
  unfold tailWord_4627013
  simp only [CollatzResearch.WordTrace]
  refine ⟨168761028386129606752013693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112507352257419737834675795 168761028386129606752013693)
  ·
    refine ⟨63285385644798602532005135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168761028386129606752013693 63285385644798602532005135)
    ·
      refine ⟨94928078467197903798007703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63285385644798602532005135 94928078467197903798007703)
      ·
        refine ⟨142392117700796855697011555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94928078467197903798007703 142392117700796855697011555)
        ·
          refine ⟨213588176551195283545517333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142392117700796855697011555 213588176551195283545517333)
          ·
            refine ⟨10011945775837278916196125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 213588176551195283545517333 10011945775837278916196125)
            ·
              refine ⟨3754479665938979593573547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10011945775837278916196125 3754479665938979593573547)
              ·
                refine ⟨5631719498908469390360321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3754479665938979593573547 5631719498908469390360321)
                ·
                  refine ⟨4223789624181352042770241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5631719498908469390360321 4223789624181352042770241)
                  ·
                    refine ⟨3167842218136014032077681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4223789624181352042770241 3167842218136014032077681)
                    ·
                      refine ⟨2375881663602010524058261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3167842218136014032077681 2375881663602010524058261)
                      ·
                        rfl

theorem cell23_4627013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 2, 2, 2].length) (baseStart_4627013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627013 prefixEnd_4627013 := by exact prefixLift 4627013
  have htrace : WordTrace (prefixWord ++ tailWord_4627013) baseStart_4627013 baseEnd_4627013 := by
    simpa [prefixWord, tailWord_4627013, baseEnd_4627013] using wordTrace_append hprefix tailTrace_4627013
  have hstable : (prefixWord ++ tailWord_4627013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627013).length < 2 ^ (prefixWord ++ tailWord_4627013).sum := by decide
  have hdescent : baseEnd_4627013 < baseStart_4627013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627052 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 4]
def baseStart_4627052 : Nat := 118140960795 + 4627052 * 2 ^ 59
def prefixEnd_4627052 : Nat := 4983230072969 + 3 ^ 40 * 4627052 * 2
def baseEnd_4627052 : Nat := 2375901689347535871470581

theorem tailTrace_4627052 : CollatzResearch.WordTrace tailWord_4627052 prefixEnd_4627052 2375901689347535871470581 := by
  unfold tailWord_4627052
  simp only [CollatzResearch.WordTrace]
  refine ⟨84381225416494158206341705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112508300555325544275122273 84381225416494158206341705)
  ·
    refine ⟨63285919062370618654756279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84381225416494158206341705 63285919062370618654756279)
    ·
      refine ⟨94928878593555927982134419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63285919062370618654756279 94928878593555927982134419)
      ·
        refine ⟨142393317890333891973201629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94928878593555927982134419 142393317890333891973201629)
        ·
          refine ⟨53397494208875209489950611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142393317890333891973201629 53397494208875209489950611)
          ·
            refine ⟨80096241313312814234925917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53397494208875209489950611 80096241313312814234925917)
            ·
              refine ⟨30036090492492305338097219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80096241313312814234925917 30036090492492305338097219)
              ·
                refine ⟨45054135738738458007145829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30036090492492305338097219 45054135738738458007145829)
                ·
                  refine ⟨8447650451013460876339843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45054135738738458007145829 8447650451013460876339843)
                  ·
                    refine ⟨12671475676520191314509765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8447650451013460876339843 12671475676520191314509765)
                    ·
                      refine ⟨2375901689347535871470581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12671475676520191314509765 2375901689347535871470581)
                      ·
                        rfl

theorem cell23_4627052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_4627052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627052 prefixEnd_4627052 := by exact prefixLift 4627052
  have htrace : WordTrace (prefixWord ++ tailWord_4627052) baseStart_4627052 baseEnd_4627052 := by
    simpa [prefixWord, tailWord_4627052, baseEnd_4627052] using wordTrace_append hprefix tailTrace_4627052
  have hstable : (prefixWord ++ tailWord_4627052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627052).length < 2 ^ (prefixWord ++ tailWord_4627052).sum := by decide
  have hdescent : baseEnd_4627052 < baseStart_4627052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627096 : List Nat := [2, 1, 2, 4, 1, 1, 2, 5, 1, 4]
def baseStart_4627096 : Nat := 118140960795 + 4627096 * 2 ^ 59
def prefixEnd_4627096 : Nat := 4983230072969 + 3 ^ 40 * 4627096 * 2
def baseEnd_4627096 : Nat := 791974760832111233106793

theorem tailTrace_4627096 : CollatzResearch.WordTrace tailWord_4627096 prefixEnd_4627096 791974760832111233106793 := by
  unfold tailWord_4627096
  simp only [CollatzResearch.WordTrace]
  refine ⟨84382027822414455963642571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112509370429885941284856761 84382027822414455963642571)
  ·
    refine ⟨126573041733621683945463857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84382027822414455963642571 126573041733621683945463857)
    ·
      refine ⟨94929781300216262959097893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126573041733621683945463857 94929781300216262959097893)
      ·
        refine ⟨17799333993790549304830855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94929781300216262959097893 17799333993790549304830855)
        ·
          refine ⟨26699000990685823957246283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17799333993790549304830855 26699000990685823957246283)
          ·
            refine ⟨40048501486028735935869425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26699000990685823957246283 40048501486028735935869425)
            ·
              refine ⟨30036376114521551951902069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40048501486028735935869425 30036376114521551951902069)
              ·
                refine ⟨2815910260736395495490819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30036376114521551951902069 2815910260736395495490819)
                ·
                  refine ⟨4223865391104593243236229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2815910260736395495490819 4223865391104593243236229)
                  ·
                    refine ⟨791974760832111233106793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4223865391104593243236229 791974760832111233106793)
                    ·
                      rfl

theorem cell23_4627096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 1, 4].length) (baseStart_4627096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627096 prefixEnd_4627096 := by exact prefixLift 4627096
  have htrace : WordTrace (prefixWord ++ tailWord_4627096) baseStart_4627096 baseEnd_4627096 := by
    simpa [prefixWord, tailWord_4627096, baseEnd_4627096] using wordTrace_append hprefix tailTrace_4627096
  have hstable : (prefixWord ++ tailWord_4627096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627096).length < 2 ^ (prefixWord ++ tailWord_4627096).sum := by decide
  have hdescent : baseEnd_4627096 < baseStart_4627096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627129 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 1, 5, 2]
def baseStart_4627129 : Nat := 118140960795 + 4627129 * 2 ^ 59
def prefixEnd_4627129 : Nat := 4983230072969 + 3 ^ 40 * 4627129 * 2
def baseEnd_4627129 : Nat := 2375941227357932070207727

theorem tailTrace_4627129 : CollatzResearch.WordTrace tailWord_4627129 prefixEnd_4627129 2375941227357932070207727 := by
  unfold tailWord_4627129
  simp only [CollatzResearch.WordTrace]
  refine ⟨168765259253709358563236441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112510172835806239042157627 168765259253709358563236441)
  ·
    refine ⟨126573944440282018922427331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168765259253709358563236441 126573944440282018922427331)
    ·
      refine ⟨189860916660423028383640997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126573944440282018922427331 189860916660423028383640997)
      ·
        refine ⟨35598921873829317821932687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189860916660423028383640997 35598921873829317821932687)
        ·
          refine ⟨53398382810743976732899031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35598921873829317821932687 53398382810743976732899031)
          ·
            refine ⟨80097574216115965099348547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53398382810743976732899031 80097574216115965099348547)
            ·
              refine ⟨120146361324173947649022821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80097574216115965099348547 120146361324173947649022821)
              ·
                refine ⟨22527442748282615184191779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120146361324173947649022821 22527442748282615184191779)
                ·
                  refine ⟨33791164122423922776287669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22527442748282615184191779 33791164122423922776287669)
                  ·
                    refine ⟨3167921636477242760276969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33791164122423922776287669 3167921636477242760276969)
                    ·
                      refine ⟨2375941227357932070207727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3167921636477242760276969 2375941227357932070207727)
                      ·
                        rfl

theorem cell23_4627129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_4627129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627129 prefixEnd_4627129 := by exact prefixLift 4627129
  have htrace : WordTrace (prefixWord ++ tailWord_4627129) baseStart_4627129 baseEnd_4627129 := by
    simpa [prefixWord, tailWord_4627129, baseEnd_4627129] using wordTrace_append hprefix tailTrace_4627129
  have hstable : (prefixWord ++ tailWord_4627129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627129).length < 2 ^ (prefixWord ++ tailWord_4627129).sum := by decide
  have hdescent : baseEnd_4627129 < baseStart_4627129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627132 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_4627132 : Nat := 118140960795 + 4627132 * 2 ^ 59
def prefixEnd_4627132 : Nat := 4983230072969 + 3 ^ 40 * 4627132 * 2
def baseEnd_4627132 : Nat := 2375942767799895558470213

theorem tailTrace_4627132 : CollatzResearch.WordTrace tailWord_4627132 prefixEnd_4627132 2375942767799895558470213 := by
  unfold tailWord_4627132
  simp only [CollatzResearch.WordTrace]
  refine ⟨84382684336349245037797825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112510245781798993383730433 84382684336349245037797825)
  ·
    refine ⟨63287013252261933778348369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84382684336349245037797825 63287013252261933778348369)
    ·
      refine ⟨47465259939196450333761277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63287013252261933778348369 47465259939196450333761277)
      ·
        refine ⟨17799472477198668875160479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47465259939196450333761277 17799472477198668875160479)
        ·
          refine ⟨26699208715798003312740719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17799472477198668875160479 26699208715798003312740719)
          ·
            refine ⟨40048813073697004969111079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26699208715798003312740719 40048813073697004969111079)
            ·
              refine ⟨60073219610545507453666619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40048813073697004969111079 60073219610545507453666619)
              ·
                refine ⟨90109829415818261180499929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60073219610545507453666619 90109829415818261180499929)
                ·
                  refine ⟨67582372061863695885374947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90109829415818261180499929 67582372061863695885374947)
                  ·
                    refine ⟨101373558092795543828062421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67582372061863695885374947 101373558092795543828062421)
                    ·
                      refine ⟨2375942767799895558470213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101373558092795543828062421 2375942767799895558470213)
                      ·
                        rfl

theorem cell23_4627132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_4627132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627132 prefixEnd_4627132 := by exact prefixLift 4627132
  have htrace : WordTrace (prefixWord ++ tailWord_4627132) baseStart_4627132 baseEnd_4627132 := by
    simpa [prefixWord, tailWord_4627132, baseEnd_4627132] using wordTrace_append hprefix tailTrace_4627132
  have hstable : (prefixWord ++ tailWord_4627132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627132).length < 2 ^ (prefixWord ++ tailWord_4627132).sum := by decide
  have hdescent : baseEnd_4627132 < baseStart_4627132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627136 : List Nat := [2, 1, 1, 2, 4, 3, 1, 2, 3, 1, 3]
def baseStart_4627136 : Nat := 118140960795 + 4627136 * 2 ^ 59
def prefixEnd_4627136 : Nat := 4983230072969 + 3 ^ 40 * 4627136 * 2
def baseEnd_4627136 : Nat := 2375944821722513542820195

theorem tailTrace_4627136 : CollatzResearch.WordTrace tailWord_4627136 prefixEnd_4627136 2375944821722513542820195 := by
  unfold tailWord_4627136
  simp only [CollatzResearch.WordTrace]
  refine ⟨84382757282341999379370631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112510343043122665839160841 84382757282341999379370631)
  ·
    refine ⟨126574135923512999069055947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84382757282341999379370631 126574135923512999069055947)
    ·
      refine ⟨189861203885269498603583921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126574135923512999069055947 189861203885269498603583921)
      ·
        refine ⟨142395902913952123952687941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189861203885269498603583921 142395902913952123952687941)
        ·
          refine ⟨26699231796366023241128989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142395902913952123952687941 26699231796366023241128989)
          ·
            refine ⟨10012211923637258715423371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26699231796366023241128989 10012211923637258715423371)
            ·
              refine ⟨15018317885455888073135057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10012211923637258715423371 15018317885455888073135057)
              ·
                refine ⟨11263738414091916054851293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15018317885455888073135057 11263738414091916054851293)
                ·
                  refine ⟨4223901905284468520569235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11263738414091916054851293 4223901905284468520569235)
                  ·
                    refine ⟨6335852857926702780853853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4223901905284468520569235 6335852857926702780853853)
                    ·
                      refine ⟨2375944821722513542820195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6335852857926702780853853 2375944821722513542820195)
                      ·
                        rfl

theorem cell23_4627136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 3, 1, 3].length) (baseStart_4627136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627136 prefixEnd_4627136 := by exact prefixLift 4627136
  have htrace : WordTrace (prefixWord ++ tailWord_4627136) baseStart_4627136 baseEnd_4627136 := by
    simpa [prefixWord, tailWord_4627136, baseEnd_4627136] using wordTrace_append hprefix tailTrace_4627136
  have hstable : (prefixWord ++ tailWord_4627136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627136).length < 2 ^ (prefixWord ++ tailWord_4627136).sum := by decide
  have hdescent : baseEnd_4627136 < baseStart_4627136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627146 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 1, 5, 2]
def baseStart_4627146 : Nat := 118140960795 + 4627146 * 2 ^ 59
def prefixEnd_4627146 : Nat := 4983230072969 + 3 ^ 40 * 4627146 * 2
def baseEnd_4627146 : Nat := 2375949956529058503695149

theorem tailTrace_4627146 : CollatzResearch.WordTrace tailWord_4627146 prefixEnd_4627146 2375949956529058503695149 := by
  unfold tailWord_4627146
  simp only [CollatzResearch.WordTrace]
  refine ⟨42191469823661942616651323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112510586196431846977736861 42191469823661942616651323)
  ·
    refine ⟨63287204735492913924976985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42191469823661942616651323 63287204735492913924976985)
    ·
      refine ⟨47465403551619685443732739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63287204735492913924976985 47465403551619685443732739)
      ·
        refine ⟨71198105327429528165599109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47465403551619685443732739 71198105327429528165599109)
        ·
          refine ⟨13349644748893036531049833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71198105327429528165599109 13349644748893036531049833)
          ·
            refine ⟨10012233561669777398287375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13349644748893036531049833 10012233561669777398287375)
            ·
              refine ⟨15018350342504666097431063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10012233561669777398287375 15018350342504666097431063)
              ·
                refine ⟨22527525513756999146146595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15018350342504666097431063 22527525513756999146146595)
                ·
                  refine ⟨33791288270635498719219893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22527525513756999146146595 33791288270635498719219893)
                  ·
                    refine ⟨3167933275372078004926865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33791288270635498719219893 3167933275372078004926865)
                    ·
                      refine ⟨2375949956529058503695149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3167933275372078004926865 2375949956529058503695149)
                      ·
                        rfl

theorem cell23_4627146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_4627146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627146 prefixEnd_4627146 := by exact prefixLift 4627146
  have htrace : WordTrace (prefixWord ++ tailWord_4627146) baseStart_4627146 baseEnd_4627146 := by
    simpa [prefixWord, tailWord_4627146, baseEnd_4627146] using wordTrace_append hprefix tailTrace_4627146
  have hstable : (prefixWord ++ tailWord_4627146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627146).length < 2 ^ (prefixWord ++ tailWord_4627146).sum := by decide
  have hdescent : baseEnd_4627146 < baseStart_4627146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627153 : List Nat := [1, 2, 2, 1, 2, 3, 4, 3, 1, 1, 3]
def baseStart_4627153 : Nat := 118140960795 + 4627153 * 2 ^ 59
def prefixEnd_4627153 : Nat := 4983230072969 + 3 ^ 40 * 4627153 * 2
def baseEnd_4627153 : Nat := 2375953550893639976307617

theorem tailTrace_4627153 : CollatzResearch.WordTrace tailWord_4627153 prefixEnd_4627153 2375953550893639976307617 := by
  unfold tailWord_4627153
  simp only [CollatzResearch.WordTrace]
  refine ⟨168766134605622410662110113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112510756403748273774740075 168766134605622410662110113)
  ·
    refine ⟨126574600954216807996582585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168766134605622410662110113 126574600954216807996582585)
    ·
      refine ⟨94930950715662605997436939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126574600954216807996582585 94930950715662605997436939)
      ·
        refine ⟨142396426073493908996155409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94930950715662605997436939 142396426073493908996155409)
        ·
          refine ⟨106797319555120431747116557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142396426073493908996155409 106797319555120431747116557)
          ·
            refine ⟨40048994833170161905168709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106797319555120431747116557 40048994833170161905168709)
            ·
              refine ⟨7509186531219405357219133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40048994833170161905168709 7509186531219405357219133)
              ·
                refine ⟨2815944949207277008957175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7509186531219405357219133 2815944949207277008957175)
                ·
                  refine ⟨4223917423810915513435763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2815944949207277008957175 4223917423810915513435763)
                  ·
                    refine ⟨6335876135716373270153645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4223917423810915513435763 6335876135716373270153645)
                    ·
                      refine ⟨2375953550893639976307617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6335876135716373270153645 2375953550893639976307617)
                      ·
                        rfl

theorem cell23_4627153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 1, 1, 3].length) (baseStart_4627153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627153 prefixEnd_4627153 := by exact prefixLift 4627153
  have htrace : WordTrace (prefixWord ++ tailWord_4627153) baseStart_4627153 baseEnd_4627153 := by
    simpa [prefixWord, tailWord_4627153, baseEnd_4627153] using wordTrace_append hprefix tailTrace_4627153
  have hstable : (prefixWord ++ tailWord_4627153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627153).length < 2 ^ (prefixWord ++ tailWord_4627153).sum := by decide
  have hdescent : baseEnd_4627153 < baseStart_4627153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627186 : List Nat := [3, 2, 1, 3, 1, 4, 1, 1, 1, 6]
def baseStart_4627186 : Nat := 118140960795 + 4627186 * 2 ^ 59
def prefixEnd_4627186 : Nat := 4983230072969 + 3 ^ 40 * 4627186 * 2
def baseEnd_4627186 : Nat := 791990165251746115731655

theorem tailTrace_4627186 : CollatzResearch.WordTrace tailWord_4627186 prefixEnd_4627186 791990165251746115731655 := by
  unfold tailWord_4627186
  simp only [CollatzResearch.WordTrace]
  refine ⟨42191834553625714324515353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112511558809668571532040941 42191834553625714324515353)
  ·
    refine ⟨31643875915219285743386515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42191834553625714324515353 31643875915219285743386515)
    ·
      refine ⟨47465813872828928615079773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31643875915219285743386515 47465813872828928615079773)
      ·
        refine ⟨17799680202310848230654915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47465813872828928615079773 17799680202310848230654915)
        ·
          refine ⟨26699520303466272345982373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17799680202310848230654915 26699520303466272345982373)
          ·
            refine ⟨5006160056899926064871695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26699520303466272345982373 5006160056899926064871695)
            ·
              refine ⟨7509240085349889097307543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5006160056899926064871695 7509240085349889097307543)
              ·
                refine ⟨11263860128024833645961315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7509240085349889097307543 11263860128024833645961315)
                ·
                  refine ⟨16895790192037250468941973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11263860128024833645961315 16895790192037250468941973)
                  ·
                    refine ⟨791990165251746115731655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16895790192037250468941973 791990165251746115731655)
                    ·
                      rfl

theorem cell23_4627186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_4627186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627186 prefixEnd_4627186 := by exact prefixLift 4627186
  have htrace : WordTrace (prefixWord ++ tailWord_4627186) baseStart_4627186 baseEnd_4627186 := by
    simpa [prefixWord, tailWord_4627186, baseEnd_4627186] using wordTrace_append hprefix tailTrace_4627186
  have hstable : (prefixWord ++ tailWord_4627186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627186).length < 2 ^ (prefixWord ++ tailWord_4627186).sum := by decide
  have hdescent : baseEnd_4627186 < baseStart_4627186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627196 : List Nat := [2, 2, 2, 1, 3, 2, 1, 4, 1, 2, 3]
def baseStart_4627196 : Nat := 118140960795 + 4627196 * 2 ^ 59
def prefixEnd_4627196 : Nat := 4983230072969 + 3 ^ 40 * 4627196 * 2
def baseEnd_4627196 : Nat := 2375975630561783308069919

theorem tailTrace_4627196 : CollatzResearch.WordTrace tailWord_4627196 prefixEnd_4627196 2375975630561783308069919 := by
  unfold tailWord_4627196
  simp only [CollatzResearch.WordTrace]
  refine ⟨84383851472233314502962721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112511801962977752670616961 84383851472233314502962721)
  ·
    refine ⟨63287888604174985877222041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84383851472233314502962721 63287888604174985877222041)
    ·
      refine ⟨47465916453131239407916531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63287888604174985877222041 47465916453131239407916531)
      ·
        refine ⟨71198874679696859111874797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47465916453131239407916531 71198874679696859111874797)
        ·
          refine ⟨26699578004886322166953049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71198874679696859111874797 26699578004886322166953049)
          ·
            refine ⟨20024683503664741625214787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26699578004886322166953049 20024683503664741625214787)
            ·
              refine ⟨30037025255497112437822181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20024683503664741625214787 30037025255497112437822181)
              ·
                refine ⟨5631942235405708582091659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30037025255497112437822181 5631942235405708582091659)
                ·
                  refine ⟨8447913353108562873137489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5631942235405708582091659 8447913353108562873137489)
                  ·
                    refine ⟨6335935014831422154853117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8447913353108562873137489 6335935014831422154853117)
                    ·
                      refine ⟨2375975630561783308069919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6335935014831422154853117 2375975630561783308069919)
                      ·
                        rfl

theorem cell23_4627196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_4627196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627196 prefixEnd_4627196 := by exact prefixLift 4627196
  have htrace : WordTrace (prefixWord ++ tailWord_4627196) baseStart_4627196 baseEnd_4627196 := by
    simpa [prefixWord, tailWord_4627196, baseEnd_4627196] using wordTrace_append hprefix tailTrace_4627196
  have hstable : (prefixWord ++ tailWord_4627196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627196).length < 2 ^ (prefixWord ++ tailWord_4627196).sum := by decide
  have hdescent : baseEnd_4627196 < baseStart_4627196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627209 : List Nat := [1, 2, 1, 1, 3, 2, 2, 4, 1, 3, 3]
def baseStart_4627209 : Nat := 118140960795 + 4627209 * 2 ^ 59
def prefixEnd_4627209 : Nat := 4983230072969 + 3 ^ 40 * 4627209 * 2
def baseEnd_4627209 : Nat := 2375982305810291757207359

theorem tailTrace_4627209 : CollatzResearch.WordTrace tailWord_4627209 prefixEnd_4627209 2375982305810291757207359 := by
  unfold tailWord_4627209
  simp only [CollatzResearch.WordTrace]
  refine ⟨168768177093419532226148681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112512118062279688150765787 168768177093419532226148681)
  ·
    refine ⟨126576132820064649169611511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168768177093419532226148681 126576132820064649169611511)
    ·
      refine ⟨189864199230096973754417267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126576132820064649169611511 189864199230096973754417267)
      ·
        refine ⟨284796298845145460631625901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189864199230096973754417267 284796298845145460631625901)
        ·
          refine ⟨106798612066929547736859713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 284796298845145460631625901 106798612066929547736859713)
          ·
            refine ⟨80098959050197160802644785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106798612066929547736859713 80098959050197160802644785)
            ·
              refine ⟨60074219287647870601983589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80098959050197160802644785 60074219287647870601983589)
              ·
                refine ⟨11263916116433975737871923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60074219287647870601983589 11263916116433975737871923)
                ·
                  refine ⟨16895874174650963606807885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11263916116433975737871923 16895874174650963606807885)
                  ·
                    refine ⟨6335952815494111352552957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16895874174650963606807885 6335952815494111352552957)
                    ·
                      refine ⟨2375982305810291757207359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6335952815494111352552957 2375982305810291757207359)
                      ·
                        rfl

theorem cell23_4627209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 3, 3].length) (baseStart_4627209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627209 prefixEnd_4627209 := by exact prefixLift 4627209
  have htrace : WordTrace (prefixWord ++ tailWord_4627209) baseStart_4627209 baseEnd_4627209 := by
    simpa [prefixWord, tailWord_4627209, baseEnd_4627209] using wordTrace_append hprefix tailTrace_4627209
  have hstable : (prefixWord ++ tailWord_4627209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627209).length < 2 ^ (prefixWord ++ tailWord_4627209).sum := by decide
  have hdescent : baseEnd_4627209 < baseStart_4627209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627212 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 1, 9]
def baseStart_4627212 : Nat := 118140960795 + 4627212 * 2 ^ 59
def prefixEnd_4627212 : Nat := 4983230072969 + 3 ^ 40 * 4627212 * 2
def baseEnd_4627212 : Nat := 791994615417418415156615

theorem tailTrace_4627212 : CollatzResearch.WordTrace tailWord_4627212 prefixEnd_4627212 791994615417418415156615 := by
  unfold tailWord_4627212
  simp only [CollatzResearch.WordTrace]
  refine ⟨84384143256204331869253945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112512191008272442492338593 84384143256204331869253945)
  ·
    refine ⟨63288107442153248901940459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84384143256204331869253945 63288107442153248901940459)
    ·
      refine ⟨94932161163229873352910689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63288107442153248901940459 94932161163229873352910689)
      ·
        refine ⟨71199120872422405014683017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94932161163229873352910689 71199120872422405014683017)
        ·
          refine ⟨53399340654316803761012263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71199120872422405014683017 53399340654316803761012263)
          ·
            refine ⟨80099010981475205641518395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53399340654316803761012263 80099010981475205641518395)
            ·
              refine ⟨120148516472212808462277593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80099010981475205641518395 120148516472212808462277593)
              ·
                refine ⟨90111387354159606346708195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120148516472212808462277593 90111387354159606346708195)
                ·
                  refine ⟨135167081031239409520062293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90111387354159606346708195 135167081031239409520062293)
                  ·
                    refine ⟨791994615417418415156615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 135167081031239409520062293 791994615417418415156615)
                    ·
                      rfl

theorem cell23_4627212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_4627212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627212 prefixEnd_4627212 := by exact prefixLift 4627212
  have htrace : WordTrace (prefixWord ++ tailWord_4627212) baseStart_4627212 baseEnd_4627212 := by
    simpa [prefixWord, tailWord_4627212, baseEnd_4627212] using wordTrace_append hprefix tailTrace_4627212
  have hstable : (prefixWord ++ tailWord_4627212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627212).length < 2 ^ (prefixWord ++ tailWord_4627212).sum := by decide
  have hdescent : baseEnd_4627212 < baseStart_4627212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627226 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3]
def baseStart_4627226 : Nat := 118140960795 + 4627226 * 2 ^ 59
def prefixEnd_4627226 : Nat := 4983230072969 + 3 ^ 40 * 4627226 * 2
def baseEnd_4627226 : Nat := 2375991034981418190694781

theorem tailTrace_4627226 : CollatzResearch.WordTrace tailWord_4627226 prefixEnd_4627226 2375991034981418190694781 := by
  unfold tailWord_4627226
  simp only [CollatzResearch.WordTrace]
  refine ⟨42192199283589486032379383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112512531422905296086345021 42192199283589486032379383)
  ·
    refine ⟨63288298925384229048569075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42192199283589486032379383 63288298925384229048569075)
    ·
      refine ⟨94932448388076343572853613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63288298925384229048569075 94932448388076343572853613)
      ·
        refine ⟨35599668145528628839820105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94932448388076343572853613 35599668145528628839820105)
        ·
          refine ⟨26699751109146471629865079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35599668145528628839820105 26699751109146471629865079)
          ·
            refine ⟨40049626663719707444797619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26699751109146471629865079 40049626663719707444797619)
            ·
              refine ⟨60074439995579561167196429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40049626663719707444797619 60074439995579561167196429)
              ·
                refine ⟨22527914998342335437698661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60074439995579561167196429 22527914998342335437698661)
                ·
                  refine ⟨4223984062189187894568499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22527914998342335437698661 4223984062189187894568499)
                  ·
                    refine ⟨6335976093283781841852749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4223984062189187894568499 6335976093283781841852749)
                    ·
                      refine ⟨2375991034981418190694781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6335976093283781841852749 2375991034981418190694781)
                      ·
                        rfl

theorem cell23_4627226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_4627226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627226 prefixEnd_4627226 := by exact prefixLift 4627226
  have htrace : WordTrace (prefixWord ++ tailWord_4627226) baseStart_4627226 baseEnd_4627226 := by
    simpa [prefixWord, tailWord_4627226, baseEnd_4627226] using wordTrace_append hprefix tailTrace_4627226
  have hstable : (prefixWord ++ tailWord_4627226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627226).length < 2 ^ (prefixWord ++ tailWord_4627226).sum := by decide
  have hdescent : baseEnd_4627226 < baseStart_4627226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627253 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 3, 3, 2]
def baseStart_4627253 : Nat := 118140960795 + 4627253 * 2 ^ 59
def prefixEnd_4627253 : Nat := 4983230072969 + 3 ^ 40 * 4627253 * 2
def baseEnd_4627253 : Nat := 2376004898959089585057157

theorem tailTrace_4627253 : CollatzResearch.WordTrace tailWord_4627253 prefixEnd_4627253 2376004898959089585057157 := by
  unfold tailWord_4627253
  simp only [CollatzResearch.WordTrace]
  refine ⟨168769781905260127740750413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112513187936840085160500275 168769781905260127740750413)
  ·
    refine ⟨63288668214472547902781405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168769781905260127740750413 63288668214472547902781405)
    ·
      refine ⟨23733250580427205463543027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63288668214472547902781405 23733250580427205463543027)
      ·
        refine ⟨35599875870640808195314541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23733250580427205463543027 35599875870640808195314541)
        ·
          refine ⟨13349953451490303073242953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35599875870640808195314541 13349953451490303073242953)
          ·
            refine ⟨10012465088617727304932215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13349953451490303073242953 10012465088617727304932215)
            ·
              refine ⟨15018697632926590957398323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10012465088617727304932215 15018697632926590957398323)
              ·
                refine ⟨22528046449389886436097485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15018697632926590957398323 22528046449389886436097485)
                ·
                  refine ⟨8448017418521207413536557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22528046449389886436097485 8448017418521207413536557)
                  ·
                    refine ⟨3168006531945452780076209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8448017418521207413536557 3168006531945452780076209)
                    ·
                      refine ⟨2376004898959089585057157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3168006531945452780076209 2376004898959089585057157)
                      ·
                        rfl

theorem cell23_4627253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_4627253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627253 prefixEnd_4627253 := by exact prefixLift 4627253
  have htrace : WordTrace (prefixWord ++ tailWord_4627253) baseStart_4627253 baseEnd_4627253 := by
    simpa [prefixWord, tailWord_4627253, baseEnd_4627253] using wordTrace_append hprefix tailTrace_4627253
  have hstable : (prefixWord ++ tailWord_4627253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627253).length < 2 ^ (prefixWord ++ tailWord_4627253).sum := by decide
  have hdescent : baseEnd_4627253 < baseStart_4627253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627277 : List Nat := [1, 6, 1, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_4627277 : Nat := 118140960795 + 4627277 * 2 ^ 59
def prefixEnd_4627277 : Nat := 4983230072969 + 3 ^ 40 * 4627277 * 2
def baseEnd_4627277 : Nat := 2376017222494797491157047

theorem tailTrace_4627277 : CollatzResearch.WordTrace tailWord_4627277 prefixEnd_4627277 2376017222494797491157047 := by
  unfold tailWord_4627277
  simp only [CollatzResearch.WordTrace]
  refine ⟨168770657257173179839624085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112513771504782119893082723 168770657257173179839624085)
  ·
    refine ⟨7911124558929992804982379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 168770657257173179839624085 7911124558929992804982379)
    ·
      refine ⟨11866686838394989207473569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7911124558929992804982379 11866686838394989207473569)
      ·
        refine ⟨8900015128796241905605177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11866686838394989207473569 8900015128796241905605177)
        ·
          refine ⟨6675011346597181429203883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8900015128796241905605177 6675011346597181429203883)
          ·
            refine ⟨10012517019895772143805825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6675011346597181429203883 10012517019895772143805825)
            ·
              refine ⟨7509387764921829107854369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10012517019895772143805825 7509387764921829107854369)
              ·
                refine ⟨5632040823691371830890777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7509387764921829107854369 5632040823691371830890777)
                ·
                  refine ⟨4224030617768528873168083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5632040823691371830890777 4224030617768528873168083)
                  ·
                    refine ⟨6336045926652793309752125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4224030617768528873168083 6336045926652793309752125)
                    ·
                      refine ⟨2376017222494797491157047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6336045926652793309752125 2376017222494797491157047)
                      ·
                        rfl

theorem cell23_4627277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_4627277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627277 prefixEnd_4627277 := by exact prefixLift 4627277
  have htrace : WordTrace (prefixWord ++ tailWord_4627277) baseStart_4627277 baseEnd_4627277 := by
    simpa [prefixWord, tailWord_4627277, baseEnd_4627277] using wordTrace_append hprefix tailTrace_4627277
  have hstable : (prefixWord ++ tailWord_4627277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627277).length < 2 ^ (prefixWord ++ tailWord_4627277).sum := by decide
  have hdescent : baseEnd_4627277 < baseStart_4627277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627300 : List Nat := [2, 3, 1, 1, 4, 1, 2, 3, 2, 2, 2]
def baseStart_4627300 : Nat := 118140960795 + 4627300 * 2 ^ 59
def prefixEnd_4627300 : Nat := 4983230072969 + 3 ^ 40 * 4627300 * 2
def baseEnd_4627300 : Nat := 2376029032549850901169441

theorem tailTrace_4627300 : CollatzResearch.WordTrace tailWord_4627300 prefixEnd_4627300 2376029032549850901169441 := by
  unfold tailWord_4627300
  simp only [CollatzResearch.WordTrace]
  refine ⟨84385748068044927383855677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112514330757393236511807569 84385748068044927383855677)
  ·
    refine ⟨31644655525516847768945879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84385748068044927383855677 31644655525516847768945879)
    ·
      refine ⟨47466983288275271653418819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31644655525516847768945879 47466983288275271653418819)
      ·
        refine ⟨71200474932412907480128229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47466983288275271653418819 71200474932412907480128229)
        ·
          refine ⟨13350089049827420152524043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71200474932412907480128229 13350089049827420152524043)
          ·
            refine ⟨20025133574741130228786065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13350089049827420152524043 20025133574741130228786065)
            ·
              refine ⟨15018850181055847671589549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20025133574741130228786065 15018850181055847671589549)
              ·
                refine ⟨5632068817895942876846081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15018850181055847671589549 5632068817895942876846081)
                ·
                  refine ⟨4224051613421957157634561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5632068817895942876846081 4224051613421957157634561)
                  ·
                    refine ⟨3168038710066467868225921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4224051613421957157634561 3168038710066467868225921)
                    ·
                      refine ⟨2376029032549850901169441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3168038710066467868225921 2376029032549850901169441)
                      ·
                        rfl

theorem cell23_4627300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_4627300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627300 prefixEnd_4627300 := by exact prefixLift 4627300
  have htrace : WordTrace (prefixWord ++ tailWord_4627300) baseStart_4627300 baseEnd_4627300 := by
    simpa [prefixWord, tailWord_4627300, baseEnd_4627300] using wordTrace_append hprefix tailTrace_4627300
  have hstable : (prefixWord ++ tailWord_4627300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627300).length < 2 ^ (prefixWord ++ tailWord_4627300).sum := by decide
  have hdescent : baseEnd_4627300 < baseStart_4627300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627369 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 2, 4, 4]
def baseStart_4627369 : Nat := 118140960795 + 4627369 * 2 ^ 59
def prefixEnd_4627369 : Nat := 4983230072969 + 3 ^ 40 * 4627369 * 2
def baseEnd_4627369 : Nat := 2376064462715011131206623

theorem tailTrace_4627369 : CollatzResearch.WordTrace tailWord_4627369 prefixEnd_4627369 2376064462715011131206623 := by
  unfold tailWord_4627369
  simp only [CollatzResearch.WordTrace]
  refine ⟨168774012772839879551973161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112516008515226586367982107 168774012772839879551973161)
  ·
    refine ⟨126580509579629909663979871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168774012772839879551973161 126580509579629909663979871)
    ·
      refine ⟨189870764369444864495969807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126580509579629909663979871 189870764369444864495969807)
      ·
        refine ⟨284806146554167296743954711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189870764369444864495969807 284806146554167296743954711)
        ·
          refine ⟨427209219831250945115932067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284806146554167296743954711 427209219831250945115932067)
          ·
            refine ⟨640813829746876417673898101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427209219831250945115932067 640813829746876417673898101)
            ·
              refine ⟨60076296538769664156927947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 640813829746876417673898101 60076296538769664156927947)
              ·
                refine ⟨90114444808154496235391921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60076296538769664156927947 90114444808154496235391921)
                ·
                  refine ⟨67585833606115872176543941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90114444808154496235391921 67585833606115872176543941)
                  ·
                    refine ⟨12672343801146726033101989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67585833606115872176543941 12672343801146726033101989)
                    ·
                      refine ⟨2376064462715011131206623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12672343801146726033101989 2376064462715011131206623)
                      ·
                        rfl

theorem cell23_4627369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 4, 4].length) (baseStart_4627369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627369 prefixEnd_4627369 := by exact prefixLift 4627369
  have htrace : WordTrace (prefixWord ++ tailWord_4627369) baseStart_4627369 baseEnd_4627369 := by
    simpa [prefixWord, tailWord_4627369, baseEnd_4627369] using wordTrace_append hprefix tailTrace_4627369
  have hstable : (prefixWord ++ tailWord_4627369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627369).length < 2 ^ (prefixWord ++ tailWord_4627369).sum := by decide
  have hdescent : baseEnd_4627369 < baseStart_4627369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627399 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_4627399 : Nat := 118140960795 + 4627399 * 2 ^ 59
def prefixEnd_4627399 : Nat := 4983230072969 + 3 ^ 40 * 4627399 * 2
def baseEnd_4627399 : Nat := 2376079867134646013831485

theorem tailTrace_4627399 : CollatzResearch.WordTrace tailWord_4627399 prefixEnd_4627399 2376079867134646013831485 := by
  unfold tailWord_4627399
  simp only [CollatzResearch.WordTrace]
  refine ⟨168775106962731194675565251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112516737975154129783710167 168775106962731194675565251)
  ·
    refine ⟨253162660444096792013347877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168775106962731194675565251 253162660444096792013347877)
    ·
      refine ⟨47467998833268148502502727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 253162660444096792013347877 47467998833268148502502727)
      ·
        refine ⟨71201998249902222753754091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47467998833268148502502727 71201998249902222753754091)
        ·
          refine ⟨106802997374853334130631137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71201998249902222753754091 106802997374853334130631137)
          ·
            refine ⟨80102248031140000597973353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106802997374853334130631137 80102248031140000597973353)
            ·
              refine ⟨60076686023355000448480015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80102248031140000597973353 60076686023355000448480015)
              ·
                refine ⟨90115029035032500672720023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60076686023355000448480015 90115029035032500672720023)
                ·
                  refine ⟨135172543552548751009080035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90115029035032500672720023 135172543552548751009080035)
                  ·
                    refine ⟨202758815328823126513620053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 135172543552548751009080035 202758815328823126513620053)
                    ·
                      refine ⟨2376079867134646013831485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 202758815328823126513620053 2376079867134646013831485)
                      ·
                        rfl

theorem cell23_4627399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_4627399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627399 prefixEnd_4627399 := by exact prefixLift 4627399
  have htrace : WordTrace (prefixWord ++ tailWord_4627399) baseStart_4627399 baseEnd_4627399 := by
    simpa [prefixWord, tailWord_4627399, baseEnd_4627399] using wordTrace_append hprefix tailTrace_4627399
  have hstable : (prefixWord ++ tailWord_4627399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627399).length < 2 ^ (prefixWord ++ tailWord_4627399).sum := by decide
  have hdescent : baseEnd_4627399 < baseStart_4627399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627400 : List Nat := [2, 1, 3, 1, 5, 2, 1, 1, 3, 4]
def baseStart_4627400 : Nat := 118140960795 + 4627400 * 2 ^ 59
def prefixEnd_4627400 : Nat := 4983230072969 + 3 ^ 40 * 4627400 * 2
def baseEnd_4627400 : Nat := 792026793538433503306327

theorem tailTrace_4627400 : CollatzResearch.WordTrace tailWord_4627400 prefixEnd_4627400 792026793538433503306327 := by
  unfold tailWord_4627400
  simp only [CollatzResearch.WordTrace]
  refine ⟨84387571717863785923175827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112516762290485047897567769 84387571717863785923175827)
  ·
    refine ⟨126581357576795678884763741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84387571717863785923175827 126581357576795678884763741)
    ·
      refine ⟨47468009091298379581786403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126581357576795678884763741 47468009091298379581786403)
      ·
        refine ⟨71202013636947569372679605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47468009091298379581786403 71202013636947569372679605)
        ·
          refine ⟨6675188778463834628688713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71202013636947569372679605 6675188778463834628688713)
          ·
            refine ⟨5006391583847875971516535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6675188778463834628688713 5006391583847875971516535)
            ·
              refine ⟨7509587375771813957274803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5006391583847875971516535 7509587375771813957274803)
              ·
                refine ⟨11264381063657720935912205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7509587375771813957274803 11264381063657720935912205)
                ·
                  refine ⟨4224142898871645350967077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11264381063657720935912205 4224142898871645350967077)
                  ·
                    refine ⟨792026793538433503306327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4224142898871645350967077 792026793538433503306327)
                    ·
                      rfl

theorem cell23_4627400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_4627400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627400 prefixEnd_4627400 := by exact prefixLift 4627400
  have htrace : WordTrace (prefixWord ++ tailWord_4627400) baseStart_4627400 baseEnd_4627400 := by
    simpa [prefixWord, tailWord_4627400, baseEnd_4627400] using wordTrace_append hprefix tailTrace_4627400
  have hstable : (prefixWord ++ tailWord_4627400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627400).length < 2 ^ (prefixWord ++ tailWord_4627400).sum := by decide
  have hdescent : baseEnd_4627400 < baseStart_4627400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627413 : List Nat := [1, 3, 2, 3, 3, 1, 1, 3, 6]
def baseStart_4627413 : Nat := 118140960795 + 4627413 * 2 ^ 59
def prefixEnd_4627413 : Nat := 4983230072969 + 3 ^ 40 * 4627413 * 2
def baseEnd_4627413 : Nat := 264009672873756551006269

theorem tailTrace_4627413 : CollatzResearch.WordTrace tailWord_4627413 prefixEnd_4627413 264009672873756551006269 := by
  unfold tailWord_4627413
  simp only [CollatzResearch.WordTrace]
  refine ⟨168775617584680475066574893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112517078389786983377716595 168775617584680475066574893)
  ·
    refine ⟨63290856594255178149965585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168775617584680475066574893 63290856594255178149965585)
    ·
      refine ⟨47468142445691383612474189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63290856594255178149965585 47468142445691383612474189)
      ·
        refine ⟨17800553417134268854677821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47468142445691383612474189 17800553417134268854677821)
        ·
          refine ⟨6675207531425350820504183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17800553417134268854677821 6675207531425350820504183)
          ·
            refine ⟨10012811297138026230756275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6675207531425350820504183 10012811297138026230756275)
            ·
              refine ⟨15019216945707039346134413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10012811297138026230756275 15019216945707039346134413)
              ·
                refine ⟨5632206354640139754800405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15019216945707039346134413 5632206354640139754800405)
                ·
                  refine ⟨264009672873756551006269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5632206354640139754800405 264009672873756551006269)
                  ·
                    rfl

theorem cell23_4627413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 6].length) (baseStart_4627413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627413 prefixEnd_4627413 := by exact prefixLift 4627413
  have htrace : WordTrace (prefixWord ++ tailWord_4627413) baseStart_4627413 baseEnd_4627413 := by
    simpa [prefixWord, tailWord_4627413, baseEnd_4627413] using wordTrace_append hprefix tailTrace_4627413
  have hstable : (prefixWord ++ tailWord_4627413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627413).length < 2 ^ (prefixWord ++ tailWord_4627413).sum := by decide
  have hdescent : baseEnd_4627413 < baseStart_4627413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627440 : List Nat := [2, 1, 1, 1, 3, 2, 1, 7, 1, 1, 3]
def baseStart_4627440 : Nat := 118140960795 + 4627440 * 2 ^ 59
def prefixEnd_4627440 : Nat := 4983230072969 + 3 ^ 40 * 4627440 * 2
def baseEnd_4627440 : Nat := 2376100919841480353418797

theorem tailTrace_4627440 : CollatzResearch.WordTrace tailWord_4627440 prefixEnd_4627440 2376100919841480353418797 := by
  unfold tailWord_4627440
  simp only [CollatzResearch.WordTrace]
  refine ⟨84388301177791329338903887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112517734903721772451871849 84388301177791329338903887)
  ·
    refine ⟨126582451766686994008355831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84388301177791329338903887 126582451766686994008355831)
    ·
      refine ⟨189873677650030491012533747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126582451766686994008355831 189873677650030491012533747)
      ·
        refine ⟨284810516475045736518800621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189873677650030491012533747 284810516475045736518800621)
        ·
          refine ⟨106803943678142151194550233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 284810516475045736518800621 106803943678142151194550233)
          ·
            refine ⟨80102957758606613395912675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106803943678142151194550233 80102957758606613395912675)
            ·
              refine ⟨120154436637909920093869013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80102957758606613395912675 120154436637909920093869013)
              ·
                refine ⟨2816119608701013752200055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 120154436637909920093869013 2816119608701013752200055)
                ·
                  refine ⟨4224179413051520628300083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2816119608701013752200055 4224179413051520628300083)
                  ·
                    refine ⟨6336269119577280942450125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4224179413051520628300083 6336269119577280942450125)
                    ·
                      refine ⟨2376100919841480353418797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6336269119577280942450125 2376100919841480353418797)
                      ·
                        rfl

theorem cell23_4627440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 1, 1, 3].length) (baseStart_4627440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627440 prefixEnd_4627440 := by exact prefixLift 4627440
  have htrace : WordTrace (prefixWord ++ tailWord_4627440) baseStart_4627440 baseEnd_4627440 := by
    simpa [prefixWord, tailWord_4627440, baseEnd_4627440] using wordTrace_append hprefix tailTrace_4627440
  have hstable : (prefixWord ++ tailWord_4627440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627440).length < 2 ^ (prefixWord ++ tailWord_4627440).sum := by decide
  have hdescent : baseEnd_4627440 < baseStart_4627440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627456 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 8, 4]
def baseStart_4627456 : Nat := 118140960795 + 4627456 * 2 ^ 59
def prefixEnd_4627456 : Nat := 4983230072969 + 3 ^ 40 * 4627456 * 2
def baseEnd_4627456 : Nat := 792036378510650763606241

theorem tailTrace_4627456 : CollatzResearch.WordTrace tailWord_4627456 prefixEnd_4627456 792036378510650763606241 := by
  unfold tailWord_4627456
  simp only [CollatzResearch.WordTrace]
  refine ⟨84388592961762346705195111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112518123949016462273593481 84388592961762346705195111)
  ·
    refine ⟨126582889442643520057792667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84388592961762346705195111 126582889442643520057792667)
    ·
      refine ⟨189874334163965280086689001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126582889442643520057792667 189874334163965280086689001)
      ·
        refine ⟨142405750622973960065016751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189874334163965280086689001 142405750622973960065016751)
        ·
          refine ⟨213608625934460940097525127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142405750622973960065016751 213608625934460940097525127)
          ·
            refine ⟨320412938901691410146287691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213608625934460940097525127 320412938901691410146287691)
            ·
              refine ⟨480619408352537115219431537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320412938901691410146287691 480619408352537115219431537)
              ·
                refine ⟨360464556264402836414573653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 480619408352537115219431537 360464556264402836414573653)
                ·
                  refine ⟨4224194018723470739233285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 360464556264402836414573653 4224194018723470739233285)
                  ·
                    refine ⟨792036378510650763606241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4224194018723470739233285 792036378510650763606241)
                    ·
                      rfl

theorem cell23_4627456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 8, 4].length) (baseStart_4627456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627456 prefixEnd_4627456 := by exact prefixLift 4627456
  have htrace : WordTrace (prefixWord ++ tailWord_4627456) baseStart_4627456 baseEnd_4627456 := by
    simpa [prefixWord, tailWord_4627456, baseEnd_4627456] using wordTrace_append hprefix tailTrace_4627456
  have hstable : (prefixWord ++ tailWord_4627456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627456).length < 2 ^ (prefixWord ++ tailWord_4627456).sum := by decide
  have hdescent : baseEnd_4627456 < baseStart_4627456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627457 : List Nat := [1, 2, 4, 1, 2, 3, 1, 4, 1, 1, 3]
def baseStart_4627457 : Nat := 118140960795 + 4627457 * 2 ^ 59
def prefixEnd_4627457 : Nat := 4983230072969 + 3 ^ 40 * 4627457 * 2
def baseEnd_4627457 : Nat := 2376109649012606786906219

theorem tailTrace_4627457 : CollatzResearch.WordTrace tailWord_4627457 prefixEnd_4627457 2376109649012606786906219 := by
  unfold tailWord_4627457
  simp only [CollatzResearch.WordTrace]
  refine ⟨168777222396521070581176625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112518148264347380387451083 168777222396521070581176625)
  ·
    refine ⟨126582916797390802935882469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168777222396521070581176625 126582916797390802935882469)
    ·
      refine ⟨23734296899510775550477963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126582916797390802935882469 23734296899510775550477963)
      ·
        refine ⟨35601445349266163325716945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23734296899510775550477963 35601445349266163325716945)
        ·
          refine ⟨26701084011949622494287709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35601445349266163325716945 26701084011949622494287709)
          ·
            refine ⟨10012906504481108435357891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26701084011949622494287709 10012906504481108435357891)
            ·
              refine ⟨15019359756721662653036837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10012906504481108435357891 15019359756721662653036837)
              ·
                refine ⟨2816129954385311747444407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15019359756721662653036837 2816129954385311747444407)
                ·
                  refine ⟨4224194931577967621166611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2816129954385311747444407 4224194931577967621166611)
                  ·
                    refine ⟨6336292397366951431749917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4224194931577967621166611 6336292397366951431749917)
                    ·
                      refine ⟨2376109649012606786906219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6336292397366951431749917 2376109649012606786906219)
                      ·
                        rfl

theorem cell23_4627457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_4627457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627457 prefixEnd_4627457 := by exact prefixLift 4627457
  have htrace : WordTrace (prefixWord ++ tailWord_4627457) baseStart_4627457 baseEnd_4627457 := by
    simpa [prefixWord, tailWord_4627457, baseEnd_4627457] using wordTrace_append hprefix tailTrace_4627457
  have hstable : (prefixWord ++ tailWord_4627457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627457).length < 2 ^ (prefixWord ++ tailWord_4627457).sum := by decide
  have hdescent : baseEnd_4627457 < baseStart_4627457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627480 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 5, 2, 2]
def baseStart_4627480 : Nat := 118140960795 + 4627480 * 2 ^ 59
def prefixEnd_4627480 : Nat := 4983230072969 + 3 ^ 40 * 4627480 * 2
def baseEnd_4627480 : Nat := 2376121459067660196918613

theorem tailTrace_4627480 : CollatzResearch.WordTrace tailWord_4627480 prefixEnd_4627480 2376121459067660196918613 := by
  unfold tailWord_4627480
  simp only [CollatzResearch.WordTrace]
  refine ⟨84389030637718872754631947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112518707516958497006175929 84389030637718872754631947)
  ·
    refine ⟨126583545956578309131947921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84389030637718872754631947 126583545956578309131947921)
    ·
      refine ⟨94937659467433731848960941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126583545956578309131947921 94937659467433731848960941)
      ·
        refine ⟨35601622300287649443360353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94937659467433731848960941 35601622300287649443360353)
        ·
          refine ⟨26701216725215737082520265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35601622300287649443360353 26701216725215737082520265)
          ·
            refine ⟨20025912543911802811890199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26701216725215737082520265 20025912543911802811890199)
            ·
              refine ⟨30038868815867704217835299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20025912543911802811890199 30038868815867704217835299)
              ·
                refine ⟨45058303223801556326752949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30038868815867704217835299 45058303223801556326752949)
                ·
                  refine ⟨4224215927231395905633089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45058303223801556326752949 4224215927231395905633089)
                  ·
                    refine ⟨3168161945423546929224817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4224215927231395905633089 3168161945423546929224817)
                    ·
                      refine ⟨2376121459067660196918613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3168161945423546929224817 2376121459067660196918613)
                      ·
                        rfl

theorem cell23_4627480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_4627480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627480 prefixEnd_4627480 := by exact prefixLift 4627480
  have htrace : WordTrace (prefixWord ++ tailWord_4627480) baseStart_4627480 baseEnd_4627480 := by
    simpa [prefixWord, tailWord_4627480, baseEnd_4627480] using wordTrace_append hprefix tailTrace_4627480
  have hstable : (prefixWord ++ tailWord_4627480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627480).length < 2 ^ (prefixWord ++ tailWord_4627480).sum := by decide
  have hdescent : baseEnd_4627480 < baseStart_4627480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627484 : List Nat := [2, 2, 3, 1, 5, 1, 1, 1, 2, 3, 2]
def baseStart_4627484 : Nat := 118140960795 + 4627484 * 2 ^ 59
def prefixEnd_4627484 : Nat := 4983230072969 + 3 ^ 40 * 4627484 * 2
def baseEnd_4627484 : Nat := 2376123512990278181268595

theorem tailTrace_4627484 : CollatzResearch.WordTrace tailWord_4627484 prefixEnd_4627484 2376123512990278181268595 := by
  unfold tailWord_4627484
  simp only [CollatzResearch.WordTrace]
  refine ⟨84389103583711627096204753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112518804778282169461606337 84389103583711627096204753)
  ·
    refine ⟨63291827687783720322153565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84389103583711627096204753 63291827687783720322153565)
    ·
      refine ⟨23734435382918895120807587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63291827687783720322153565 23734435382918895120807587)
      ·
        refine ⟨35601653074378342681211381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23734435382918895120807587 35601653074378342681211381)
        ·
          refine ⟨3337654975722969626363567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35601653074378342681211381 3337654975722969626363567)
          ·
            refine ⟨5006482463584454439545351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3337654975722969626363567 5006482463584454439545351)
            ·
              refine ⟨7509723695376681659318027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5006482463584454439545351 7509723695376681659318027)
              ·
                refine ⟨11264585543065022488977041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7509723695376681659318027 11264585543065022488977041)
                ·
                  refine ⟨8448439157298766866732781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11264585543065022488977041 8448439157298766866732781)
                  ·
                    refine ⟨3168164683987037575024793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8448439157298766866732781 3168164683987037575024793)
                    ·
                      refine ⟨2376123512990278181268595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3168164683987037575024793 2376123512990278181268595)
                      ·
                        rfl

theorem cell23_4627484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_4627484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627484 prefixEnd_4627484 := by exact prefixLift 4627484
  have htrace : WordTrace (prefixWord ++ tailWord_4627484) baseStart_4627484 baseEnd_4627484 := by
    simpa [prefixWord, tailWord_4627484, baseEnd_4627484] using wordTrace_append hprefix tailTrace_4627484
  have hstable : (prefixWord ++ tailWord_4627484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627484).length < 2 ^ (prefixWord ++ tailWord_4627484).sum := by decide
  have hdescent : baseEnd_4627484 < baseStart_4627484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627530 : List Nat := [3, 1, 2, 1, 1, 2, 2, 5, 2, 1, 3]
def baseStart_4627530 : Nat := 118140960795 + 4627530 * 2 ^ 59
def prefixEnd_4627530 : Nat := 4983230072969 + 3 ^ 40 * 4627530 * 2
def baseEnd_4627530 : Nat := 2376147133100385001293383

theorem tailTrace_4627530 : CollatzResearch.WordTrace tailWord_4627530 prefixEnd_4627530 2376147133100385001293383 := by
  unfold tailWord_4627530
  simp only [CollatzResearch.WordTrace]
  refine ⟨42194971231314151012146011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112519923283504402699056029 42194971231314151012146011)
  ·
    refine ⟨63292456846971226518219017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42194971231314151012146011 63292456846971226518219017)
    ·
      refine ⟨47469342635228419888664263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63292456846971226518219017 47469342635228419888664263)
      ·
        refine ⟨71204013952842629832996395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47469342635228419888664263 71204013952842629832996395)
        ·
          refine ⟨106806020929263944749494593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71204013952842629832996395 106806020929263944749494593)
          ·
            refine ⟨80104515696947958562120945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106806020929263944749494593 80104515696947958562120945)
            ·
              refine ⟨60078386772710968921590709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80104515696947958562120945 60078386772710968921590709)
              ·
                refine ⟨5632348759941653336399129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60078386772710968921590709 5632348759941653336399129)
                ·
                  refine ⟨4224261569956240002299347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5632348759941653336399129 4224261569956240002299347)
                  ·
                    refine ⟨6336392354934360003449021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4224261569956240002299347 6336392354934360003449021)
                    ·
                      refine ⟨2376147133100385001293383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6336392354934360003449021 2376147133100385001293383)
                      ·
                        rfl

theorem cell23_4627530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_4627530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627530 prefixEnd_4627530 := by exact prefixLift 4627530
  have htrace : WordTrace (prefixWord ++ tailWord_4627530) baseStart_4627530 baseEnd_4627530 := by
    simpa [prefixWord, tailWord_4627530, baseEnd_4627530] using wordTrace_append hprefix tailTrace_4627530
  have hstable : (prefixWord ++ tailWord_4627530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627530).length < 2 ^ (prefixWord ++ tailWord_4627530).sum := by decide
  have hdescent : baseEnd_4627530 < baseStart_4627530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627536 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 4]
def baseStart_4627536 : Nat := 118140960795 + 4627536 * 2 ^ 59
def prefixEnd_4627536 : Nat := 4983230072969 + 3 ^ 40 * 4627536 * 2
def baseEnd_4627536 : Nat := 2376150213984311977818355

theorem tailTrace_4627536 : CollatzResearch.WordTrace tailWord_4627536 prefixEnd_4627536 2376150213984311977818355 := by
  unfold tailWord_4627536
  simp only [CollatzResearch.WordTrace]
  refine ⟨84390051881617433536651231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112520069175489911382201641 84390051881617433536651231)
  ·
    refine ⟨126585077822426150304976847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84390051881617433536651231 126585077822426150304976847)
    ·
      refine ⟨189877616733639225457465271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126585077822426150304976847 189877616733639225457465271)
      ·
        refine ⟨284816425100458838186197907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189877616733639225457465271 284816425100458838186197907)
        ·
          refine ⟨427224637650688257279296861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284816425100458838186197907 427224637650688257279296861)
          ·
            refine ⟨160209239119008096479736323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 427224637650688257279296861 160209239119008096479736323)
            ·
              refine ⟨240313858678512144719604485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160209239119008096479736323 240313858678512144719604485)
              ·
                refine ⟨45058848502221027134925841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 240313858678512144719604485 45058848502221027134925841)
                ·
                  refine ⟨33794136376665770351194381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45058848502221027134925841 33794136376665770351194381)
                  ·
                    refine ⟨12672801141249663881697893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33794136376665770351194381 12672801141249663881697893)
                    ·
                      refine ⟨2376150213984311977818355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12672801141249663881697893 2376150213984311977818355)
                      ·
                        rfl

theorem cell23_4627536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 4].length) (baseStart_4627536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627536 prefixEnd_4627536 := by exact prefixLift 4627536
  have htrace : WordTrace (prefixWord ++ tailWord_4627536) baseStart_4627536 baseEnd_4627536 := by
    simpa [prefixWord, tailWord_4627536, baseEnd_4627536] using wordTrace_append hprefix tailTrace_4627536
  have hstable : (prefixWord ++ tailWord_4627536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627536).length < 2 ^ (prefixWord ++ tailWord_4627536).sum := by decide
  have hdescent : baseEnd_4627536 < baseStart_4627536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627540 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 3, 3, 2]
def baseStart_4627540 : Nat := 118140960795 + 4627540 * 2 ^ 59
def prefixEnd_4627540 : Nat := 4983230072969 + 3 ^ 40 * 4627540 * 2
def baseEnd_4627540 : Nat := 2376152267906929962168337

theorem tailTrace_4627540 : CollatzResearch.WordTrace tailWord_4627540 prefixEnd_4627540 2376152267906929962168337 := by
  unfold tailWord_4627540
  simp only [CollatzResearch.WordTrace]
  refine ⟨84390124827610187878224037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112520166436813583837632049 84390124827610187878224037)
  ·
    refine ⟨15823148405176910227167007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84390124827610187878224037 15823148405176910227167007)
    ·
      refine ⟨23734722607765365340750511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15823148405176910227167007 23734722607765365340750511)
      ·
        refine ⟨35602083911648048011125767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23734722607765365340750511 35602083911648048011125767)
        ·
          refine ⟨53403125867472072016688651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35602083911648048011125767 53403125867472072016688651)
          ·
            refine ⟨80104688801208108025032977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53403125867472072016688651 80104688801208108025032977)
            ·
              refine ⟨60078516600906081018774733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80104688801208108025032977 60078516600906081018774733)
              ·
                refine ⟨22529443725339780382040525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60078516600906081018774733 22529443725339780382040525)
                ·
                  refine ⟨8448541397002417643265197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22529443725339780382040525 8448541397002417643265197)
                  ·
                    refine ⟨3168203023875906616224449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8448541397002417643265197 3168203023875906616224449)
                    ·
                      refine ⟨2376152267906929962168337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3168203023875906616224449 2376152267906929962168337)
                      ·
                        rfl

theorem cell23_4627540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_4627540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627540 prefixEnd_4627540 := by exact prefixLift 4627540
  have htrace : WordTrace (prefixWord ++ tailWord_4627540) baseStart_4627540 baseEnd_4627540 := by
    simpa [prefixWord, tailWord_4627540, baseEnd_4627540] using wordTrace_append hprefix tailTrace_4627540
  have hstable : (prefixWord ++ tailWord_4627540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627540).length < 2 ^ (prefixWord ++ tailWord_4627540).sum := by decide
  have hdescent : baseEnd_4627540 < baseStart_4627540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627546 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 4, 6]
def baseStart_4627546 : Nat := 118140960795 + 4627546 * 2 ^ 59
def prefixEnd_4627546 : Nat := 4983230072969 + 3 ^ 40 * 4627546 * 2
def baseEnd_4627546 : Nat := 792051782930285646231103

theorem tailTrace_4627546 : CollatzResearch.WordTrace tailWord_4627546 prefixEnd_4627546 792051782930285646231103 := by
  unfold tailWord_4627546
  simp only [CollatzResearch.WordTrace]
  refine ⟨42195117123299659695291623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112520312328799092520777661 42195117123299659695291623)
  ·
    refine ⟨63292675684949489542937435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42195117123299659695291623 63292675684949489542937435)
    ·
      refine ⟨94939013527424234314406153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63292675684949489542937435 94939013527424234314406153)
      ·
        refine ⟨71204260145568175735804615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94939013527424234314406153 71204260145568175735804615)
        ·
          refine ⟨106806390218352263603706923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71204260145568175735804615 106806390218352263603706923)
          ·
            refine ⟨160209585327528395405560385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106806390218352263603706923 160209585327528395405560385)
            ·
              refine ⟨120157188995646296554170289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160209585327528395405560385 120157188995646296554170289)
              ·
                refine ⟨90117891746734722415627717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120157188995646296554170289 90117891746734722415627717)
                ·
                  refine ⟨16897104702512760452930197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90117891746734722415627717 16897104702512760452930197)
                  ·
                    refine ⟨792051782930285646231103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16897104702512760452930197 792051782930285646231103)
                    ·
                      rfl

theorem cell23_4627546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_4627546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627546 prefixEnd_4627546 := by exact prefixLift 4627546
  have htrace : WordTrace (prefixWord ++ tailWord_4627546) baseStart_4627546 baseEnd_4627546 := by
    simpa [prefixWord, tailWord_4627546, baseEnd_4627546] using wordTrace_append hprefix tailTrace_4627546
  have hstable : (prefixWord ++ tailWord_4627546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627546).length < 2 ^ (prefixWord ++ tailWord_4627546).sum := by decide
  have hdescent : baseEnd_4627546 < baseStart_4627546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627587 : List Nat := [1, 1, 1, 3, 3, 2, 3, 3, 2, 2, 2]
def baseStart_4627587 : Nat := 118140960795 + 4627587 * 2 ^ 59
def prefixEnd_4627587 : Nat := 4983230072969 + 3 ^ 40 * 4627587 * 2
def baseEnd_4627587 : Nat := 2376176401497691278280621

theorem tailTrace_4627587 : CollatzResearch.WordTrace tailWord_4627587 prefixEnd_4627587 2376176401497691278280621 := by
  unfold tailWord_4627587
  simp only [CollatzResearch.WordTrace]
  refine ⟨168781963886050102783409015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112521309257366735188939343 168781963886050102783409015)
  ·
    refine ⟨253172945829075154175113523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168781963886050102783409015 253172945829075154175113523)
    ·
      refine ⟨379759418743612731262670285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253172945829075154175113523 379759418743612731262670285)
      ·
        refine ⟨142409782028854774223501357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 379759418743612731262670285 142409782028854774223501357)
        ·
          refine ⟨53403668260820540333813009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142409782028854774223501357 53403668260820540333813009)
          ·
            refine ⟨40052751195615405250359757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53403668260820540333813009 40052751195615405250359757)
            ·
              refine ⟨15019781698355776968884909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40052751195615405250359757 15019781698355776968884909)
              ·
                refine ⟨5632418136883416363331841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15019781698355776968884909 5632418136883416363331841)
                ·
                  refine ⟨4224313602662562272498881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5632418136883416363331841 4224313602662562272498881)
                  ·
                    refine ⟨3168235201996921704374161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4224313602662562272498881 3168235201996921704374161)
                    ·
                      refine ⟨2376176401497691278280621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3168235201996921704374161 2376176401497691278280621)
                      ·
                        rfl

theorem cell23_4627587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 2, 2].length) (baseStart_4627587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627587 prefixEnd_4627587 := by exact prefixLift 4627587
  have htrace : WordTrace (prefixWord ++ tailWord_4627587) baseStart_4627587 baseEnd_4627587 := by
    simpa [prefixWord, tailWord_4627587, baseEnd_4627587] using wordTrace_append hprefix tailTrace_4627587
  have hstable : (prefixWord ++ tailWord_4627587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627587).length < 2 ^ (prefixWord ++ tailWord_4627587).sum := by decide
  have hdescent : baseEnd_4627587 < baseStart_4627587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627596 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 8]
def baseStart_4627596 : Nat := 118140960795 + 4627596 * 2 ^ 59
def prefixEnd_4627596 : Nat := 4983230072969 + 3 ^ 40 * 4627596 * 2
def baseEnd_4627596 : Nat := 2376181022823581743068079

theorem tailTrace_4627596 : CollatzResearch.WordTrace tailWord_4627596 prefixEnd_4627596 2376181022823581743068079 := by
  unfold tailWord_4627596
  simp only [CollatzResearch.WordTrace]
  refine ⟨84391146071508748660243321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112521528095344998213657761 84391146071508748660243321)
  ·
    refine ⟨63293359553631561495182491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84391146071508748660243321 63293359553631561495182491)
    ·
      refine ⟨94940039330447342242773737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63293359553631561495182491 94940039330447342242773737)
      ·
        refine ⟨71205029497835506682080303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94940039330447342242773737 71205029497835506682080303)
        ·
          refine ⟨106807544246753260023120455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71205029497835506682080303 106807544246753260023120455)
          ·
            refine ⟨160211316370129890034680683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106807544246753260023120455 160211316370129890034680683)
            ·
              refine ⟨240316974555194835052021025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160211316370129890034680683 240316974555194835052021025)
              ·
                refine ⟨180237730916396126289015769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240316974555194835052021025 180237730916396126289015769)
                ·
                  refine ⟨135178298187297094716761827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180237730916396126289015769 135178298187297094716761827)
                  ·
                    refine ⟨202767447280945642075142741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 135178298187297094716761827 202767447280945642075142741)
                    ·
                      refine ⟨2376181022823581743068079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 202767447280945642075142741 2376181022823581743068079)
                      ·
                        rfl

theorem cell23_4627596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_4627596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627596 prefixEnd_4627596 := by exact prefixLift 4627596
  have htrace : WordTrace (prefixWord ++ tailWord_4627596) baseStart_4627596 baseEnd_4627596 := by
    simpa [prefixWord, tailWord_4627596, baseEnd_4627596] using wordTrace_append hprefix tailTrace_4627596
  have hstable : (prefixWord ++ tailWord_4627596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627596).length < 2 ^ (prefixWord ++ tailWord_4627596).sum := by decide
  have hdescent : baseEnd_4627596 < baseStart_4627596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627661 : List Nat := [1, 6, 2, 2, 1, 1, 2, 3, 5]
def baseStart_4627661 : Nat := 118140960795 + 4627661 * 2 ^ 59
def prefixEnd_4627661 : Nat := 4983230072969 + 3 ^ 40 * 4627661 * 2
def baseEnd_4627661 : Nat := 264023822118458220972809

theorem tailTrace_4627661 : CollatzResearch.WordTrace tailWord_4627661 prefixEnd_4627661 264023822118458220972809 := by
  unfold tailWord_4627661
  simp only [CollatzResearch.WordTrace]
  refine ⟨168784662887782013421602837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112523108591854675614401891 168784662887782013421602837)
  ·
    refine ⟨7911781072864781879137633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 168784662887782013421602837 7911781072864781879137633)
    ·
      refine ⟨5933835804648586409353225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7911781072864781879137633 5933835804648586409353225)
      ·
        refine ⟨4450376853486439807014919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5933835804648586409353225 4450376853486439807014919)
        ·
          refine ⟨6675565280229659710522379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4450376853486439807014919 6675565280229659710522379)
          ·
            refine ⟨10013347920344489565783569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6675565280229659710522379 10013347920344489565783569)
            ·
              refine ⟨7510010940258367174337677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10013347920344489565783569 7510010940258367174337677)
              ·
                refine ⟨2816254102596887690376629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7510010940258367174337677 2816254102596887690376629)
                ·
                  refine ⟨264023822118458220972809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2816254102596887690376629 264023822118458220972809)
                  ·
                    rfl

theorem cell23_4627661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_4627661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627661 prefixEnd_4627661 := by exact prefixLift 4627661
  have htrace : WordTrace (prefixWord ++ tailWord_4627661) baseStart_4627661 baseEnd_4627661 := by
    simpa [prefixWord, tailWord_4627661, baseEnd_4627661] using wordTrace_append hprefix tailTrace_4627661
  have hstable : (prefixWord ++ tailWord_4627661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627661).length < 2 ^ (prefixWord ++ tailWord_4627661).sum := by decide
  have hdescent : baseEnd_4627661 < baseStart_4627661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627753 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 7, 1, 5]
def baseStart_4627753 : Nat := 118140960795 + 4627753 * 2 ^ 59
def prefixEnd_4627753 : Nat := 4983230072969 + 3 ^ 40 * 4627753 * 2
def baseEnd_4627753 : Nat := 2376261639286337628804857

theorem tailTrace_4627753 : CollatzResearch.WordTrace tailWord_4627753 prefixEnd_4627753 2376261639286337628804857 := by
  unfold tailWord_4627753
  simp only [CollatzResearch.WordTrace]
  refine ⟨168788018403448713133951913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112525345602299142089301275 168788018403448713133951913)
  ·
    refine ⟨126591013802586534850463935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168788018403448713133951913 126591013802586534850463935)
    ·
      refine ⟨189886520703879802275695903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126591013802586534850463935 189886520703879802275695903)
      ·
        refine ⟨284829781055819703413543855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189886520703879802275695903 284829781055819703413543855)
        ·
          refine ⟨427244671583729555120315783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284829781055819703413543855 427244671583729555120315783)
          ·
            refine ⟨640867007375594332680473675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427244671583729555120315783 640867007375594332680473675)
            ·
              refine ⟨961300511063391499020710513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640867007375594332680473675 961300511063391499020710513)
              ·
                refine ⟨720975383297543624265532885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 961300511063391499020710513 720975383297543624265532885)
                ·
                  refine ⟨16897860546036178693723427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 720975383297543624265532885 16897860546036178693723427)
                  ·
                    refine ⟨25346790819054268040585141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16897860546036178693723427 25346790819054268040585141)
                    ·
                      refine ⟨2376261639286337628804857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25346790819054268040585141 2376261639286337628804857)
                      ·
                        rfl

theorem cell23_4627753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 1, 5].length) (baseStart_4627753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627753 prefixEnd_4627753 := by exact prefixLift 4627753
  have htrace : WordTrace (prefixWord ++ tailWord_4627753) baseStart_4627753 baseEnd_4627753 := by
    simpa [prefixWord, tailWord_4627753, baseEnd_4627753] using wordTrace_append hprefix tailTrace_4627753
  have hstable : (prefixWord ++ tailWord_4627753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627753).length < 2 ^ (prefixWord ++ tailWord_4627753).sum := by decide
  have hdescent : baseEnd_4627753 < baseStart_4627753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627777 : List Nat := [1, 2, 5, 2, 1, 2, 1, 2, 1, 6]
def baseStart_4627777 : Nat := 118140960795 + 4627777 * 2 ^ 59
def prefixEnd_4627777 : Nat := 4983230072969 + 3 ^ 40 * 4627777 * 2
def baseEnd_4627777 : Nat := 792091320940681844968249

theorem tailTrace_4627777 : CollatzResearch.WordTrace tailWord_4627777 prefixEnd_4627777 792091320940681844968249 := by
  unfold tailWord_4627777
  simp only [CollatzResearch.WordTrace]
  refine ⟨168788893755361765232825585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112525929170241176821883723 168788893755361765232825585)
  ·
    refine ⟨126591670316521323924619189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168788893755361765232825585 126591670316521323924619189)
    ·
      refine ⟨11867969092173874117933049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126591670316521323924619189 11867969092173874117933049)
      ·
        refine ⟨8900976819130405588449787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11867969092173874117933049 8900976819130405588449787)
        ·
          refine ⟨13351465228695608382674681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8900976819130405588449787 13351465228695608382674681)
          ·
            refine ⟨10013598921521706287006011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13351465228695608382674681 10013598921521706287006011)
            ·
              refine ⟨15020398382282559430509017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10013598921521706287006011 15020398382282559430509017)
              ·
                refine ⟨11265298786711919572881763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15020398382282559430509017 11265298786711919572881763)
                ·
                  refine ⟨16897948180067879359322645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11265298786711919572881763 16897948180067879359322645)
                  ·
                    refine ⟨792091320940681844968249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16897948180067879359322645 792091320940681844968249)
                    ·
                      rfl

theorem cell23_4627777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_4627777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627777 prefixEnd_4627777 := by exact prefixLift 4627777
  have htrace : WordTrace (prefixWord ++ tailWord_4627777) baseStart_4627777 baseEnd_4627777 := by
    simpa [prefixWord, tailWord_4627777, baseEnd_4627777] using wordTrace_append hprefix tailTrace_4627777
  have hstable : (prefixWord ++ tailWord_4627777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627777).length < 2 ^ (prefixWord ++ tailWord_4627777).sum := by decide
  have hdescent : baseEnd_4627777 < baseStart_4627777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627800 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 3, 3, 3]
def baseStart_4627800 : Nat := 118140960795 + 4627800 * 2 ^ 59
def prefixEnd_4627800 : Nat := 4983230072969 + 3 ^ 40 * 4627800 * 2
def baseEnd_4627800 : Nat := 2376285772877098944917141

theorem tailTrace_4627800 : CollatzResearch.WordTrace tailWord_4627800 prefixEnd_4627800 2376285772877098944917141 := by
  unfold tailWord_4627800
  simp only [CollatzResearch.WordTrace]
  refine ⟨84394866317139220080456427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112526488422852293440608569 84394866317139220080456427)
  ·
    refine ⟨126592299475708830120684641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84394866317139220080456427 126592299475708830120684641)
    ·
      refine ⟨94944224606781622590513481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126592299475708830120684641 94944224606781622590513481)
      ·
        refine ⟨71208168455086216942885111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94944224606781622590513481 71208168455086216942885111)
        ·
          refine ⟨106812252682629325414327667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71208168455086216942885111 106812252682629325414327667)
          ·
            refine ⟨160218379023943988121491501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106812252682629325414327667 160218379023943988121491501)
            ·
              refine ⟨60081892133978995545559313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160218379023943988121491501 60081892133978995545559313)
              ·
                refine ⟨45061419100484246659169485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60081892133978995545559313 45061419100484246659169485)
                ·
                  refine ⟨16898032162681592497188557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45061419100484246659169485 16898032162681592497188557)
                  ·
                    refine ⟨6336762061005597186445709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16898032162681592497188557 6336762061005597186445709)
                    ·
                      refine ⟨2376285772877098944917141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6336762061005597186445709 2376285772877098944917141)
                      ·
                        rfl

theorem cell23_4627800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_4627800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627800 prefixEnd_4627800 := by exact prefixLift 4627800
  have htrace : WordTrace (prefixWord ++ tailWord_4627800) baseStart_4627800 baseEnd_4627800 := by
    simpa [prefixWord, tailWord_4627800, baseEnd_4627800] using wordTrace_append hprefix tailTrace_4627800
  have hstable : (prefixWord ++ tailWord_4627800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627800).length < 2 ^ (prefixWord ++ tailWord_4627800).sum := by decide
  have hdescent : baseEnd_4627800 < baseStart_4627800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627838 : List Nat := [4, 2, 3, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_4627838 : Nat := 118140960795 + 4627838 * 2 ^ 59
def prefixEnd_4627838 : Nat := 4983230072969 + 3 ^ 40 * 4627838 * 2
def baseEnd_4627838 : Nat := 2376305285141969796241967

theorem tailTrace_4627838 : CollatzResearch.WordTrace tailWord_4627838 prefixEnd_4627838 2376305285141969796241967 := by
  unfold tailWord_4627838
  simp only [CollatzResearch.WordTrace]
  refine ⟨21098889826017596581349521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112527412405427181767197445 21098889826017596581349521)
  ·
    refine ⟨15824167369513197436012141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21098889826017596581349521 15824167369513197436012141)
    ·
      refine ⟨5934062763567449038504553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15824167369513197436012141 5934062763567449038504553)
      ·
        refine ⟨4450547072675586778878415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5934062763567449038504553 4450547072675586778878415)
        ·
          refine ⟨6675820609013380168317623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4450547072675586778878415 6675820609013380168317623)
          ·
            refine ⟨10013730913520070252476435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6675820609013380168317623 10013730913520070252476435)
            ·
              refine ⟨15020596370280105378714653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10013730913520070252476435 15020596370280105378714653)
              ·
                refine ⟨5632723638855039517017995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15020596370280105378714653 5632723638855039517017995)
                ·
                  refine ⟨8449085458282559275526993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5632723638855039517017995 8449085458282559275526993)
                  ·
                    refine ⟨6336814093711919456645245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8449085458282559275526993 6336814093711919456645245)
                    ·
                      refine ⟨2376305285141969796241967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6336814093711919456645245 2376305285141969796241967)
                      ·
                        rfl

theorem cell23_4627838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_4627838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627838 prefixEnd_4627838 := by exact prefixLift 4627838
  have htrace : WordTrace (prefixWord ++ tailWord_4627838) baseStart_4627838 baseEnd_4627838 := by
    simpa [prefixWord, tailWord_4627838, baseEnd_4627838] using wordTrace_append hprefix tailTrace_4627838
  have hstable : (prefixWord ++ tailWord_4627838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627838).length < 2 ^ (prefixWord ++ tailWord_4627838).sum := by decide
  have hdescent : baseEnd_4627838 < baseStart_4627838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627868 : List Nat := [2, 2, 3, 4, 2, 1, 1, 1, 1, 3, 3]
def baseStart_4627868 : Nat := 118140960795 + 4627868 * 2 ^ 59
def prefixEnd_4627868 : Nat := 4983230072969 + 3 ^ 40 * 4627868 * 2
def baseEnd_4627868 : Nat := 2376320689561604678866829

theorem tailTrace_4627868 : CollatzResearch.WordTrace tailWord_4627868 prefixEnd_4627868 2376320689561604678866829 := by
  unfold tailWord_4627868
  simp only [CollatzResearch.WordTrace]
  refine ⟨84396106399016043887194129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112528141865354725182925505 84396106399016043887194129)
  ·
    refine ⟨63297079799262032915395597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84396106399016043887194129 63297079799262032915395597)
    ·
      refine ⟨23736404924723262343273349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63297079799262032915395597 23736404924723262343273349)
      ·
        refine ⟨4450575923385611689363753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23736404924723262343273349 4450575923385611689363753)
        ·
          refine ⟨3337931942539208767022815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4450575923385611689363753 3337931942539208767022815)
          ·
            refine ⟨5006897913808813150534223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3337931942539208767022815 5006897913808813150534223)
            ·
              refine ⟨7510346870713219725801335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5006897913808813150534223 7510346870713219725801335)
              ·
                refine ⟨11265520306069829588702003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7510346870713219725801335 11265520306069829588702003)
                ·
                  refine ⟨16898280459104744383053005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11265520306069829588702003 16898280459104744383053005)
                  ·
                    refine ⟨6336855172164279143644877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16898280459104744383053005 6336855172164279143644877)
                    ·
                      refine ⟨2376320689561604678866829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6336855172164279143644877 2376320689561604678866829)
                      ·
                        rfl

theorem cell23_4627868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_4627868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627868 prefixEnd_4627868 := by exact prefixLift 4627868
  have htrace : WordTrace (prefixWord ++ tailWord_4627868) baseStart_4627868 baseEnd_4627868 := by
    simpa [prefixWord, tailWord_4627868, baseEnd_4627868] using wordTrace_append hprefix tailTrace_4627868
  have hstable : (prefixWord ++ tailWord_4627868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627868).length < 2 ^ (prefixWord ++ tailWord_4627868).sum := by decide
  have hdescent : baseEnd_4627868 < baseStart_4627868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627920 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 5]
def baseStart_4627920 : Nat := 118140960795 + 4627920 * 2 ^ 59
def prefixEnd_4627920 : Nat := 4983230072969 + 3 ^ 40 * 4627920 * 2
def baseEnd_4627920 : Nat := 2376347390555638475416589

theorem tailTrace_4627920 : CollatzResearch.WordTrace tailWord_4627920 prefixEnd_4627920 2376347390555638475416589 := by
  unfold tailWord_4627920
  simp only [CollatzResearch.WordTrace]
  refine ⟨84397054696921850327640607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112529406262562467103520809 84397054696921850327640607)
  ·
    refine ⟨126595582045382775491460911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84397054696921850327640607 126595582045382775491460911)
    ·
      refine ⟨189893373068074163237191367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126595582045382775491460911 189893373068074163237191367)
      ·
        refine ⟨284840059602111244855787051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189893373068074163237191367 284840059602111244855787051)
        ·
          refine ⟨427260089403166867283680577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284840059602111244855787051 427260089403166867283680577)
          ·
            refine ⟨320445067052375150462760433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 427260089403166867283680577 320445067052375150462760433)
            ·
              refine ⟨240333800289281362847070325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320445067052375150462760433 240333800289281362847070325)
              ·
                refine ⟨22531293777120127766912843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 240333800289281362847070325 22531293777120127766912843)
                ·
                  refine ⟨33796940665680191650369265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22531293777120127766912843 33796940665680191650369265)
                  ·
                    refine ⟨25347705499260143737776949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33796940665680191650369265 25347705499260143737776949)
                    ·
                      refine ⟨2376347390555638475416589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25347705499260143737776949 2376347390555638475416589)
                      ·
                        rfl

theorem cell23_4627920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_4627920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627920 prefixEnd_4627920 := by exact prefixLift 4627920
  have htrace : WordTrace (prefixWord ++ tailWord_4627920) baseStart_4627920 baseEnd_4627920 := by
    simpa [prefixWord, tailWord_4627920, baseEnd_4627920] using wordTrace_append hprefix tailTrace_4627920
  have hstable : (prefixWord ++ tailWord_4627920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627920).length < 2 ^ (prefixWord ++ tailWord_4627920).sum := by decide
  have hdescent : baseEnd_4627920 < baseStart_4627920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627940 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 2, 8]
def baseStart_4627940 : Nat := 118140960795 + 4627940 * 2 ^ 59
def prefixEnd_4627940 : Nat := 4983230072969 + 3 ^ 40 * 4627940 * 2
def baseEnd_4627940 : Nat := 792119220056242799055499

theorem tailTrace_4627940 : CollatzResearch.WordTrace tailWord_4627940 prefixEnd_4627940 792119220056242799055499 := by
  unfold tailWord_4627940
  simp only [CollatzResearch.WordTrace]
  refine ⟨84397419426885622035504637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112529892569180829380672849 84397419426885622035504637)
  ·
    refine ⟨31649032285082108263314239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84397419426885622035504637 31649032285082108263314239)
    ·
      refine ⟨47473548427623162394971359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31649032285082108263314239 47473548427623162394971359)
      ·
        refine ⟨71210322641434743592457039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47473548427623162394971359 71210322641434743592457039)
        ·
          refine ⟨106815483962152115388685559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71210322641434743592457039 106815483962152115388685559)
          ·
            refine ⟨160223225943228173083028339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106815483962152115388685559 160223225943228173083028339)
            ·
              refine ⟨240334838914842259624542509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160223225943228173083028339 240334838914842259624542509)
              ·
                refine ⟨90125564593065847359203441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 240334838914842259624542509 90125564593065847359203441)
                ·
                  refine ⟨67594173444799385519402581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90125564593065847359203441 67594173444799385519402581)
                  ·
                    refine ⟨792119220056242799055499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67594173444799385519402581 792119220056242799055499)
                    ·
                      rfl

theorem cell23_4627940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_4627940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627940 prefixEnd_4627940 := by exact prefixLift 4627940
  have htrace : WordTrace (prefixWord ++ tailWord_4627940) baseStart_4627940 baseEnd_4627940 := by
    simpa [prefixWord, tailWord_4627940, baseEnd_4627940] using wordTrace_append hprefix tailTrace_4627940
  have hstable : (prefixWord ++ tailWord_4627940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627940).length < 2 ^ (prefixWord ++ tailWord_4627940).sum := by decide
  have hdescent : baseEnd_4627940 < baseStart_4627940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627947 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 3, 6, 2]
def baseStart_4627947 : Nat := 118140960795 + 4627947 * 2 ^ 59
def prefixEnd_4627947 : Nat := 4983230072969 + 3 ^ 40 * 4627947 * 2
def baseEnd_4627947 : Nat := 2376361254533309869778965

theorem tailTrace_4627947 : CollatzResearch.WordTrace tailWord_4627947 prefixEnd_4627947 2376361254533309869778965 := by
  unfold tailWord_4627947
  simp only [CollatzResearch.WordTrace]
  refine ⟨168795094164745884266514095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112530062776497256177676063 168795094164745884266514095)
  ·
    refine ⟨253192641247118826399771143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168795094164745884266514095 253192641247118826399771143)
    ·
      refine ⟨379788961870678239599656715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253192641247118826399771143 379788961870678239599656715)
      ·
        refine ⟨569683442806017359399485073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379788961870678239599656715 569683442806017359399485073)
        ·
          refine ⟨427262582104513019549613805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 569683442806017359399485073 427262582104513019549613805)
          ·
            refine ⟨160223468289192382331105177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 427262582104513019549613805 160223468289192382331105177)
            ·
              refine ⟨120167601216894286748328883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160223468289192382331105177 120167601216894286748328883)
              ·
                refine ⟨180251401825341430122493325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120167601216894286748328883 180251401825341430122493325)
                ·
                  refine ⟨67594275684503036295934997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180251401825341430122493325 67594275684503036295934997)
                  ·
                    refine ⟨3168481672711079826371953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67594275684503036295934997 3168481672711079826371953)
                    ·
                      refine ⟨2376361254533309869778965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3168481672711079826371953 2376361254533309869778965)
                      ·
                        rfl

theorem cell23_4627947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 6, 2].length) (baseStart_4627947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627947 prefixEnd_4627947 := by exact prefixLift 4627947
  have htrace : WordTrace (prefixWord ++ tailWord_4627947) baseStart_4627947 baseEnd_4627947 := by
    simpa [prefixWord, tailWord_4627947, baseEnd_4627947] using wordTrace_append hprefix tailTrace_4627947
  have hstable : (prefixWord ++ tailWord_4627947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627947).length < 2 ^ (prefixWord ++ tailWord_4627947).sum := by decide
  have hdescent : baseEnd_4627947 < baseStart_4627947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627967 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 3]
def baseStart_4627967 : Nat := 118140960795 + 4627967 * 2 ^ 59
def prefixEnd_4627967 : Nat := 4983230072969 + 3 ^ 40 * 4627967 * 2
def baseEnd_4627967 : Nat := 2376371524146399791528873

theorem tailTrace_4627967 : CollatzResearch.WordTrace tailWord_4627967 prefixEnd_4627967 2376371524146399791528873 := by
  unfold tailWord_4627967
  simp only [CollatzResearch.WordTrace]
  refine ⟨168795823624673427682242155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112530549083115618454828103 168795823624673427682242155)
  ·
    refine ⟨253193735437010141523363233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168795823624673427682242155 253193735437010141523363233)
    ·
      refine ⟨189895301577757606142522425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253193735437010141523363233 189895301577757606142522425)
      ·
        refine ⟨142421476183318204606891819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189895301577757606142522425 142421476183318204606891819)
        ·
          refine ⟨213632214274977306910337729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142421476183318204606891819 213632214274977306910337729)
          ·
            refine ⟨160224160706232980182753297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213632214274977306910337729 160224160706232980182753297)
            ·
              refine ⟨120168120529674735137064973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160224160706232980182753297 120168120529674735137064973)
              ·
                refine ⟨45063045198628025676399365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120168120529674735137064973 45063045198628025676399365)
                ·
                  refine ⟨8449320974742754814324881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45063045198628025676399365 8449320974742754814324881)
                  ·
                    refine ⟨6336990731057066110743661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8449320974742754814324881 6336990731057066110743661)
                    ·
                      refine ⟨2376371524146399791528873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6336990731057066110743661 2376371524146399791528873)
                      ·
                        rfl

theorem cell23_4627967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_4627967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627967 prefixEnd_4627967 := by exact prefixLift 4627967
  have htrace : WordTrace (prefixWord ++ tailWord_4627967) baseStart_4627967 baseEnd_4627967 := by
    simpa [prefixWord, tailWord_4627967, baseEnd_4627967] using wordTrace_append hprefix tailTrace_4627967
  have hstable : (prefixWord ++ tailWord_4627967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627967).length < 2 ^ (prefixWord ++ tailWord_4627967).sum := by decide
  have hdescent : baseEnd_4627967 < baseStart_4627967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4627987 : List Nat := [1, 1, 1, 2, 1, 6, 2, 3, 6]
def baseStart_4627987 : Nat := 118140960795 + 4627987 * 2 ^ 59
def prefixEnd_4627987 : Nat := 4983230072969 + 3 ^ 40 * 4627987 * 2
def baseEnd_4627987 : Nat := 264042421528832190364309

theorem tailTrace_4627987 : CollatzResearch.WordTrace tailWord_4627987 prefixEnd_4627987 264042421528832190364309 := by
  unfold tailWord_4627987
  simp only [CollatzResearch.WordTrace]
  refine ⟨168796553084600971097970215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112531035389733980731980143 168796553084600971097970215)
  ·
    refine ⟨253194829626901456646955323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168796553084600971097970215 253194829626901456646955323)
    ·
      refine ⟨379792244440352184970432985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253194829626901456646955323 379792244440352184970432985)
      ·
        refine ⟨284844183330264138727824739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 379792244440352184970432985 284844183330264138727824739)
        ·
          refine ⟨427266274995396208091737109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284844183330264138727824739 427266274995396208091737109)
          ·
            refine ⟨20028106640409197254300177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 427266274995396208091737109 20028106640409197254300177)
            ·
              refine ⟨15021079980306897940725133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20028106640409197254300177 15021079980306897940725133)
              ·
                refine ⟨5632904992615086727771925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15021079980306897940725133 5632904992615086727771925)
                ·
                  refine ⟨264042421528832190364309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5632904992615086727771925 264042421528832190364309)
                  ·
                    rfl

theorem cell23_4627987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 6].length) (baseStart_4627987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4627987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4627987 prefixEnd_4627987 := by exact prefixLift 4627987
  have htrace : WordTrace (prefixWord ++ tailWord_4627987) baseStart_4627987 baseEnd_4627987 := by
    simpa [prefixWord, tailWord_4627987, baseEnd_4627987] using wordTrace_append hprefix tailTrace_4627987
  have hstable : (prefixWord ++ tailWord_4627987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4627987).length < 2 ^ (prefixWord ++ tailWord_4627987).sum := by decide
  have hdescent : baseEnd_4627987 < baseStart_4627987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4627987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628001 : List Nat := [1, 2, 3, 2, 2, 4, 1, 1, 2, 2, 3]
def baseStart_4628001 : Nat := 118140960795 + 4628001 * 2 ^ 59
def prefixEnd_4628001 : Nat := 4983230072969 + 3 ^ 40 * 4628001 * 2
def baseEnd_4628001 : Nat := 2376388982488652658503717

theorem tailTrace_4628001 : CollatzResearch.WordTrace tailWord_4628001 prefixEnd_4628001 2376388982488652658503717 := by
  unfold tailWord_4628001
  simp only [CollatzResearch.WordTrace]
  refine ⟨168797063706550251488979857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112531375804366834325986571 168797063706550251488979857)
  ·
    refine ⟨126597797779912688616734893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168797063706550251488979857 126597797779912688616734893)
    ·
      refine ⟨47474174167467258231275585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126597797779912688616734893 47474174167467258231275585)
      ·
        refine ⟨35605630625600443673456689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47474174167467258231275585 35605630625600443673456689)
        ·
          refine ⟨26704222969200332755092517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35605630625600443673456689 26704222969200332755092517)
          ·
            refine ⟨5007041806725062391579847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26704222969200332755092517 5007041806725062391579847)
            ·
              refine ⟨7510562710087593587369771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5007041806725062391579847 7510562710087593587369771)
              ·
                refine ⟨11265844065131390381054657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7510562710087593587369771 11265844065131390381054657)
                ·
                  refine ⟨8449383048848542785790993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11265844065131390381054657 8449383048848542785790993)
                  ·
                    refine ⟨6337037286636407089343245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8449383048848542785790993 6337037286636407089343245)
                    ·
                      refine ⟨2376388982488652658503717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6337037286636407089343245 2376388982488652658503717)
                      ·
                        rfl

theorem cell23_4628001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_4628001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628001 prefixEnd_4628001 := by exact prefixLift 4628001
  have htrace : WordTrace (prefixWord ++ tailWord_4628001) baseStart_4628001 baseEnd_4628001 := by
    simpa [prefixWord, tailWord_4628001, baseEnd_4628001] using wordTrace_append hprefix tailTrace_4628001
  have hstable : (prefixWord ++ tailWord_4628001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628001).length < 2 ^ (prefixWord ++ tailWord_4628001).sum := by decide
  have hdescent : baseEnd_4628001 < baseStart_4628001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628031 : List Nat := [1, 1, 2, 2, 3, 4, 2, 1, 3, 1, 3]
def baseStart_4628031 : Nat := 118140960795 + 4628031 * 2 ^ 59
def prefixEnd_4628031 : Nat := 4983230072969 + 3 ^ 40 * 4628031 * 2
def baseEnd_4628031 : Nat := 2376404386908287541128579

theorem tailTrace_4628031 : CollatzResearch.WordTrace tailWord_4628031 prefixEnd_4628031 2376404386908287541128579 := by
  unfold tailWord_4628031
  simp only [CollatzResearch.WordTrace]
  refine ⟨168798157896441566612571947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112532105264294377741714631 168798157896441566612571947)
  ·
    refine ⟨253197236844662349918857921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168798157896441566612571947 253197236844662349918857921)
    ·
      refine ⟨189897927633496762439143441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253197236844662349918857921 189897927633496762439143441)
      ·
        refine ⟨142423445725122571829357581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189897927633496762439143441 142423445725122571829357581)
        ·
          refine ⟨53408792146920964436009093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142423445725122571829357581 53408792146920964436009093)
          ·
            refine ⟨10014148527547680831751705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53408792146920964436009093 10014148527547680831751705)
            ·
              refine ⟨7510611395660760623813779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10014148527547680831751705 7510611395660760623813779)
              ·
                refine ⟨11265917093491140935720669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7510611395660760623813779 11265917093491140935720669)
                ·
                  refine ⟨4224718910059177850895251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11265917093491140935720669 4224718910059177850895251)
                  ·
                    refine ⟨6337078365088766776342877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4224718910059177850895251 6337078365088766776342877)
                    ·
                      refine ⟨2376404386908287541128579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6337078365088766776342877 2376404386908287541128579)
                      ·
                        rfl

theorem cell23_4628031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 1, 3].length) (baseStart_4628031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628031 prefixEnd_4628031 := by exact prefixLift 4628031
  have htrace : WordTrace (prefixWord ++ tailWord_4628031) baseStart_4628031 baseEnd_4628031 := by
    simpa [prefixWord, tailWord_4628031, baseEnd_4628031] using wordTrace_append hprefix tailTrace_4628031
  have hstable : (prefixWord ++ tailWord_4628031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628031).length < 2 ^ (prefixWord ++ tailWord_4628031).sum := by decide
  have hdescent : baseEnd_4628031 < baseStart_4628031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628057 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 2, 6, 3]
def baseStart_4628057 : Nat := 118140960795 + 4628057 * 2 ^ 59
def prefixEnd_4628057 : Nat := 4983230072969 + 3 ^ 40 * 4628057 * 2
def baseEnd_4628057 : Nat := 2376417737405304439403459

theorem tailTrace_4628057 : CollatzResearch.WordTrace tailWord_4628057 prefixEnd_4628057 2376417737405304439403459 := by
  unfold tailWord_4628057
  simp only [CollatzResearch.WordTrace]
  refine ⟨168799106194347373053018425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112532737462898248702012283 168799106194347373053018425)
  ·
    refine ⟨126599329645760529789763819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168799106194347373053018425 126599329645760529789763819)
    ·
      refine ⟨189898994468640794684645729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126599329645760529789763819 189898994468640794684645729)
      ·
        refine ⟨142424245851480596013484297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189898994468640794684645729 142424245851480596013484297)
        ·
          refine ⟨106818184388610447010113223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142424245851480596013484297 106818184388610447010113223)
          ·
            refine ⟨160227276582915670515169835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106818184388610447010113223 160227276582915670515169835)
            ·
              refine ⟨240340914874373505772754753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160227276582915670515169835 240340914874373505772754753)
              ·
                refine ⟨180255686155780129329566065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240340914874373505772754753 180255686155780129329566065)
                ·
                  refine ⟨135191764616835096997174549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180255686155780129329566065 135191764616835096997174549)
                  ·
                    refine ⟨6337113966414145171742557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 135191764616835096997174549 6337113966414145171742557)
                    ·
                      refine ⟨2376417737405304439403459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6337113966414145171742557 2376417737405304439403459)
                      ·
                        rfl

theorem cell23_4628057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_4628057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628057 prefixEnd_4628057 := by exact prefixLift 4628057
  have htrace : WordTrace (prefixWord ++ tailWord_4628057) baseStart_4628057 baseEnd_4628057 := by
    simpa [prefixWord, tailWord_4628057, baseEnd_4628057] using wordTrace_append hprefix tailTrace_4628057
  have hstable : (prefixWord ++ tailWord_4628057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628057).length < 2 ^ (prefixWord ++ tailWord_4628057).sum := by decide
  have hdescent : baseEnd_4628057 < baseStart_4628057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628071 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 5, 2, 2]
def baseStart_4628071 : Nat := 118140960795 + 4628071 * 2 ^ 59
def prefixEnd_4628071 : Nat := 4983230072969 + 3 ^ 40 * 4628071 * 2
def baseEnd_4628071 : Nat := 2376424926134467384628395

theorem tailTrace_4628071 : CollatzResearch.WordTrace tailWord_4628071 prefixEnd_4628071 2376424926134467384628395 := by
  unfold tailWord_4628071
  simp only [CollatzResearch.WordTrace]
  refine ⟨168799616816296653444028067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112533077877531102296018711 168799616816296653444028067)
  ·
    refine ⟨253199425224444980166042101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168799616816296653444028067 253199425224444980166042101)
    ·
      refine ⟨23737446114791716890566447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 253199425224444980166042101 23737446114791716890566447)
      ·
        refine ⟨35606169172187575335849671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23737446114791716890566447 35606169172187575335849671)
        ·
          refine ⟨53409253758281363003774507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35606169172187575335849671 53409253758281363003774507)
          ·
            refine ⟨80113880637422044505661761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53409253758281363003774507 80113880637422044505661761)
            ·
              refine ⟨60085410478066533379246321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80113880637422044505661761 60085410478066533379246321)
              ·
                refine ⟨45064057858549900034434741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60085410478066533379246321 45064057858549900034434741)
                ·
                  refine ⟨4224755424239053128228257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45064057858549900034434741 4224755424239053128228257)
                  ·
                    refine ⟨3168566568179289846171193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4224755424239053128228257 3168566568179289846171193)
                    ·
                      refine ⟨2376424926134467384628395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3168566568179289846171193 2376424926134467384628395)
                      ·
                        rfl

theorem cell23_4628071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_4628071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628071 prefixEnd_4628071 := by exact prefixLift 4628071
  have htrace : WordTrace (prefixWord ++ tailWord_4628071) baseStart_4628071 baseEnd_4628071 := by
    simpa [prefixWord, tailWord_4628071, baseEnd_4628071] using wordTrace_append hprefix tailTrace_4628071
  have hstable : (prefixWord ++ tailWord_4628071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628071).length < 2 ^ (prefixWord ++ tailWord_4628071).sum := by decide
  have hdescent : baseEnd_4628071 < baseStart_4628071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628074 : List Nat := [3, 1, 3, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_4628074 : Nat := 118140960795 + 4628074 * 2 ^ 59
def prefixEnd_4628074 : Nat := 4983230072969 + 3 ^ 40 * 4628074 * 2
def baseEnd_4628074 : Nat := 2376426466576430872890881

theorem tailTrace_4628074 : CollatzResearch.WordTrace tailWord_4628074 prefixEnd_4628074 2376426466576430872890881 := by
  unfold tailWord_4628074
  simp only [CollatzResearch.WordTrace]
  refine ⟨42199931558821446239096819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112533150823523856637591517 42199931558821446239096819)
  ·
    refine ⟨63299897338232169358645229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42199931558821446239096819 63299897338232169358645229)
    ·
      refine ⟨23737461501837063509491961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63299897338232169358645229 23737461501837063509491961)
      ·
        refine ⟨17803096126377797632118971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23737461501837063509491961 17803096126377797632118971)
        ·
          refine ⟨26704644189566696448178457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17803096126377797632118971 26704644189566696448178457)
          ·
            refine ⟨20028483142175022336133843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26704644189566696448178457 20028483142175022336133843)
            ·
              refine ⟨30042724713262533504200765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20028483142175022336133843 30042724713262533504200765)
              ·
                refine ⟨11266021767473450064075287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30042724713262533504200765 11266021767473450064075287)
                ·
                  refine ⟨16899032651210175096112931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11266021767473450064075287 16899032651210175096112931)
                  ·
                    refine ⟨25348548976815262644169397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16899032651210175096112931 25348548976815262644169397)
                    ·
                      refine ⟨2376426466576430872890881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25348548976815262644169397 2376426466576430872890881)
                      ·
                        rfl

theorem cell23_4628074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_4628074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628074 prefixEnd_4628074 := by exact prefixLift 4628074
  have htrace : WordTrace (prefixWord ++ tailWord_4628074) baseStart_4628074 baseEnd_4628074 := by
    simpa [prefixWord, tailWord_4628074, baseEnd_4628074] using wordTrace_append hprefix tailTrace_4628074
  have hstable : (prefixWord ++ tailWord_4628074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628074).length < 2 ^ (prefixWord ++ tailWord_4628074).sum := by decide
  have hdescent : baseEnd_4628074 < baseStart_4628074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628117 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_4628117 : Nat := 118140960795 + 4628117 * 2 ^ 59
def prefixEnd_4628117 : Nat := 4983230072969 + 3 ^ 40 * 4628117 * 2
def baseEnd_4628117 : Nat := 2376448546244574204653183

theorem tailTrace_4628117 : CollatzResearch.WordTrace tailWord_4628117 prefixEnd_4628117 2376448546244574204653183 := by
  unfold tailWord_4628117
  simp only [CollatzResearch.WordTrace]
  refine ⟨168801294574130003300202605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112534196382753335533468403 168801294574130003300202605)
  ·
    refine ⟨63300485465298751237575977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168801294574130003300202605 63300485465298751237575977)
    ·
      refine ⟨47475364098974063428181983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63300485465298751237575977 47475364098974063428181983)
      ·
        refine ⟨71213046148461095142272975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47475364098974063428181983 71213046148461095142272975)
        ·
          refine ⟨106819569222691642713409463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71213046148461095142272975 106819569222691642713409463)
          ·
            refine ⟨160229353834037464070114195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106819569222691642713409463 160229353834037464070114195)
            ·
              refine ⟨240344030751056196105171293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160229353834037464070114195 240344030751056196105171293)
              ·
                refine ⟨90129011531646073539439235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 240344030751056196105171293 90129011531646073539439235)
                ·
                  refine ⟨135193517297469110309158853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90129011531646073539439235 135193517297469110309158853)
                  ·
                    refine ⟨25348784493275458182967285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 135193517297469110309158853 25348784493275458182967285)
                    ·
                      refine ⟨2376448546244574204653183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25348784493275458182967285 2376448546244574204653183)
                      ·
                        rfl

theorem cell23_4628117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_4628117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628117 prefixEnd_4628117 := by exact prefixLift 4628117
  have htrace : WordTrace (prefixWord ++ tailWord_4628117) baseStart_4628117 baseEnd_4628117 := by
    simpa [prefixWord, tailWord_4628117, baseEnd_4628117] using wordTrace_append hprefix tailTrace_4628117
  have hstable : (prefixWord ++ tailWord_4628117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628117).length < 2 ^ (prefixWord ++ tailWord_4628117).sum := by decide
  have hdescent : baseEnd_4628117 < baseStart_4628117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628154 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 2, 6]
def baseStart_4628154 : Nat := 118140960795 + 4628154 * 2 ^ 59
def prefixEnd_4628154 : Nat := 4983230072969 + 3 ^ 40 * 4628154 * 2
def baseEnd_4628154 : Nat := 792155848342930186630171

theorem tailTrace_4628154 : CollatzResearch.WordTrace tailWord_4628154 prefixEnd_4628154 792155848342930186630171 := by
  unfold tailWord_4628154
  simp only [CollatzResearch.WordTrace]
  refine ⟨42200661018748989654824879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112535096049997305746199677 42200661018748989654824879)
  ·
    refine ⟨63300991528123484482237319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42200661018748989654824879 63300991528123484482237319)
    ·
      refine ⟨94951487292185226723355979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63300991528123484482237319 94951487292185226723355979)
      ·
        refine ⟨142427230938277840085033969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94951487292185226723355979 142427230938277840085033969)
        ·
          refine ⟨106820423203708380063775477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142427230938277840085033969 106820423203708380063775477)
          ·
            refine ⟨10014414675347660630978951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106820423203708380063775477 10014414675347660630978951)
            ·
              refine ⟨15021622013021490946468427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10014414675347660630978951 15021622013021490946468427)
              ·
                refine ⟨22532433019532236419702641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15021622013021490946468427 22532433019532236419702641)
                ·
                  refine ⟨16899324764649177314776981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22532433019532236419702641 16899324764649177314776981)
                  ·
                    refine ⟨792155848342930186630171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16899324764649177314776981 792155848342930186630171)
                    ·
                      rfl

theorem cell23_4628154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_4628154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628154 prefixEnd_4628154 := by exact prefixLift 4628154
  have htrace : WordTrace (prefixWord ++ tailWord_4628154) baseStart_4628154 baseEnd_4628154 := by
    simpa [prefixWord, tailWord_4628154, baseEnd_4628154] using wordTrace_append hprefix tailTrace_4628154
  have hstable : (prefixWord ++ tailWord_4628154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628154).length < 2 ^ (prefixWord ++ tailWord_4628154).sum := by decide
  have hdescent : baseEnd_4628154 < baseStart_4628154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628174 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_4628174 : Nat := 118140960795 + 4628174 * 2 ^ 59
def prefixEnd_4628174 : Nat := 4983230072969 + 3 ^ 40 * 4628174 * 2
def baseEnd_4628174 : Nat := 2376477814641880481640421

theorem tailTrace_4628174 : CollatzResearch.WordTrace tailWord_4628174 prefixEnd_4628174 2376477814641880481640421 := by
  unfold tailWord_4628174
  simp only [CollatzResearch.WordTrace]
  refine ⟨21100421691865437754378447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112535582356615668023351717 21100421691865437754378447)
  ·
    refine ⟨31650632537798156631567671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21100421691865437754378447 31650632537798156631567671)
    ·
      refine ⟨47475948806697234947351507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31650632537798156631567671 47475948806697234947351507)
      ·
        refine ⟨71213923210045852421027261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47475948806697234947351507 71213923210045852421027261)
        ·
          refine ⟨26705221203767194657885223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71213923210045852421027261 26705221203767194657885223)
          ·
            refine ⟨40057831805650791986827835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26705221203767194657885223 40057831805650791986827835)
            ·
              refine ⟨60086747708476187980241753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40057831805650791986827835 60086747708476187980241753)
              ·
                refine ⟨45065060781357140985181315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60086747708476187980241753 45065060781357140985181315)
                ·
                  refine ⟨67597591172035711477771973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45065060781357140985181315 67597591172035711477771973)
                  ·
                    refine ⟨12674548344756695902082245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67597591172035711477771973 12674548344756695902082245)
                    ·
                      refine ⟨2376477814641880481640421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12674548344756695902082245 2376477814641880481640421)
                      ·
                        rfl

theorem cell23_4628174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_4628174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628174 prefixEnd_4628174 := by exact prefixLift 4628174
  have htrace : WordTrace (prefixWord ++ tailWord_4628174) baseStart_4628174 baseEnd_4628174 := by
    simpa [prefixWord, tailWord_4628174, baseEnd_4628174] using wordTrace_append hprefix tailTrace_4628174
  have hstable : (prefixWord ++ tailWord_4628174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628174).length < 2 ^ (prefixWord ++ tailWord_4628174).sum := by decide
  have hdescent : baseEnd_4628174 < baseStart_4628174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628178 : List Nat := [3, 2, 2, 2, 2, 1, 2, 2, 1, 4, 2]
def baseStart_4628178 : Nat := 118140960795 + 4628178 * 2 ^ 59
def prefixEnd_4628178 : Nat := 4983230072969 + 3 ^ 40 * 4628178 * 2
def baseEnd_4628178 : Nat := 2376479868564498465990403

theorem tailTrace_4628178 : CollatzResearch.WordTrace tailWord_4628178 prefixEnd_4628178 2376479868564498465990403 := by
  unfold tailWord_4628178
  simp only [CollatzResearch.WordTrace]
  refine ⟨42200879856727252679543297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112535679617939340478782125 42200879856727252679543297)
  ·
    refine ⟨31650659892545439509657473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42200879856727252679543297 31650659892545439509657473)
    ·
      refine ⟨23737994919409079632243105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31650659892545439509657473 23737994919409079632243105)
      ·
        refine ⟨17803496189556809724182329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23737994919409079632243105 17803496189556809724182329)
        ·
          refine ⟨13352622142167607293136747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17803496189556809724182329 13352622142167607293136747)
          ·
            refine ⟨20028933213251410939705121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13352622142167607293136747 20028933213251410939705121)
            ·
              refine ⟨15021699909938558204778841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20028933213251410939705121 15021699909938558204778841)
              ·
                refine ⟨11266274932453918653584131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15021699909938558204778841 11266274932453918653584131)
                ·
                  refine ⟨16899412398680877980376197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11266274932453918653584131 16899412398680877980376197)
                  ·
                    refine ⟨3168639824752664621320537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16899412398680877980376197 3168639824752664621320537)
                    ·
                      refine ⟨2376479868564498465990403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3168639824752664621320537 2376479868564498465990403)
                      ·
                        rfl

theorem cell23_4628178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_4628178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628178 prefixEnd_4628178 := by exact prefixLift 4628178
  have htrace : WordTrace (prefixWord ++ tailWord_4628178) baseStart_4628178 baseEnd_4628178 := by
    simpa [prefixWord, tailWord_4628178, baseEnd_4628178] using wordTrace_append hprefix tailTrace_4628178
  have hstable : (prefixWord ++ tailWord_4628178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628178).length < 2 ^ (prefixWord ++ tailWord_4628178).sum := by decide
  have hdescent : baseEnd_4628178 < baseStart_4628178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628187 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 6]
def baseStart_4628187 : Nat := 118140960795 + 4628187 * 2 ^ 59
def prefixEnd_4628187 : Nat := 4983230072969 + 3 ^ 40 * 4628187 * 2
def baseEnd_4628187 : Nat := 2376484489890388930777861

theorem tailTrace_4628187 : CollatzResearch.WordTrace tailWord_4628187 prefixEnd_4628187 2376484489890388930777861 := by
  unfold tailWord_4628187
  simp only [CollatzResearch.WordTrace]
  refine ⟨168803847683876405255250815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112535898455917603503500543 168803847683876405255250815)
  ·
    refine ⟨253205771525814607882876223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168803847683876405255250815 253205771525814607882876223)
    ·
      refine ⟨379808657288721911824314335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253205771525814607882876223 379808657288721911824314335)
      ·
        refine ⟨569712985933082867736471503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379808657288721911824314335 569712985933082867736471503)
        ·
          refine ⟨854569478899624301604707255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569712985933082867736471503 854569478899624301604707255)
          ·
            refine ⟨1281854218349436452407060883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854569478899624301604707255 1281854218349436452407060883)
            ·
              refine ⟨1922781327524154678610591325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281854218349436452407060883 1922781327524154678610591325)
              ·
                refine ⟨721042997821558004478971747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1922781327524154678610591325 721042997821558004478971747)
                ·
                  refine ⟨1081564496732337006718457621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721042997821558004478971747 1081564496732337006718457621)
                  ·
                    refine ⟨50698335784328297189927701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1081564496732337006718457621 50698335784328297189927701)
                    ·
                      refine ⟨2376484489890388930777861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50698335784328297189927701 2376484489890388930777861)
                      ·
                        rfl

theorem cell23_4628187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 6].length) (baseStart_4628187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628187 prefixEnd_4628187 := by exact prefixLift 4628187
  have htrace : WordTrace (prefixWord ++ tailWord_4628187) baseStart_4628187 baseEnd_4628187 := by
    simpa [prefixWord, tailWord_4628187, baseEnd_4628187] using wordTrace_append hprefix tailTrace_4628187
  have hstable : (prefixWord ++ tailWord_4628187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628187).length < 2 ^ (prefixWord ++ tailWord_4628187).sum := by decide
  have hdescent : baseEnd_4628187 < baseStart_4628187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628189 : List Nat := [1, 4, 3, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_4628189 : Nat := 118140960795 + 4628189 * 2 ^ 59
def prefixEnd_4628189 : Nat := 4983230072969 + 3 ^ 40 * 4628189 * 2
def baseEnd_4628189 : Nat := 2376485516851697922952853

theorem tailTrace_4628189 : CollatzResearch.WordTrace tailWord_4628189 prefixEnd_4628189 2376485516851697922952853 := by
  unfold tailWord_4628189
  simp only [CollatzResearch.WordTrace]
  refine ⟨168803920629869159596823621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112535947086579439731215747 168803920629869159596823621)
  ·
    refine ⟨31650735118100467424404429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168803920629869159596823621 31650735118100467424404429)
    ·
      refine ⟨11869025669287675284151661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31650735118100467424404429 11869025669287675284151661)
      ·
        refine ⟨4450884625982878231556873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11869025669287675284151661 4450884625982878231556873)
        ·
          refine ⟨3338163469487158673667655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4450884625982878231556873 3338163469487158673667655)
          ·
            refine ⟨5007245204230738010501483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3338163469487158673667655 5007245204230738010501483)
            ·
              refine ⟨7510867806346107015752225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5007245204230738010501483 7510867806346107015752225)
              ·
                refine ⟨5633150854759580261814169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7510867806346107015752225 5633150854759580261814169)
                ·
                  refine ⟨4224863141069685196360627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5633150854759580261814169 4224863141069685196360627)
                  ·
                    refine ⟨6337294711604527794540941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4224863141069685196360627 6337294711604527794540941)
                    ·
                      refine ⟨2376485516851697922952853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6337294711604527794540941 2376485516851697922952853)
                      ·
                        rfl

theorem cell23_4628189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_4628189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628189 prefixEnd_4628189 := by exact prefixLift 4628189
  have htrace : WordTrace (prefixWord ++ tailWord_4628189) baseStart_4628189 baseEnd_4628189 := by
    simpa [prefixWord, tailWord_4628189, baseEnd_4628189] using wordTrace_append hprefix tailTrace_4628189
  have hstable : (prefixWord ++ tailWord_4628189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628189).length < 2 ^ (prefixWord ++ tailWord_4628189).sum := by decide
  have hdescent : baseEnd_4628189 < baseStart_4628189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628195 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 4, 2, 2]
def baseStart_4628195 : Nat := 118140960795 + 4628195 * 2 ^ 59
def prefixEnd_4628195 : Nat := 4983230072969 + 3 ^ 40 * 4628195 * 2
def baseEnd_4628195 : Nat := 2376488597735624899477825

theorem tailTrace_4628195 : CollatzResearch.WordTrace tailWord_4628195 prefixEnd_4628195 2376488597735624899477825 := by
  unfold tailWord_4628195
  simp only [CollatzResearch.WordTrace]
  refine ⟨168804139467847422621542039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112536092978564948414361359 168804139467847422621542039)
  ·
    refine ⟨253206209201771133932313059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168804139467847422621542039 253206209201771133932313059)
    ·
      refine ⟨379809313802656700898469589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253206209201771133932313059 379809313802656700898469589)
      ·
        refine ⟨8901780792249766427307881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 379809313802656700898469589 8901780792249766427307881)
        ·
          refine ⟨6676335594187324820480911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8901780792249766427307881 6676335594187324820480911)
          ·
            refine ⟨10014503391280987230721367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6676335594187324820480911 10014503391280987230721367)
            ·
              refine ⟨15021755086921480846082051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10014503391280987230721367 15021755086921480846082051)
              ·
                refine ⟨22532632630382221269123077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15021755086921480846082051 22532632630382221269123077)
                ·
                  refine ⟨4224868618196666487960577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22532632630382221269123077 4224868618196666487960577)
                  ·
                    refine ⟨3168651463647499865970433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4224868618196666487960577 3168651463647499865970433)
                    ·
                      refine ⟨2376488597735624899477825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3168651463647499865970433 2376488597735624899477825)
                      ·
                        rfl

theorem cell23_4628195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_4628195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628195 prefixEnd_4628195 := by exact prefixLift 4628195
  have htrace : WordTrace (prefixWord ++ tailWord_4628195) baseStart_4628195 baseEnd_4628195 := by
    simpa [prefixWord, tailWord_4628195, baseEnd_4628195] using wordTrace_append hprefix tailTrace_4628195
  have hstable : (prefixWord ++ tailWord_4628195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628195).length < 2 ^ (prefixWord ++ tailWord_4628195).sum := by decide
  have hdescent : baseEnd_4628195 < baseStart_4628195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628212 : List Nat := [2, 6, 1, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_4628212 : Nat := 118140960795 + 4628212 * 2 ^ 59
def prefixEnd_4628212 : Nat := 4983230072969 + 3 ^ 40 * 4628212 * 2
def baseEnd_4628212 : Nat := 2376497326906751332965247

theorem tailTrace_4628212 : CollatzResearch.WordTrace tailWord_4628212 prefixEnd_4628212 2376497326906751332965247 := by
  unfold tailWord_4628212
  simp only [CollatzResearch.WordTrace]
  refine ⟨84402379754392917262455445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112536506339190556349940593 84402379754392917262455445)
  ·
    refine ⟨3956361550987167996677599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 84402379754392917262455445 3956361550987167996677599)
    ·
      refine ⟨5934542326480751995016399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3956361550987167996677599 5934542326480751995016399)
      ·
        refine ⟨8901813489721127992524599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5934542326480751995016399 8901813489721127992524599)
        ·
          refine ⟨13352720234581691988786899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8901813489721127992524599 13352720234581691988786899)
          ·
            refine ⟨20029080351872537983180349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13352720234581691988786899 20029080351872537983180349)
            ·
              refine ⟨7510905131952201743692631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20029080351872537983180349 7510905131952201743692631)
              ·
                refine ⟨11266357697928302615538947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7510905131952201743692631 11266357697928302615538947)
                ·
                  refine ⟨16899536546892453923308421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11266357697928302615538947 16899536546892453923308421)
                  ·
                    refine ⟨3168663102542335110620329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16899536546892453923308421 3168663102542335110620329)
                    ·
                      refine ⟨2376497326906751332965247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3168663102542335110620329 2376497326906751332965247)
                      ·
                        rfl

theorem cell23_4628212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_4628212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628212 prefixEnd_4628212 := by exact prefixLift 4628212
  have htrace : WordTrace (prefixWord ++ tailWord_4628212) baseStart_4628212 baseEnd_4628212 := by
    simpa [prefixWord, tailWord_4628212, baseEnd_4628212] using wordTrace_append hprefix tailTrace_4628212
  have hstable : (prefixWord ++ tailWord_4628212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628212).length < 2 ^ (prefixWord ++ tailWord_4628212).sum := by decide
  have hdescent : baseEnd_4628212 < baseStart_4628212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628308 : List Nat := [2, 4, 1, 1, 3, 2, 2, 2, 6]
def baseStart_4628308 : Nat := 118140960795 + 4628308 * 2 ^ 59
def prefixEnd_4628308 : Nat := 4983230072969 + 3 ^ 40 * 4628308 * 2
def baseEnd_4628308 : Nat := 264060735672175884151645

theorem tailTrace_4628308 : CollatzResearch.WordTrace tailWord_4628308 prefixEnd_4628308 264060735672175884151645 := by
  unfold tailWord_4628308
  simp only [CollatzResearch.WordTrace]
  refine ⟨84404130458219021460202789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112538840610958695280270385 84404130458219021460202789)
  ·
    refine ⟨15825774460916066523788023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84404130458219021460202789 15825774460916066523788023)
    ·
      refine ⟨23738661691374099785682035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15825774460916066523788023 23738661691374099785682035)
      ·
        refine ⟨35607992537061149678523053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23738661691374099785682035 35607992537061149678523053)
        ·
          refine ⟨13352997201397931129446145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35607992537061149678523053 13352997201397931129446145)
          ·
            refine ⟨10014747901048448347084609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13352997201397931129446145 10014747901048448347084609)
            ·
              refine ⟨7511060925786336260313457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10014747901048448347084609 7511060925786336260313457)
              ·
                refine ⟨5633295694339752195235093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7511060925786336260313457 5633295694339752195235093)
                ·
                  refine ⟨264060735672175884151645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5633295694339752195235093 264060735672175884151645)
                  ·
                    rfl

theorem cell23_4628308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_4628308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628308 prefixEnd_4628308 := by exact prefixLift 4628308
  have htrace : WordTrace (prefixWord ++ tailWord_4628308) baseStart_4628308 baseEnd_4628308 := by
    simpa [prefixWord, tailWord_4628308, baseEnd_4628308] using wordTrace_append hprefix tailTrace_4628308
  have hstable : (prefixWord ++ tailWord_4628308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628308).length < 2 ^ (prefixWord ++ tailWord_4628308).sum := by decide
  have hdescent : baseEnd_4628308 < baseStart_4628308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628328 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 1, 5, 2]
def baseStart_4628328 : Nat := 118140960795 + 4628328 * 2 ^ 59
def prefixEnd_4628328 : Nat := 4983230072969 + 3 ^ 40 * 4628328 * 2
def baseEnd_4628328 : Nat := 2376556890662672879114713

theorem tailTrace_4628328 : CollatzResearch.WordTrace tailWord_4628328 prefixEnd_4628328 2376556890662672879114713 := by
  unfold tailWord_4628328
  simp only [CollatzResearch.WordTrace]
  refine ⟨84404495188182793168066819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112539326917577057557422425 84404495188182793168066819)
  ·
    refine ⟨126606742782274189752100229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84404495188182793168066819 126606742782274189752100229)
    ·
      refine ⟨23738764271676410578518793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126606742782274189752100229 23738764271676410578518793)
      ·
        refine ⟨17804073203757307933889095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23738764271676410578518793 17804073203757307933889095)
        ·
          refine ⟨26706109805635961900833643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17804073203757307933889095 26706109805635961900833643)
          ·
            refine ⟨40059164708453942851250465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26706109805635961900833643 40059164708453942851250465)
            ·
              refine ⟨30044373531340457138437849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40059164708453942851250465 30044373531340457138437849)
              ·
                refine ⟨22533280148505342853828387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30044373531340457138437849 22533280148505342853828387)
                ·
                  refine ⟨33799920222758014280742581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22533280148505342853828387 33799920222758014280742581)
                  ·
                    refine ⟨3168742520883563838819617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33799920222758014280742581 3168742520883563838819617)
                    ·
                      refine ⟨2376556890662672879114713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3168742520883563838819617 2376556890662672879114713)
                      ·
                        rfl

theorem cell23_4628328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_4628328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628328 prefixEnd_4628328 := by exact prefixLift 4628328
  have htrace : WordTrace (prefixWord ++ tailWord_4628328) baseStart_4628328 baseEnd_4628328 := by
    simpa [prefixWord, tailWord_4628328, baseEnd_4628328] using wordTrace_append hprefix tailTrace_4628328
  have hstable : (prefixWord ++ tailWord_4628328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628328).length < 2 ^ (prefixWord ++ tailWord_4628328).sum := by decide
  have hdescent : baseEnd_4628328 < baseStart_4628328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628351 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 4, 4]
def baseStart_4628351 : Nat := 118140960795 + 4628351 * 2 ^ 59
def prefixEnd_4628351 : Nat := 4983230072969 + 3 ^ 40 * 4628351 * 2
def baseEnd_4628351 : Nat := 792189566905908763042369

theorem tailTrace_4628351 : CollatzResearch.WordTrace tailWord_4628351 prefixEnd_4628351 792189566905908763042369 := by
  unfold tailWord_4628351
  simp only [CollatzResearch.WordTrace]
  refine ⟨168809829255282261264220907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112539886170188174176147271 168809829255282261264220907)
  ·
    refine ⟨253214743882923391896331361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168809829255282261264220907 253214743882923391896331361)
    ·
      refine ⟨189911057912192543922248521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253214743882923391896331361 189911057912192543922248521)
      ·
        refine ⟨142433293434144407941686391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189911057912192543922248521 142433293434144407941686391)
        ·
          refine ⟨213649940151216611912529587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142433293434144407941686391 213649940151216611912529587)
          ·
            refine ⟨320474910226824917868794381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213649940151216611912529587 320474910226824917868794381)
            ·
              refine ⟨120178091335059344200797893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 320474910226824917868794381 120178091335059344200797893)
              ·
                refine ⟨22533392125323627037649605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120178091335059344200797893 22533392125323627037649605)
                ·
                  refine ⟨4225011023498180069559301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22533392125323627037649605 4225011023498180069559301)
                  ·
                    refine ⟨792189566905908763042369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4225011023498180069559301 792189566905908763042369)
                    ·
                      rfl

theorem cell23_4628351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 4].length) (baseStart_4628351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628351 prefixEnd_4628351 := by exact prefixLift 4628351
  have htrace : WordTrace (prefixWord ++ tailWord_4628351) baseStart_4628351 baseEnd_4628351 := by
    simpa [prefixWord, tailWord_4628351, baseEnd_4628351] using wordTrace_append hprefix tailTrace_4628351
  have hstable : (prefixWord ++ tailWord_4628351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628351).length < 2 ^ (prefixWord ++ tailWord_4628351).sum := by decide
  have hdescent : baseEnd_4628351 < baseStart_4628351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628355 : List Nat := [1, 1, 1, 3, 4, 4, 2, 1, 1, 5]
def baseStart_4628355 : Nat := 118140960795 + 4628355 * 2 ^ 59
def prefixEnd_4628355 : Nat := 4983230072969 + 3 ^ 40 * 4628355 * 2
def baseEnd_4628355 : Nat := 792190251546781424492363

theorem tailTrace_4628355 : CollatzResearch.WordTrace tailWord_4628355 prefixEnd_4628355 792190251546781424492363 := by
  unfold tailWord_4628355
  simp only [CollatzResearch.WordTrace]
  refine ⟨168809975147267769947366519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112539983431511846631577679 168809975147267769947366519)
  ·
    refine ⟨253214962720901654921049779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168809975147267769947366519 253214962720901654921049779)
    ·
      refine ⟨379822444081352482381574669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253214962720901654921049779 379822444081352482381574669)
      ·
        refine ⟨142433416530507180893090501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 379822444081352482381574669 142433416530507180893090501)
        ·
          refine ⟨26706265599470096417454469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142433416530507180893090501 26706265599470096417454469)
          ·
            refine ⟨5007424799900643078272713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26706265599470096417454469 5007424799900643078272713)
            ·
              refine ⟨3755568599925482308704535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5007424799900643078272713 3755568599925482308704535)
              ·
                refine ⟨5633352899888223463056803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3755568599925482308704535 5633352899888223463056803)
                ·
                  refine ⟨8450029349832335194585205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5633352899888223463056803 8450029349832335194585205)
                  ·
                    refine ⟨792190251546781424492363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8450029349832335194585205 792190251546781424492363)
                    ·
                      rfl

theorem cell23_4628355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 1, 5].length) (baseStart_4628355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628355 prefixEnd_4628355 := by exact prefixLift 4628355
  have htrace : WordTrace (prefixWord ++ tailWord_4628355) baseStart_4628355 baseEnd_4628355 := by
    simpa [prefixWord, tailWord_4628355, baseEnd_4628355] using wordTrace_append hprefix tailTrace_4628355
  have hstable : (prefixWord ++ tailWord_4628355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628355).length < 2 ^ (prefixWord ++ tailWord_4628355).sum := by decide
  have hdescent : baseEnd_4628355 < baseStart_4628355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628361 : List Nat := [1, 2, 1, 1, 5, 1, 2, 3, 1, 1, 5]
def baseStart_4628361 : Nat := 118140960795 + 4628361 * 2 ^ 59
def prefixEnd_4628361 : Nat := 4983230072969 + 3 ^ 40 * 4628361 * 2
def baseEnd_4628361 : Nat := 2376573835524271250002061

theorem tailTrace_4628361 : CollatzResearch.WordTrace tailWord_4628361 prefixEnd_4628361 2376573835524271250002061 := by
  unfold tailWord_4628361
  simp only [CollatzResearch.WordTrace]
  refine ⟨168810193985246032972084937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112540129323497355314723291 168810193985246032972084937)
  ·
    refine ⟨126607645488934524729063703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168810193985246032972084937 126607645488934524729063703)
    ·
      refine ⟨189911468233401787093595555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126607645488934524729063703 189911468233401787093595555)
      ·
        refine ⟨284867202350102680640393333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189911468233401787093595555 284867202350102680640393333)
        ·
          refine ⟨26706300220322126310036875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 284867202350102680640393333 26706300220322126310036875)
          ·
            refine ⟨40059450330483189465055313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26706300220322126310036875 40059450330483189465055313)
            ·
              refine ⟨30044587747862392098791485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40059450330483189465055313 30044587747862392098791485)
              ·
                refine ⟨11266720405448397037046807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30044587747862392098791485 11266720405448397037046807)
                ·
                  refine ⟨16900080608172595555570211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11266720405448397037046807 16900080608172595555570211)
                  ·
                    refine ⟨25350120912258893333355317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16900080608172595555570211 25350120912258893333355317)
                    ·
                      refine ⟨2376573835524271250002061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25350120912258893333355317 2376573835524271250002061)
                      ·
                        rfl

theorem cell23_4628361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 1, 5].length) (baseStart_4628361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628361 prefixEnd_4628361 := by exact prefixLift 4628361
  have htrace : WordTrace (prefixWord ++ tailWord_4628361) baseStart_4628361 baseEnd_4628361 := by
    simpa [prefixWord, tailWord_4628361, baseEnd_4628361] using wordTrace_append hprefix tailTrace_4628361
  have hstable : (prefixWord ++ tailWord_4628361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628361).length < 2 ^ (prefixWord ++ tailWord_4628361).sum := by decide
  have hdescent : baseEnd_4628361 < baseStart_4628361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628375 : List Nat := [1, 1, 3, 3, 1, 3, 1, 3, 3, 2, 2]
def baseStart_4628375 : Nat := 118140960795 + 4628375 * 2 ^ 59
def prefixEnd_4628375 : Nat := 4983230072969 + 3 ^ 40 * 4628375 * 2
def baseEnd_4628375 : Nat := 2376581024253434195226997

theorem tailTrace_4628375 : CollatzResearch.WordTrace tailWord_4628375 prefixEnd_4628375 2376581024253434195226997 := by
  unfold tailWord_4628375
  simp only [CollatzResearch.WordTrace]
  refine ⟨168810704607195313363094579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112540469738130208908729719 168810704607195313363094579)
  ·
    refine ⟨253216056910792970044641869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168810704607195313363094579 253216056910792970044641869)
    ·
      refine ⟨94956021341547363766740701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253216056910792970044641869 94956021341547363766740701)
      ·
        refine ⟨35608508003080261412527763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94956021341547363766740701 35608508003080261412527763)
        ·
          refine ⟨53412762004620392118791645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35608508003080261412527763 53412762004620392118791645)
          ·
            refine ⟨20029785751732647044546867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53412762004620392118791645 20029785751732647044546867)
            ·
              refine ⟨30044678627598970566820301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20029785751732647044546867 30044678627598970566820301)
              ·
                refine ⟨11266754485349613962557613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30044678627598970566820301 11266754485349613962557613)
                ·
                  refine ⟨4225032932006105235959105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11266754485349613962557613 4225032932006105235959105)
                  ·
                    refine ⟨3168774699004578926969329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4225032932006105235959105 3168774699004578926969329)
                    ·
                      refine ⟨2376581024253434195226997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3168774699004578926969329 2376581024253434195226997)
                      ·
                        rfl

theorem cell23_4628375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_4628375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628375 prefixEnd_4628375 := by exact prefixLift 4628375
  have htrace : WordTrace (prefixWord ++ tailWord_4628375) baseStart_4628375 baseEnd_4628375 := by
    simpa [prefixWord, tailWord_4628375, baseEnd_4628375] using wordTrace_append hprefix tailTrace_4628375
  have hstable : (prefixWord ++ tailWord_4628375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628375).length < 2 ^ (prefixWord ++ tailWord_4628375).sum := by decide
  have hdescent : baseEnd_4628375 < baseStart_4628375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628378 : List Nat := [3, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5]
def baseStart_4628378 : Nat := 118140960795 + 4628378 * 2 ^ 59
def prefixEnd_4628378 : Nat := 4983230072969 + 3 ^ 40 * 4628378 * 2
def baseEnd_4628378 : Nat := 2376582564695397683489483

theorem tailTrace_4628378 : CollatzResearch.WordTrace tailWord_4628378 prefixEnd_4628378 2376582564695397683489483 := by
  unfold tailWord_4628378
  simp only [CollatzResearch.WordTrace]
  refine ⟨42202703506546111218863447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112540542684122963250302525 42202703506546111218863447)
  ·
    refine ⟨63304055259819166828295171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42202703506546111218863447 63304055259819166828295171)
    ·
      refine ⟨94956082889728750242442757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63304055259819166828295171 94956082889728750242442757)
      ·
        refine ⟨17804265541824140670458017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94956082889728750242442757 17804265541824140670458017)
        ·
          refine ⟨13353199156368105502843513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17804265541824140670458017 13353199156368105502843513)
          ·
            refine ⟨10014899367276079127132635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13353199156368105502843513 10014899367276079127132635)
            ·
              refine ⟨15022349050914118690698953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10014899367276079127132635 15022349050914118690698953)
              ·
                refine ⟨11266761788185589018024215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15022349050914118690698953 11266761788185589018024215)
                ·
                  refine ⟨16900142682278383527036323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11266761788185589018024215 16900142682278383527036323)
                  ·
                    refine ⟨25350214023417575290554485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16900142682278383527036323 25350214023417575290554485)
                    ·
                      refine ⟨2376582564695397683489483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25350214023417575290554485 2376582564695397683489483)
                      ·
                        rfl

theorem cell23_4628378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_4628378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628378 prefixEnd_4628378 := by exact prefixLift 4628378
  have htrace : WordTrace (prefixWord ++ tailWord_4628378) baseStart_4628378 baseEnd_4628378 := by
    simpa [prefixWord, tailWord_4628378, baseEnd_4628378] using wordTrace_append hprefix tailTrace_4628378
  have hstable : (prefixWord ++ tailWord_4628378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628378).length < 2 ^ (prefixWord ++ tailWord_4628378).sum := by decide
  have hdescent : baseEnd_4628378 < baseStart_4628378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628385 : List Nat := [1, 2, 3, 4, 2, 2, 1, 1, 1, 6]
def baseStart_4628385 : Nat := 118140960795 + 4628385 * 2 ^ 59
def prefixEnd_4628385 : Nat := 4983230072969 + 3 ^ 40 * 4628385 * 2
def baseEnd_4628385 : Nat := 792195386353326385367317

theorem tailTrace_4628385 : CollatzResearch.WordTrace tailWord_4628385 prefixEnd_4628385 792195386353326385367317 := by
  unfold tailWord_4628385
  simp only [CollatzResearch.WordTrace]
  refine ⟨168811069337159085070958609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112540712891439390047305739 168811069337159085070958609)
  ·
    refine ⟨126608302002869313803218957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168811069337159085070958609 126608302002869313803218957)
    ·
      refine ⟨47478113251075992676207109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126608302002869313803218957 47478113251075992676207109)
      ·
        refine ⟨8902146234576748626788833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47478113251075992676207109 8902146234576748626788833)
        ·
          refine ⟨6676609675932561470091625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8902146234576748626788833 6676609675932561470091625)
          ·
            refine ⟨5007457256949421102568719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6676609675932561470091625 5007457256949421102568719)
            ·
              refine ⟨7511185885424131653853079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5007457256949421102568719 7511185885424131653853079)
              ·
                refine ⟨11266778828136197480779619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7511185885424131653853079 11266778828136197480779619)
                ·
                  refine ⟨16900168242204296221169429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11266778828136197480779619 16900168242204296221169429)
                  ·
                    refine ⟨792195386353326385367317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16900168242204296221169429 792195386353326385367317)
                    ·
                      rfl

theorem cell23_4628385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_4628385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628385 prefixEnd_4628385 := by exact prefixLift 4628385
  have htrace : WordTrace (prefixWord ++ tailWord_4628385) baseStart_4628385 baseEnd_4628385 := by
    simpa [prefixWord, tailWord_4628385, baseEnd_4628385] using wordTrace_append hprefix tailTrace_4628385
  have hstable : (prefixWord ++ tailWord_4628385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628385).length < 2 ^ (prefixWord ++ tailWord_4628385).sum := by decide
  have hdescent : baseEnd_4628385 < baseStart_4628385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628388 : List Nat := [2, 3, 1, 2, 1, 3, 3, 1, 1, 2, 4]
def baseStart_4628388 : Nat := 118140960795 + 4628388 * 2 ^ 59
def prefixEnd_4628388 : Nat := 4983230072969 + 3 ^ 40 * 4628388 * 2
def baseEnd_4628388 : Nat := 2376587699501942644364437

theorem tailTrace_4628388 : CollatzResearch.WordTrace tailWord_4628388 prefixEnd_4628388 2376587699501942644364437 := by
  unfold tailWord_4628388
  simp only [CollatzResearch.WordTrace]
  refine ⟨84405589378074108291658909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112540785837432144388878545 84405589378074108291658909)
  ·
    refine ⟨31652096016777790609372091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84405589378074108291658909 31652096016777790609372091)
    ·
      refine ⟨47478144025166685914058137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31652096016777790609372091 47478144025166685914058137)
      ·
        refine ⟨35608608018875014435543603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47478144025166685914058137 35608608018875014435543603)
        ·
          refine ⟨53412912028312521653315405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35608608018875014435543603 53412912028312521653315405)
          ·
            refine ⟨20029842010617195619993277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53412912028312521653315405 20029842010617195619993277)
            ·
              refine ⟨7511190753981448357497479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20029842010617195619993277 7511190753981448357497479)
              ·
                refine ⟨11266786130972172536246219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7511190753981448357497479 11266786130972172536246219)
                ·
                  refine ⟨16900179196458258804369329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11266786130972172536246219 16900179196458258804369329)
                  ·
                    refine ⟨12675134397343694103276997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16900179196458258804369329 12675134397343694103276997)
                    ·
                      refine ⟨2376587699501942644364437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12675134397343694103276997 2376587699501942644364437)
                      ·
                        rfl

theorem cell23_4628388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_4628388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628388 prefixEnd_4628388 := by exact prefixLift 4628388
  have htrace : WordTrace (prefixWord ++ tailWord_4628388) baseStart_4628388 baseEnd_4628388 := by
    simpa [prefixWord, tailWord_4628388, baseEnd_4628388] using wordTrace_append hprefix tailTrace_4628388
  have hstable : (prefixWord ++ tailWord_4628388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628388).length < 2 ^ (prefixWord ++ tailWord_4628388).sum := by decide
  have hdescent : baseEnd_4628388 < baseStart_4628388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628408 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 6, 1, 3]
def baseStart_4628408 : Nat := 118140960795 + 4628408 * 2 ^ 59
def prefixEnd_4628408 : Nat := 4983230072969 + 3 ^ 40 * 4628408 * 2
def baseEnd_4628408 : Nat := 2376597969115032566114345

theorem tailTrace_4628408 : CollatzResearch.WordTrace tailWord_4628408 prefixEnd_4628408 2376597969115032566114345 := by
  unfold tailWord_4628408
  simp only [CollatzResearch.WordTrace]
  refine ⟨84405954108037879999522939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112541272144050506666030585 84405954108037879999522939)
  ·
    refine ⟨126608931162056819999284409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84405954108037879999522939 126608931162056819999284409)
    ·
      refine ⟨94956698371542614999463307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126608931162056819999284409 94956698371542614999463307)
      ·
        refine ⟨142435047557313922499194961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94956698371542614999463307 142435047557313922499194961)
        ·
          refine ⟨106826285667985441874396221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142435047557313922499194961 106826285667985441874396221)
          ·
            refine ⟨40059857125494540702898583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106826285667985441874396221 40059857125494540702898583)
            ·
              refine ⟨60089785688241811054347875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40059857125494540702898583 60089785688241811054347875)
              ·
                refine ⟨90134678532362716581521813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60089785688241811054347875 90134678532362716581521813)
                ·
                  refine ⟨4225063056204502339758835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90134678532362716581521813 4225063056204502339758835)
                  ·
                    refine ⟨6337594584306753509638253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4225063056204502339758835 6337594584306753509638253)
                    ·
                      refine ⟨2376597969115032566114345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6337594584306753509638253 2376597969115032566114345)
                      ·
                        rfl

theorem cell23_4628408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 6, 1, 3].length) (baseStart_4628408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628408 prefixEnd_4628408 := by exact prefixLift 4628408
  have htrace : WordTrace (prefixWord ++ tailWord_4628408) baseStart_4628408 baseEnd_4628408 := by
    simpa [prefixWord, tailWord_4628408, baseEnd_4628408] using wordTrace_append hprefix tailTrace_4628408
  have hstable : (prefixWord ++ tailWord_4628408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628408).length < 2 ^ (prefixWord ++ tailWord_4628408).sum := by decide
  have hdescent : baseEnd_4628408 < baseStart_4628408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628431 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 4]
def baseStart_4628431 : Nat := 118140960795 + 4628431 * 2 ^ 59
def prefixEnd_4628431 : Nat := 4983230072969 + 3 ^ 40 * 4628431 * 2
def baseEnd_4628431 : Nat := 2376609779170085976126739

theorem tailTrace_4628431 : CollatzResearch.WordTrace tailWord_4628431 prefixEnd_4628431 2376609779170085976126739 := by
  unfold tailWord_4628431
  simp only [CollatzResearch.WordTrace]
  refine ⟨168812747094992434927133147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112541831396661623284755431 168812747094992434927133147)
  ·
    refine ⟨253219120642488652390699721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168812747094992434927133147 253219120642488652390699721)
    ·
      refine ⟨189914340481866489293024791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253219120642488652390699721 189914340481866489293024791)
      ·
        refine ⟨284871510722799733939537187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189914340481866489293024791 284871510722799733939537187)
        ·
          refine ⟨427307266084199600909305781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284871510722799733939537187 427307266084199600909305781)
          ·
            refine ⟨40060056195393712585247417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 427307266084199600909305781 40060056195393712585247417)
            ·
              refine ⟨30045042146545284438935563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40060056195393712585247417 30045042146545284438935563)
              ·
                refine ⟨45067563219817926658403345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30045042146545284438935563 45067563219817926658403345)
                ·
                  refine ⟨33800672414863444993802509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45067563219817926658403345 33800672414863444993802509)
                  ·
                    refine ⟨12675252155573791872675941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33800672414863444993802509 12675252155573791872675941)
                    ·
                      refine ⟨2376609779170085976126739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12675252155573791872675941 2376609779170085976126739)
                      ·
                        rfl

theorem cell23_4628431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 4].length) (baseStart_4628431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628431 prefixEnd_4628431 := by exact prefixLift 4628431
  have htrace : WordTrace (prefixWord ++ tailWord_4628431) baseStart_4628431 baseEnd_4628431 := by
    simpa [prefixWord, tailWord_4628431, baseEnd_4628431] using wordTrace_append hprefix tailTrace_4628431
  have hstable : (prefixWord ++ tailWord_4628431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628431).length < 2 ^ (prefixWord ++ tailWord_4628431).sum := by decide
  have hdescent : baseEnd_4628431 < baseStart_4628431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628442 : List Nat := [3, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3]
def baseStart_4628442 : Nat := 118140960795 + 4628442 * 2 ^ 59
def prefixEnd_4628442 : Nat := 4983230072969 + 3 ^ 40 * 4628442 * 2
def baseEnd_4628442 : Nat := 2376615427457285433089189

theorem tailTrace_4628442 : CollatzResearch.WordTrace tailWord_4628442 prefixEnd_4628442 2376615427457285433089189 := by
  unfold tailWord_4628442
  simp only [CollatzResearch.WordTrace]
  refine ⟨42203287074488145951445895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112542098865301722537189053 42203287074488145951445895)
  ·
    refine ⟨63304930611732218927168843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42203287074488145951445895 63304930611732218927168843)
    ·
      refine ⟨94957395917598328390753265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63304930611732218927168843 94957395917598328390753265)
      ·
        refine ⟨71218046938198746293064949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94957395917598328390753265 71218046938198746293064949)
        ·
          refine ⟨6676691900456132464974839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71218046938198746293064949 6676691900456132464974839)
          ·
            refine ⟨10015037850684198697462259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6676691900456132464974839 10015037850684198697462259)
            ·
              refine ⟨15022556776026298046193389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10015037850684198697462259 15022556776026298046193389)
              ·
                refine ⟨5633458791009861767322521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15022556776026298046193389 5633458791009861767322521)
                ·
                  refine ⟨4225094093257396325491891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5633458791009861767322521 4225094093257396325491891)
                  ·
                    refine ⟨6337641139886094488237837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4225094093257396325491891 6337641139886094488237837)
                    ·
                      refine ⟨2376615427457285433089189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6337641139886094488237837 2376615427457285433089189)
                      ·
                        rfl

theorem cell23_4628442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_4628442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628442 prefixEnd_4628442 := by exact prefixLift 4628442
  have htrace : WordTrace (prefixWord ++ tailWord_4628442) baseStart_4628442 baseEnd_4628442 := by
    simpa [prefixWord, tailWord_4628442, baseEnd_4628442] using wordTrace_append hprefix tailTrace_4628442
  have hstable : (prefixWord ++ tailWord_4628442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628442).length < 2 ^ (prefixWord ++ tailWord_4628442).sum := by decide
  have hdescent : baseEnd_4628442 < baseStart_4628442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628448 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 5, 4, 2]
def baseStart_4628448 : Nat := 118140960795 + 4628448 * 2 ^ 59
def prefixEnd_4628448 : Nat := 4983230072969 + 3 ^ 40 * 4628448 * 2
def baseEnd_4628448 : Nat := 2376618508341212409614161

theorem tailTrace_4628448 : CollatzResearch.WordTrace tailWord_4628448 prefixEnd_4628448 2376618508341212409614161 := by
  unfold tailWord_4628448
  simp only [CollatzResearch.WordTrace]
  refine ⟨84406683567965423415250999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112542244757287231220334665 84406683567965423415250999)
  ·
    refine ⟨126610025351948135122876499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84406683567965423415250999 126610025351948135122876499)
    ·
      refine ⟨189915038027922202684314749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126610025351948135122876499 189915038027922202684314749)
      ·
        refine ⟨71218139260470826006618031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189915038027922202684314749 71218139260470826006618031)
        ·
          refine ⟨106827208890706239009927047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71218139260470826006618031 106827208890706239009927047)
          ·
            refine ⟨160240813336059358514890571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106827208890706239009927047 160240813336059358514890571)
            ·
              refine ⟨240361220004089037772335857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160240813336059358514890571 240361220004089037772335857)
              ·
                refine ⟨180270915003066778329251893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240361220004089037772335857 180270915003066778329251893)
                ·
                  refine ⟨16900398281537510468367365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 180270915003066778329251893 16900398281537510468367365)
                  ·
                    refine ⟨3168824677788283212818881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16900398281537510468367365 3168824677788283212818881)
                    ·
                      refine ⟨2376618508341212409614161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3168824677788283212818881 2376618508341212409614161)
                      ·
                        rfl

theorem cell23_4628448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_4628448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628448 prefixEnd_4628448 := by exact prefixLift 4628448
  have htrace : WordTrace (prefixWord ++ tailWord_4628448) baseStart_4628448 baseEnd_4628448 := by
    simpa [prefixWord, tailWord_4628448, baseEnd_4628448] using wordTrace_append hprefix tailTrace_4628448
  have hstable : (prefixWord ++ tailWord_4628448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628448).length < 2 ^ (prefixWord ++ tailWord_4628448).sum := by decide
  have hdescent : baseEnd_4628448 < baseStart_4628448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628522 : List Nat := [3, 1, 4, 1, 2, 2, 2, 3, 5]
def baseStart_4628522 : Nat := 118140960795 + 4628522 * 2 ^ 59
def prefixEnd_4628522 : Nat := 4983230072969 + 3 ^ 40 * 4628522 * 2
def baseEnd_4628522 : Nat := 264072945101071680009869

theorem tailTrace_4628522 : CollatzResearch.WordTrace tailWord_4628522 prefixEnd_4628522 264072945101071680009869 := by
  unfold tailWord_4628522
  simp only [CollatzResearch.WordTrace]
  refine ⟨42204016534415689367173955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112544044091775171645797213 42204016534415689367173955)
  ·
    refine ⟨63306024801623534050760933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42204016534415689367173955 63306024801623534050760933)
    ·
      refine ⟨11869879650304412634517675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63306024801623534050760933 11869879650304412634517675)
      ·
        refine ⟨17804819475456618951776513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11869879650304412634517675 17804819475456618951776513)
        ·
          refine ⟨13353614606592464213832385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17804819475456618951776513 13353614606592464213832385)
          ·
            refine ⟨10015210954944348160374289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13353614606592464213832385 10015210954944348160374289)
            ·
              refine ⟨7511408216208261120280717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10015210954944348160374289 7511408216208261120280717)
              ·
                refine ⟨2816778081078097920105269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7511408216208261120280717 2816778081078097920105269)
                ·
                  refine ⟨264072945101071680009869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2816778081078097920105269 264072945101071680009869)
                  ·
                    rfl

theorem cell23_4628522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 5].length) (baseStart_4628522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628522 prefixEnd_4628522 := by exact prefixLift 4628522
  have htrace : WordTrace (prefixWord ++ tailWord_4628522) baseStart_4628522 baseEnd_4628522 := by
    simpa [prefixWord, tailWord_4628522, baseEnd_4628522] using wordTrace_append hprefix tailTrace_4628522
  have hstable : (prefixWord ++ tailWord_4628522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628522).length < 2 ^ (prefixWord ++ tailWord_4628522).sum := by decide
  have hdescent : baseEnd_4628522 < baseStart_4628522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628538 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4]
def baseStart_4628538 : Nat := 118140960795 + 4628538 * 2 ^ 59
def prefixEnd_4628538 : Nat := 4983230072969 + 3 ^ 40 * 4628538 * 2
def baseEnd_4628538 : Nat := 2376664721600117057488747

theorem tailTrace_4628538 : CollatzResearch.WordTrace tailWord_4628538 prefixEnd_4628538 2376664721600117057488747 := by
  unfold tailWord_4628538
  simp only [CollatzResearch.WordTrace]
  refine ⟨42204162426401198050319567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112544433137069861467518845 42204162426401198050319567)
  ·
    refine ⟨63306243639601797075479351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42204162426401198050319567 63306243639601797075479351)
    ·
      refine ⟨94959365459402695613219027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63306243639601797075479351 94959365459402695613219027)
      ·
        refine ⟨142439048189104043419828541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94959365459402695613219027 142439048189104043419828541)
        ·
          refine ⟨53414643070914016282435703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142439048189104043419828541 53414643070914016282435703)
          ·
            refine ⟨80121964606371024423653555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53414643070914016282435703 80121964606371024423653555)
            ·
              refine ⟨120182946909556536635480333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80121964606371024423653555 120182946909556536635480333)
              ·
                refine ⟨45068605091083701238305125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120182946909556536635480333 45068605091083701238305125)
                ·
                  refine ⟨8450363454578193982182211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45068605091083701238305125 8450363454578193982182211)
                  ·
                    refine ⟨12675545181867290973273317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8450363454578193982182211 12675545181867290973273317)
                    ·
                      refine ⟨2376664721600117057488747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12675545181867290973273317 2376664721600117057488747)
                      ·
                        rfl

theorem cell23_4628538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_4628538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628538 prefixEnd_4628538 := by exact prefixLift 4628538
  have htrace : WordTrace (prefixWord ++ tailWord_4628538) baseStart_4628538 baseEnd_4628538 := by
    simpa [prefixWord, tailWord_4628538, baseEnd_4628538] using wordTrace_append hprefix tailTrace_4628538
  have hstable : (prefixWord ++ tailWord_4628538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628538).length < 2 ^ (prefixWord ++ tailWord_4628538).sum := by decide
  have hdescent : baseEnd_4628538 < baseStart_4628538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628565 : List Nat := [1, 3, 2, 2, 1, 3, 2, 2, 3, 4]
def baseStart_4628565 : Nat := 118140960795 + 4628565 * 2 ^ 59
def prefixEnd_4628565 : Nat := 4983230072969 + 3 ^ 40 * 4628565 * 2
def baseEnd_4628565 : Nat := 792226195192596150617041

theorem tailTrace_4628565 : CollatzResearch.WordTrace tailWord_4628565 prefixEnd_4628565 792226195192596150617041 := by
  unfold tailWord_4628565
  simp only [CollatzResearch.WordTrace]
  refine ⟨168817634476506975812511149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112545089651004650541674099 168817634476506975812511149)
  ·
    refine ⟨63306612928690115929691681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168817634476506975812511149 63306612928690115929691681)
    ·
      refine ⟨47479959696517586947268761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63306612928690115929691681 47479959696517586947268761)
      ·
        refine ⟨35609969772388190210451571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47479959696517586947268761 35609969772388190210451571)
        ·
          refine ⟨53414954658582285315677357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35609969772388190210451571 53414954658582285315677357)
          ·
            refine ⟨20030607996968356993379009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53414954658582285315677357 20030607996968356993379009)
            ·
              refine ⟨15022955997726267745034257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20030607996968356993379009 15022955997726267745034257)
              ·
                refine ⟨11267216998294700808775693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15022955997726267745034257 11267216998294700808775693)
                ·
                  refine ⟨4225206374360512803290885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11267216998294700808775693 4225206374360512803290885)
                  ·
                    refine ⟨792226195192596150617041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4225206374360512803290885 792226195192596150617041)
                    ·
                      rfl

theorem cell23_4628565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_4628565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628565 prefixEnd_4628565 := by exact prefixLift 4628565
  have htrace : WordTrace (prefixWord ++ tailWord_4628565) baseStart_4628565 baseEnd_4628565 := by
    simpa [prefixWord, tailWord_4628565, baseEnd_4628565] using wordTrace_append hprefix tailTrace_4628565
  have hstable : (prefixWord ++ tailWord_4628565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628565).length < 2 ^ (prefixWord ++ tailWord_4628565).sum := by decide
  have hdescent : baseEnd_4628565 < baseStart_4628565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628599 : List Nat := [1, 1, 3, 1, 1, 6, 3, 2, 1, 4]
def baseStart_4628599 : Nat := 118140960795 + 4628599 * 2 ^ 59
def prefixEnd_4628599 : Nat := 4983230072969 + 3 ^ 40 * 4628599 * 2
def baseEnd_4628599 : Nat := 792232014640013772941989

theorem tailTrace_4628599 : CollatzResearch.WordTrace tailWord_4628599 prefixEnd_4628599 792232014640013772941989 := by
  unfold tailWord_4628599
  simp only [CollatzResearch.WordTrace]
  refine ⟨168818874558383799619248851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112545916372255866412832567 168818874558383799619248851)
  ·
    refine ⟨253228311837575699428873277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168818874558383799619248851 253228311837575699428873277)
    ·
      refine ⟨94960616939090887285827479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253228311837575699428873277 94960616939090887285827479)
      ·
        refine ⟨142440925408636330928741219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94960616939090887285827479 142440925408636330928741219)
        ·
          refine ⟨213661388112954496393111829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142440925408636330928741219 213661388112954496393111829)
          ·
            refine ⟨10015377567794742018427117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 213661388112954496393111829 10015377567794742018427117)
            ·
              refine ⟨3755766587923028256910169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10015377567794742018427117 3755766587923028256910169)
              ·
                refine ⟨2816824940942271192682627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3755766587923028256910169 2816824940942271192682627)
                ·
                  refine ⟨4225237411413406789023941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2816824940942271192682627 4225237411413406789023941)
                  ·
                    refine ⟨792232014640013772941989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4225237411413406789023941 792232014640013772941989)
                    ·
                      rfl

theorem cell23_4628599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 1, 4].length) (baseStart_4628599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628599 prefixEnd_4628599 := by exact prefixLift 4628599
  have htrace : WordTrace (prefixWord ++ tailWord_4628599) baseStart_4628599 baseEnd_4628599 := by
    simpa [prefixWord, tailWord_4628599, baseEnd_4628599] using wordTrace_append hprefix tailTrace_4628599
  have hstable : (prefixWord ++ tailWord_4628599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628599).length < 2 ^ (prefixWord ++ tailWord_4628599).sum := by decide
  have hdescent : baseEnd_4628599 < baseStart_4628599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628608 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 3, 5]
def baseStart_4628608 : Nat := 118140960795 + 4628608 * 2 ^ 59
def prefixEnd_4628608 : Nat := 4983230072969 + 3 ^ 40 * 4628608 * 2
def baseEnd_4628608 : Nat := 792233555081977261204475

theorem tailTrace_4628608 : CollatzResearch.WordTrace tailWord_4628608 prefixEnd_4628608 792233555081977261204475 := by
  unfold tailWord_4628608
  simp only [CollatzResearch.WordTrace]
  refine ⟨84409601407675597078163239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112546135210234129437550985 84409601407675597078163239)
  ·
    refine ⟨126614402111513395617244859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84409601407675597078163239 126614402111513395617244859)
    ·
      refine ⟨189921603167270093425867289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126614402111513395617244859 189921603167270093425867289)
      ·
        refine ⟨142441202375452570069400467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189921603167270093425867289 142441202375452570069400467)
        ·
          refine ⟨213661803563178855104100701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142441202375452570069400467 213661803563178855104100701)
          ·
            refine ⟨80123176336192070664037763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213661803563178855104100701 80123176336192070664037763)
            ·
              refine ⟨120184764504288105996056645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80123176336192070664037763 120184764504288105996056645)
              ·
                refine ⟨22534643344554019874260621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120184764504288105996056645 22534643344554019874260621)
                ·
                  refine ⟨8450491254207757452847733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22534643344554019874260621 8450491254207757452847733)
                  ·
                    refine ⟨792233555081977261204475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8450491254207757452847733 792233555081977261204475)
                    ·
                      rfl

theorem cell23_4628608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 3, 5].length) (baseStart_4628608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628608 prefixEnd_4628608 := by exact prefixLift 4628608
  have htrace : WordTrace (prefixWord ++ tailWord_4628608) baseStart_4628608 baseEnd_4628608 := by
    simpa [prefixWord, tailWord_4628608, baseEnd_4628608] using wordTrace_append hprefix tailTrace_4628608
  have hstable : (prefixWord ++ tailWord_4628608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628608).length < 2 ^ (prefixWord ++ tailWord_4628608).sum := by decide
  have hdescent : baseEnd_4628608 < baseStart_4628608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628615 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 3, 5, 2]
def baseStart_4628615 : Nat := 118140960795 + 4628615 * 2 ^ 59
def prefixEnd_4628615 : Nat := 4983230072969 + 3 ^ 40 * 4628615 * 2
def baseEnd_4628615 : Nat := 2376704259610513256225893

theorem tailTrace_4628615 : CollatzResearch.WordTrace tailWord_4628615 prefixEnd_4628615 2376704259610513256225893 := by
  unfold tailWord_4628615
  simp only [CollatzResearch.WordTrace]
  refine ⟨168819458126325834351831299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112546305417550556234554199 168819458126325834351831299)
  ·
    refine ⟨253229187189488751527746949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168819458126325834351831299 253229187189488751527746949)
    ·
      refine ⟨47480472598029140911452553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 253229187189488751527746949 47480472598029140911452553)
      ·
        refine ⟨35610354448521855683589415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47480472598029140911452553 35610354448521855683589415)
        ·
          refine ⟨53415531672782783525384123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35610354448521855683589415 53415531672782783525384123)
          ·
            refine ⟨80123297509174175288076185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53415531672782783525384123 80123297509174175288076185)
            ·
              refine ⟨60092473131880631466057139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80123297509174175288076185 60092473131880631466057139)
              ·
                refine ⟨90138709697820947199085709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60092473131880631466057139 90138709697820947199085709)
                ·
                  refine ⟨33802016136682855199657141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90138709697820947199085709 33802016136682855199657141)
                  ·
                    refine ⟨3168939012814017674967857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33802016136682855199657141 3168939012814017674967857)
                    ·
                      refine ⟨2376704259610513256225893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3168939012814017674967857 2376704259610513256225893)
                      ·
                        rfl

theorem cell23_4628615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_4628615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628615 prefixEnd_4628615 := by exact prefixLift 4628615
  have htrace : WordTrace (prefixWord ++ tailWord_4628615) baseStart_4628615 baseEnd_4628615 := by
    simpa [prefixWord, tailWord_4628615, baseEnd_4628615] using wordTrace_append hprefix tailTrace_4628615
  have hstable : (prefixWord ++ tailWord_4628615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628615).length < 2 ^ (prefixWord ++ tailWord_4628615).sum := by decide
  have hdescent : baseEnd_4628615 < baseStart_4628615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628650 : List Nat := [3, 1, 5, 1, 3, 1, 2, 2, 1, 4]
def baseStart_4628650 : Nat := 118140960795 + 4628650 * 2 ^ 59
def prefixEnd_4628650 : Nat := 4983230072969 + 3 ^ 40 * 4628650 * 2
def baseEnd_4628650 : Nat := 792240743811140206429411

theorem tailTrace_4628650 : CollatzResearch.WordTrace tailWord_4628650 prefixEnd_4628650 792240743811140206429411 := by
  unfold tailWord_4628650
  simp only [CollatzResearch.WordTrace]
  refine ⟨42205183670299758832338851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112547156454132690219570269 42205183670299758832338851)
  ·
    refine ⟨63307775505449638248508277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42205183670299758832338851 63307775505449638248508277)
    ·
      refine ⟨5935103953635903585797651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63307775505449638248508277 5935103953635903585797651)
      ·
        refine ⟨8902655930453855378696477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5935103953635903585797651 8902655930453855378696477)
        ·
          refine ⟨3338495973920195767011179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8902655930453855378696477 3338495973920195767011179)
          ·
            refine ⟨5007743960880293650516769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3338495973920195767011179 5007743960880293650516769)
            ·
              refine ⟨3755807970660220237887577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5007743960880293650516769 3755807970660220237887577)
              ·
                refine ⟨2816855977995165178415683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3755807970660220237887577 2816855977995165178415683)
                ·
                  refine ⟨4225283966992747767623525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2816855977995165178415683 4225283966992747767623525)
                  ·
                    refine ⟨792240743811140206429411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4225283966992747767623525 792240743811140206429411)
                    ·
                      rfl

theorem cell23_4628650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_4628650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628650 prefixEnd_4628650 := by exact prefixLift 4628650
  have htrace : WordTrace (prefixWord ++ tailWord_4628650) baseStart_4628650 baseEnd_4628650 := by
    simpa [prefixWord, tailWord_4628650, baseEnd_4628650] using wordTrace_append hprefix tailTrace_4628650
  have hstable : (prefixWord ++ tailWord_4628650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628650).length < 2 ^ (prefixWord ++ tailWord_4628650).sum := by decide
  have hdescent : baseEnd_4628650 < baseStart_4628650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628665 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 5, 2, 3]
def baseStart_4628665 : Nat := 118140960795 + 4628665 * 2 ^ 59
def prefixEnd_4628665 : Nat := 4983230072969 + 3 ^ 40 * 4628665 * 2
def baseEnd_4628665 : Nat := 2376729933643238060600663

theorem tailTrace_4628665 : CollatzResearch.WordTrace tailWord_4628665 prefixEnd_4628665 2376729933643238060600663 := by
  unfold tailWord_4628665
  simp only [CollatzResearch.WordTrace]
  refine ⟨168821281776144692891151449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112547521184096461927434299 168821281776144692891151449)
  ·
    refine ⟨126615961332108519668363587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168821281776144692891151449 126615961332108519668363587)
    ·
      refine ⟨189923941998162779502545381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126615961332108519668363587 189923941998162779502545381)
      ·
        refine ⟨35610739124655521156727259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189923941998162779502545381 35610739124655521156727259)
        ·
          refine ⟨53416108686983281735090889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35610739124655521156727259 53416108686983281735090889)
          ·
            refine ⟨40062081515237461301318167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53416108686983281735090889 40062081515237461301318167)
            ·
              refine ⟨60093122272856191951977251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40062081515237461301318167 60093122272856191951977251)
              ·
                refine ⟨90139683409284287927965877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60093122272856191951977251 90139683409284287927965877)
                ·
                  refine ⟨8450595319620401993246801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90139683409284287927965877 8450595319620401993246801)
                  ·
                    refine ⟨6337946489715301494935101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8450595319620401993246801 6337946489715301494935101)
                    ·
                      refine ⟨2376729933643238060600663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6337946489715301494935101 2376729933643238060600663)
                      ·
                        rfl

theorem cell23_4628665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_4628665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628665 prefixEnd_4628665 := by exact prefixLift 4628665
  have htrace : WordTrace (prefixWord ++ tailWord_4628665) baseStart_4628665 baseEnd_4628665 := by
    simpa [prefixWord, tailWord_4628665, baseEnd_4628665] using wordTrace_append hprefix tailTrace_4628665
  have hstable : (prefixWord ++ tailWord_4628665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628665).length < 2 ^ (prefixWord ++ tailWord_4628665).sum := by decide
  have hdescent : baseEnd_4628665 < baseStart_4628665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628672 : List Nat := [2, 1, 1, 2, 5, 1, 2, 3, 2, 4]
def baseStart_4628672 : Nat := 118140960795 + 4628672 * 2 ^ 59
def prefixEnd_4628672 : Nat := 4983230072969 + 3 ^ 40 * 4628672 * 2
def baseEnd_4628672 : Nat := 792244509335939844404377

theorem tailTrace_4628672 : CollatzResearch.WordTrace tailWord_4628672 prefixEnd_4628672 792244509335939844404377 := by
  unfold tailWord_4628672
  simp only [CollatzResearch.WordTrace]
  refine ⟨84410768543559666543328135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112547691391412888724437513 84410768543559666543328135)
  ·
    refine ⟨126616152815339499814992203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84410768543559666543328135 126616152815339499814992203)
    ·
      refine ⟨189924229223009249722488305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126616152815339499814992203 189924229223009249722488305)
      ·
        refine ⟨142443171917256937291866229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189924229223009249722488305 142443171917256937291866229)
        ·
          refine ⟨13354047367242837871112459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 142443171917256937291866229 13354047367242837871112459)
          ·
            refine ⟨20031071050864256806668689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13354047367242837871112459 20031071050864256806668689)
            ·
              refine ⟨15023303288148192605001517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20031071050864256806668689 15023303288148192605001517)
              ·
                refine ⟨5633738733055572226875569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15023303288148192605001517 5633738733055572226875569)
                ·
                  refine ⟨4225304049791679170156677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5633738733055572226875569 4225304049791679170156677)
                  ·
                    refine ⟨792244509335939844404377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4225304049791679170156677 792244509335939844404377)
                    ·
                      rfl

theorem cell23_4628672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 2, 4].length) (baseStart_4628672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628672 prefixEnd_4628672 := by exact prefixLift 4628672
  have htrace : WordTrace (prefixWord ++ tailWord_4628672) baseStart_4628672 baseEnd_4628672 := by
    simpa [prefixWord, tailWord_4628672, baseEnd_4628672] using wordTrace_append hprefix tailTrace_4628672
  have hstable : (prefixWord ++ tailWord_4628672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628672).length < 2 ^ (prefixWord ++ tailWord_4628672).sum := by decide
  have hdescent : baseEnd_4628672 < baseStart_4628672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628682 : List Nat := [3, 1, 2, 1, 3, 1, 2, 4, 1, 2, 3]
def baseStart_4628682 : Nat := 118140960795 + 4628682 * 2 ^ 59
def prefixEnd_4628682 : Nat := 4983230072969 + 3 ^ 40 * 4628682 * 2
def baseEnd_4628682 : Nat := 2376738662814364494088085

theorem tailTrace_4628682 : CollatzResearch.WordTrace tailWord_4628682 prefixEnd_4628682 2376738662814364494088085 := by
  unfold tailWord_4628682
  simp only [CollatzResearch.WordTrace]
  refine ⟨42205475454270776198630075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112547934544722069863013533 42205475454270776198630075)
  ·
    refine ⟨63308213181406164297945113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42205475454270776198630075 63308213181406164297945113)
    ·
      refine ⟨47481159886054623223458835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63308213181406164297945113 47481159886054623223458835)
      ·
        refine ⟨71221739829081934835188253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47481159886054623223458835 71221739829081934835188253)
        ·
          refine ⟨26708152435905725563195595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71221739829081934835188253 26708152435905725563195595)
          ·
            refine ⟨40062228653858588344793393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26708152435905725563195595 40062228653858588344793393)
            ·
              refine ⟨30046671490393941258595045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40062228653858588344793393 30046671490393941258595045)
              ·
                refine ⟨5633750904448863985986571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30046671490393941258595045 5633750904448863985986571)
                ·
                  refine ⟨8450626356673295978979857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5633750904448863985986571 8450626356673295978979857)
                  ·
                    refine ⟨6337969767504971984234893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8450626356673295978979857 6337969767504971984234893)
                    ·
                      refine ⟨2376738662814364494088085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6337969767504971984234893 2376738662814364494088085)
                      ·
                        rfl

theorem cell23_4628682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_4628682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628682 prefixEnd_4628682 := by exact prefixLift 4628682
  have htrace : WordTrace (prefixWord ++ tailWord_4628682) baseStart_4628682 baseEnd_4628682 := by
    simpa [prefixWord, tailWord_4628682, baseEnd_4628682] using wordTrace_append hprefix tailTrace_4628682
  have hstable : (prefixWord ++ tailWord_4628682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628682).length < 2 ^ (prefixWord ++ tailWord_4628682).sum := by decide
  have hdescent : baseEnd_4628682 < baseStart_4628682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628696 : List Nat := [2, 1, 2, 2, 4, 1, 1, 5, 1, 2, 2]
def baseStart_4628696 : Nat := 118140960795 + 4628696 * 2 ^ 59
def prefixEnd_4628696 : Nat := 4983230072969 + 3 ^ 40 * 4628696 * 2
def baseEnd_4628696 : Nat := 2376745851543527439313021

theorem tailTrace_4628696 : CollatzResearch.WordTrace tailWord_4628696 prefixEnd_4628696 2376745851543527439313021 := by
  unfold tailWord_4628696
  simp only [CollatzResearch.WordTrace]
  refine ⟨84411206219516192592764971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112548274959354923457019961 84411206219516192592764971)
  ·
    refine ⟨126616809329274288889147457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84411206219516192592764971 126616809329274288889147457)
    ·
      refine ⟨94962606996955716666860593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126616809329274288889147457 94962606996955716666860593)
      ·
        refine ⟨71221955247716787500145445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94962606996955716666860593 71221955247716787500145445)
        ·
          refine ⟨13354116608946897656277271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71221955247716787500145445 13354116608946897656277271)
          ·
            refine ⟨20031174913420346484415907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13354116608946897656277271 20031174913420346484415907)
            ·
              refine ⟨30046762370130519726623861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20031174913420346484415907 30046762370130519726623861)
              ·
                refine ⟨2816883972199736224370987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30046762370130519726623861 2816883972199736224370987)
                ·
                  refine ⟨4225325958299604336556481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2816883972199736224370987 4225325958299604336556481)
                  ·
                    refine ⟨3168994468724703252417361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4225325958299604336556481 3168994468724703252417361)
                    ·
                      refine ⟨2376745851543527439313021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3168994468724703252417361 2376745851543527439313021)
                      ·
                        rfl

theorem cell23_4628696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 1, 2, 2].length) (baseStart_4628696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628696 prefixEnd_4628696 := by exact prefixLift 4628696
  have htrace : WordTrace (prefixWord ++ tailWord_4628696) baseStart_4628696 baseEnd_4628696 := by
    simpa [prefixWord, tailWord_4628696, baseEnd_4628696] using wordTrace_append hprefix tailTrace_4628696
  have hstable : (prefixWord ++ tailWord_4628696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628696).length < 2 ^ (prefixWord ++ tailWord_4628696).sum := by decide
  have hdescent : baseEnd_4628696 < baseStart_4628696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628739 : List Nat := [1, 1, 1, 3, 2, 3, 4, 2, 1, 3, 2]
def baseStart_4628739 : Nat := 118140960795 + 4628739 * 2 ^ 59
def prefixEnd_4628739 : Nat := 4983230072969 + 3 ^ 40 * 4628739 * 2
def baseEnd_4628739 : Nat := 2376767931211670771075323

theorem tailTrace_4628739 : CollatzResearch.WordTrace tailWord_4628739 prefixEnd_4628739 2376767931211670771075323 := by
  unfold tailWord_4628739
  simp only [CollatzResearch.WordTrace]
  refine ⟨168823980777876603529345271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112549320518584402352896847 168823980777876603529345271)
  ·
    refine ⟨253235971166814905294017907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168823980777876603529345271 253235971166814905294017907)
    ·
      refine ⟨379853956750222357941026861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253235971166814905294017907 379853956750222357941026861)
      ·
        refine ⟨142445233781333384227885073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 379853956750222357941026861 142445233781333384227885073)
        ·
          refine ⟨106833925336000038170913805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142445233781333384227885073 106833925336000038170913805)
          ·
            refine ⟨40062722001000014314092677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106833925336000038170913805 40062722001000014314092677)
            ·
              refine ⟨7511760375187502683892377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40062722001000014314092677 7511760375187502683892377)
              ·
                refine ⟨5633820281390627012919283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7511760375187502683892377 5633820281390627012919283)
                ·
                  refine ⟨8450730422085940519378925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5633820281390627012919283 8450730422085940519378925)
                  ·
                    refine ⟨3169023908282227694767097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8450730422085940519378925 3169023908282227694767097)
                    ·
                      refine ⟨2376767931211670771075323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3169023908282227694767097 2376767931211670771075323)
                      ·
                        rfl

theorem cell23_4628739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 3, 2].length) (baseStart_4628739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628739 prefixEnd_4628739 := by exact prefixLift 4628739
  have htrace : WordTrace (prefixWord ++ tailWord_4628739) baseStart_4628739 baseEnd_4628739 := by
    simpa [prefixWord, tailWord_4628739, baseEnd_4628739] using wordTrace_append hprefix tailTrace_4628739
  have hstable : (prefixWord ++ tailWord_4628739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628739).length < 2 ^ (prefixWord ++ tailWord_4628739).sum := by decide
  have hdescent : baseEnd_4628739 < baseStart_4628739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628769 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 4, 2, 2]
def baseStart_4628769 : Nat := 118140960795 + 4628769 * 2 ^ 59
def prefixEnd_4628769 : Nat := 4983230072969 + 3 ^ 40 * 4628769 * 2
def baseEnd_4628769 : Nat := 2376783335631305653700185

theorem tailTrace_4628769 : CollatzResearch.WordTrace tailWord_4628769 prefixEnd_4628769 2376783335631305653700185 := by
  unfold tailWord_4628769
  simp only [CollatzResearch.WordTrace]
  refine ⟨168825074967767918652937361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112550049978511945768624907 168825074967767918652937361)
  ·
    refine ⟨126618806225825938989703021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168825074967767918652937361 126618806225825938989703021)
    ·
      refine ⟨47482052334684727121138633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126618806225825938989703021 47482052334684727121138633)
      ·
        refine ⟨35611539251013545340853975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47482052334684727121138633 35611539251013545340853975)
        ·
          refine ⟨53417308876520318011280963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35611539251013545340853975 53417308876520318011280963)
          ·
            refine ⟨80125963314780477016921445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53417308876520318011280963 80125963314780477016921445)
            ·
              refine ⟨15023618121521339440672771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80125963314780477016921445 15023618121521339440672771)
              ·
                refine ⟨22535427182282009161009157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15023618121521339440672771 22535427182282009161009157)
                ·
                  refine ⟨4225392596677876717689217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22535427182282009161009157 4225392596677876717689217)
                  ·
                    refine ⟨3169044447508407538266913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4225392596677876717689217 3169044447508407538266913)
                    ·
                      refine ⟨2376783335631305653700185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3169044447508407538266913 2376783335631305653700185)
                      ·
                        rfl

theorem cell23_4628769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_4628769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628769 prefixEnd_4628769 := by exact prefixLift 4628769
  have htrace : WordTrace (prefixWord ++ tailWord_4628769) baseStart_4628769 baseEnd_4628769 := by
    simpa [prefixWord, tailWord_4628769, baseEnd_4628769] using wordTrace_append hprefix tailTrace_4628769
  have hstable : (prefixWord ++ tailWord_4628769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628769).length < 2 ^ (prefixWord ++ tailWord_4628769).sum := by decide
  have hdescent : baseEnd_4628769 < baseStart_4628769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628825 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 3, 3, 4]
def baseStart_4628825 : Nat := 118140960795 + 4628825 * 2 ^ 59
def prefixEnd_4628825 : Nat := 4983230072969 + 3 ^ 40 * 4628825 * 2
def baseEnd_4628825 : Nat := 2376812090547957434599927

theorem tailTrace_4628825 : CollatzResearch.WordTrace tailWord_4628825 prefixEnd_4628825 2376812090547957434599927 := by
  unfold tailWord_4628825
  simp only [CollatzResearch.WordTrace]
  refine ⟨168827117455565040216975929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112551411637043360144650619 168827117455565040216975929)
  ·
    refine ⟨126620338091673780162731947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168827117455565040216975929 126620338091673780162731947)
    ·
      refine ⟨189930507137510670244097921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126620338091673780162731947 189930507137510670244097921)
      ·
        refine ⟨142447880353133002683073441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189930507137510670244097921 142447880353133002683073441)
        ·
          refine ⟨106835910264849752012305081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142447880353133002683073441 106835910264849752012305081)
          ·
            refine ⟨80126932698637314009228811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106835910264849752012305081 80126932698637314009228811)
            ·
              refine ⟨120190399047955971013843217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80126932698637314009228811 120190399047955971013843217)
              ·
                refine ⟨90142799285966978260382413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120190399047955971013843217 90142799285966978260382413)
                ·
                  refine ⟨33803549732237616847643405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90142799285966978260382413 33803549732237616847643405)
                  ·
                    refine ⟨12676331149589106317866277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33803549732237616847643405 12676331149589106317866277)
                    ·
                      refine ⟨2376812090547957434599927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12676331149589106317866277 2376812090547957434599927)
                      ·
                        rfl

theorem cell23_4628825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_4628825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628825 prefixEnd_4628825 := by exact prefixLift 4628825
  have htrace : WordTrace (prefixWord ++ tailWord_4628825) baseStart_4628825 baseEnd_4628825 := by
    simpa [prefixWord, tailWord_4628825, baseEnd_4628825] using wordTrace_append hprefix tailTrace_4628825
  have hstable : (prefixWord ++ tailWord_4628825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628825).length < 2 ^ (prefixWord ++ tailWord_4628825).sum := by decide
  have hdescent : baseEnd_4628825 < baseStart_4628825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628855 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 4]
def baseStart_4628855 : Nat := 118140960795 + 4628855 * 2 ^ 59
def prefixEnd_4628855 : Nat := 4983230072969 + 3 ^ 40 * 4628855 * 2
def baseEnd_4628855 : Nat := 2376827494967592317224789

theorem tailTrace_4628855 : CollatzResearch.WordTrace tailWord_4628855 prefixEnd_4628855 2376827494967592317224789 := by
  unfold tailWord_4628855
  simp only [CollatzResearch.WordTrace]
  refine ⟨168828211645456355340568019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112552141096970903560378679 168828211645456355340568019)
  ·
    refine ⟨253242317468184533010852029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168828211645456355340568019 253242317468184533010852029)
    ·
      refine ⟨94965869050569199879069511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253242317468184533010852029 94965869050569199879069511)
      ·
        refine ⟨142448803575853799818604267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94965869050569199879069511 142448803575853799818604267)
        ·
          refine ⟨213673205363780699727906401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142448803575853799818604267 213673205363780699727906401)
          ·
            refine ⟨160254904022835524795929801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213673205363780699727906401 160254904022835524795929801)
            ·
              refine ⟨120191178017126643596947351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160254904022835524795929801 120191178017126643596947351)
              ·
                refine ⟨180286767025689965395421027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120191178017126643596947351 180286767025689965395421027)
                ·
                  refine ⟨270430150538534948093131541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180286767025689965395421027 270430150538534948093131541)
                  ·
                    refine ⟨12676413306493825691865541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 270430150538534948093131541 12676413306493825691865541)
                    ·
                      refine ⟨2376827494967592317224789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12676413306493825691865541 2376827494967592317224789)
                      ·
                        rfl

theorem cell23_4628855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_4628855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628855 prefixEnd_4628855 := by exact prefixLift 4628855
  have htrace : WordTrace (prefixWord ++ tailWord_4628855) baseStart_4628855 baseEnd_4628855 := by
    simpa [prefixWord, tailWord_4628855, baseEnd_4628855] using wordTrace_append hprefix tailTrace_4628855
  have hstable : (prefixWord ++ tailWord_4628855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628855).length < 2 ^ (prefixWord ++ tailWord_4628855).sum := by decide
  have hdescent : baseEnd_4628855 < baseStart_4628855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628859 : List Nat := [1, 1, 1, 1, 1, 9, 1, 1, 2, 1, 4]
def baseStart_4628859 : Nat := 118140960795 + 4628859 * 2 ^ 59
def prefixEnd_4628859 : Nat := 4983230072969 + 3 ^ 40 * 4628859 * 2
def baseEnd_4628859 : Nat := 2376829548890210301574771

theorem tailTrace_4628859 : CollatzResearch.WordTrace tailWord_4628859 prefixEnd_4628859 2376829548890210301574771 := by
  unfold tailWord_4628859
  simp only [CollatzResearch.WordTrace]
  refine ⟨168828357537441864023713631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112552238358294576015809087 168828357537441864023713631)
  ·
    refine ⟨253242536306162796035570447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168828357537441864023713631 253242536306162796035570447)
    ·
      refine ⟨379863804459244194053355671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253242536306162796035570447 379863804459244194053355671)
      ·
        refine ⟨569795706688866291080033507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379863804459244194053355671 569795706688866291080033507)
        ·
          refine ⟨854693560033299436620050261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569795706688866291080033507 854693560033299436620050261)
          ·
            refine ⟨5007970078320113886445607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 854693560033299436620050261 5007970078320113886445607)
            ·
              refine ⟨7511955117480170829668411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5007970078320113886445607 7511955117480170829668411)
              ·
                refine ⟨11267932676220256244502617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7511955117480170829668411 11267932676220256244502617)
                ·
                  refine ⟨8450949507165192183376963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11267932676220256244502617 8450949507165192183376963)
                  ·
                    refine ⟨12676424260747788275065445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8450949507165192183376963 12676424260747788275065445)
                    ·
                      refine ⟨2376829548890210301574771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12676424260747788275065445 2376829548890210301574771)
                      ·
                        rfl

theorem cell23_4628859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 1, 4].length) (baseStart_4628859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628859 prefixEnd_4628859 := by exact prefixLift 4628859
  have htrace : WordTrace (prefixWord ++ tailWord_4628859) baseStart_4628859 baseEnd_4628859 := by
    simpa [prefixWord, tailWord_4628859, baseEnd_4628859] using wordTrace_append hprefix tailTrace_4628859
  have hstable : (prefixWord ++ tailWord_4628859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628859).length < 2 ^ (prefixWord ++ tailWord_4628859).sum := by decide
  have hdescent : baseEnd_4628859 < baseStart_4628859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628899 : List Nat := [1, 1, 1, 4, 1, 5, 3, 1, 6]
def baseStart_4628899 : Nat := 118140960795 + 4628899 * 2 ^ 59
def prefixEnd_4628899 : Nat := 4983230072969 + 3 ^ 40 * 4628899 * 2
def baseEnd_4628899 : Nat := 264094454235154460563843

theorem tailTrace_4628899 : CollatzResearch.WordTrace tailWord_4628899 prefixEnd_4628899 264094454235154460563843 := by
  unfold tailWord_4628899
  simp only [CollatzResearch.WordTrace]
  refine ⟨168829816457296950855169751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112553210971531300570113167 168829816457296950855169751)
  ·
    refine ⟨253244724685945426282754627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168829816457296950855169751 253244724685945426282754627)
    ·
      refine ⟨379867087028918139424131941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253244724685945426282754627 379867087028918139424131941)
      ·
        refine ⟨71225078817922151142024739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 379867087028918139424131941 71225078817922151142024739)
        ·
          refine ⟨106837618226883226713037109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71225078817922151142024739 106837618226883226713037109)
          ·
            refine ⟨10016026708770302504347229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106837618226883226713037109 10016026708770302504347229)
            ·
              refine ⟨3756010015788863439130211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10016026708770302504347229 3756010015788863439130211)
              ·
                refine ⟨5634015023683295158695317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3756010015788863439130211 5634015023683295158695317)
                ·
                  refine ⟨264094454235154460563843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5634015023683295158695317 264094454235154460563843)
                  ·
                    rfl

theorem cell23_4628899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 6].length) (baseStart_4628899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628899 prefixEnd_4628899 := by exact prefixLift 4628899
  have htrace : WordTrace (prefixWord ++ tailWord_4628899) baseStart_4628899 baseEnd_4628899 := by
    simpa [prefixWord, tailWord_4628899, baseEnd_4628899] using wordTrace_append hprefix tailTrace_4628899
  have hstable : (prefixWord ++ tailWord_4628899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628899).length < 2 ^ (prefixWord ++ tailWord_4628899).sum := by decide
  have hdescent : baseEnd_4628899 < baseStart_4628899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628905 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 2, 1, 7]
def baseStart_4628905 : Nat := 118140960795 + 4628905 * 2 ^ 59
def prefixEnd_4628905 : Nat := 4983230072969 + 3 ^ 40 * 4628905 * 2
def baseEnd_4628905 : Nat := 2376853169000317121599559

theorem tailTrace_4628905 : CollatzResearch.WordTrace tailWord_4628905 prefixEnd_4628905 2376853169000317121599559 := by
  unfold tailWord_4628905
  simp only [CollatzResearch.WordTrace]
  refine ⟨168830035295275213879888169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112553356863516809253258779 168830035295275213879888169)
  ·
    refine ⟨126622526471456410409916127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168830035295275213879888169 126622526471456410409916127)
    ·
      refine ⟨189933789707184615614874191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126622526471456410409916127 189933789707184615614874191)
      ·
        refine ⟨284900684560776923422311287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189933789707184615614874191 284900684560776923422311287)
        ·
          refine ⟨427351026841165385133466931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284900684560776923422311287 427351026841165385133466931)
          ·
            refine ⟨641026540261748077700200397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427351026841165385133466931 641026540261748077700200397)
            ·
              refine ⟨240384952598155529137575149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 641026540261748077700200397 240384952598155529137575149)
              ·
                refine ⟨90144357224308323426590681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 240384952598155529137575149 90144357224308323426590681)
                ·
                  refine ⟨67608267918231242569943011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90144357224308323426590681 67608267918231242569943011)
                  ·
                    refine ⟨101412401877346863854914517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67608267918231242569943011 101412401877346863854914517)
                    ·
                      refine ⟨2376853169000317121599559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101412401877346863854914517 2376853169000317121599559)
                      ·
                        rfl

theorem cell23_4628905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_4628905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628905 prefixEnd_4628905 := by exact prefixLift 4628905
  have htrace : WordTrace (prefixWord ++ tailWord_4628905) baseStart_4628905 baseEnd_4628905 := by
    simpa [prefixWord, tailWord_4628905, baseEnd_4628905] using wordTrace_append hprefix tailTrace_4628905
  have hstable : (prefixWord ++ tailWord_4628905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628905).length < 2 ^ (prefixWord ++ tailWord_4628905).sum := by decide
  have hdescent : baseEnd_4628905 < baseStart_4628905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628919 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 1, 5, 2]
def baseStart_4628919 : Nat := 118140960795 + 4628919 * 2 ^ 59
def prefixEnd_4628919 : Nat := 4983230072969 + 3 ^ 40 * 4628919 * 2
def baseEnd_4628919 : Nat := 2376860357729480066824495

theorem tailTrace_4628919 : CollatzResearch.WordTrace tailWord_4628919 prefixEnd_4628919 2376860357729480066824495 := by
  unfold tailWord_4628919
  simp only [CollatzResearch.WordTrace]
  refine ⟨168830545917224494270897811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112553697278149662847265207 168830545917224494270897811)
  ·
    refine ⟨253245818875836741406346717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168830545917224494270897811 253245818875836741406346717)
    ·
      refine ⟨94967182078438778027380019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253245818875836741406346717 94967182078438778027380019)
      ·
        refine ⟨142450773117658167041070029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94967182078438778027380019 142450773117658167041070029)
        ·
          refine ⟨53419039919121812640401261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142450773117658167041070029 53419039919121812640401261)
          ·
            refine ⟨20032139969670679740150473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53419039919121812640401261 20032139969670679740150473)
            ·
              refine ⟨15024104977253009805112855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20032139969670679740150473 15024104977253009805112855)
              ·
                refine ⟨22536157465879514707669283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15024104977253009805112855 22536157465879514707669283)
                ·
                  refine ⟨33804236198819272061503925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22536157465879514707669283 33804236198819272061503925)
                  ·
                    refine ⟨3169147143639306755765993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33804236198819272061503925 3169147143639306755765993)
                    ·
                      refine ⟨2376860357729480066824495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3169147143639306755765993 2376860357729480066824495)
                      ·
                        rfl

theorem cell23_4628919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 5, 2].length) (baseStart_4628919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628919 prefixEnd_4628919 := by exact prefixLift 4628919
  have htrace : WordTrace (prefixWord ++ tailWord_4628919) baseStart_4628919 baseEnd_4628919 := by
    simpa [prefixWord, tailWord_4628919, baseEnd_4628919] using wordTrace_append hprefix tailTrace_4628919
  have hstable : (prefixWord ++ tailWord_4628919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628919).length < 2 ^ (prefixWord ++ tailWord_4628919).sum := by decide
  have hdescent : baseEnd_4628919 < baseStart_4628919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628936 : List Nat := [2, 1, 3, 1, 3, 3, 1, 2, 2, 3, 2]
def baseStart_4628936 : Nat := 118140960795 + 4628936 * 2 ^ 59
def prefixEnd_4628936 : Nat := 4983230072969 + 3 ^ 40 * 4628936 * 2
def baseEnd_4628936 : Nat := 2376869086900606500311917

theorem tailTrace_4628936 : CollatzResearch.WordTrace tailWord_4628936 prefixEnd_4628936 2376869086900606500311917 := by
  unfold tailWord_4628936
  simp only [CollatzResearch.WordTrace]
  refine ⟨84415582979081453087133331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112554110638775270782844441 84415582979081453087133331)
  ·
    refine ⟨126623374468622179630699997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84415582979081453087133331 126623374468622179630699997)
    ·
      refine ⟨47483765425733317361512499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126623374468622179630699997 47483765425733317361512499)
      ·
        refine ⟨71225648138599976042268749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47483765425733317361512499 71225648138599976042268749)
        ·
          refine ⟨26709618051974991015850781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71225648138599976042268749 26709618051974991015850781)
          ·
            refine ⟨10016106769490621630944043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26709618051974991015850781 10016106769490621630944043)
            ·
              refine ⟨15024160154235932446416065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10016106769490621630944043 15024160154235932446416065)
              ·
                refine ⟨11268120115676949334812049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15024160154235932446416065 11268120115676949334812049)
                ·
                  refine ⟨8451090086757712001109037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11268120115676949334812049 8451090086757712001109037)
                  ·
                    refine ⟨3169158782534142000415889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8451090086757712001109037 3169158782534142000415889)
                    ·
                      refine ⟨2376869086900606500311917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3169158782534142000415889 2376869086900606500311917)
                      ·
                        rfl

theorem cell23_4628936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_4628936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628936 prefixEnd_4628936 := by exact prefixLift 4628936
  have htrace : WordTrace (prefixWord ++ tailWord_4628936) baseStart_4628936 baseEnd_4628936 := by
    simpa [prefixWord, tailWord_4628936, baseEnd_4628936] using wordTrace_append hprefix tailTrace_4628936
  have hstable : (prefixWord ++ tailWord_4628936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628936).length < 2 ^ (prefixWord ++ tailWord_4628936).sum := by decide
  have hdescent : baseEnd_4628936 < baseStart_4628936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628952 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 2, 6, 3]
def baseStart_4628952 : Nat := 118140960795 + 4628952 * 2 ^ 59
def prefixEnd_4628952 : Nat := 4983230072969 + 3 ^ 40 * 4628952 * 2
def baseEnd_4628952 : Nat := 2376877302591078437711843

theorem tailTrace_4628952 : CollatzResearch.WordTrace tailWord_4628952 prefixEnd_4628952 2376877302591078437711843 := by
  unfold tailWord_4628952
  simp only [CollatzResearch.WordTrace]
  refine ⟨84415874763052470453424555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112554499684069960604566073 84415874763052470453424555)
  ·
    refine ⟨126623812144578705680136833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84415874763052470453424555 126623812144578705680136833)
    ·
      refine ⟨94967859108434029260102625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126623812144578705680136833 94967859108434029260102625)
      ·
        refine ⟨71225894331325521945076969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94967859108434029260102625 71225894331325521945076969)
        ·
          refine ⟨53419420748494141458807727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71225894331325521945076969 53419420748494141458807727)
          ·
            refine ⟨80129131122741212188211591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53419420748494141458807727 80129131122741212188211591)
            ·
              refine ⟨120193696684111818282317387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80129131122741212188211591 120193696684111818282317387)
              ·
                refine ⟨180290545026167727423476081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120193696684111818282317387 180290545026167727423476081)
                ·
                  refine ⟨135217908769625795567607061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180290545026167727423476081 135217908769625795567607061)
                  ·
                    refine ⟨6338339473576209167231581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 135217908769625795567607061 6338339473576209167231581)
                    ·
                      refine ⟨2376877302591078437711843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6338339473576209167231581 2376877302591078437711843)
                      ·
                        rfl

theorem cell23_4628952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_4628952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628952 prefixEnd_4628952 := by exact prefixLift 4628952
  have htrace : WordTrace (prefixWord ++ tailWord_4628952) baseStart_4628952 baseEnd_4628952 := by
    simpa [prefixWord, tailWord_4628952, baseEnd_4628952] using wordTrace_append hprefix tailTrace_4628952
  have hstable : (prefixWord ++ tailWord_4628952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628952).length < 2 ^ (prefixWord ++ tailWord_4628952).sum := by decide
  have hdescent : baseEnd_4628952 < baseStart_4628952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628963 : List Nat := [1, 1, 1, 6, 4, 1, 1, 2, 1, 5]
def baseStart_4628963 : Nat := 118140960795 + 4628963 * 2 ^ 59
def prefixEnd_4628963 : Nat := 4983230072969 + 3 ^ 40 * 4628963 * 2
def baseEnd_4628963 : Nat := 792294316959425964891431

theorem tailTrace_4628963 : CollatzResearch.WordTrace tailWord_4628963 prefixEnd_4628963 792294316959425964891431 := by
  unfold tailWord_4628963
  simp only [CollatzResearch.WordTrace]
  refine ⟨168832150729065089785499543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112554767152710059856999695 168832150729065089785499543)
  ·
    refine ⟨253248226093597634678249315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168832150729065089785499543 253248226093597634678249315)
    ·
      refine ⟨379872339140396452017373973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253248226093597634678249315 379872339140396452017373973)
      ·
        refine ⟨17806515897206083688314405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 379872339140396452017373973 17806515897206083688314405)
        ·
          refine ⟨3338721730726140691558951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17806515897206083688314405 3338721730726140691558951)
          ·
            refine ⟨5008082596089211037338427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3338721730726140691558951 5008082596089211037338427)
            ·
              refine ⟨7512123894133816556007641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5008082596089211037338427 7512123894133816556007641)
              ·
                refine ⟨5634092920600362417005731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7512123894133816556007641 5634092920600362417005731)
                ·
                  refine ⟨8451139380900543625508597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5634092920600362417005731 8451139380900543625508597)
                  ·
                    refine ⟨792294316959425964891431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8451139380900543625508597 792294316959425964891431)
                    ·
                      rfl

theorem cell23_4628963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 1, 5].length) (baseStart_4628963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628963 prefixEnd_4628963 := by exact prefixLift 4628963
  have htrace : WordTrace (prefixWord ++ tailWord_4628963) baseStart_4628963 baseEnd_4628963 := by
    simpa [prefixWord, tailWord_4628963, baseEnd_4628963] using wordTrace_append hprefix tailTrace_4628963
  have hstable : (prefixWord ++ tailWord_4628963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628963).length < 2 ^ (prefixWord ++ tailWord_4628963).sum := by decide
  have hdescent : baseEnd_4628963 < baseStart_4628963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628969 : List Nat := [1, 2, 1, 1, 1, 2, 1, 8, 1, 2, 3]
def baseStart_4628969 : Nat := 118140960795 + 4628969 * 2 ^ 59
def prefixEnd_4628969 : Nat := 4983230072969 + 3 ^ 40 * 4628969 * 2
def baseEnd_4628969 : Nat := 2376886031762204871199265

theorem tailTrace_4628969 : CollatzResearch.WordTrace tailWord_4628969 prefixEnd_4628969 2376886031762204871199265 := by
  unfold tailWord_4628969
  simp only [CollatzResearch.WordTrace]
  refine ⟨168832369567043352810217961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112554913044695568540145307 168832369567043352810217961)
  ·
    refine ⟨126624277175282514607663471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168832369567043352810217961 126624277175282514607663471)
    ·
      refine ⟨189936415762923771911495207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126624277175282514607663471 189936415762923771911495207)
      ·
        refine ⟨284904623644385657867242811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189936415762923771911495207 284904623644385657867242811)
        ·
          refine ⟨427356935466578486800864217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284904623644385657867242811 427356935466578486800864217)
          ·
            refine ⟨320517701599933865100648163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 427356935466578486800864217 320517701599933865100648163)
            ·
              refine ⟨480776552399900797650972245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320517701599933865100648163 480776552399900797650972245)
              ·
                refine ⟨5634100223436337472472331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 480776552399900797650972245 5634100223436337472472331)
                ·
                  refine ⟨8451150335154506208708497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5634100223436337472472331 8451150335154506208708497)
                  ·
                    refine ⟨6338362751365879656531373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8451150335154506208708497 6338362751365879656531373)
                    ·
                      refine ⟨2376886031762204871199265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6338362751365879656531373 2376886031762204871199265)
                      ·
                        rfl

theorem cell23_4628969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 2, 3].length) (baseStart_4628969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628969 prefixEnd_4628969 := by exact prefixLift 4628969
  have htrace : WordTrace (prefixWord ++ tailWord_4628969) baseStart_4628969 baseEnd_4628969 := by
    simpa [prefixWord, tailWord_4628969, baseEnd_4628969] using wordTrace_append hprefix tailTrace_4628969
  have hstable : (prefixWord ++ tailWord_4628969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628969).length < 2 ^ (prefixWord ++ tailWord_4628969).sum := by decide
  have hdescent : baseEnd_4628969 < baseStart_4628969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4628994 : List Nat := [3, 4, 1, 2, 2, 2, 2, 2, 1, 1, 3]
def baseStart_4628994 : Nat := 118140960795 + 4628994 * 2 ^ 59
def prefixEnd_4628994 : Nat := 4983230072969 + 3 ^ 40 * 4628994 * 2
def baseEnd_4628994 : Nat := 2376898868778567273386651

theorem tailTrace_4628994 : CollatzResearch.WordTrace tailWord_4628994 prefixEnd_4628994 2376898868778567273386651 := by
  unfold tailWord_4628994
  simp only [CollatzResearch.WordTrace]
  refine ⟨42208320347988195519969509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112555520927968521386585357 42208320347988195519969509)
  ·
    refine ⟨7914060065247786659994283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42208320347988195519969509 7914060065247786659994283)
    ·
      refine ⟨11871090097871679989991425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7914060065247786659994283 11871090097871679989991425)
      ·
        refine ⟨8903317573403759992493569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11871090097871679989991425 8903317573403759992493569)
        ·
          refine ⟨6677488180052819994370177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8903317573403759992493569 6677488180052819994370177)
          ·
            refine ⟨5008116135039614995777633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6677488180052819994370177 5008116135039614995777633)
            ·
              refine ⟨3756087101279711246833225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5008116135039614995777633 3756087101279711246833225)
              ·
                refine ⟨2817065325959783435124919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3756087101279711246833225 2817065325959783435124919)
                ·
                  refine ⟨4225597988939675152687379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2817065325959783435124919 4225597988939675152687379)
                  ·
                    refine ⟨6338396983409512729031069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4225597988939675152687379 6338396983409512729031069)
                    ·
                      refine ⟨2376898868778567273386651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6338396983409512729031069 2376898868778567273386651)
                      ·
                        rfl

theorem cell23_4628994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_4628994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4628994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4628994 prefixEnd_4628994 := by exact prefixLift 4628994
  have htrace : WordTrace (prefixWord ++ tailWord_4628994) baseStart_4628994 baseEnd_4628994 := by
    simpa [prefixWord, tailWord_4628994, baseEnd_4628994] using wordTrace_append hprefix tailTrace_4628994
  have hstable : (prefixWord ++ tailWord_4628994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4628994).length < 2 ^ (prefixWord ++ tailWord_4628994).sum := by decide
  have hdescent : baseEnd_4628994 < baseStart_4628994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4628994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629002 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 1, 9]
def baseStart_4629002 : Nat := 118140960795 + 4629002 * 2 ^ 59
def prefixEnd_4629002 : Nat := 4983230072969 + 3 ^ 40 * 4629002 * 2
def baseEnd_4629002 : Nat := 792300992207934414028871

theorem tailTrace_4629002 : CollatzResearch.WordTrace tailWord_4629002 prefixEnd_4629002 792300992207934414028871 := by
  unfold tailWord_4629002
  simp only [CollatzResearch.WordTrace]
  refine ⟨42208393293980949861542315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112555715450615866297446173 42208393293980949861542315)
  ·
    refine ⟨63312589940971424792313473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42208393293980949861542315 63312589940971424792313473)
    ·
      refine ⟨47484442455728568594235105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63312589940971424792313473 47484442455728568594235105)
      ·
        refine ⟨35613331841796426445676329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47484442455728568594235105 35613331841796426445676329)
        ·
          refine ⟨26709998881347319834257247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35613331841796426445676329 26709998881347319834257247)
          ·
            refine ⟨40064998322020979751385871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26709998881347319834257247 40064998322020979751385871)
            ·
              refine ⟨60097497483031469627078807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40064998322020979751385871 60097497483031469627078807)
              ·
                refine ⟨90146246224547204440618211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60097497483031469627078807 90146246224547204440618211)
                ·
                  refine ⟨135219369336820806660927317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90146246224547204440618211 135219369336820806660927317)
                  ·
                    refine ⟨792300992207934414028871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 135219369336820806660927317 792300992207934414028871)
                    ·
                      rfl

theorem cell23_4629002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_4629002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629002 prefixEnd_4629002 := by exact prefixLift 4629002
  have htrace : WordTrace (prefixWord ++ tailWord_4629002) baseStart_4629002 baseEnd_4629002 := by
    simpa [prefixWord, tailWord_4629002, baseEnd_4629002] using wordTrace_append hprefix tailTrace_4629002
  have hstable : (prefixWord ++ tailWord_4629002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629002).length < 2 ^ (prefixWord ++ tailWord_4629002).sum := by decide
  have hdescent : baseEnd_4629002 < baseStart_4629002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629016 : List Nat := [2, 1, 2, 3, 3, 2, 2, 1, 1, 3, 3]
def baseStart_4629016 : Nat := 118140960795 + 4629016 * 2 ^ 59
def prefixEnd_4629016 : Nat := 4983230072969 + 3 ^ 40 * 4629016 * 2
def baseEnd_4629016 : Nat := 2376910165352966187311549

theorem tailTrace_4629016 : CollatzResearch.WordTrace tailWord_4629016 prefixEnd_4629016 2376910165352966187311549 := by
  unfold tailWord_4629016
  simp only [CollatzResearch.WordTrace]
  refine ⟨84417041898936539918589451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112556055865248719891452601 84417041898936539918589451)
  ·
    refine ⟨126625562848404809877884177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84417041898936539918589451 126625562848404809877884177)
    ·
      refine ⟨94969172136303607408413133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126625562848404809877884177 94969172136303607408413133)
      ·
        refine ⟨35613439551113852778154925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94969172136303607408413133 35613439551113852778154925)
        ·
          refine ⟨13355039831667694791808097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35613439551113852778154925 13355039831667694791808097)
          ·
            refine ⟨10016279873750771093856073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13355039831667694791808097 10016279873750771093856073)
            ·
              refine ⟨7512209905313078320392055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10016279873750771093856073 7512209905313078320392055)
              ·
                refine ⟨11268314857969617480588083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7512209905313078320392055 11268314857969617480588083)
                ·
                  refine ⟨16902472286954426220882125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11268314857969617480588083 16902472286954426220882125)
                  ·
                    refine ⟨6338427107607909832830797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16902472286954426220882125 6338427107607909832830797)
                    ·
                      refine ⟨2376910165352966187311549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6338427107607909832830797 2376910165352966187311549)
                      ·
                        rfl

theorem cell23_4629016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_4629016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629016 prefixEnd_4629016 := by exact prefixLift 4629016
  have htrace : WordTrace (prefixWord ++ tailWord_4629016) baseStart_4629016 baseEnd_4629016 := by
    simpa [prefixWord, tailWord_4629016, baseEnd_4629016] using wordTrace_append hprefix tailTrace_4629016
  have hstable : (prefixWord ++ tailWord_4629016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629016).length < 2 ^ (prefixWord ++ tailWord_4629016).sum := by decide
  have hdescent : baseEnd_4629016 < baseStart_4629016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629037 : List Nat := [1, 5, 4, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_4629037 : Nat := 118140960795 + 4629037 * 2 ^ 59
def prefixEnd_4629037 : Nat := 4983230072969 + 3 ^ 40 * 4629037 * 2
def baseEnd_4629037 : Nat := 2376920948446710605148953

theorem tailTrace_4629037 : CollatzResearch.WordTrace tailWord_4629037 prefixEnd_4629037 2376920948446710605148953 := by
  unfold tailWord_4629037
  simp only [CollatzResearch.WordTrace]
  refine ⟨168834849730797000423693365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112556566487198000282462243 168834849730797000423693365)
  ·
    refine ⟨15828267162262218789721253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 168834849730797000423693365 15828267162262218789721253)
    ·
      refine ⟨2967800092924166023072735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15828267162262218789721253 2967800092924166023072735)
      ·
        refine ⟨4451700139386249034609103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2967800092924166023072735 4451700139386249034609103)
        ·
          refine ⟨6677550209079373551913655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4451700139386249034609103 6677550209079373551913655)
          ·
            refine ⟨10016325313619060327870483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6677550209079373551913655 10016325313619060327870483)
            ·
              refine ⟨15024487970428590491805725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10016325313619060327870483 15024487970428590491805725)
              ·
                refine ⟨5634182988910721434427147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15024487970428590491805725 5634182988910721434427147)
                ·
                  refine ⟨8451274483366082151640721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5634182988910721434427147 8451274483366082151640721)
                  ·
                    refine ⟨6338455862524561613730541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8451274483366082151640721 6338455862524561613730541)
                    ·
                      refine ⟨2376920948446710605148953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6338455862524561613730541 2376920948446710605148953)
                      ·
                        rfl

theorem cell23_4629037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_4629037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629037 prefixEnd_4629037 := by exact prefixLift 4629037
  have htrace : WordTrace (prefixWord ++ tailWord_4629037) baseStart_4629037 baseEnd_4629037 := by
    simpa [prefixWord, tailWord_4629037, baseEnd_4629037] using wordTrace_append hprefix tailTrace_4629037
  have hstable : (prefixWord ++ tailWord_4629037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629037).length < 2 ^ (prefixWord ++ tailWord_4629037).sum := by decide
  have hdescent : baseEnd_4629037 < baseStart_4629037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629073 : List Nat := [1, 2, 2, 1, 3, 5, 1, 1, 1, 4, 2]
def baseStart_4629073 : Nat := 118140960795 + 4629073 * 2 ^ 59
def prefixEnd_4629073 : Nat := 4983230072969 + 3 ^ 40 * 4629073 * 2
def baseEnd_4629073 : Nat := 2376939433750272464298787

theorem tailTrace_4629073 : CollatzResearch.WordTrace tailWord_4629073 prefixEnd_4629073 2376939433750272464298787 := by
  unfold tailWord_4629073
  simp only [CollatzResearch.WordTrace]
  refine ⟨168836162758666578572003873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112557441839111052381335915 168836162758666578572003873)
  ·
    refine ⟨126627122068999933929002905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168836162758666578572003873 126627122068999933929002905)
    ·
      refine ⟨94970341551749950446752179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126627122068999933929002905 94970341551749950446752179)
      ·
        refine ⟨142455512327624925670128269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94970341551749950446752179 142455512327624925670128269)
        ·
          refine ⟨53420817122859347126298101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142455512327624925670128269 53420817122859347126298101)
          ·
            refine ⟨5008201605268063793090447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53420817122859347126298101 5008201605268063793090447)
            ·
              refine ⟨7512302407902095689635671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5008201605268063793090447 7512302407902095689635671)
              ·
                refine ⟨11268453611853143534453507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7512302407902095689635671 11268453611853143534453507)
                ·
                  refine ⟨16902680417779715301680261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11268453611853143534453507 16902680417779715301680261)
                  ·
                    refine ⟨3169252578333696619065049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16902680417779715301680261 3169252578333696619065049)
                    ·
                      refine ⟨2376939433750272464298787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3169252578333696619065049 2376939433750272464298787)
                      ·
                        rfl

theorem cell23_4629073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 4, 2].length) (baseStart_4629073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629073 prefixEnd_4629073 := by exact prefixLift 4629073
  have htrace : WordTrace (prefixWord ++ tailWord_4629073) baseStart_4629073 baseEnd_4629073 := by
    simpa [prefixWord, tailWord_4629073, baseEnd_4629073] using wordTrace_append hprefix tailTrace_4629073
  have hstable : (prefixWord ++ tailWord_4629073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629073).length < 2 ^ (prefixWord ++ tailWord_4629073).sum := by decide
  have hdescent : baseEnd_4629073 < baseStart_4629073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629113 : List Nat := [1, 2, 1, 3, 3, 3, 3, 2, 5]
def baseStart_4629113 : Nat := 118140960795 + 4629113 * 2 ^ 59
def prefixEnd_4629113 : Nat := 4983230072969 + 3 ^ 40 * 4629113 * 2
def baseEnd_4629113 : Nat := 264106663664050256422067

theorem tailTrace_4629113 : CollatzResearch.WordTrace tailWord_4629113 prefixEnd_4629113 264106663664050256422067 := by
  unfold tailWord_4629113
  simp only [CollatzResearch.WordTrace]
  refine ⟨168837621678521665403459993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112558414452347776935639995 168837621678521665403459993)
  ·
    refine ⟨126628216258891249052594995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168837621678521665403459993 126628216258891249052594995)
    ·
      refine ⟨189942324388336873578892493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126628216258891249052594995 189942324388336873578892493)
      ·
        refine ⟨71228371645626327592084685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189942324388336873578892493 71228371645626327592084685)
        ·
          refine ⟨26710639367109872847031757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71228371645626327592084685 26710639367109872847031757)
          ·
            refine ⟨10016489762666202317636909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26710639367109872847031757 10016489762666202317636909)
            ·
              refine ⟨3756183660999825869113841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10016489762666202317636909 3756183660999825869113841)
              ·
                refine ⟨2817137745749869401835381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3756183660999825869113841 2817137745749869401835381)
                ·
                  refine ⟨264106663664050256422067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2817137745749869401835381 264106663664050256422067)
                  ·
                    rfl

theorem cell23_4629113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 5].length) (baseStart_4629113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629113 prefixEnd_4629113 := by exact prefixLift 4629113
  have htrace : WordTrace (prefixWord ++ tailWord_4629113) baseStart_4629113 baseEnd_4629113 := by
    simpa [prefixWord, tailWord_4629113, baseEnd_4629113] using wordTrace_append hprefix tailTrace_4629113
  have hstable : (prefixWord ++ tailWord_4629113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629113).length < 2 ^ (prefixWord ++ tailWord_4629113).sum := by decide
  have hdescent : baseEnd_4629113 < baseStart_4629113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629129 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 6, 1, 4]
def baseStart_4629129 : Nat := 118140960795 + 4629129 * 2 ^ 59
def prefixEnd_4629129 : Nat := 4983230072969 + 3 ^ 40 * 4629129 * 2
def baseEnd_4629129 : Nat := 2376968188666924245198529

theorem tailTrace_4629129 : CollatzResearch.WordTrace tailWord_4629129 prefixEnd_4629129 2376968188666924245198529 := by
  unfold tailWord_4629129
  simp only [CollatzResearch.WordTrace]
  refine ⟨168838205246463700136042441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112558803497642466757361627 168838205246463700136042441)
  ·
    refine ⟨126628653934847775102031831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168838205246463700136042441 126628653934847775102031831)
    ·
      refine ⟨189942980902271662653047747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126628653934847775102031831 189942980902271662653047747)
      ·
        refine ⟨284914471353407493979571621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189942980902271662653047747 284914471353407493979571621)
        ·
          refine ⟨53421463378763905121169679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 284914471353407493979571621 53421463378763905121169679)
          ·
            refine ⟨80132195068145857681754519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53421463378763905121169679 80132195068145857681754519)
            ·
              refine ⟨120198292602218786522631779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80132195068145857681754519 120198292602218786522631779)
              ·
                refine ⟨180297438903328179783947669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120198292602218786522631779 180297438903328179783947669)
                ·
                  refine ⟨8451442448593508427372547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 180297438903328179783947669 8451442448593508427372547)
                  ·
                    refine ⟨12677163672890262641058821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8451442448593508427372547 12677163672890262641058821)
                    ·
                      refine ⟨2376968188666924245198529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12677163672890262641058821 2376968188666924245198529)
                      ·
                        rfl

theorem cell23_4629129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 1, 4].length) (baseStart_4629129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629129 prefixEnd_4629129 := by exact prefixLift 4629129
  have htrace : WordTrace (prefixWord ++ tailWord_4629129) baseStart_4629129 baseEnd_4629129 := by
    simpa [prefixWord, tailWord_4629129, baseEnd_4629129] using wordTrace_append hprefix tailTrace_4629129
  have hstable : (prefixWord ++ tailWord_4629129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629129).length < 2 ^ (prefixWord ++ tailWord_4629129).sum := by decide
  have hdescent : baseEnd_4629129 < baseStart_4629129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629179 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 3]
def baseStart_4629179 : Nat := 118140960795 + 4629179 * 2 ^ 59
def prefixEnd_4629179 : Nat := 4983230072969 + 3 ^ 40 * 4629179 * 2
def baseEnd_4629179 : Nat := 2376993862699649049573299

theorem tailTrace_4629179 : CollatzResearch.WordTrace tailWord_4629179 prefixEnd_4629179 2376993862699649049573299 := by
  unfold tailWord_4629179
  simp only [CollatzResearch.WordTrace]
  refine ⟨168840028896282558675362591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112560019264188372450241727 168840028896282558675362591)
  ·
    refine ⟨253260043344423838013043887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168840028896282558675362591 253260043344423838013043887)
    ·
      refine ⟨379890065016635757019565831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253260043344423838013043887 379890065016635757019565831)
      ·
        refine ⟨569835097524953635529348747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379890065016635757019565831 569835097524953635529348747)
        ·
          refine ⟨854752646287430453294023121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569835097524953635529348747 854752646287430453294023121)
          ·
            refine ⟨641064484715572839970517341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 854752646287430453294023121 641064484715572839970517341)
            ·
              refine ⟨240399181768339814988944003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 641064484715572839970517341 240399181768339814988944003)
              ·
                refine ⟨360598772652509722483416005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240399181768339814988944003 360598772652509722483416005)
                ·
                  refine ⟨67612269872345572965640501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 360598772652509722483416005 67612269872345572965640501)
                  ·
                    refine ⟨6338650300532397465528797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67612269872345572965640501 6338650300532397465528797)
                    ·
                      refine ⟨2376993862699649049573299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6338650300532397465528797 2376993862699649049573299)
                      ·
                        rfl

theorem cell23_4629179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 3].length) (baseStart_4629179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629179 prefixEnd_4629179 := by exact prefixLift 4629179
  have htrace : WordTrace (prefixWord ++ tailWord_4629179) baseStart_4629179 baseEnd_4629179 := by
    simpa [prefixWord, tailWord_4629179, baseEnd_4629179] using wordTrace_append hprefix tailTrace_4629179
  have hstable : (prefixWord ++ tailWord_4629179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629179).length < 2 ^ (prefixWord ++ tailWord_4629179).sum := by decide
  have hdescent : baseEnd_4629179 < baseStart_4629179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629197 : List Nat := [1, 6, 2, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_4629197 : Nat := 118140960795 + 4629197 * 2 ^ 59
def prefixEnd_4629197 : Nat := 4983230072969 + 3 ^ 40 * 4629197 * 2
def baseEnd_4629197 : Nat := 2377003105351429979148217

theorem tailTrace_4629197 : CollatzResearch.WordTrace tailWord_4629197 prefixEnd_4629197 2377003105351429979148217 := by
  unfold tailWord_4629197
  simp only [CollatzResearch.WordTrace]
  refine ⟨168840685410217347749517845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112560456940144898499678563 168840685410217347749517845)
  ·
    refine ⟨7914407128603938175758649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 168840685410217347749517845 7914407128603938175758649)
    ·
      refine ⟨5935805346452953631818987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7914407128603938175758649 5935805346452953631818987)
      ·
        refine ⟨8903708019679430447728481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5935805346452953631818987 8903708019679430447728481)
        ·
          refine ⟨6677781014759572835796361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8903708019679430447728481 6677781014759572835796361)
          ·
            refine ⟨5008335761069679626847271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6677781014759572835796361 5008335761069679626847271)
            ·
              refine ⟨7512503641604519440270907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5008335761069679626847271 7512503641604519440270907)
              ·
                refine ⟨11268755462406779160406361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7512503641604519440270907 11268755462406779160406361)
                ·
                  refine ⟨8451566596805084370304771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11268755462406779160406361 8451566596805084370304771)
                  ·
                    refine ⟨12677349895207626555457157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8451566596805084370304771 12677349895207626555457157)
                    ·
                      refine ⟨2377003105351429979148217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12677349895207626555457157 2377003105351429979148217)
                      ·
                        rfl

theorem cell23_4629197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_4629197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629197 prefixEnd_4629197 := by exact prefixLift 4629197
  have htrace : WordTrace (prefixWord ++ tailWord_4629197) baseStart_4629197 baseEnd_4629197 := by
    simpa [prefixWord, tailWord_4629197, baseEnd_4629197] using wordTrace_append hprefix tailTrace_4629197
  have hstable : (prefixWord ++ tailWord_4629197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629197).length < 2 ^ (prefixWord ++ tailWord_4629197).sum := by decide
  have hdescent : baseEnd_4629197 < baseStart_4629197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629230 : List Nat := [4, 1, 2, 1, 1, 4, 2, 1, 3, 1, 3]
def baseStart_4629230 : Nat := 118140960795 + 4629230 * 2 ^ 59
def prefixEnd_4629230 : Nat := 4983230072969 + 3 ^ 40 * 4629230 * 2
def baseEnd_4629230 : Nat := 2377020050213028350035565

theorem tailTrace_4629230 : CollatzResearch.WordTrace tailWord_4629230 prefixEnd_4629230 2377020050213028350035565 := by
  unfold tailWord_4629230
  simp only [CollatzResearch.WordTrace]
  refine ⟨21105236127387224298183643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112561259346065196256979429 21105236127387224298183643)
  ·
    refine ⟨31657854191080836447275465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21105236127387224298183643 31657854191080836447275465)
    ·
      refine ⟨23743390643310627335456599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31657854191080836447275465 23743390643310627335456599)
      ·
        refine ⟨35615085964965941003184899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23743390643310627335456599 35615085964965941003184899)
        ·
          refine ⟨53422628947448911504777349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35615085964965941003184899 53422628947448911504777349)
          ·
            refine ⟨10016742927646670907145753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53422628947448911504777349 10016742927646670907145753)
            ·
              refine ⟨7512557195735003180359315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10016742927646670907145753 7512557195735003180359315)
              ·
                refine ⟨11268835793602504770538973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7512557195735003180359315 11268835793602504770538973)
                ·
                  refine ⟨4225813422600939288952115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11268835793602504770538973 4225813422600939288952115)
                  ·
                    refine ⟨6338720133901408933428173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4225813422600939288952115 6338720133901408933428173)
                    ·
                      refine ⟨2377020050213028350035565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6338720133901408933428173 2377020050213028350035565)
                      ·
                        rfl

theorem cell23_4629230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_4629230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629230 prefixEnd_4629230 := by exact prefixLift 4629230
  have htrace : WordTrace (prefixWord ++ tailWord_4629230) baseStart_4629230 baseEnd_4629230 := by
    simpa [prefixWord, tailWord_4629230, baseEnd_4629230] using wordTrace_append hprefix tailTrace_4629230
  have hstable : (prefixWord ++ tailWord_4629230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629230).length < 2 ^ (prefixWord ++ tailWord_4629230).sum := by decide
  have hdescent : baseEnd_4629230 < baseStart_4629230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629250 : List Nat := [3, 4, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_4629250 : Nat := 118140960795 + 4629250 * 2 ^ 59
def prefixEnd_4629250 : Nat := 4983230072969 + 3 ^ 40 * 4629250 * 2
def baseEnd_4629250 : Nat := 792343439942039423928491

theorem tailTrace_4629250 : CollatzResearch.WordTrace tailWord_4629250 prefixEnd_4629250 792343439942039423928491 := by
  unfold tailWord_4629250
  simp only [CollatzResearch.WordTrace]
  refine ⟨42210654619756334450299301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112561745652683558534131469 42210654619756334450299301)
  ·
    refine ⟨7914497741204312709431119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42210654619756334450299301 7914497741204312709431119)
    ·
      refine ⟨11871746611806469064146679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7914497741204312709431119 11871746611806469064146679)
      ·
        refine ⟨17807619917709703596220019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11871746611806469064146679 17807619917709703596220019)
        ·
          refine ⟨26711429876564555394330029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17807619917709703596220019 26711429876564555394330029)
          ·
            refine ⟨10016786203711708272873761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26711429876564555394330029 10016786203711708272873761)
            ·
              refine ⟨7512589652783781204655321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10016786203711708272873761 7512589652783781204655321)
              ·
                refine ⟨5634442239587835903491491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7512589652783781204655321 5634442239587835903491491)
                ·
                  refine ⟨8451663359381753855237237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5634442239587835903491491 8451663359381753855237237)
                  ·
                    refine ⟨792343439942039423928491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8451663359381753855237237 792343439942039423928491)
                    ·
                      rfl

theorem cell23_4629250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_4629250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629250 prefixEnd_4629250 := by exact prefixLift 4629250
  have htrace : WordTrace (prefixWord ++ tailWord_4629250) baseStart_4629250 baseEnd_4629250 := by
    simpa [prefixWord, tailWord_4629250, baseEnd_4629250] using wordTrace_append hprefix tailTrace_4629250
  have hstable : (prefixWord ++ tailWord_4629250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629250).length < 2 ^ (prefixWord ++ tailWord_4629250).sum := by decide
  have hdescent : baseEnd_4629250 < baseStart_4629250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629276 : List Nat := [2, 2, 3, 1, 1, 5, 9]
def baseStart_4629276 : Nat := 118140960795 + 4629276 * 2 ^ 59
def prefixEnd_4629276 : Nat := 4983230072969 + 3 ^ 40 * 4629276 * 2
def baseEnd_4629276 : Nat := 29346218152137471235313

theorem tailTrace_4629276 : CollatzResearch.WordTrace tailWord_4629276 prefixEnd_4629276 29346218152137471235313 := by
  unfold tailWord_4629276
  simp only [CollatzResearch.WordTrace]
  refine ⟨84421783388465572120821841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112562377851287429494429121 84421783388465572120821841)
  ·
    refine ⟨63316337541349179090616381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84421783388465572120821841 63316337541349179090616381)
    ·
      refine ⟨23743626578005942158981143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63316337541349179090616381 23743626578005942158981143)
      ·
        refine ⟨35615439867008913238471715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23743626578005942158981143 35615439867008913238471715)
        ·
          refine ⟨53423159800513369857707573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35615439867008913238471715 53423159800513369857707573)
          ·
            refine ⟨5008421231298128424160085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53423159800513369857707573 5008421231298128424160085)
            ·
              refine ⟨29346218152137471235313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5008421231298128424160085 29346218152137471235313)
              ·
                rfl

theorem cell23_4629276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 9].length) (baseStart_4629276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629276 prefixEnd_4629276 := by exact prefixLift 4629276
  have htrace : WordTrace (prefixWord ++ tailWord_4629276) baseStart_4629276 baseEnd_4629276 := by
    simpa [prefixWord, tailWord_4629276, baseEnd_4629276] using wordTrace_append hprefix tailTrace_4629276
  have hstable : (prefixWord ++ tailWord_4629276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629276).length < 2 ^ (prefixWord ++ tailWord_4629276).sum := by decide
  have hdescent : baseEnd_4629276 < baseStart_4629276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629289 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 1, 9]
def baseStart_4629289 : Nat := 118140960795 + 4629289 * 2 ^ 59
def prefixEnd_4629289 : Nat := 4983230072969 + 3 ^ 40 * 4629289 * 2
def baseEnd_4629289 : Nat := 792350115190547873065931

theorem tailTrace_4629289 : CollatzResearch.WordTrace tailWord_4629289 prefixEnd_4629289 792350115190547873065931 := by
  unfold tailWord_4629289
  simp only [CollatzResearch.WordTrace]
  refine ⟨168844040925884047461866921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112562693950589364974577947 168844040925884047461866921)
  ·
    refine ⟨126633030694413035596400191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168844040925884047461866921 126633030694413035596400191)
    ·
      refine ⟨189949546041619553394600287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126633030694413035596400191 189949546041619553394600287)
      ·
        refine ⟨284924319062429330091900431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189949546041619553394600287 284924319062429330091900431)
        ·
          refine ⟨427386478593643995137850647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284924319062429330091900431 427386478593643995137850647)
          ·
            refine ⟨641079717890465992706775971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427386478593643995137850647 641079717890465992706775971)
            ·
              refine ⟨961619576835698989060163957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 641079717890465992706775971 961619576835698989060163957)
              ·
                refine ⟨90151835328346780224390371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 961619576835698989060163957 90151835328346780224390371)
                ·
                  refine ⟨135227752992520170336585557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90151835328346780224390371 135227752992520170336585557)
                  ·
                    refine ⟨792350115190547873065931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 135227752992520170336585557 792350115190547873065931)
                    ·
                      rfl

theorem cell23_4629289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 9].length) (baseStart_4629289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629289 prefixEnd_4629289 := by exact prefixLift 4629289
  have htrace : WordTrace (prefixWord ++ tailWord_4629289) baseStart_4629289 baseEnd_4629289 := by
    simpa [prefixWord, tailWord_4629289, baseEnd_4629289] using wordTrace_append hprefix tailTrace_4629289
  have hstable : (prefixWord ++ tailWord_4629289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629289).length < 2 ^ (prefixWord ++ tailWord_4629289).sum := by decide
  have hdescent : baseEnd_4629289 < baseStart_4629289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629326 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_4629326 : Nat := 118140960795 + 4629326 * 2 ^ 59
def prefixEnd_4629326 : Nat := 4983230072969 + 3 ^ 40 * 4629326 * 2
def baseEnd_4629326 : Nat := 2377069344355859974435123

theorem tailTrace_4629326 : CollatzResearch.WordTrace tailWord_4629326 prefixEnd_4629326 2377069344355859974435123 := by
  unfold tailWord_4629326
  simp only [CollatzResearch.WordTrace]
  refine ⟨21105673803343750347620479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112563593617833335187309221 21105673803343750347620479)
  ·
    refine ⟨31658510705015625521430719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21105673803343750347620479 31658510705015625521430719)
    ·
      refine ⟨47487766057523438282146079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31658510705015625521430719 47487766057523438282146079)
      ·
        refine ⟨71231649086285157423219119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47487766057523438282146079 71231649086285157423219119)
        ·
          refine ⟨106847473629427736134828679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71231649086285157423219119 106847473629427736134828679)
          ·
            refine ⟨160271210444141604202243019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106847473629427736134828679 160271210444141604202243019)
            ·
              refine ⟨240406815666212406303364529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160271210444141604202243019 240406815666212406303364529)
              ·
                refine ⟨180305111749659304727523397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240406815666212406303364529 180305111749659304727523397)
                ·
                  refine ⟨33807208453061119636410637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 180305111749659304727523397 33807208453061119636410637)
                  ·
                    refine ⟨12677703169897919863653989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33807208453061119636410637 12677703169897919863653989)
                    ·
                      refine ⟨2377069344355859974435123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12677703169897919863653989 2377069344355859974435123)
                      ·
                        rfl

theorem cell23_4629326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_4629326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629326 prefixEnd_4629326 := by exact prefixLift 4629326
  have htrace : WordTrace (prefixWord ++ tailWord_4629326) baseStart_4629326 baseEnd_4629326 := by
    simpa [prefixWord, tailWord_4629326, baseEnd_4629326] using wordTrace_append hprefix tailTrace_4629326
  have hstable : (prefixWord ++ tailWord_4629326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629326).length < 2 ^ (prefixWord ++ tailWord_4629326).sum := by decide
  have hdescent : baseEnd_4629326 < baseStart_4629326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629343 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 3, 4, 2]
def baseStart_4629343 : Nat := 118140960795 + 4629343 * 2 ^ 59
def prefixEnd_4629343 : Nat := 4983230072969 + 3 ^ 40 * 4629343 * 2
def baseEnd_4629343 : Nat := 2377078073526986407922545

theorem tailTrace_4629343 : CollatzResearch.WordTrace tailWord_4629343 prefixEnd_4629343 2377078073526986407922545 := by
  unfold tailWord_4629343
  simp only [CollatzResearch.WordTrace]
  refine ⟨168846010467688414684332683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112564006978458943122888455 168846010467688414684332683)
  ·
    refine ⟨253269015701532622026499025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168846010467688414684332683 253269015701532622026499025)
    ·
      refine ⟨189951761776149466519874269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253269015701532622026499025 189951761776149466519874269)
      ·
        refine ⟨71231910666056049944952851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189951761776149466519874269 71231910666056049944952851)
        ·
          refine ⟨106847865999084074917429277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71231910666056049944952851 106847865999084074917429277)
          ·
            refine ⟨40067949749656528094035979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106847865999084074917429277 40067949749656528094035979)
            ·
              refine ⟨60101924624484792141053969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40067949749656528094035979 60101924624484792141053969)
              ·
                refine ⟨45076443468363594105790477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60101924624484792141053969 45076443468363594105790477)
                ·
                  refine ⟨16903666300636347789671429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45076443468363594105790477 16903666300636347789671429)
                  ·
                    refine ⟨3169437431369315210563393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16903666300636347789671429 3169437431369315210563393)
                    ·
                      refine ⟨2377078073526986407922545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3169437431369315210563393 2377078073526986407922545)
                      ·
                        rfl

theorem cell23_4629343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_4629343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629343 prefixEnd_4629343 := by exact prefixLift 4629343
  have htrace : WordTrace (prefixWord ++ tailWord_4629343) baseStart_4629343 baseEnd_4629343 := by
    simpa [prefixWord, tailWord_4629343, baseEnd_4629343] using wordTrace_append hprefix tailTrace_4629343
  have hstable : (prefixWord ++ tailWord_4629343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629343).length < 2 ^ (prefixWord ++ tailWord_4629343).sum := by decide
  have hdescent : baseEnd_4629343 < baseStart_4629343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629394 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_4629394 : Nat := 118140960795 + 4629394 * 2 ^ 59
def prefixEnd_4629394 : Nat := 4983230072969 + 3 ^ 40 * 4629394 * 2
def baseEnd_4629394 : Nat := 2377104261040365708384811

theorem tailTrace_4629394 : CollatzResearch.WordTrace tailWord_4629394 prefixEnd_4629394 2377104261040365708384811 := by
  unfold tailWord_4629394
  simp only [CollatzResearch.WordTrace]
  refine ⟨42211967647625912598609809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112565247060335766929626157 42211967647625912598609809)
  ·
    refine ⟨31658975735719434448957357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42211967647625912598609809 31658975735719434448957357)
    ·
      refine ⟨11872115900894787918359009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31658975735719434448957357 11872115900894787918359009)
      ·
        refine ⟨8904086925671090938769257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11872115900894787918359009 8904086925671090938769257)
        ·
          refine ⟨6678065194253318204076943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8904086925671090938769257 6678065194253318204076943)
          ·
            refine ⟨10017097791379977306115415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6678065194253318204076943 10017097791379977306115415)
            ·
              refine ⟨15025646687069965959173123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10017097791379977306115415 15025646687069965959173123)
              ·
                refine ⟨22538470030604948938759685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15025646687069965959173123 22538470030604948938759685)
                ·
                  refine ⟨4225963130738427926017441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22538470030604948938759685 4225963130738427926017441)
                  ·
                    refine ⟨3169472348053820944513081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4225963130738427926017441 3169472348053820944513081)
                    ·
                      refine ⟨2377104261040365708384811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3169472348053820944513081 2377104261040365708384811)
                      ·
                        rfl

theorem cell23_4629394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_4629394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629394 prefixEnd_4629394 := by exact prefixLift 4629394
  have htrace : WordTrace (prefixWord ++ tailWord_4629394) baseStart_4629394 baseEnd_4629394 := by
    simpa [prefixWord, tailWord_4629394, baseEnd_4629394] using wordTrace_append hprefix tailTrace_4629394
  have hstable : (prefixWord ++ tailWord_4629394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629394).length < 2 ^ (prefixWord ++ tailWord_4629394).sum := by decide
  have hdescent : baseEnd_4629394 < baseStart_4629394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629410 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_4629410 : Nat := 118140960795 + 4629410 * 2 ^ 59
def prefixEnd_4629410 : Nat := 4983230072969 + 3 ^ 40 * 4629410 * 2
def baseEnd_4629410 : Nat := 2377112476730837645784737

theorem tailTrace_4629410 : CollatzResearch.WordTrace tailWord_4629410 prefixEnd_4629410 2377112476730837645784737 := by
  unfold tailWord_4629410
  simp only [CollatzResearch.WordTrace]
  refine ⟨42212113539611421281755421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112565636105630456751347789 42212113539611421281755421)
  ·
    refine ⟨15829542577354282980658283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42212113539611421281755421 15829542577354282980658283)
    ·
      refine ⟨23744313866031424470987425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15829542577354282980658283 23744313866031424470987425)
      ·
        refine ⟨17808235399523568353240569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23744313866031424470987425 17808235399523568353240569)
        ·
          refine ⟨13356176549642676264930427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17808235399523568353240569 13356176549642676264930427)
          ·
            refine ⟨20034264824464014397395641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13356176549642676264930427 20034264824464014397395641)
            ·
              refine ⟨15025698618348010798046731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20034264824464014397395641 15025698618348010798046731)
              ·
                refine ⟨22538547927522016197070097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15025698618348010798046731 22538547927522016197070097)
                ·
                  refine ⟨16903910945641512147802573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22538547927522016197070097 16903910945641512147802573)
                  ·
                    refine ⟨6338966604615567055425965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16903910945641512147802573 6338966604615567055425965)
                    ·
                      refine ⟨2377112476730837645784737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6338966604615567055425965 2377112476730837645784737)
                      ·
                        rfl

theorem cell23_4629410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_4629410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629410 prefixEnd_4629410 := by exact prefixLift 4629410
  have htrace : WordTrace (prefixWord ++ tailWord_4629410) baseStart_4629410 baseEnd_4629410 := by
    simpa [prefixWord, tailWord_4629410, baseEnd_4629410] using wordTrace_append hprefix tailTrace_4629410
  have hstable : (prefixWord ++ tailWord_4629410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629410).length < 2 ^ (prefixWord ++ tailWord_4629410).sum := by decide
  have hdescent : baseEnd_4629410 < baseStart_4629410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629433 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 1, 3, 4]
def baseStart_4629433 : Nat := 118140960795 + 4629433 * 2 ^ 59
def prefixEnd_4629433 : Nat := 4983230072969 + 3 ^ 40 * 4629433 * 2
def baseEnd_4629433 : Nat := 2377124286785891055797131

theorem tailTrace_4629433 : CollatzResearch.WordTrace tailWord_4629433 prefixEnd_4629433 2377124286785891055797131 := by
  unfold tailWord_4629433
  simp only [CollatzResearch.WordTrace]
  refine ⟨168849293037362360055108953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112566195358241573370072635 168849293037362360055108953)
  ·
    refine ⟨126636969778021770041331715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168849293037362360055108953 126636969778021770041331715)
    ·
      refine ⟨189955454667032655061997573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126636969778021770041331715 189955454667032655061997573)
      ·
        refine ⟨35616647750068622824124545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189955454667032655061997573 35616647750068622824124545)
        ·
          refine ⟨26712485812551467118093409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35616647750068622824124545 26712485812551467118093409)
          ·
            refine ⟨20034364359413600338570057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26712485812551467118093409 20034364359413600338570057)
            ·
              refine ⟨15025773269560200253927543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20034364359413600338570057 15025773269560200253927543)
              ·
                refine ⟨22538659904340300380891315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15025773269560200253927543 22538659904340300380891315)
                ·
                  refine ⟨33807989856510450571336973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22538659904340300380891315 33807989856510450571336973)
                  ·
                    refine ⟨12677996196191418964251365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33807989856510450571336973 12677996196191418964251365)
                    ·
                      refine ⟨2377124286785891055797131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12677996196191418964251365 2377124286785891055797131)
                      ·
                        rfl

theorem cell23_4629433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_4629433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629433 prefixEnd_4629433 := by exact prefixLift 4629433
  have htrace : WordTrace (prefixWord ++ tailWord_4629433) baseStart_4629433 baseEnd_4629433 := by
    simpa [prefixWord, tailWord_4629433, baseEnd_4629433] using wordTrace_append hprefix tailTrace_4629433
  have hstable : (prefixWord ++ tailWord_4629433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629433).length < 2 ^ (prefixWord ++ tailWord_4629433).sum := by decide
  have hdescent : baseEnd_4629433 < baseStart_4629433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629550 : List Nat := [4, 1, 3, 1, 1, 1, 1, 4, 1, 6]
def baseStart_4629550 : Nat := 118140960795 + 4629550 * 2 ^ 59
def prefixEnd_4629550 : Nat := 4983230072969 + 3 ^ 40 * 4629550 * 2
def baseEnd_4629550 : Nat := 792394788007489032678031

theorem tailTrace_4629550 : CollatzResearch.WordTrace tailWord_4629550 prefixEnd_4629550 792394788007489032678031 := by
  unfold tailWord_4629550
  simp only [CollatzResearch.WordTrace]
  refine ⟨21106695047242311129639763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112569040251958992691412069 21106695047242311129639763)
  ·
    refine ⟨31660042570863466694459645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21106695047242311129639763 31660042570863466694459645)
    ·
      refine ⟨11872515964073800010422367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31660042570863466694459645 11872515964073800010422367)
      ·
        refine ⟨17808773946110700015633551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11872515964073800010422367 17808773946110700015633551)
        ·
          refine ⟨26713160919166050023450327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17808773946110700015633551 26713160919166050023450327)
          ·
            refine ⟨40069741378749075035175491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26713160919166050023450327 40069741378749075035175491)
            ·
              refine ⟨60104612068123612552763237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40069741378749075035175491 60104612068123612552763237)
              ·
                refine ⟨11269614762773177353643107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60104612068123612552763237 11269614762773177353643107)
                ·
                  refine ⟨16904422144159766030464661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11269614762773177353643107 16904422144159766030464661)
                  ·
                    refine ⟨792394788007489032678031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16904422144159766030464661 792394788007489032678031)
                    ·
                      rfl

theorem cell23_4629550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_4629550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629550 prefixEnd_4629550 := by exact prefixLift 4629550
  have htrace : WordTrace (prefixWord ++ tailWord_4629550) baseStart_4629550 baseEnd_4629550 := by
    simpa [prefixWord, tailWord_4629550, baseEnd_4629550] using wordTrace_append hprefix tailTrace_4629550
  have hstable : (prefixWord ++ tailWord_4629550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629550).length < 2 ^ (prefixWord ++ tailWord_4629550).sum := by decide
  have hdescent : baseEnd_4629550 < baseStart_4629550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629557 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 7, 2, 2]
def baseStart_4629557 : Nat := 118140960795 + 4629557 * 2 ^ 59
def prefixEnd_4629557 : Nat := 4983230072969 + 3 ^ 40 * 4629557 * 2
def baseEnd_4629557 : Nat := 2377187958387048570646561

theorem tailTrace_4629557 : CollatzResearch.WordTrace tailWord_4629557 prefixEnd_4629557 2377187958387048570646561 := by
  unfold tailWord_4629557
  simp only [CollatzResearch.WordTrace]
  refine ⟨168853815688913129232622925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112569210459275419488415283 168853815688913129232622925)
  ·
    refine ⟨63320180883342423462233597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168853815688913129232622925 63320180883342423462233597)
    ·
      refine ⟨23745067831253408798337599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63320180883342423462233597 23745067831253408798337599)
      ·
        refine ⟨35617601746880113197506399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23745067831253408798337599 35617601746880113197506399)
        ·
          refine ⟨53426402620320169796259599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35617601746880113197506399 53426402620320169796259599)
          ·
            refine ⟨80139603930480254694389399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53426402620320169796259599 80139603930480254694389399)
            ·
              refine ⟨120209405895720382041584099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80139603930480254694389399 120209405895720382041584099)
              ·
                refine ⟨180314108843580573062376149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120209405895720382041584099 180314108843580573062376149)
                ·
                  refine ⟨4226111926021419681149441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 180314108843580573062376149 4226111926021419681149441)
                  ·
                    refine ⟨3169583944516064760862081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4226111926021419681149441 3169583944516064760862081)
                    ·
                      refine ⟨2377187958387048570646561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3169583944516064760862081 2377187958387048570646561)
                      ·
                        rfl

theorem cell23_4629557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_4629557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629557 prefixEnd_4629557 := by exact prefixLift 4629557
  have htrace : WordTrace (prefixWord ++ tailWord_4629557) baseStart_4629557 baseEnd_4629557 := by
    simpa [prefixWord, tailWord_4629557, baseEnd_4629557] using wordTrace_append hprefix tailTrace_4629557
  have hstable : (prefixWord ++ tailWord_4629557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629557).length < 2 ^ (prefixWord ++ tailWord_4629557).sum := by decide
  have hdescent : baseEnd_4629557 < baseStart_4629557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629597 : List Nat := [1, 4, 4, 1, 2, 1, 1, 9]
def baseStart_4629597 : Nat := 118140960795 + 4629597 * 2 ^ 59
def prefixEnd_4629597 : Nat := 4983230072969 + 3 ^ 40 * 4629597 * 2
def baseEnd_4629597 : Nat := 88044759170860311635051

theorem tailTrace_4629597 : CollatzResearch.WordTrace tailWord_4629597 prefixEnd_4629597 88044759170860311635051 := by
  unfold tailWord_4629597
  simp only [CollatzResearch.WordTrace]
  refine ⟨168855274608768216064079045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112570183072512144042719363 168855274608768216064079045)
  ·
    refine ⟨31660363989144040512014821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168855274608768216064079045 31660363989144040512014821)
    ·
      refine ⟨5936318247964507596002779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31660363989144040512014821 5936318247964507596002779)
      ·
        refine ⟨8904477371946761394004169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5936318247964507596002779 8904477371946761394004169)
        ·
          refine ⟨6678358028960071045503127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8904477371946761394004169 6678358028960071045503127)
          ·
            refine ⟨10017537043440106568254691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6678358028960071045503127 10017537043440106568254691)
            ·
              refine ⟨15026305565160159852382037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10017537043440106568254691 15026305565160159852382037)
              ·
                refine ⟨88044759170860311635051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15026305565160159852382037 88044759170860311635051)
                ·
                  rfl

theorem cell23_4629597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 9].length) (baseStart_4629597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629597 prefixEnd_4629597 := by exact prefixLift 4629597
  have htrace : WordTrace (prefixWord ++ tailWord_4629597) baseStart_4629597 baseEnd_4629597 := by
    simpa [prefixWord, tailWord_4629597, baseEnd_4629597] using wordTrace_append hprefix tailTrace_4629597
  have hstable : (prefixWord ++ tailWord_4629597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629597).length < 2 ^ (prefixWord ++ tailWord_4629597).sum := by decide
  have hdescent : baseEnd_4629597 < baseStart_4629597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629607 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 4, 1, 3]
def baseStart_4629607 : Nat := 118140960795 + 4629607 * 2 ^ 59
def prefixEnd_4629607 : Nat := 4983230072969 + 3 ^ 40 * 4629607 * 2
def baseEnd_4629607 : Nat := 2377213632419773375021331

theorem tailTrace_4629607 : CollatzResearch.WordTrace tailWord_4629607 prefixEnd_4629607 2377213632419773375021331 := by
  unfold tailWord_4629607
  simp only [CollatzResearch.WordTrace]
  refine ⟨168855639338731987771943075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112570426225821325181295383 168855639338731987771943075)
  ·
    refine ⟨253283459008097981657914613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168855639338731987771943075 253283459008097981657914613)
    ·
      refine ⟨23745324282009185780429495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 253283459008097981657914613 23745324282009185780429495)
      ·
        refine ⟨35617986423013778670644243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23745324282009185780429495 35617986423013778670644243)
        ·
          refine ⟨53426979634520668005966365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35617986423013778670644243 53426979634520668005966365)
          ·
            refine ⟨20035117362945250502237387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53426979634520668005966365 20035117362945250502237387)
            ·
              refine ⟨30052676044417875753356081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20035117362945250502237387 30052676044417875753356081)
              ·
                refine ⟨22539507033313406815017061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30052676044417875753356081 22539507033313406815017061)
                ·
                  refine ⟨4226157568746263777815699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22539507033313406815017061 4226157568746263777815699)
                  ·
                    refine ⟨6339236353119395666723549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4226157568746263777815699 6339236353119395666723549)
                    ·
                      refine ⟨2377213632419773375021331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6339236353119395666723549 2377213632419773375021331)
                      ·
                        rfl

theorem cell23_4629607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_4629607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629607 prefixEnd_4629607 := by exact prefixLift 4629607
  have htrace : WordTrace (prefixWord ++ tailWord_4629607) baseStart_4629607 baseEnd_4629607 := by
    simpa [prefixWord, tailWord_4629607, baseEnd_4629607] using wordTrace_append hprefix tailTrace_4629607
  have hstable : (prefixWord ++ tailWord_4629607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629607).length < 2 ^ (prefixWord ++ tailWord_4629607).sum := by decide
  have hdescent : baseEnd_4629607 < baseStart_4629607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629641 : List Nat := [1, 2, 1, 1, 4, 5, 2, 1, 2, 1, 3]
def baseStart_4629641 : Nat := 118140960795 + 4629641 * 2 ^ 59
def prefixEnd_4629641 : Nat := 4983230072969 + 3 ^ 40 * 4629641 * 2
def baseEnd_4629641 : Nat := 2377231090762026241996175

theorem tailTrace_4629641 : CollatzResearch.WordTrace tailWord_4629641 prefixEnd_4629641 2377231090762026241996175 := by
  unfold tailWord_4629641
  simp only [CollatzResearch.WordTrace]
  refine ⟨168856879420608811578680777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112571252947072541052453851 168856879420608811578680777)
  ·
    refine ⟨126642659565456608684010583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168856879420608811578680777 126642659565456608684010583)
    ·
      refine ⟨189963989348184913026015875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126642659565456608684010583 189963989348184913026015875)
      ·
        refine ⟨284945984022277369539023813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189963989348184913026015875 284945984022277369539023813)
        ·
          refine ⟨53427372004177006788566965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 284945984022277369539023813 53427372004177006788566965)
          ·
            refine ⟨5008816125391594386428153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53427372004177006788566965 5008816125391594386428153)
            ·
              refine ⟨3756612094043695789821115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5008816125391594386428153 3756612094043695789821115)
              ·
                refine ⟨5634918141065543684731673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3756612094043695789821115 5634918141065543684731673)
                ·
                  refine ⟨4226188605799157763548755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5634918141065543684731673 4226188605799157763548755)
                  ·
                    refine ⟨6339282908698736645323133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4226188605799157763548755 6339282908698736645323133)
                    ·
                      refine ⟨2377231090762026241996175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6339282908698736645323133 2377231090762026241996175)
                      ·
                        rfl

theorem cell23_4629641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 2, 1, 3].length) (baseStart_4629641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629641 prefixEnd_4629641 := by exact prefixLift 4629641
  have htrace : WordTrace (prefixWord ++ tailWord_4629641) baseStart_4629641 baseEnd_4629641 := by
    simpa [prefixWord, tailWord_4629641, baseEnd_4629641] using wordTrace_append hprefix tailTrace_4629641
  have hstable : (prefixWord ++ tailWord_4629641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629641).length < 2 ^ (prefixWord ++ tailWord_4629641).sum := by decide
  have hdescent : baseEnd_4629641 < baseStart_4629641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629643 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 6]
def baseStart_4629643 : Nat := 118140960795 + 4629643 * 2 ^ 59
def prefixEnd_4629643 : Nat := 4983230072969 + 3 ^ 40 * 4629643 * 2
def baseEnd_4629643 : Nat := 2377232117723335234171165

theorem tailTrace_4629643 : CollatzResearch.WordTrace tailWord_4629643 prefixEnd_4629643 2377232117723335234171165 := by
  unfold tailWord_4629643
  simp only [CollatzResearch.WordTrace]
  refine ⟨168856952366601565920253583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112571301577734377280169055 168856952366601565920253583)
  ·
    refine ⟨253285428549902348880380375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168856952366601565920253583 253285428549902348880380375)
    ·
      refine ⟨379928142824853523320570563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253285428549902348880380375 379928142824853523320570563)
      ·
        refine ⟨569892214237280284980855845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379928142824853523320570563 569892214237280284980855845)
        ·
          refine ⟨106854790169490053433910471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 569892214237280284980855845 106854790169490053433910471)
          ·
            refine ⟨160282185254235080150865707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106854790169490053433910471 160282185254235080150865707)
            ·
              refine ⟨240423277881352620226298561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160282185254235080150865707 240423277881352620226298561)
              ·
                refine ⟨180317458411014465169723921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240423277881352620226298561 180317458411014465169723921)
                ·
                  refine ⟨135238093808260848877292941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180317458411014465169723921 135238093808260848877292941)
                  ·
                    refine ⟨50714285178097818328984853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 135238093808260848877292941 50714285178097818328984853)
                    ·
                      refine ⟨2377232117723335234171165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50714285178097818328984853 2377232117723335234171165)
                      ·
                        rfl

theorem cell23_4629643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 6].length) (baseStart_4629643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629643 prefixEnd_4629643 := by exact prefixLift 4629643
  have htrace : WordTrace (prefixWord ++ tailWord_4629643) baseStart_4629643 baseEnd_4629643 := by
    simpa [prefixWord, tailWord_4629643, baseEnd_4629643] using wordTrace_append hprefix tailTrace_4629643
  have hstable : (prefixWord ++ tailWord_4629643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629643).length < 2 ^ (prefixWord ++ tailWord_4629643).sum := by decide
  have hdescent : baseEnd_4629643 < baseStart_4629643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629680 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 3]
def baseStart_4629680 : Nat := 118140960795 + 4629680 * 2 ^ 59
def prefixEnd_4629680 : Nat := 4983230072969 + 3 ^ 40 * 4629680 * 2
def baseEnd_4629680 : Nat := 2377251116507551589408495

theorem tailTrace_4629680 : CollatzResearch.WordTrace tailWord_4629680 prefixEnd_4629680 2377251116507551589408495 := by
  unfold tailWord_4629680
  simp only [CollatzResearch.WordTrace]
  refine ⟨84429150933733760619675247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112572201244978347492900329 84429150933733760619675247)
  ·
    refine ⟨126643726400600640929512871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84429150933733760619675247 126643726400600640929512871)
    ·
      refine ⟨189965589600900961394269307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126643726400600640929512871 189965589600900961394269307)
      ·
        refine ⟨284948384401351442091403961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189965589600900961394269307 284948384401351442091403961)
        ·
          refine ⟨213711288301013581568552971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284948384401351442091403961 213711288301013581568552971)
          ·
            refine ⟨320566932451520372352829457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213711288301013581568552971 320566932451520372352829457)
            ·
              refine ⟨240425199338640279264622093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320566932451520372352829457 240425199338640279264622093)
              ·
                refine ⟨90159449751990104724233285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 240425199338640279264622093 90159449751990104724233285)
                ·
                  refine ⟨16904896828498144635793741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90159449751990104724233285 16904896828498144635793741)
                  ·
                    refine ⟨6339336310686804238422653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16904896828498144635793741 6339336310686804238422653)
                    ·
                      refine ⟨2377251116507551589408495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6339336310686804238422653 2377251116507551589408495)
                      ·
                        rfl

theorem cell23_4629680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 3].length) (baseStart_4629680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629680 prefixEnd_4629680 := by exact prefixLift 4629680
  have htrace : WordTrace (prefixWord ++ tailWord_4629680) baseStart_4629680 baseEnd_4629680 := by
    simpa [prefixWord, tailWord_4629680, baseEnd_4629680] using wordTrace_append hprefix tailTrace_4629680
  have hstable : (prefixWord ++ tailWord_4629680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629680).length < 2 ^ (prefixWord ++ tailWord_4629680).sum := by decide
  have hdescent : baseEnd_4629680 < baseStart_4629680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629681 : List Nat := [1, 2, 2, 5, 1, 1, 1, 4, 2, 2, 2]
def baseStart_4629681 : Nat := 118140960795 + 4629681 * 2 ^ 59
def prefixEnd_4629681 : Nat := 4983230072969 + 3 ^ 40 * 4629681 * 2
def baseEnd_4629681 : Nat := 2377251629988206085495991

theorem tailTrace_4629681 : CollatzResearch.WordTrace tailWord_4629681 prefixEnd_4629681 2377251629988206085495991 := by
  unfold tailWord_4629681
  simp only [CollatzResearch.WordTrace]
  refine ⟨168858338340463898410136897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112572225560309265606757931 168858338340463898410136897)
  ·
    refine ⟨126643753755347923807602673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168858338340463898410136897 126643753755347923807602673)
    ·
      refine ⟨94982815316510942855702005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126643753755347923807602673 94982815316510942855702005)
      ·
        refine ⟨8904638935922900892722063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94982815316510942855702005 8904638935922900892722063)
        ·
          refine ⟨13356958403884351339083095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8904638935922900892722063 13356958403884351339083095)
          ·
            refine ⟨20035437605826527008624643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13356958403884351339083095 20035437605826527008624643)
            ·
              refine ⟨30053156408739790512936965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20035437605826527008624643 30053156408739790512936965)
              ·
                refine ⟨5634966826638710721175681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30053156408739790512936965 5634966826638710721175681)
                ·
                  refine ⟨4226225119979033040881761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5634966826638710721175681 4226225119979033040881761)
                  ·
                    refine ⟨3169668839984274780661321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4226225119979033040881761 3169668839984274780661321)
                    ·
                      refine ⟨2377251629988206085495991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3169668839984274780661321 2377251629988206085495991)
                      ·
                        rfl

theorem cell23_4629681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_4629681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629681 prefixEnd_4629681 := by exact prefixLift 4629681
  have htrace : WordTrace (prefixWord ++ tailWord_4629681) baseStart_4629681 baseEnd_4629681 := by
    simpa [prefixWord, tailWord_4629681, baseEnd_4629681] using wordTrace_append hprefix tailTrace_4629681
  have hstable : (prefixWord ++ tailWord_4629681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629681).length < 2 ^ (prefixWord ++ tailWord_4629681).sum := by decide
  have hdescent : baseEnd_4629681 < baseStart_4629681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629687 : List Nat := [1, 1, 3, 1, 4, 1, 3, 4, 5]
def baseStart_4629687 : Nat := 118140960795 + 4629687 * 2 ^ 59
def prefixEnd_4629687 : Nat := 4983230072969 + 3 ^ 40 * 4629687 * 2
def baseEnd_4629687 : Nat := 264139412319125895780107

theorem tailTrace_4629687 : CollatzResearch.WordTrace tailWord_4629687 prefixEnd_4629687 264139412319125895780107 := by
  unfold tailWord_4629687
  simp only [CollatzResearch.WordTrace]
  refine ⟨168858557178442161434855315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112572371452294774289903543 168858557178442161434855315)
  ·
    refine ⟨253287835767663242152282973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168858557178442161434855315 253287835767663242152282973)
    ·
      refine ⟨94982938412873715807106115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253287835767663242152282973 94982938412873715807106115)
      ·
        refine ⟨142474407619310573710659173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94982938412873715807106115 142474407619310573710659173)
        ·
          refine ⟨26713951428620732570748595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142474407619310573710659173 26713951428620732570748595)
          ·
            refine ⟨40070927142931098856122893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26713951428620732570748595 40070927142931098856122893)
            ·
              refine ⟨15026597678599162071046085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40070927142931098856122893 15026597678599162071046085)
              ·
                refine ⟨2817487064737342888321141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15026597678599162071046085 2817487064737342888321141)
                ·
                  refine ⟨264139412319125895780107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2817487064737342888321141 264139412319125895780107)
                  ·
                    rfl

theorem cell23_4629687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 5].length) (baseStart_4629687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629687 prefixEnd_4629687 := by exact prefixLift 4629687
  have htrace : WordTrace (prefixWord ++ tailWord_4629687) baseStart_4629687 baseEnd_4629687 := by
    simpa [prefixWord, tailWord_4629687, baseEnd_4629687] using wordTrace_append hprefix tailTrace_4629687
  have hstable : (prefixWord ++ tailWord_4629687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629687).length < 2 ^ (prefixWord ++ tailWord_4629687).sum := by decide
  have hdescent : baseEnd_4629687 < baseStart_4629687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629717 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 1, 7]
def baseStart_4629717 : Nat := 118140960795 + 4629717 * 2 ^ 59
def prefixEnd_4629717 : Nat := 4983230072969 + 3 ^ 40 * 4629717 * 2
def baseEnd_4629717 : Nat := 792423371763922648215275

theorem tailTrace_4629717 : CollatzResearch.WordTrace tailWord_4629717 prefixEnd_4629717 792423371763922648215275 := by
  unfold tailWord_4629717
  simp only [CollatzResearch.WordTrace]
  refine ⟨168859651368333476558447405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112573100912222317705631603 168859651368333476558447405)
  ·
    refine ⟨63322369263125053709417777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168859651368333476558447405 63322369263125053709417777)
    ·
      refine ⟨47491776947343790282063333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63322369263125053709417777 47491776947343790282063333)
      ·
        refine ⟨8904708177626960677886875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47491776947343790282063333 8904708177626960677886875)
        ·
          refine ⟨13357062266440441016830313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8904708177626960677886875 13357062266440441016830313)
          ·
            refine ⟨10017796699830330762622735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13357062266440441016830313 10017796699830330762622735)
            ·
              refine ⟨15026695049745496143934103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10017796699830330762622735 15026695049745496143934103)
              ·
                refine ⟨22540042574618244215901155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15026695049745496143934103 22540042574618244215901155)
                ·
                  refine ⟨33810063861927366323851733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22540042574618244215901155 33810063861927366323851733)
                  ·
                    refine ⟨792423371763922648215275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33810063861927366323851733 792423371763922648215275)
                    ·
                      rfl

theorem cell23_4629717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_4629717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629717 prefixEnd_4629717 := by exact prefixLift 4629717
  have htrace : WordTrace (prefixWord ++ tailWord_4629717) baseStart_4629717 baseEnd_4629717 := by
    simpa [prefixWord, tailWord_4629717, baseEnd_4629717] using wordTrace_append hprefix tailTrace_4629717
  have hstable : (prefixWord ++ tailWord_4629717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629717).length < 2 ^ (prefixWord ++ tailWord_4629717).sum := by decide
  have hdescent : baseEnd_4629717 < baseStart_4629717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629747 : List Nat := [1, 1, 1, 2, 2, 5, 1, 3, 3, 4]
def baseStart_4629747 : Nat := 118140960795 + 4629747 * 2 ^ 59
def prefixEnd_4629747 : Nat := 4983230072969 + 3 ^ 40 * 4629747 * 2
def baseEnd_4629747 : Nat := 792428506570467609090229

theorem tailTrace_4629747 : CollatzResearch.WordTrace tailWord_4629747 prefixEnd_4629747 792428506570467609090229 := by
  unfold tailWord_4629747
  simp only [CollatzResearch.WordTrace]
  refine ⟨168860745558224791682039495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112573830372149861121359663 168860745558224791682039495)
  ·
    refine ⟨253291118337337187523059243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168860745558224791682039495 253291118337337187523059243)
    ·
      refine ⟨379936677506005781284588865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253291118337337187523059243 379936677506005781284588865)
      ·
        refine ⟨284952508129504335963441649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 379936677506005781284588865 284952508129504335963441649)
        ·
          refine ⟨213714381097128251972581237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284952508129504335963441649 213714381097128251972581237)
          ·
            refine ⟨20035723227855773622429491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 213714381097128251972581237 20035723227855773622429491)
            ·
              refine ⟨30053584841783660433644237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20035723227855773622429491 30053584841783660433644237)
              ·
                refine ⟨11270094315668872662616589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30053584841783660433644237 11270094315668872662616589)
                ·
                  refine ⟨4226285368375827248481221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11270094315668872662616589 4226285368375827248481221)
                  ·
                    refine ⟨792428506570467609090229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4226285368375827248481221 792428506570467609090229)
                    ·
                      rfl

theorem cell23_4629747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 4].length) (baseStart_4629747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629747 prefixEnd_4629747 := by exact prefixLift 4629747
  have htrace : WordTrace (prefixWord ++ tailWord_4629747) baseStart_4629747 baseEnd_4629747 := by
    simpa [prefixWord, tailWord_4629747, baseEnd_4629747] using wordTrace_append hprefix tailTrace_4629747
  have hstable : (prefixWord ++ tailWord_4629747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629747).length < 2 ^ (prefixWord ++ tailWord_4629747).sum := by decide
  have hdescent : baseEnd_4629747 < baseStart_4629747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629764 : List Nat := [2, 3, 2, 2, 2, 1, 2, 2, 3, 4]
def baseStart_4629764 : Nat := 118140960795 + 4629764 * 2 ^ 59
def prefixEnd_4629764 : Nat := 4983230072969 + 3 ^ 40 * 4629764 * 2
def baseEnd_4629764 : Nat := 792431416294176420252703

theorem tailTrace_4629764 : CollatzResearch.WordTrace tailWord_4629764 prefixEnd_4629764 792431416294176420252703 := by
  unfold tailWord_4629764
  simp only [CollatzResearch.WordTrace]
  refine ⟨84430682799581601792704173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112574243732775469056938897 84430682799581601792704173)
  ·
    refine ⟨31661506049843100672264065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84430682799581601792704173 31661506049843100672264065)
    ·
      refine ⟨23746129537382325504198049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31661506049843100672264065 23746129537382325504198049)
      ·
        refine ⟨17809597153036744128148537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23746129537382325504198049 17809597153036744128148537)
        ·
          refine ⟨13357197864777558096111403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17809597153036744128148537 13357197864777558096111403)
          ·
            refine ⟨20035796797166337144167105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13357197864777558096111403 20035796797166337144167105)
            ·
              refine ⟨15026847597874752858125329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20035796797166337144167105 15026847597874752858125329)
              ·
                refine ⟨11270135698406064643593997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15026847597874752858125329 11270135698406064643593997)
                ·
                  refine ⟨4226300886902274241347749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11270135698406064643593997 4226300886902274241347749)
                  ·
                    refine ⟨792431416294176420252703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4226300886902274241347749 792431416294176420252703)
                    ·
                      rfl

theorem cell23_4629764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_4629764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629764 prefixEnd_4629764 := by exact prefixLift 4629764
  have htrace : WordTrace (prefixWord ++ tailWord_4629764) baseStart_4629764 baseEnd_4629764 := by
    simpa [prefixWord, tailWord_4629764, baseEnd_4629764] using wordTrace_append hprefix tailTrace_4629764
  have hstable : (prefixWord ++ tailWord_4629764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629764).length < 2 ^ (prefixWord ++ tailWord_4629764).sum := by decide
  have hdescent : baseEnd_4629764 < baseStart_4629764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629831 : List Nat := [1, 1, 4, 1, 2, 4, 2, 1, 2, 3, 2]
def baseStart_4629831 : Nat := 118140960795 + 4629831 * 2 ^ 59
def prefixEnd_4629831 : Nat := 4983230072969 + 3 ^ 40 * 4629831 * 2
def baseEnd_4629831 : Nat := 2377328652086380498620301

theorem tailTrace_4629831 : CollatzResearch.WordTrace tailWord_4629831 prefixEnd_4629831 2377328652086380498620301 := by
  unfold tailWord_4629831
  simp only [CollatzResearch.WordTrace]
  refine ⟨168863809289920474028097347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112575872859946982685398231 168863809289920474028097347)
  ·
    refine ⟨253295713934880711042146021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168863809289920474028097347 253295713934880711042146021)
    ·
      refine ⟨47492946362790133320402379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 253295713934880711042146021 47492946362790133320402379)
      ·
        refine ⟨71239419544185199980603569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47492946362790133320402379 71239419544185199980603569)
        ·
          refine ⟨53429564658138899985452677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71239419544185199980603569 53429564658138899985452677)
          ·
            refine ⟨10018043373401043747272377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53429564658138899985452677 10018043373401043747272377)
            ·
              refine ⟨7513532530050782810454283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10018043373401043747272377 7513532530050782810454283)
              ·
                refine ⟨11270298795076174215681425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7513532530050782810454283 11270298795076174215681425)
                ·
                  refine ⟨8452724096307130661761069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11270298795076174215681425 8452724096307130661761069)
                  ·
                    refine ⟨3169771536115173998160401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8452724096307130661761069 3169771536115173998160401)
                    ·
                      refine ⟨2377328652086380498620301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3169771536115173998160401 2377328652086380498620301)
                      ·
                        rfl

theorem cell23_4629831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_4629831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629831 prefixEnd_4629831 := by exact prefixLift 4629831
  have htrace : WordTrace (prefixWord ++ tailWord_4629831) baseStart_4629831 baseEnd_4629831 := by
    simpa [prefixWord, tailWord_4629831, baseEnd_4629831] using wordTrace_append hprefix tailTrace_4629831
  have hstable : (prefixWord ++ tailWord_4629831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629831).length < 2 ^ (prefixWord ++ tailWord_4629831).sum := by decide
  have hdescent : baseEnd_4629831 < baseStart_4629831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629861 : List Nat := [1, 3, 1, 3, 1, 2, 2, 3, 3, 2, 2]
def baseStart_4629861 : Nat := 118140960795 + 4629861 * 2 ^ 59
def prefixEnd_4629861 : Nat := 4983230072969 + 3 ^ 40 * 4629861 * 2
def baseEnd_4629861 : Nat := 2377344056506015381245163

theorem tailTrace_4629861 : CollatzResearch.WordTrace tailWord_4629861 prefixEnd_4629861 2377344056506015381245163 := by
  unfold tailWord_4629861
  simp only [CollatzResearch.WordTrace]
  refine ⟨168864903479811789151689437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112576602319874526101126291 168864903479811789151689437)
  ·
    refine ⟨63324338804929420931883539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168864903479811789151689437 63324338804929420931883539)
    ·
      refine ⟨94986508207394131397825309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63324338804929420931883539 94986508207394131397825309)
      ·
        refine ⟨35619940577772799274184491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94986508207394131397825309 35619940577772799274184491)
        ·
          refine ⟨53429910866659198911276737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35619940577772799274184491 53429910866659198911276737)
          ·
            refine ⟨40072433149994399183457553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53429910866659198911276737 40072433149994399183457553)
            ·
              refine ⟨30054324862495799387593165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40072433149994399183457553 30054324862495799387593165)
              ·
                refine ⟨11270371823435924770347437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30054324862495799387593165 11270371823435924770347437)
                ·
                  refine ⟨4226389433788471788880289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11270371823435924770347437 4226389433788471788880289)
                  ·
                    refine ⟨3169792075341353841660217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4226389433788471788880289 3169792075341353841660217)
                    ·
                      refine ⟨2377344056506015381245163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3169792075341353841660217 2377344056506015381245163)
                      ·
                        rfl

theorem cell23_4629861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_4629861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629861 prefixEnd_4629861 := by exact prefixLift 4629861
  have htrace : WordTrace (prefixWord ++ tailWord_4629861) baseStart_4629861 baseEnd_4629861 := by
    simpa [prefixWord, tailWord_4629861, baseEnd_4629861] using wordTrace_append hprefix tailTrace_4629861
  have hstable : (prefixWord ++ tailWord_4629861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629861).length < 2 ^ (prefixWord ++ tailWord_4629861).sum := by decide
  have hdescent : baseEnd_4629861 < baseStart_4629861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629874 : List Nat := [3, 2, 1, 2, 1, 2, 4, 1, 1, 2, 4]
def baseStart_4629874 : Nat := 118140960795 + 4629874 * 2 ^ 59
def prefixEnd_4629874 : Nat := 4983230072969 + 3 ^ 40 * 4629874 * 2
def baseEnd_4629874 : Nat := 2377350731754523830382603

theorem tailTrace_4629874 : CollatzResearch.WordTrace tailWord_4629874 prefixEnd_4629874 2377350731754523830382603 := by
  unfold tailWord_4629874
  simp only [CollatzResearch.WordTrace]
  refine ⟨42216344407191173092978169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112576918419176461581275117 42216344407191173092978169)
  ·
    refine ⟨31662258305393379819733627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42216344407191173092978169 31662258305393379819733627)
    ·
      refine ⟨47493387458090069729600441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31662258305393379819733627 47493387458090069729600441)
      ·
        refine ⟨35620040593567552297200331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47493387458090069729600441 35620040593567552297200331)
        ·
          refine ⟨53430060890351328445800497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35620040593567552297200331 53430060890351328445800497)
          ·
            refine ⟨40072545667763496334350373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53430060890351328445800497 40072545667763496334350373)
            ·
              refine ⟨7513602312705655562690695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40072545667763496334350373 7513602312705655562690695)
              ·
                refine ⟨11270403469058483344036043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7513602312705655562690695 11270403469058483344036043)
                ·
                  refine ⟨16905605203587725016054065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11270403469058483344036043 16905605203587725016054065)
                  ·
                    refine ⟨12679203902690793762040549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16905605203587725016054065 12679203902690793762040549)
                    ·
                      refine ⟨2377350731754523830382603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12679203902690793762040549 2377350731754523830382603)
                      ·
                        rfl

theorem cell23_4629874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_4629874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629874 prefixEnd_4629874 := by exact prefixLift 4629874
  have htrace : WordTrace (prefixWord ++ tailWord_4629874) baseStart_4629874 baseEnd_4629874 := by
    simpa [prefixWord, tailWord_4629874, baseEnd_4629874] using wordTrace_append hprefix tailTrace_4629874
  have hstable : (prefixWord ++ tailWord_4629874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629874).length < 2 ^ (prefixWord ++ tailWord_4629874).sum := by decide
  have hdescent : baseEnd_4629874 < baseStart_4629874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629895 : List Nat := [1, 1, 4, 2, 2, 3, 2, 3, 1, 2, 2]
def baseStart_4629895 : Nat := 118140960795 + 4629895 * 2 ^ 59
def prefixEnd_4629895 : Nat := 4983230072969 + 3 ^ 40 * 4629895 * 2
def baseEnd_4629895 : Nat := 2377361514848268248220007

theorem tailTrace_4629895 : CollatzResearch.WordTrace tailWord_4629895 prefixEnd_4629895 2377361514848268248220007 := by
  unfold tailWord_4629895
  simp only [CollatzResearch.WordTrace]
  refine ⟨168866143561688612958427139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112577429041125741972284759 168866143561688612958427139)
  ·
    refine ⟨253299215342532919437640709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168866143561688612958427139 253299215342532919437640709)
    ·
      refine ⟨47493602876724922394557633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 253299215342532919437640709 47493602876724922394557633)
      ·
        refine ⟨35620202157543691795918225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47493602876724922394557633 35620202157543691795918225)
        ·
          refine ⟨26715151618157768846938669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35620202157543691795918225 26715151618157768846938669)
          ·
            refine ⟨10018181856809163317602001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26715151618157768846938669 10018181856809163317602001)
            ·
              refine ⟨7513636392606872488201501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10018181856809163317602001 7513636392606872488201501)
              ·
                refine ⟨2817613647227577183075563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7513636392606872488201501 2817613647227577183075563)
                ·
                  refine ⟨4226420470841365774613345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2817613647227577183075563 4226420470841365774613345)
                  ·
                    refine ⟨3169815353131024330960009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4226420470841365774613345 3169815353131024330960009)
                    ·
                      refine ⟨2377361514848268248220007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3169815353131024330960009 2377361514848268248220007)
                      ·
                        rfl

theorem cell23_4629895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_4629895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629895 prefixEnd_4629895 := by exact prefixLift 4629895
  have htrace : WordTrace (prefixWord ++ tailWord_4629895) baseStart_4629895 baseEnd_4629895 := by
    simpa [prefixWord, tailWord_4629895, baseEnd_4629895] using wordTrace_append hprefix tailTrace_4629895
  have hstable : (prefixWord ++ tailWord_4629895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629895).length < 2 ^ (prefixWord ++ tailWord_4629895).sum := by decide
  have hdescent : baseEnd_4629895 < baseStart_4629895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4629985 : List Nat := [1, 2, 3, 1, 2, 3, 4, 1, 2, 2, 2]
def baseStart_4629985 : Nat := 118140960795 + 4629985 * 2 ^ 59
def prefixEnd_4629985 : Nat := 4983230072969 + 3 ^ 40 * 4629985 * 2
def baseEnd_4629985 : Nat := 2377407728107172896094593

theorem tailTrace_4629985 : CollatzResearch.WordTrace tailWord_4629985 prefixEnd_4629985 2377407728107172896094593 := by
  unfold tailWord_4629985
  simp only [CollatzResearch.WordTrace]
  refine ⟨168869426131362558329203409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112579617420908372219468939 168869426131362558329203409)
  ·
    refine ⟨126652069598521918746902557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168869426131362558329203409 126652069598521918746902557)
    ·
      refine ⟨47494526099445719530088459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126652069598521918746902557 47494526099445719530088459)
      ·
        refine ⟨71241789149168579295132689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47494526099445719530088459 71241789149168579295132689)
        ·
          refine ⟨53431341861876434471349517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71241789149168579295132689 53431341861876434471349517)
          ·
            refine ⟨20036753198203662926756069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53431341861876434471349517 20036753198203662926756069)
            ·
              refine ⟨3756891224663186798766763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20036753198203662926756069 3756891224663186798766763)
              ·
                refine ⟨5635336836994780198150145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3756891224663186798766763 5635336836994780198150145)
                ·
                  refine ⟨4226502627746085148612609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5635336836994780198150145 4226502627746085148612609)
                  ·
                    refine ⟨3169876970809563861459457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4226502627746085148612609 3169876970809563861459457)
                    ·
                      refine ⟨2377407728107172896094593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3169876970809563861459457 2377407728107172896094593)
                      ·
                        rfl

theorem cell23_4629985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_4629985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4629985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4629985 prefixEnd_4629985 := by exact prefixLift 4629985
  have htrace : WordTrace (prefixWord ++ tailWord_4629985) baseStart_4629985 baseEnd_4629985 := by
    simpa [prefixWord, tailWord_4629985, baseEnd_4629985] using wordTrace_append hprefix tailTrace_4629985
  have hstable : (prefixWord ++ tailWord_4629985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4629985).length < 2 ^ (prefixWord ++ tailWord_4629985).sum := by decide
  have hdescent : baseEnd_4629985 < baseStart_4629985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4629985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630098 : List Nat := [3, 2, 2, 1, 2, 3, 3, 1, 6]
def baseStart_4630098 : Nat := 118140960795 + 4630098 * 2 ^ 59
def prefixEnd_4630098 : Nat := 4983230072969 + 3 ^ 40 * 4630098 * 2
def baseEnd_4630098 : Nat := 264162861269014550442397

theorem tailTrace_4630098 : CollatzResearch.WordTrace tailWord_4630098 prefixEnd_4630098 264162861269014550442397 := by
  unfold tailWord_4630098
  simp only [CollatzResearch.WordTrace]
  refine ⟨42218386894988294657016737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112582365053302119085377965 42218386894988294657016737)
  ·
    refine ⟨31663790171241220992762553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42218386894988294657016737 31663790171241220992762553)
    ·
      refine ⟨23747842628430915744571915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31663790171241220992762553 23747842628430915744571915)
      ·
        refine ⟨35621763942646373616857873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23747842628430915744571915 35621763942646373616857873)
        ·
          refine ⟨26716322956984780212643405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35621763942646373616857873 26716322956984780212643405)
          ·
            refine ⟨10018621108869292579741277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26716322956984780212643405 10018621108869292579741277)
            ·
              refine ⟨3756982915825984717402979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10018621108869292579741277 3756982915825984717402979)
              ·
                refine ⟨5635474373738977076104469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3756982915825984717402979 5635474373738977076104469)
                ·
                  refine ⟨264162861269014550442397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5635474373738977076104469 264162861269014550442397)
                  ·
                    rfl

theorem cell23_4630098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_4630098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630098 prefixEnd_4630098 := by exact prefixLift 4630098
  have htrace : WordTrace (prefixWord ++ tailWord_4630098) baseStart_4630098 baseEnd_4630098 := by
    simpa [prefixWord, tailWord_4630098, baseEnd_4630098] using wordTrace_append hprefix tailTrace_4630098
  have hstable : (prefixWord ++ tailWord_4630098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630098).length < 2 ^ (prefixWord ++ tailWord_4630098).sum := by decide
  have hdescent : baseEnd_4630098 < baseStart_4630098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630124 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 3, 6]
def baseStart_4630124 : Nat := 118140960795 + 4630124 * 2 ^ 59
def prefixEnd_4630124 : Nat := 4983230072969 + 3 ^ 40 * 4630124 * 2
def baseEnd_4630124 : Nat := 792493033972715950752151

theorem tailTrace_4630124 : CollatzResearch.WordTrace tailWord_4630124 prefixEnd_4630124 792493033972715950752151 := by
  unfold tailWord_4630124
  simp only [CollatzResearch.WordTrace]
  refine ⟨84437247938929492534256713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112582997251905990045675617 84437247938929492534256713)
  ·
    refine ⟨63327935954197119400692535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84437247938929492534256713 63327935954197119400692535)
    ·
      refine ⟨94991903931295679101038803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63327935954197119400692535 94991903931295679101038803)
      ·
        refine ⟨142487855896943518651558205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94991903931295679101038803 142487855896943518651558205)
        ·
          refine ⟨53432945961353819494334327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142487855896943518651558205 53432945961353819494334327)
          ·
            refine ⟨80149418942030729241501491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53432945961353819494334327 80149418942030729241501491)
            ·
              refine ⟨120224128413046093862252237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80149418942030729241501491 120224128413046093862252237)
              ·
                refine ⟨45084048154892285198344589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120224128413046093862252237 45084048154892285198344589)
                ·
                  refine ⟨16906518058084606949379221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45084048154892285198344589 16906518058084606949379221)
                  ·
                    refine ⟨792493033972715950752151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16906518058084606949379221 792493033972715950752151)
                    ·
                      rfl

theorem cell23_4630124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_4630124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630124 prefixEnd_4630124 := by exact prefixLift 4630124
  have htrace : WordTrace (prefixWord ++ tailWord_4630124) baseStart_4630124 baseEnd_4630124 := by
    simpa [prefixWord, tailWord_4630124, baseEnd_4630124] using wordTrace_append hprefix tailTrace_4630124
  have hstable : (prefixWord ++ tailWord_4630124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630124).length < 2 ^ (prefixWord ++ tailWord_4630124).sum := by decide
  have hdescent : baseEnd_4630124 < baseStart_4630124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630144 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 6]
def baseStart_4630144 : Nat := 118140960795 + 4630144 * 2 ^ 59
def prefixEnd_4630144 : Nat := 4983230072969 + 3 ^ 40 * 4630144 * 2
def baseEnd_4630144 : Nat := 2377489371531237774006361

theorem tailTrace_4630144 : CollatzResearch.WordTrace tailWord_4630144 prefixEnd_4630144 2377489371531237774006361 := by
  unfold tailWord_4630144
  simp only [CollatzResearch.WordTrace]
  refine ⟨84437612668893264242120743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112583483558524352322827657 84437612668893264242120743)
  ·
    refine ⟨126656419003339896363181115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84437612668893264242120743 126656419003339896363181115)
    ·
      refine ⟨189984628505009844544771673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126656419003339896363181115 189984628505009844544771673)
      ·
        refine ⟨142488471378757383408578755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189984628505009844544771673 142488471378757383408578755)
        ·
          refine ⟨213732707068136075112868133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142488471378757383408578755 213732707068136075112868133)
          ·
            refine ⟨40074882575275514083662775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 213732707068136075112868133 40074882575275514083662775)
            ·
              refine ⟨60112323862913271125494163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40074882575275514083662775 60112323862913271125494163)
              ·
                refine ⟨90168485794369906688241245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60112323862913271125494163 90168485794369906688241245)
                ·
                  refine ⟨33813182172888715008090467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90168485794369906688241245 33813182172888715008090467)
                  ·
                    refine ⟨50719773259333072512135701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33813182172888715008090467 50719773259333072512135701)
                    ·
                      refine ⟨2377489371531237774006361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50719773259333072512135701 2377489371531237774006361)
                      ·
                        rfl

theorem cell23_4630144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_4630144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630144 prefixEnd_4630144 := by exact prefixLift 4630144
  have htrace : WordTrace (prefixWord ++ tailWord_4630144) baseStart_4630144 baseEnd_4630144 := by
    simpa [prefixWord, tailWord_4630144, baseEnd_4630144] using wordTrace_append hprefix tailTrace_4630144
  have hstable : (prefixWord ++ tailWord_4630144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630144).length < 2 ^ (prefixWord ++ tailWord_4630144).sum := by decide
  have hdescent : baseEnd_4630144 < baseStart_4630144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630151 : List Nat := [1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 5]
def baseStart_4630151 : Nat := 118140960795 + 4630151 * 2 ^ 59
def prefixEnd_4630151 : Nat := 4983230072969 + 3 ^ 40 * 4630151 * 2
def baseEnd_4630151 : Nat := 2377492965895819246618829

theorem tailTrace_4630151 : CollatzResearch.WordTrace tailWord_4630151 prefixEnd_4630151 2377492965895819246618829 := by
  unfold tailWord_4630151
  simp only [CollatzResearch.WordTrace]
  refine ⟨168875480648761168679746307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112583653765840779119830871 168875480648761168679746307)
  ·
    refine ⟨253313220973141753019619461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168875480648761168679746307 253313220973141753019619461)
    ·
      refine ⟨47496228932464078691178649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 253313220973141753019619461 47496228932464078691178649)
      ·
        refine ⟨35622171699348059018383987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47496228932464078691178649 35622171699348059018383987)
        ·
          refine ⟨53433257549022088527575981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35622171699348059018383987 53433257549022088527575981)
          ·
            refine ⟨20037471580883283197840993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53433257549022088527575981 20037471580883283197840993)
            ·
              refine ⟨15028103685662462398380745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20037471580883283197840993 15028103685662462398380745)
              ·
                refine ⟨11271077764246846798785559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15028103685662462398380745 11271077764246846798785559)
                ·
                  refine ⟨16906616646370270198178339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11271077764246846798785559 16906616646370270198178339)
                  ·
                    refine ⟨25359924969555405297267509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16906616646370270198178339 25359924969555405297267509)
                    ·
                      refine ⟨2377492965895819246618829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25359924969555405297267509 2377492965895819246618829)
                      ·
                        rfl

theorem cell23_4630151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_4630151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630151 prefixEnd_4630151 := by exact prefixLift 4630151
  have htrace : WordTrace (prefixWord ++ tailWord_4630151) baseStart_4630151 baseEnd_4630151 := by
    simpa [prefixWord, tailWord_4630151, baseEnd_4630151] using wordTrace_append hprefix tailTrace_4630151
  have hstable : (prefixWord ++ tailWord_4630151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630151).length < 2 ^ (prefixWord ++ tailWord_4630151).sum := by decide
  have hdescent : baseEnd_4630151 < baseStart_4630151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630162 : List Nat := [3, 2, 3, 1, 4, 1, 1, 2, 1, 5]
def baseStart_4630162 : Nat := 118140960795 + 4630162 * 2 ^ 59
def prefixEnd_4630162 : Nat := 4983230072969 + 3 ^ 40 * 4630162 * 2
def baseEnd_4630162 : Nat := 792499538061006234527093

theorem tailTrace_4630162 : CollatzResearch.WordTrace tailWord_4630162 prefixEnd_4630162 792499538061006234527093 := by
  unfold tailWord_4630162
  simp only [CollatzResearch.WordTrace]
  refine ⟨42218970462930329389599185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112583921234480878372264493 42218970462930329389599185)
  ·
    refine ⟨31664227847197747042199389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42218970462930329389599185 31664227847197747042199389)
    ·
      refine ⟨11874085442699155140824771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31664227847197747042199389 11874085442699155140824771)
      ·
        refine ⟨17811128164048732711237157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11874085442699155140824771 17811128164048732711237157)
        ·
          refine ⟨3339586530759137383356967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17811128164048732711237157 3339586530759137383356967)
          ·
            refine ⟨5009379796138706075035451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3339586530759137383356967 5009379796138706075035451)
            ·
              refine ⟨7514069694208059112553177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5009379796138706075035451 7514069694208059112553177)
              ·
                refine ⟨5635552270656044334414883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7514069694208059112553177 5635552270656044334414883)
                ·
                  refine ⟨8453328405984066501622325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5635552270656044334414883 8453328405984066501622325)
                  ·
                    refine ⟨792499538061006234527093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8453328405984066501622325 792499538061006234527093)
                    ·
                      rfl

theorem cell23_4630162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_4630162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630162 prefixEnd_4630162 := by exact prefixLift 4630162
  have htrace : WordTrace (prefixWord ++ tailWord_4630162) baseStart_4630162 baseEnd_4630162 := by
    simpa [prefixWord, tailWord_4630162, baseEnd_4630162] using wordTrace_append hprefix tailTrace_4630162
  have hstable : (prefixWord ++ tailWord_4630162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630162).length < 2 ^ (prefixWord ++ tailWord_4630162).sum := by decide
  have hdescent : baseEnd_4630162 < baseStart_4630162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630168 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 3, 2, 3]
def baseStart_4630168 : Nat := 118140960795 + 4630168 * 2 ^ 59
def prefixEnd_4630168 : Nat := 4983230072969 + 3 ^ 40 * 4630168 * 2
def baseEnd_4630168 : Nat := 2377501695066945680106251

theorem tailTrace_4630168 : CollatzResearch.WordTrace tailWord_4630168 prefixEnd_4630168 2377501695066945680106251 := by
  unfold tailWord_4630168
  simp only [CollatzResearch.WordTrace]
  refine ⟨84438050344849790291557579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112584067126466387055410105 84438050344849790291557579)
  ·
    refine ⟨126657075517274685437336369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84438050344849790291557579 126657075517274685437336369)
    ·
      refine ⟨94992806637956014078002277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126657075517274685437336369 94992806637956014078002277)
      ·
        refine ⟨17811151244616752639625427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94992806637956014078002277 17811151244616752639625427)
        ·
          refine ⟨26716726866925128959438141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17811151244616752639625427 26716726866925128959438141)
          ·
            refine ⟨10018772575096923359789303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26716726866925128959438141 10018772575096923359789303)
            ·
              refine ⟨15028158862645385039683955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10018772575096923359789303 15028158862645385039683955)
              ·
                refine ⟨22542238293968077559525933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15028158862645385039683955 22542238293968077559525933)
                ·
                  refine ⟨8453339360238029084822225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22542238293968077559525933 8453339360238029084822225)
                  ·
                    refine ⟨6340004520178521813616669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8453339360238029084822225 6340004520178521813616669)
                    ·
                      refine ⟨2377501695066945680106251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6340004520178521813616669 2377501695066945680106251)
                      ·
                        rfl

theorem cell23_4630168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_4630168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630168 prefixEnd_4630168 := by exact prefixLift 4630168
  have htrace : WordTrace (prefixWord ++ tailWord_4630168) baseStart_4630168 baseEnd_4630168 := by
    simpa [prefixWord, tailWord_4630168, baseEnd_4630168] using wordTrace_append hprefix tailTrace_4630168
  have hstable : (prefixWord ++ tailWord_4630168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630168).length < 2 ^ (prefixWord ++ tailWord_4630168).sum := by decide
  have hdescent : baseEnd_4630168 < baseStart_4630168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630181 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 3, 3, 3]
def baseStart_4630181 : Nat := 118140960795 + 4630181 * 2 ^ 59
def prefixEnd_4630181 : Nat := 4983230072969 + 3 ^ 40 * 4630181 * 2
def baseEnd_4630181 : Nat := 2377508370315454129243691

theorem tailTrace_4630181 : CollatzResearch.WordTrace tailWord_4630181 prefixEnd_4630181 2377508370315454129243691 := by
  unfold tailWord_4630181
  simp only [CollatzResearch.WordTrace]
  refine ⟨168876574838652483803338397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112584383225768322535558931 168876574838652483803338397)
  ·
    refine ⟨63328715564494681426251899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168876574838652483803338397 63328715564494681426251899)
    ·
      refine ⟨94993073346742022139377849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63328715564494681426251899 94993073346742022139377849)
      ·
        refine ⟨71244805010056516604533387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94993073346742022139377849 71244805010056516604533387)
        ·
          refine ⟨106867207515084774906800081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71244805010056516604533387 106867207515084774906800081)
          ·
            refine ⟨80150405636313581180100061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106867207515084774906800081 80150405636313581180100061)
            ·
              refine ⟨30056402113617592942537523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80150405636313581180100061 30056402113617592942537523)
              ·
                refine ⟨45084603170426389413806285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30056402113617592942537523 45084603170426389413806285)
                ·
                  refine ⟨16906726188909896030177357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45084603170426389413806285 16906726188909896030177357)
                  ·
                    refine ⟨6340022320841211011316509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16906726188909896030177357 6340022320841211011316509)
                    ·
                      refine ⟨2377508370315454129243691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6340022320841211011316509 2377508370315454129243691)
                      ·
                        rfl

theorem cell23_4630181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_4630181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630181 prefixEnd_4630181 := by exact prefixLift 4630181
  have htrace : WordTrace (prefixWord ++ tailWord_4630181) baseStart_4630181 baseEnd_4630181 := by
    simpa [prefixWord, tailWord_4630181, baseEnd_4630181] using wordTrace_append hprefix tailTrace_4630181
  have hstable : (prefixWord ++ tailWord_4630181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630181).length < 2 ^ (prefixWord ++ tailWord_4630181).sum := by decide
  have hdescent : baseEnd_4630181 < baseStart_4630181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630199 : List Nat := [1, 1, 3, 1, 5, 1, 4, 2, 1, 2, 2]
def baseStart_4630199 : Nat := 118140960795 + 4630199 * 2 ^ 59
def prefixEnd_4630199 : Nat := 4983230072969 + 3 ^ 40 * 4630199 * 2
def baseEnd_4630199 : Nat := 2377517612967235058818609

theorem tailTrace_4630199 : CollatzResearch.WordTrace tailWord_4630199 prefixEnd_4630199 2377517612967235058818609 := by
  unfold tailWord_4630199
  simp only [CollatzResearch.WordTrace]
  refine ⟨168877231352587272877493651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112584820901724848584995767 168877231352587272877493651)
  ·
    refine ⟨253315847028880909316240477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168877231352587272877493651 253315847028880909316240477)
    ·
      refine ⟨94993442635830340993590179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253315847028880909316240477 94993442635830340993590179)
      ·
        refine ⟨142490163953745511490385269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94993442635830340993590179 142490163953745511490385269)
        ·
          refine ⟨13358452870663641702223619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 142490163953745511490385269 13358452870663641702223619)
          ·
            refine ⟨20037679305995462553335429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13358452870663641702223619 20037679305995462553335429)
            ·
              refine ⟨3757064869874149228750393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20037679305995462553335429 3757064869874149228750393)
              ·
                refine ⟨2817798652405611921562795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3757064869874149228750393 2817798652405611921562795)
                ·
                  refine ⟨4226697978608417882344193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2817798652405611921562795 4226697978608417882344193)
                  ·
                    refine ⟨3170023483956313411758145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4226697978608417882344193 3170023483956313411758145)
                    ·
                      refine ⟨2377517612967235058818609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3170023483956313411758145 2377517612967235058818609)
                      ·
                        rfl

theorem cell23_4630199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 1, 2, 2].length) (baseStart_4630199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630199 prefixEnd_4630199 := by exact prefixLift 4630199
  have htrace : WordTrace (prefixWord ++ tailWord_4630199) baseStart_4630199 baseEnd_4630199 := by
    simpa [prefixWord, tailWord_4630199, baseEnd_4630199] using wordTrace_append hprefix tailTrace_4630199
  have hstable : (prefixWord ++ tailWord_4630199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630199).length < 2 ^ (prefixWord ++ tailWord_4630199).sum := by decide
  have hdescent : baseEnd_4630199 < baseStart_4630199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630208 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 5, 3, 2]
def baseStart_4630208 : Nat := 118140960795 + 4630208 * 2 ^ 59
def prefixEnd_4630208 : Nat := 4983230072969 + 3 ^ 40 * 4630208 * 2
def baseEnd_4630208 : Nat := 2377522234293125523606067

theorem tailTrace_4630208 : CollatzResearch.WordTrace tailWord_4630208 prefixEnd_4630208 2377522234293125523606067 := by
  unfold tailWord_4630208
  simp only [CollatzResearch.WordTrace]
  refine ⟨84438779804777333707285639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112585039739703111609714185 84438779804777333707285639)
  ·
    refine ⟨126658169707166000560928459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84438779804777333707285639 126658169707166000560928459)
    ·
      refine ⟨189987254560749000841392689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126658169707166000560928459 189987254560749000841392689)
      ·
        refine ⟨142490440920561750631044517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189987254560749000841392689 142490440920561750631044517)
        ·
          refine ⟨26716957672605328243320847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142490440920561750631044517 26716957672605328243320847)
          ·
            refine ⟨40075436508907992364981271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26716957672605328243320847 40075436508907992364981271)
            ·
              refine ⟨60113154763361988547471907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40075436508907992364981271 60113154763361988547471907)
              ·
                refine ⟨90169732145042982821207861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60113154763361988547471907 90169732145042982821207861)
                ·
                  refine ⟨8453412388597779639488237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90169732145042982821207861 8453412388597779639488237)
                  ·
                    refine ⟨3170029645724167364808089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8453412388597779639488237 3170029645724167364808089)
                    ·
                      refine ⟨2377522234293125523606067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3170029645724167364808089 2377522234293125523606067)
                      ·
                        rfl

theorem cell23_4630208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 5, 3, 2].length) (baseStart_4630208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630208 prefixEnd_4630208 := by exact prefixLift 4630208
  have htrace : WordTrace (prefixWord ++ tailWord_4630208) baseStart_4630208 baseEnd_4630208 := by
    simpa [prefixWord, tailWord_4630208, baseEnd_4630208] using wordTrace_append hprefix tailTrace_4630208
  have hstable : (prefixWord ++ tailWord_4630208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630208).length < 2 ^ (prefixWord ++ tailWord_4630208).sum := by decide
  have hdescent : baseEnd_4630208 < baseStart_4630208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630236 : List Nat := [2, 2, 5, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_4630236 : Nat := 118140960795 + 4630236 * 2 ^ 59
def prefixEnd_4630236 : Nat := 4983230072969 + 3 ^ 40 * 4630236 * 2
def baseEnd_4630236 : Nat := 2377536611751451414055939

theorem tailTrace_4630236 : CollatzResearch.WordTrace tailWord_4630236 prefixEnd_4630236 2377536611751451414055939 := by
  unfold tailWord_4630236
  simp only [CollatzResearch.WordTrace]
  refine ⟨84439290426726614098295281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112585720568968818797727041 84439290426726614098295281)
  ·
    refine ⟨63329467820044960573721461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84439290426726614098295281 63329467820044960573721461)
    ·
      refine ⟨5937137608129215053786387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63329467820044960573721461 5937137608129215053786387)
      ·
        refine ⟨8905706412193822580679581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5937137608129215053786387 8905706412193822580679581)
        ·
          refine ⟨3339639904572683467754843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8905706412193822580679581 3339639904572683467754843)
          ·
            refine ⟨5009459856859025201632265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3339639904572683467754843 5009459856859025201632265)
            ·
              refine ⟨3757094892644268901224199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5009459856859025201632265 3757094892644268901224199)
              ·
                refine ⟨5635642338966403351836299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3757094892644268901224199 5635642338966403351836299)
                ·
                  refine ⟨8453463508449605027754449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5635642338966403351836299 8453463508449605027754449)
                  ·
                    refine ⟨6340097631337203770815837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8453463508449605027754449 6340097631337203770815837)
                    ·
                      refine ⟨2377536611751451414055939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6340097631337203770815837 2377536611751451414055939)
                      ·
                        rfl

theorem cell23_4630236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_4630236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630236 prefixEnd_4630236 := by exact prefixLift 4630236
  have htrace : WordTrace (prefixWord ++ tailWord_4630236) baseStart_4630236 baseEnd_4630236 := by
    simpa [prefixWord, tailWord_4630236, baseEnd_4630236] using wordTrace_append hprefix tailTrace_4630236
  have hstable : (prefixWord ++ tailWord_4630236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630236).length < 2 ^ (prefixWord ++ tailWord_4630236).sum := by decide
  have hdescent : baseEnd_4630236 < baseStart_4630236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630251 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 4]
def baseStart_4630251 : Nat := 118140960795 + 4630251 * 2 ^ 59
def prefixEnd_4630251 : Nat := 4983230072969 + 3 ^ 40 * 4630251 * 2
def baseEnd_4630251 : Nat := 2377544313961268855368369

theorem tailTrace_4630251 : CollatzResearch.WordTrace tailWord_4630251 prefixEnd_4630251 2377544313961268855368369 := by
  unfold tailWord_4630251
  simp only [CollatzResearch.WordTrace]
  refine ⟨168879127948398885758386607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112586085298932590505591071 168879127948398885758386607)
  ·
    refine ⟨253318691922598328637579911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168879127948398885758386607 253318691922598328637579911)
    ·
      refine ⟨379978037883897492956369867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253318691922598328637579911 379978037883897492956369867)
      ·
        refine ⟨569967056825846239434554801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379978037883897492956369867 569967056825846239434554801)
        ·
          refine ⟨427475292619384679575916101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 569967056825846239434554801 427475292619384679575916101)
          ·
            refine ⟨80151617366134627420484269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 427475292619384679575916101 80151617366134627420484269)
            ·
              refine ⟨30056856512300485282681601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80151617366134627420484269 30056856512300485282681601)
              ·
                refine ⟨22542642384225363962011201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30056856512300485282681601 22542642384225363962011201)
                ·
                  refine ⟨16906981788169022971508401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22542642384225363962011201 16906981788169022971508401)
                  ·
                    refine ⟨12680236341126767228631301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16906981788169022971508401 12680236341126767228631301)
                    ·
                      refine ⟨2377544313961268855368369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12680236341126767228631301 2377544313961268855368369)
                      ·
                        rfl

theorem cell23_4630251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 4].length) (baseStart_4630251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630251 prefixEnd_4630251 := by exact prefixLift 4630251
  have htrace : WordTrace (prefixWord ++ tailWord_4630251) baseStart_4630251 baseEnd_4630251 := by
    simpa [prefixWord, tailWord_4630251, baseEnd_4630251] using wordTrace_append hprefix tailTrace_4630251
  have hstable : (prefixWord ++ tailWord_4630251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630251).length < 2 ^ (prefixWord ++ tailWord_4630251).sum := by decide
  have hdescent : baseEnd_4630251 < baseStart_4630251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630255 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 4, 2, 2]
def baseStart_4630255 : Nat := 118140960795 + 4630255 * 2 ^ 59
def prefixEnd_4630255 : Nat := 4983230072969 + 3 ^ 40 * 4630255 * 2
def baseEnd_4630255 : Nat := 2377546367883886839718351

theorem tailTrace_4630255 : CollatzResearch.WordTrace tailWord_4630255 prefixEnd_4630255 2377546367883886839718351 := by
  unfold tailWord_4630255
  simp only [CollatzResearch.WordTrace]
  refine ⟨168879273840384394441532219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112586182560256262961021479 168879273840384394441532219)
  ·
    refine ⟨253318910760576591662298329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168879273840384394441532219 253318910760576591662298329)
    ·
      refine ⟨189989183070432443746723747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253318910760576591662298329 189989183070432443746723747)
      ·
        refine ⟨284983774605648665620085621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189989183070432443746723747 284983774605648665620085621)
        ·
          refine ⟨26717228869279562401883027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 284983774605648665620085621 26717228869279562401883027)
          ·
            refine ⟨40075843303919343602824541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26717228869279562401883027 40075843303919343602824541)
            ·
              refine ⟨15028441238969753851059203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40075843303919343602824541 15028441238969753851059203)
              ·
                refine ⟨22542661858454630776588805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15028441238969753851059203 22542661858454630776588805)
                ·
                  refine ⟨4226749098460243270610401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22542661858454630776588805 4226749098460243270610401)
                  ·
                    refine ⟨3170061823845182452957801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4226749098460243270610401 3170061823845182452957801)
                    ·
                      refine ⟨2377546367883886839718351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3170061823845182452957801 2377546367883886839718351)
                      ·
                        rfl

theorem cell23_4630255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 2, 2].length) (baseStart_4630255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630255 prefixEnd_4630255 := by exact prefixLift 4630255
  have htrace : WordTrace (prefixWord ++ tailWord_4630255) baseStart_4630255 baseEnd_4630255 := by
    simpa [prefixWord, tailWord_4630255, baseEnd_4630255] using wordTrace_append hprefix tailTrace_4630255
  have hstable : (prefixWord ++ tailWord_4630255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630255).length < 2 ^ (prefixWord ++ tailWord_4630255).sum := by decide
  have hdescent : baseEnd_4630255 < baseStart_4630255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630295 : List Nat := [1, 1, 3, 4, 2, 1, 3, 3, 5]
def baseStart_4630295 : Nat := 118140960795 + 4630295 * 2 ^ 59
def prefixEnd_4630295 : Nat := 4983230072969 + 3 ^ 40 * 4630295 * 2
def baseEnd_4630295 : Nat := 264174100790007409246463

theorem tailTrace_4630295 : CollatzResearch.WordTrace tailWord_4630295 prefixEnd_4630295 264174100790007409246463 := by
  unfold tailWord_4630295
  simp only [CollatzResearch.WordTrace]
  refine ⟨168880732760239481272988339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112587155173492987515325559 168880732760239481272988339)
  ·
    refine ⟨253321099140359221909482509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168880732760239481272988339 253321099140359221909482509)
    ·
      refine ⟨94995412177634708216055941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253321099140359221909482509 94995412177634708216055941)
      ·
        refine ⟨17811639783306507790510489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94995412177634708216055941 17811639783306507790510489)
        ·
          refine ⟨13358729837479880842882867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17811639783306507790510489 13358729837479880842882867)
          ·
            refine ⟨20038094756219821264324301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13358729837479880842882867 20038094756219821264324301)
            ·
              refine ⟨7514285533582432974121613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20038094756219821264324301 7514285533582432974121613)
              ·
                refine ⟨2817857075093412365295605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7514285533582432974121613 2817857075093412365295605)
                ·
                  refine ⟨264174100790007409246463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2817857075093412365295605 264174100790007409246463)
                  ·
                    rfl

theorem cell23_4630295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 5].length) (baseStart_4630295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630295 prefixEnd_4630295 := by exact prefixLift 4630295
  have htrace : WordTrace (prefixWord ++ tailWord_4630295) baseStart_4630295 baseEnd_4630295 := by
    simpa [prefixWord, tailWord_4630295, baseEnd_4630295] using wordTrace_append hprefix tailTrace_4630295
  have hstable : (prefixWord ++ tailWord_4630295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630295).length < 2 ^ (prefixWord ++ tailWord_4630295).sum := by decide
  have hdescent : baseEnd_4630295 < baseStart_4630295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630308 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 4, 5]
def baseStart_4630308 : Nat := 118140960795 + 4630308 * 2 ^ 59
def prefixEnd_4630308 : Nat := 4983230072969 + 3 ^ 40 * 4630308 * 2
def baseEnd_4630308 : Nat := 792524527452858377451869

theorem tailTrace_4630308 : CollatzResearch.WordTrace tailWord_4630308 prefixEnd_4630308 792524527452858377451869 := by
  unfold tailWord_4630308
  simp only [CollatzResearch.WordTrace]
  refine ⟨84440603454596192246605789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112587471272794922995474385 84440603454596192246605789)
  ·
    refine ⟨31665226295473572092477171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84440603454596192246605789 31665226295473572092477171)
    ·
      refine ⟨47497839443210358138715757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31665226295473572092477171 47497839443210358138715757)
      ·
        refine ⟨17811689791203884302018409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47497839443210358138715757 17811689791203884302018409)
        ·
          refine ⟨13358767343402913226513807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17811689791203884302018409 13358767343402913226513807)
          ·
            refine ⟨20038151015104369839770711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13358767343402913226513807 20038151015104369839770711)
            ·
              refine ⟨30057226522656554759656067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20038151015104369839770711 30057226522656554759656067)
              ·
                refine ⟨45085839783984832139484101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30057226522656554759656067 45085839783984832139484101)
                ·
                  refine ⟨8453594959497156026153269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45085839783984832139484101 8453594959497156026153269)
                  ·
                    refine ⟨792524527452858377451869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8453594959497156026153269 792524527452858377451869)
                    ·
                      rfl

theorem cell23_4630308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_4630308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630308 prefixEnd_4630308 := by exact prefixLift 4630308
  have htrace : WordTrace (prefixWord ++ tailWord_4630308) baseStart_4630308 baseEnd_4630308 := by
    simpa [prefixWord, tailWord_4630308, baseEnd_4630308] using wordTrace_append hprefix tailTrace_4630308
  have hstable : (prefixWord ++ tailWord_4630308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630308).length < 2 ^ (prefixWord ++ tailWord_4630308).sum := by decide
  have hdescent : baseEnd_4630308 < baseStart_4630308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630312 : List Nat := [2, 1, 5, 1, 1, 3, 3, 2, 5]
def baseStart_4630312 : Nat := 118140960795 + 4630312 * 2 ^ 59
def prefixEnd_4630312 : Nat := 4983230072969 + 3 ^ 40 * 4630312 * 2
def baseEnd_4630312 : Nat := 264175070697910346300621

theorem tailTrace_4630312 : CollatzResearch.WordTrace tailWord_4630312 prefixEnd_4630312 264175070697910346300621 := by
  unfold tailWord_4630312
  simp only [CollatzResearch.WordTrace]
  refine ⟨84440676400588946588178595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112587568534118595450904793 84440676400588946588178595)
  ·
    refine ⟨126661014600883419882267893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84440676400588946588178595 126661014600883419882267893)
    ·
      refine ⟨11874470118832820613962615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126661014600883419882267893 11874470118832820613962615)
      ·
        refine ⟨17811705178249230920943923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11874470118832820613962615 17811705178249230920943923)
        ·
          refine ⟨26717557767373846381415885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17811705178249230920943923 26717557767373846381415885)
          ·
            refine ⟨10019084162765192393030957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26717557767373846381415885 10019084162765192393030957)
            ·
              refine ⟨3757156561036947147386609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10019084162765192393030957 3757156561036947147386609)
              ·
                refine ⟨2817867420777710360539957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3757156561036947147386609 2817867420777710360539957)
                ·
                  refine ⟨264175070697910346300621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2817867420777710360539957 264175070697910346300621)
                  ·
                    rfl

theorem cell23_4630312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 5].length) (baseStart_4630312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630312 prefixEnd_4630312 := by exact prefixLift 4630312
  have htrace : WordTrace (prefixWord ++ tailWord_4630312) baseStart_4630312 baseEnd_4630312 := by
    simpa [prefixWord, tailWord_4630312, baseEnd_4630312] using wordTrace_append hprefix tailTrace_4630312
  have hstable : (prefixWord ++ tailWord_4630312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630312).length < 2 ^ (prefixWord ++ tailWord_4630312).sum := by decide
  have hdescent : baseEnd_4630312 < baseStart_4630312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630342 : List Nat := [6, 1, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_4630342 : Nat := 118140960795 + 4630342 * 2 ^ 59
def prefixEnd_4630342 : Nat := 4983230072969 + 3 ^ 40 * 4630342 * 2
def baseEnd_4630342 : Nat := 792530346900275999776817

theorem tailTrace_4630342 : CollatzResearch.WordTrace tailWord_4630342 prefixEnd_4630342 792530346900275999776817 := by
  unfold tailWord_4630342
  simp only [CollatzResearch.WordTrace]
  refine ⟨5277576468470912759373415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 112588297994046138866632853 5277576468470912759373415)
  ·
    refine ⟨7916364702706369139060123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5277576468470912759373415 7916364702706369139060123)
    ·
      refine ⟨11874547054059553708590185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7916364702706369139060123 11874547054059553708590185)
      ·
        refine ⟨8905910290544665281442639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11874547054059553708590185 8905910290544665281442639)
        ·
          refine ⟨13358865435816997922163959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8905910290544665281442639 13358865435816997922163959)
          ·
            refine ⟨20038298153725496883245939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13358865435816997922163959 20038298153725496883245939)
            ·
              refine ⟨30057447230588245324868909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20038298153725496883245939 30057447230588245324868909)
              ·
                refine ⟨11271542711470591996825841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30057447230588245324868909 11271542711470591996825841)
                ·
                  refine ⟨8453657033602943997619381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11271542711470591996825841 8453657033602943997619381)
                  ·
                    refine ⟨792530346900275999776817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8453657033602943997619381 792530346900275999776817)
                    ·
                      rfl

theorem cell23_4630342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_4630342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630342 prefixEnd_4630342 := by exact prefixLift 4630342
  have htrace : WordTrace (prefixWord ++ tailWord_4630342) baseStart_4630342 baseEnd_4630342 := by
    simpa [prefixWord, tailWord_4630342, baseEnd_4630342] using wordTrace_append hprefix tailTrace_4630342
  have hstable : (prefixWord ++ tailWord_4630342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630342).length < 2 ^ (prefixWord ++ tailWord_4630342).sum := by decide
  have hdescent : baseEnd_4630342 < baseStart_4630342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630368 : List Nat := [2, 1, 1, 3, 3, 2, 1, 4, 6]
def baseStart_4630368 : Nat := 118140960795 + 4630368 * 2 ^ 59
def prefixEnd_4630368 : Nat := 4983230072969 + 3 ^ 40 * 4630368 * 2
def baseEnd_4630368 : Nat := 264178265688649433067259

theorem tailTrace_4630368 : CollatzResearch.WordTrace tailWord_4630368 prefixEnd_4630368 264178265688649433067259 := by
  unfold tailWord_4630368
  simp only [CollatzResearch.WordTrace]
  refine ⟨84441697644487507370197879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112588930192650009826930505 84441697644487507370197879)
  ·
    refine ⟨126662546466731261055296819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84441697644487507370197879 126662546466731261055296819)
    ·
      refine ⟨189993819700096891582945229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126662546466731261055296819 189993819700096891582945229)
      ·
        refine ⟨71247682387536334343604461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189993819700096891582945229 71247682387536334343604461)
        ·
          refine ⟨26717880895326125378851673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71247682387536334343604461 26717880895326125378851673)
          ·
            refine ⟨20038410671494594034138755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26717880895326125378851673 20038410671494594034138755)
            ·
              refine ⟨30057616007241891051208133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20038410671494594034138755 30057616007241891051208133)
              ·
                refine ⟨5635803001357854572101525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30057616007241891051208133 5635803001357854572101525)
                ·
                  refine ⟨264178265688649433067259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5635803001357854572101525 264178265688649433067259)
                  ·
                    rfl

theorem cell23_4630368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 6].length) (baseStart_4630368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630368 prefixEnd_4630368 := by exact prefixLift 4630368
  have htrace : WordTrace (prefixWord ++ tailWord_4630368) baseStart_4630368 baseEnd_4630368 := by
    simpa [prefixWord, tailWord_4630368, baseEnd_4630368] using wordTrace_append hprefix tailTrace_4630368
  have hstable : (prefixWord ++ tailWord_4630368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630368).length < 2 ^ (prefixWord ++ tailWord_4630368).sum := by decide
  have hdescent : baseEnd_4630368 < baseStart_4630368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630405 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 1, 5, 2]
def baseStart_4630405 : Nat := 118140960795 + 4630405 * 2 ^ 59
def prefixEnd_4630405 : Nat := 4983230072969 + 3 ^ 40 * 4630405 * 2
def baseEnd_4630405 : Nat := 2377623389982061252842661

theorem tailTrace_4630405 : CollatzResearch.WordTrace tailWord_4630405 prefixEnd_4630405 2377623389982061252842661 := by
  unfold tailWord_4630405
  simp only [CollatzResearch.WordTrace]
  refine ⟨168884744789840970059492669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112589829859893980039661779 168884744789840970059492669)
  ·
    refine ⟨63331779296190363772309751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168884744789840970059492669 63331779296190363772309751)
    ·
      refine ⟨94997668944285545658464627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63331779296190363772309751 94997668944285545658464627)
      ·
        refine ⟨142496503416428318487696941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94997668944285545658464627 142496503416428318487696941)
        ·
          refine ⟨53436188781160619432886353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142496503416428318487696941 53436188781160619432886353)
          ·
            refine ⟨40077141585870464574664765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53436188781160619432886353 40077141585870464574664765)
            ·
              refine ⟨15028928094701424215499287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40077141585870464574664765 15028928094701424215499287)
              ·
                refine ⟨22543392142052136323248931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15028928094701424215499287 22543392142052136323248931)
                ·
                  refine ⟨33815088213078204484873397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22543392142052136323248931 33815088213078204484873397)
                  ·
                    refine ⟨3170164519976081670456881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33815088213078204484873397 3170164519976081670456881)
                    ·
                      refine ⟨2377623389982061252842661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3170164519976081670456881 2377623389982061252842661)
                      ·
                        rfl

theorem cell23_4630405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 5, 2].length) (baseStart_4630405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630405 prefixEnd_4630405 := by exact prefixLift 4630405
  have htrace : WordTrace (prefixWord ++ tailWord_4630405) baseStart_4630405 baseEnd_4630405 := by
    simpa [prefixWord, tailWord_4630405, baseEnd_4630405] using wordTrace_append hprefix tailTrace_4630405
  have hstable : (prefixWord ++ tailWord_4630405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630405).length < 2 ^ (prefixWord ++ tailWord_4630405).sum := by decide
  have hdescent : baseEnd_4630405 < baseStart_4630405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630429 : List Nat := [1, 4, 2, 1, 2, 2, 2, 4, 1, 1, 3]
def baseStart_4630429 : Nat := 118140960795 + 4630429 * 2 ^ 59
def prefixEnd_4630429 : Nat := 4983230072969 + 3 ^ 40 * 4630429 * 2
def baseEnd_4630429 : Nat := 2377635713517769158942551

theorem tailTrace_4630429 : CollatzResearch.WordTrace tailWord_4630429 prefixEnd_4630429 2377635713517769158942551 := by
  unfold tailWord_4630429
  simp only [CollatzResearch.WordTrace]
  refine ⟨168885620141754022158366341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112590413427836014772244227 168885620141754022158366341)
  ·
    refine ⟨31666053776578879154693689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168885620141754022158366341 31666053776578879154693689)
    ·
      refine ⟨23749540332434159366020267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31666053776578879154693689 23749540332434159366020267)
      ·
        refine ⟨35624310498651239049030401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23749540332434159366020267 35624310498651239049030401)
        ·
          refine ⟨26718232873988429286772801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35624310498651239049030401 26718232873988429286772801)
          ·
            refine ⟨20038674655491321965079601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26718232873988429286772801 20038674655491321965079601)
            ·
              refine ⟨15029005991618491473809701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20038674655491321965079601 15029005991618491473809701)
              ·
                refine ⟨2817938623428467151339319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15029005991618491473809701 2817938623428467151339319)
                ·
                  refine ⟨4226907935142700727008979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2817938623428467151339319 4226907935142700727008979)
                  ·
                    refine ⟨6340361902714051090513469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4226907935142700727008979 6340361902714051090513469)
                    ·
                      refine ⟨2377635713517769158942551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6340361902714051090513469 2377635713517769158942551)
                      ·
                        rfl

theorem cell23_4630429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_4630429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630429 prefixEnd_4630429 := by exact prefixLift 4630429
  have htrace : WordTrace (prefixWord ++ tailWord_4630429) baseStart_4630429 baseEnd_4630429 := by
    simpa [prefixWord, tailWord_4630429, baseEnd_4630429] using wordTrace_append hprefix tailTrace_4630429
  have hstable : (prefixWord ++ tailWord_4630429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630429).length < 2 ^ (prefixWord ++ tailWord_4630429).sum := by decide
  have hdescent : baseEnd_4630429 < baseStart_4630429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630469 : List Nat := [1, 3, 1, 1, 1, 1, 1, 9, 1, 2, 2]
def baseStart_4630469 : Nat := 118140960795 + 4630469 * 2 ^ 59
def prefixEnd_4630469 : Nat := 4983230072969 + 3 ^ 40 * 4630469 * 2
def baseEnd_4630469 : Nat := 2377656252743949002442367

theorem tailTrace_4630469 : CollatzResearch.WordTrace tailWord_4630469 prefixEnd_4630469 2377656252743949002442367 := by
  unfold tailWord_4630469
  simp only [CollatzResearch.WordTrace]
  refine ⟨168887079061609108989822461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112591386041072739326548307 168887079061609108989822461)
  ·
    refine ⟨63332654648103415871183423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168887079061609108989822461 63332654648103415871183423)
    ·
      refine ⟨94998981972155123806775135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63332654648103415871183423 94998981972155123806775135)
      ·
        refine ⟨142498472958232685710162703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94998981972155123806775135 142498472958232685710162703)
        ·
          refine ⟨213747709437349028565244055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142498472958232685710162703 213747709437349028565244055)
          ·
            refine ⟨320621564156023542847866083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213747709437349028565244055 320621564156023542847866083)
            ·
              refine ⟨480932346234035314271799125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320621564156023542847866083 480932346234035314271799125)
              ·
                refine ⟨2817962966215050669561323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 480932346234035314271799125 2817962966215050669561323)
                ·
                  refine ⟨4226944449322576004341985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2817962966215050669561323 4226944449322576004341985)
                  ·
                    refine ⟨3170208336991932003256489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4226944449322576004341985 3170208336991932003256489)
                    ·
                      refine ⟨2377656252743949002442367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3170208336991932003256489 2377656252743949002442367)
                      ·
                        rfl

theorem cell23_4630469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 1, 2, 2].length) (baseStart_4630469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630469 prefixEnd_4630469 := by exact prefixLift 4630469
  have htrace : WordTrace (prefixWord ++ tailWord_4630469) baseStart_4630469 baseEnd_4630469 := by
    simpa [prefixWord, tailWord_4630469, baseEnd_4630469] using wordTrace_append hprefix tailTrace_4630469
  have hstable : (prefixWord ++ tailWord_4630469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630469).length < 2 ^ (prefixWord ++ tailWord_4630469).sum := by decide
  have hdescent : baseEnd_4630469 < baseStart_4630469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630472 : List Nat := [2, 1, 3, 1, 4, 1, 2, 3, 1, 2, 3]
def baseStart_4630472 : Nat := 118140960795 + 4630472 * 2 ^ 59
def prefixEnd_4630472 : Nat := 4983230072969 + 3 ^ 40 * 4630472 * 2
def baseEnd_4630472 : Nat := 2377657793185912490704853

theorem tailTrace_4630472 : CollatzResearch.WordTrace tailWord_4630472 prefixEnd_4630472 2377657793185912490704853 := by
  unfold tailWord_4630472
  simp only [CollatzResearch.WordTrace]
  refine ⟨84443594240299120251090835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112591458987065493668121113 84443594240299120251090835)
  ·
    refine ⟨126665391360448680376636253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84443594240299120251090835 126665391360448680376636253)
    ·
      refine ⟨47499521760168255141238595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126665391360448680376636253 47499521760168255141238595)
      ·
        refine ⟨71249282640252382711857893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47499521760168255141238595 71249282640252382711857893)
        ·
          refine ⟨13359240495047321758473355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71249282640252382711857893 13359240495047321758473355)
          ·
            refine ⟨20038860742570982637710033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13359240495047321758473355 20038860742570982637710033)
            ·
              refine ⟨15029145556928236978282525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20038860742570982637710033 15029145556928236978282525)
              ·
                refine ⟨5635929583848088866855947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15029145556928236978282525 5635929583848088866855947)
                ·
                  refine ⟨8453894375772133300283921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5635929583848088866855947 8453894375772133300283921)
                  ·
                    refine ⟨6340420781829099975212941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8453894375772133300283921 6340420781829099975212941)
                    ·
                      refine ⟨2377657793185912490704853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6340420781829099975212941 2377657793185912490704853)
                      ·
                        rfl

theorem cell23_4630472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_4630472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630472 prefixEnd_4630472 := by exact prefixLift 4630472
  have htrace : WordTrace (prefixWord ++ tailWord_4630472) baseStart_4630472 baseEnd_4630472 := by
    simpa [prefixWord, tailWord_4630472, baseEnd_4630472] using wordTrace_append hprefix tailTrace_4630472
  have hstable : (prefixWord ++ tailWord_4630472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630472).length < 2 ^ (prefixWord ++ tailWord_4630472).sum := by decide
  have hdescent : baseEnd_4630472 < baseStart_4630472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630488 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 2, 7]
def baseStart_4630488 : Nat := 118140960795 + 4630488 * 2 ^ 59
def prefixEnd_4630488 : Nat := 4983230072969 + 3 ^ 40 * 4630488 * 2
def baseEnd_4630488 : Nat := 792555336292128142701593

theorem tailTrace_4630488 : CollatzResearch.WordTrace tailWord_4630488 prefixEnd_4630488 792555336292128142701593 := by
  unfold tailWord_4630488
  simp only [CollatzResearch.WordTrace]
  refine ⟨84443886024270137617382059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112591848032360183489842745 84443886024270137617382059)
  ·
    refine ⟨126665829036405206426073089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84443886024270137617382059 126665829036405206426073089)
    ·
      refine ⟨94999371777303904819554817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126665829036405206426073089 94999371777303904819554817)
      ·
        refine ⟨71249528832977928614666113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94999371777303904819554817 71249528832977928614666113)
        ·
          refine ⟨53437146624733446460999585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71249528832977928614666113 53437146624733446460999585)
          ·
            refine ⟨40077859968550084845749689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53437146624733446460999585 40077859968550084845749689)
            ·
              refine ⟨30058394976412563634312267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40077859968550084845749689 30058394976412563634312267)
              ·
                refine ⟨45087592464618845451468401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30058394976412563634312267 45087592464618845451468401)
                ·
                  refine ⟨33815694348464134088601301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45087592464618845451468401 33815694348464134088601301)
                  ·
                    refine ⟨792555336292128142701593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33815694348464134088601301 792555336292128142701593)
                    ·
                      rfl

theorem cell23_4630488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_4630488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630488 prefixEnd_4630488 := by exact prefixLift 4630488
  have htrace : WordTrace (prefixWord ++ tailWord_4630488) baseStart_4630488 baseEnd_4630488 := by
    simpa [prefixWord, tailWord_4630488, baseEnd_4630488] using wordTrace_append hprefix tailTrace_4630488
  have hstable : (prefixWord ++ tailWord_4630488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630488).length < 2 ^ (prefixWord ++ tailWord_4630488).sum := by decide
  have hdescent : baseEnd_4630488 < baseStart_4630488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630528 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 5]
def baseStart_4630528 : Nat := 118140960795 + 4630528 * 2 ^ 59
def prefixEnd_4630528 : Nat := 4983230072969 + 3 ^ 40 * 4630528 * 2
def baseEnd_4630528 : Nat := 2377686548102564271604595

theorem tailTrace_4630528 : CollatzResearch.WordTrace tailWord_4630528 prefixEnd_4630528 2377686548102564271604595 := by
  unfold tailWord_4630528
  simp only [CollatzResearch.WordTrace]
  refine ⟨84444615484197681033110119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112592820645596908044146825 84444615484197681033110119)
  ·
    refine ⟨126666923226296521549665179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84444615484197681033110119 126666923226296521549665179)
    ·
      refine ⟨190000384839444782324497769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126666923226296521549665179 190000384839444782324497769)
      ·
        refine ⟨142500288629583586743373327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190000384839444782324497769 142500288629583586743373327)
        ·
          refine ⟨213750432944375380115059991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142500288629583586743373327 213750432944375380115059991)
          ·
            refine ⟨320625649416563070172589987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213750432944375380115059991 320625649416563070172589987)
            ·
              refine ⟨480938474124844605258884981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320625649416563070172589987 480938474124844605258884981)
              ·
                refine ⟨45087981949204181743020467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 480938474124844605258884981 45087981949204181743020467)
                ·
                  refine ⟨67631972923806272614530701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45087981949204181743020467 67631972923806272614530701)
                  ·
                    refine ⟨25361989846427352230449013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67631972923806272614530701 25361989846427352230449013)
                    ·
                      refine ⟨2377686548102564271604595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25361989846427352230449013 2377686548102564271604595)
                      ·
                        rfl

theorem cell23_4630528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_4630528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630528 prefixEnd_4630528 := by exact prefixLift 4630528
  have htrace : WordTrace (prefixWord ++ tailWord_4630528) baseStart_4630528 baseEnd_4630528 := by
    simpa [prefixWord, tailWord_4630528, baseEnd_4630528] using wordTrace_append hprefix tailTrace_4630528
  have hstable : (prefixWord ++ tailWord_4630528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630528).length < 2 ^ (prefixWord ++ tailWord_4630528).sum := by decide
  have hdescent : baseEnd_4630528 < baseStart_4630528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630542 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2]
def baseStart_4630542 : Nat := 118140960795 + 4630542 * 2 ^ 59
def prefixEnd_4630542 : Nat := 4983230072969 + 3 ^ 40 * 4630542 * 2
def baseEnd_4630542 : Nat := 2377693736831727216829531

theorem tailTrace_4630542 : CollatzResearch.WordTrace tailWord_4630542 prefixEnd_4630542 2377693736831727216829531 := by
  unfold tailWord_4630542
  simp only [CollatzResearch.WordTrace]
  refine ⟨21111217698793080307153735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112593161060229761638153253 21111217698793080307153735)
  ·
    refine ⟨31666826548189620460730603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21111217698793080307153735 31666826548189620460730603)
    ·
      refine ⟨47500239822284430691095905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31666826548189620460730603 47500239822284430691095905)
      ·
        refine ⟨35625179866713323018321929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47500239822284430691095905 35625179866713323018321929)
        ·
          refine ⟨26718884900034992263741447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35625179866713323018321929 26718884900034992263741447)
          ·
            refine ⟨40078327350052488395612171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26718884900034992263741447 40078327350052488395612171)
            ·
              refine ⟨60117491025078732593418257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40078327350052488395612171 60117491025078732593418257)
              ·
                refine ⟨45088118268809049445063693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60117491025078732593418257 45088118268809049445063693)
                ·
                  refine ⟨16908044350803393541898885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45088118268809049445063693 16908044350803393541898885)
                  ·
                    refine ⟨3170258315775636289106041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16908044350803393541898885 3170258315775636289106041)
                    ·
                      refine ⟨2377693736831727216829531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3170258315775636289106041 2377693736831727216829531)
                      ·
                        rfl

theorem cell23_4630542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_4630542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630542 prefixEnd_4630542 := by exact prefixLift 4630542
  have htrace : WordTrace (prefixWord ++ tailWord_4630542) baseStart_4630542 baseEnd_4630542 := by
    simpa [prefixWord, tailWord_4630542, baseEnd_4630542] using wordTrace_append hprefix tailTrace_4630542
  have hstable : (prefixWord ++ tailWord_4630542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630542).length < 2 ^ (prefixWord ++ tailWord_4630542).sum := by decide
  have hdescent : baseEnd_4630542 < baseStart_4630542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630559 : List Nat := [1, 1, 2, 4, 1, 2, 1, 5, 2, 2, 2]
def baseStart_4630559 : Nat := 118140960795 + 4630559 * 2 ^ 59
def prefixEnd_4630559 : Nat := 4983230072969 + 3 ^ 40 * 4630559 * 2
def baseEnd_4630559 : Nat := 2377702466002853650316953

theorem tailTrace_4630559 : CollatzResearch.WordTrace tailWord_4630559 prefixEnd_4630559 2377702466002853650316953 := by
  unfold tailWord_4630559
  simp only [CollatzResearch.WordTrace]
  refine ⟨168890361631283054360598731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112593574420855369573732487 168890361631283054360598731)
  ·
    refine ⟨253335542446924581540898097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168890361631283054360598731 253335542446924581540898097)
    ·
      refine ⟨190001656835193436155673573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253335542446924581540898097 190001656835193436155673573)
      ·
        refine ⟨35625310656598769279188795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190001656835193436155673573 35625310656598769279188795)
        ·
          refine ⟨53437965984898153918783193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35625310656598769279188795 53437965984898153918783193)
          ·
            refine ⟨40078474488673615439087395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53437965984898153918783193 40078474488673615439087395)
            ·
              refine ⟨60117711733010423158631093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40078474488673615439087395 60117711733010423158631093)
              ·
                refine ⟨5636035474969727171121665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60117711733010423158631093 5636035474969727171121665)
                ·
                  refine ⟨4227026606227295378341249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5636035474969727171121665 4227026606227295378341249)
                  ·
                    refine ⟨3170269954670471533755937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4227026606227295378341249 3170269954670471533755937)
                    ·
                      refine ⟨2377702466002853650316953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3170269954670471533755937 2377702466002853650316953)
                      ·
                        rfl

theorem cell23_4630559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_4630559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630559 prefixEnd_4630559 := by exact prefixLift 4630559
  have htrace : WordTrace (prefixWord ++ tailWord_4630559) baseStart_4630559 baseEnd_4630559 := by
    simpa [prefixWord, tailWord_4630559, baseEnd_4630559] using wordTrace_append hprefix tailTrace_4630559
  have hstable : (prefixWord ++ tailWord_4630559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630559).length < 2 ^ (prefixWord ++ tailWord_4630559).sum := by decide
  have hdescent : baseEnd_4630559 < baseStart_4630559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630565 : List Nat := [1, 3, 1, 2, 2, 4, 1, 2, 7]
def baseStart_4630565 : Nat := 118140960795 + 4630565 * 2 ^ 59
def prefixEnd_4630565 : Nat := 4983230072969 + 3 ^ 40 * 4630565 * 2
def baseEnd_4630565 : Nat := 264189505209642291871325

theorem tailTrace_4630565 : CollatzResearch.WordTrace tailWord_4630565 prefixEnd_4630565 264189505209642291871325 := by
  unfold tailWord_4630565
  simp only [CollatzResearch.WordTrace]
  refine ⟨168890580469261317385317149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112593720312840878256878099 168890580469261317385317149)
  ·
    refine ⟨63333967675972994019493931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168890580469261317385317149 63333967675972994019493931)
    ·
      refine ⟨95000951513959491029240897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63333967675972994019493931 95000951513959491029240897)
      ·
        refine ⟨71250713635469618271930673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95000951513959491029240897 71250713635469618271930673)
        ·
          refine ⟨53438035226602213703948005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71250713635469618271930673 53438035226602213703948005)
          ·
            refine ⟨10019631604987915069490251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53438035226602213703948005 10019631604987915069490251)
            ·
              refine ⟨15029447407481872604235377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10019631604987915069490251 15029447407481872604235377)
              ·
                refine ⟨11272085555611404453176533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15029447407481872604235377 11272085555611404453176533)
                ·
                  refine ⟨264189505209642291871325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11272085555611404453176533 264189505209642291871325)
                  ·
                    rfl

theorem cell23_4630565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 7].length) (baseStart_4630565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630565 prefixEnd_4630565 := by exact prefixLift 4630565
  have htrace : WordTrace (prefixWord ++ tailWord_4630565) baseStart_4630565 baseEnd_4630565 := by
    simpa [prefixWord, tailWord_4630565, baseEnd_4630565] using wordTrace_append hprefix tailTrace_4630565
  have hstable : (prefixWord ++ tailWord_4630565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630565).length < 2 ^ (prefixWord ++ tailWord_4630565).sum := by decide
  have hdescent : baseEnd_4630565 < baseStart_4630565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630580 : List Nat := [2, 5, 1, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_4630580 : Nat := 118140960795 + 4630580 * 2 ^ 59
def prefixEnd_4630580 : Nat := 4983230072969 + 3 ^ 40 * 4630580 * 2
def baseEnd_4630580 : Nat := 2377713249096598068154357

theorem tailTrace_4630580 : CollatzResearch.WordTrace tailWord_4630580 prefixEnd_4630580 2377713249096598068154357 := by
  unfold tailWord_4630580
  simp only [CollatzResearch.WordTrace]
  refine ⟨84445563782103487473556597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112594085042804649964742129 84445563782103487473556597)
  ·
    refine ⟨7916771604572201950645931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84445563782103487473556597 7916771604572201950645931)
    ·
      refine ⟨11875157406858302925968897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7916771604572201950645931 11875157406858302925968897)
      ·
        refine ⟨8906368055143727194476673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11875157406858302925968897 8906368055143727194476673)
        ·
          refine ⟨6679776041357795395857505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8906368055143727194476673 6679776041357795395857505)
          ·
            refine ⟨5009832031018346546893129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6679776041357795395857505 5009832031018346546893129)
            ·
              refine ⟨3757374023263759910169847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5009832031018346546893129 3757374023263759910169847)
              ·
                refine ⟨5636061034895639865254771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3757374023263759910169847 5636061034895639865254771)
                ·
                  refine ⟨8454091552343459797882157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5636061034895639865254771 8454091552343459797882157)
                  ·
                    refine ⟨3170284332128797424205809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8454091552343459797882157 3170284332128797424205809)
                    ·
                      refine ⟨2377713249096598068154357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3170284332128797424205809 2377713249096598068154357)
                      ·
                        rfl

theorem cell23_4630580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_4630580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630580 prefixEnd_4630580 := by exact prefixLift 4630580
  have htrace : WordTrace (prefixWord ++ tailWord_4630580) baseStart_4630580 baseEnd_4630580 := by
    simpa [prefixWord, tailWord_4630580, baseEnd_4630580] using wordTrace_append hprefix tailTrace_4630580
  have hstable : (prefixWord ++ tailWord_4630580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630580).length < 2 ^ (prefixWord ++ tailWord_4630580).sum := by decide
  have hdescent : baseEnd_4630580 < baseStart_4630580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630593 : List Nat := [1, 2, 5, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_4630593 : Nat := 118140960795 + 4630593 * 2 ^ 59
def prefixEnd_4630593 : Nat := 4983230072969 + 3 ^ 40 * 4630593 * 2
def baseEnd_4630593 : Nat := 2377719924345106517291797

theorem tailTrace_4630593 : CollatzResearch.WordTrace tailWord_4630593 prefixEnd_4630593 2377719924345106517291797 := by
  unfold tailWord_4630593
  simp only [CollatzResearch.WordTrace]
  refine ⟨168891601713159878167336433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112594401142106585444890955 168891601713159878167336433)
  ·
    refine ⟨126668701284869908625502325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168891601713159878167336433 126668701284869908625502325)
    ·
      refine ⟨11875190745456553933640843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126668701284869908625502325 11875190745456553933640843)
      ·
        refine ⟨17812786118184830900461265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11875190745456553933640843 17812786118184830900461265)
        ·
          refine ⟨13359589588638623175345949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17812786118184830900461265 13359589588638623175345949)
          ·
            refine ⟨5009846095739483690754731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13359589588638623175345949 5009846095739483690754731)
            ·
              refine ⟨7514769143609225536132097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5009846095739483690754731 7514769143609225536132097)
              ·
                refine ⟨5636076857706919152099073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7514769143609225536132097 5636076857706919152099073)
                ·
                  refine ⟨4227057643280189364074305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5636076857706919152099073 4227057643280189364074305)
                  ·
                    refine ⟨3170293232460142023055729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4227057643280189364074305 3170293232460142023055729)
                    ·
                      refine ⟨2377719924345106517291797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3170293232460142023055729 2377719924345106517291797)
                      ·
                        rfl

theorem cell23_4630593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_4630593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630593 prefixEnd_4630593 := by exact prefixLift 4630593
  have htrace : WordTrace (prefixWord ++ tailWord_4630593) baseStart_4630593 baseEnd_4630593 := by
    simpa [prefixWord, tailWord_4630593, baseEnd_4630593] using wordTrace_append hprefix tailTrace_4630593
  have hstable : (prefixWord ++ tailWord_4630593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630593).length < 2 ^ (prefixWord ++ tailWord_4630593).sum := by decide
  have hdescent : baseEnd_4630593 < baseStart_4630593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630615 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 4]
def baseStart_4630615 : Nat := 118140960795 + 4630615 * 2 ^ 59
def prefixEnd_4630615 : Nat := 4983230072969 + 3 ^ 40 * 4630615 * 2
def baseEnd_4630615 : Nat := 2377731220919505431216695

theorem tailTrace_4630615 : CollatzResearch.WordTrace tailWord_4630615 prefixEnd_4630615 2377731220919505431216695 := by
  unfold tailWord_4630615
  simp only [CollatzResearch.WordTrace]
  refine ⟨168892404119080175924637299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112594936079386783949758199 168892404119080175924637299)
  ·
    refine ⟨253338606178620263886955949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168892404119080175924637299 253338606178620263886955949)
    ·
      refine ⟨95001977316982598957608481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253338606178620263886955949 95001977316982598957608481)
      ·
        refine ⟨71251482987736949218206361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95001977316982598957608481 71251482987736949218206361)
        ·
          refine ⟨53438612240802711913654771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71251482987736949218206361 53438612240802711913654771)
          ·
            refine ⟨80157918361204067870482157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53438612240802711913654771 80157918361204067870482157)
            ·
              refine ⟨30059219385451525451430809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80157918361204067870482157 30059219385451525451430809)
              ·
                refine ⟨22544414539088644088573107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30059219385451525451430809 22544414539088644088573107)
                ·
                  refine ⟨33816621808632966132859661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22544414539088644088573107 33816621808632966132859661)
                  ·
                    refine ⟨12681233178237362299822373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33816621808632966132859661 12681233178237362299822373)
                    ·
                      refine ⟨2377731220919505431216695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12681233178237362299822373 2377731220919505431216695)
                      ·
                        rfl

theorem cell23_4630615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_4630615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630615 prefixEnd_4630615 := by exact prefixLift 4630615
  have htrace : WordTrace (prefixWord ++ tailWord_4630615) baseStart_4630615 baseEnd_4630615 := by
    simpa [prefixWord, tailWord_4630615, baseEnd_4630615] using wordTrace_append hprefix tailTrace_4630615
  have hstable : (prefixWord ++ tailWord_4630615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630615).length < 2 ^ (prefixWord ++ tailWord_4630615).sum := by decide
  have hdescent : baseEnd_4630615 < baseStart_4630615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630652 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 4, 2, 3]
def baseStart_4630652 : Nat := 118140960795 + 4630652 * 2 ^ 59
def prefixEnd_4630652 : Nat := 4983230072969 + 3 ^ 40 * 4630652 * 2
def baseEnd_4630652 : Nat := 2377750219703721786454025

theorem tailTrace_4630652 : CollatzResearch.WordTrace tailWord_4630652 prefixEnd_4630652 2377750219703721786454025 := by
  unfold tailWord_4630652
  simp only [CollatzResearch.WordTrace]
  refine ⟨84446876809973065621867105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112595835746630754162489473 84446876809973065621867105)
  ·
    refine ⟨63335157607479799216400329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84446876809973065621867105 63335157607479799216400329)
    ·
      refine ⟨47501368205609849412300247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63335157607479799216400329 47501368205609849412300247)
      ·
        refine ⟨71252052308414774118450371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47501368205609849412300247 71252052308414774118450371)
        ·
          refine ⟨106878078462622161177675557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71252052308414774118450371 106878078462622161177675557)
          ·
            refine ⟨20039639711741655220814167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106878078462622161177675557 20039639711741655220814167)
            ·
              refine ⟨30059459567612482831221251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20039639711741655220814167 30059459567612482831221251)
              ·
                refine ⟨45089189351418724246831877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30059459567612482831221251 45089189351418724246831877)
                ·
                  refine ⟨8454223003391010796280977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45089189351418724246831877 8454223003391010796280977)
                  ·
                    refine ⟨6340667252543258097210733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8454223003391010796280977 6340667252543258097210733)
                    ·
                      refine ⟨2377750219703721786454025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6340667252543258097210733 2377750219703721786454025)
                      ·
                        rfl

theorem cell23_4630652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_4630652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630652 prefixEnd_4630652 := by exact prefixLift 4630652
  have htrace : WordTrace (prefixWord ++ tailWord_4630652) baseStart_4630652 baseEnd_4630652 := by
    simpa [prefixWord, tailWord_4630652, baseEnd_4630652] using wordTrace_append hprefix tailTrace_4630652
  have hstable : (prefixWord ++ tailWord_4630652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630652).length < 2 ^ (prefixWord ++ tailWord_4630652).sum := by decide
  have hdescent : baseEnd_4630652 < baseStart_4630652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630659 : List Nat := [1, 1, 1, 3, 3, 5, 1, 1, 3, 4]
def baseStart_4630659 : Nat := 118140960795 + 4630659 * 2 ^ 59
def prefixEnd_4630659 : Nat := 4983230072969 + 3 ^ 40 * 4630659 * 2
def baseEnd_4630659 : Nat := 792584604689434419688831

theorem tailTrace_4630659 : CollatzResearch.WordTrace tailWord_4630659 prefixEnd_4630659 792584604689434419688831 := by
  unfold tailWord_4630659
  simp only [CollatzResearch.WordTrace]
  refine ⟨168894008930920771439239031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112596005953947180959492687 168894008930920771439239031)
  ·
    refine ⟨253341013396381157158858547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168894008930920771439239031 253341013396381157158858547)
    ·
      refine ⟨380011520094571735738287821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253341013396381157158858547 380011520094571735738287821)
      ·
        refine ⟨142504320035464400901857933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 380011520094571735738287821 142504320035464400901857933)
        ·
          refine ⟨53439120013299150338196725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142504320035464400901857933 53439120013299150338196725)
          ·
            refine ⟨5009917501246795344205943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53439120013299150338196725 5009917501246795344205943)
            ·
              refine ⟨7514876251870193016308915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5009917501246795344205943 7514876251870193016308915)
              ·
                refine ⟨11272314377805289524463373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7514876251870193016308915 11272314377805289524463373)
                ·
                  refine ⟨4227117891676983571673765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11272314377805289524463373 4227117891676983571673765)
                  ·
                    refine ⟨792584604689434419688831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4227117891676983571673765 792584604689434419688831)
                    ·
                      rfl

theorem cell23_4630659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 4].length) (baseStart_4630659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630659 prefixEnd_4630659 := by exact prefixLift 4630659
  have htrace : WordTrace (prefixWord ++ tailWord_4630659) baseStart_4630659 baseEnd_4630659 := by
    simpa [prefixWord, tailWord_4630659, baseEnd_4630659] using wordTrace_append hprefix tailTrace_4630659
  have hstable : (prefixWord ++ tailWord_4630659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630659).length < 2 ^ (prefixWord ++ tailWord_4630659).sum := by decide
  have hdescent : baseEnd_4630659 < baseStart_4630659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630715 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 3, 6]
def baseStart_4630715 : Nat := 118140960795 + 4630715 * 2 ^ 59
def prefixEnd_4630715 : Nat := 4983230072969 + 3 ^ 40 * 4630715 * 2
def baseEnd_4630715 : Nat := 792594189661651679988745

theorem tailTrace_4630715 : CollatzResearch.WordTrace tailWord_4630715 prefixEnd_4630715 792594189661651679988745 := by
  unfold tailWord_4630715
  simp only [CollatzResearch.WordTrace]
  refine ⟨168896051418717893003277599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112597367612478595335518399 168896051418717893003277599)
  ·
    refine ⟨253344077128076839504916399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168896051418717893003277599 253344077128076839504916399)
    ·
      refine ⟨380016115692115259257374599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253344077128076839504916399 380016115692115259257374599)
      ·
        refine ⟨570024173538172888886061899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380016115692115259257374599 570024173538172888886061899)
        ·
          refine ⟨855036260307259333329092849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570024173538172888886061899 855036260307259333329092849)
          ·
            refine ⟨641277195230444499996819637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 855036260307259333329092849 641277195230444499996819637)
            ·
              refine ⟨60119737052854171874701841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 641277195230444499996819637 60119737052854171874701841)
              ·
                refine ⟨45089802789640628906026381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60119737052854171874701841 45089802789640628906026381)
                ·
                  refine ⟨16908676046115235839759893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45089802789640628906026381 16908676046115235839759893)
                  ·
                    refine ⟨792594189661651679988745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16908676046115235839759893 792594189661651679988745)
                    ·
                      rfl

theorem cell23_4630715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 6].length) (baseStart_4630715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630715 prefixEnd_4630715 := by exact prefixLift 4630715
  have htrace : WordTrace (prefixWord ++ tailWord_4630715) baseStart_4630715 baseEnd_4630715 := by
    simpa [prefixWord, tailWord_4630715, baseEnd_4630715] using wordTrace_append hprefix tailTrace_4630715
  have hstable : (prefixWord ++ tailWord_4630715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630715).length < 2 ^ (prefixWord ++ tailWord_4630715).sum := by decide
  have hdescent : baseEnd_4630715 < baseStart_4630715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630745 : List Nat := [1, 2, 1, 2, 3, 1, 2, 11]
def baseStart_4630745 : Nat := 118140960795 + 4630745 * 2 ^ 59
def prefixEnd_4630745 : Nat := 4983230072969 + 3 ^ 40 * 4630745 * 2
def baseEnd_4630745 : Nat := 88066591607577404540411

theorem tailTrace_4630745 : CollatzResearch.WordTrace tailWord_4630745 prefixEnd_4630745 88066591607577404540411 := by
  unfold tailWord_4630745
  simp only [CollatzResearch.WordTrace]
  refine ⟨168897145608609208126869689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112598097072406138751246459 168897145608609208126869689)
  ·
    refine ⟨126672859206456906095152267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168897145608609208126869689 126672859206456906095152267)
    ·
      refine ⟨190009288809685359142728401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126672859206456906095152267 190009288809685359142728401)
      ·
        refine ⟨142506966607264019357046301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190009288809685359142728401 142506966607264019357046301)
        ·
          refine ⟨53440112477724007258892363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142506966607264019357046301 53440112477724007258892363)
          ·
            refine ⟨80160168716586010888338545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53440112477724007258892363 80160168716586010888338545)
            ·
              refine ⟨60120126537439508166253909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80160168716586010888338545 60120126537439508166253909)
              ·
                refine ⟨88066591607577404540411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 60120126537439508166253909 88066591607577404540411)
                ·
                  rfl

theorem cell23_4630745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 11].length) (baseStart_4630745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630745 prefixEnd_4630745 := by exact prefixLift 4630745
  have htrace : WordTrace (prefixWord ++ tailWord_4630745) baseStart_4630745 baseEnd_4630745 := by
    simpa [prefixWord, tailWord_4630745, baseEnd_4630745] using wordTrace_append hprefix tailTrace_4630745
  have hstable : (prefixWord ++ tailWord_4630745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630745).length < 2 ^ (prefixWord ++ tailWord_4630745).sum := by decide
  have hdescent : baseEnd_4630745 < baseStart_4630745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630749 : List Nat := [1, 4, 3, 2, 1, 1, 2, 2, 1, 6]
def baseStart_4630749 : Nat := 118140960795 + 4630749 * 2 ^ 59
def prefixEnd_4630749 : Nat := 4983230072969 + 3 ^ 40 * 4630749 * 2
def baseEnd_4630749 : Nat := 792600009109069302313693

theorem tailTrace_4630749 : CollatzResearch.WordTrace tailWord_4630749 prefixEnd_4630749 792600009109069302313693 := by
  unfold tailWord_4630749
  simp only [CollatzResearch.WordTrace]
  refine ⟨168897291500594716810015301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112598194333729811206676867 168897291500594716810015301)
  ·
    refine ⟨31668242156361509401877869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168897291500594716810015301 31668242156361509401877869)
    ·
      refine ⟨11875590808635566025704201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31668242156361509401877869 11875590808635566025704201)
      ·
        refine ⟨8906693106476674519278151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11875590808635566025704201 8906693106476674519278151)
        ·
          refine ⟨13360039659715011778917227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8906693106476674519278151 13360039659715011778917227)
          ·
            refine ⟨20040059489572517668375841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13360039659715011778917227 20040059489572517668375841)
            ·
              refine ⟨15030044617179388251281881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20040059489572517668375841 15030044617179388251281881)
              ·
                refine ⟨11272533462884541188461411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15030044617179388251281881 11272533462884541188461411)
                ·
                  refine ⟨16908800194326811782692117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11272533462884541188461411 16908800194326811782692117)
                  ·
                    refine ⟨792600009109069302313693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16908800194326811782692117 792600009109069302313693)
                    ·
                      rfl

theorem cell23_4630749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_4630749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630749 prefixEnd_4630749 := by exact prefixLift 4630749
  have htrace : WordTrace (prefixWord ++ tailWord_4630749) baseStart_4630749 baseEnd_4630749 := by
    simpa [prefixWord, tailWord_4630749, baseEnd_4630749] using wordTrace_append hprefix tailTrace_4630749
  have hstable : (prefixWord ++ tailWord_4630749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630749).length < 2 ^ (prefixWord ++ tailWord_4630749).sum := by decide
  have hdescent : baseEnd_4630749 < baseStart_4630749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630752 : List Nat := [2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 4]
def baseStart_4630752 : Nat := 118140960795 + 4630752 * 2 ^ 59
def prefixEnd_4630752 : Nat := 4983230072969 + 3 ^ 40 * 4630752 * 2
def baseEnd_4630752 : Nat := 2377801567769171395203565

theorem tailTrace_4630752 : CollatzResearch.WordTrace tailWord_4630752 prefixEnd_4630752 2377801567769171395203565 := by
  unfold tailWord_4630752
  simp only [CollatzResearch.WordTrace]
  refine ⟨84448700459791924161187255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112598267279722565548249673 84448700459791924161187255)
  ·
    refine ⟨126673050689687886241780883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84448700459791924161187255 126673050689687886241780883)
    ·
      refine ⟨190009576034531829362671325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126673050689687886241780883 190009576034531829362671325)
      ·
        refine ⟨71253591012949436011001747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190009576034531829362671325 71253591012949436011001747)
        ·
          refine ⟨106880386519424154016502621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71253591012949436011001747 106880386519424154016502621)
          ·
            refine ⟨40080144944784057756188483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106880386519424154016502621 40080144944784057756188483)
            ·
              refine ⟨60120217417176086634282725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40080144944784057756188483 60120217417176086634282725)
              ·
                refine ⟨11272540765720516243928011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60120217417176086634282725 11272540765720516243928011)
                ·
                  refine ⟨16908811148580774365892017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11272540765720516243928011 16908811148580774365892017)
                  ·
                    refine ⟨12681608361435580774419013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16908811148580774365892017 12681608361435580774419013)
                    ·
                      refine ⟨2377801567769171395203565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12681608361435580774419013 2377801567769171395203565)
                      ·
                        rfl

theorem cell23_4630752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_4630752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630752 prefixEnd_4630752 := by exact prefixLift 4630752
  have htrace : WordTrace (prefixWord ++ tailWord_4630752) baseStart_4630752 baseEnd_4630752 := by
    simpa [prefixWord, tailWord_4630752, baseEnd_4630752] using wordTrace_append hprefix tailTrace_4630752
  have hstable : (prefixWord ++ tailWord_4630752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630752).length < 2 ^ (prefixWord ++ tailWord_4630752).sum := by decide
  have hdescent : baseEnd_4630752 < baseStart_4630752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630786 : List Nat := [3, 4, 1, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_4630786 : Nat := 118140960795 + 4630786 * 2 ^ 59
def prefixEnd_4630786 : Nat := 4983230072969 + 3 ^ 40 * 4630786 * 2
def baseEnd_4630786 : Nat := 2377819026111424262178409

theorem tailTrace_4630786 : CollatzResearch.WordTrace tailWord_4630786 prefixEnd_4630786 2377819026111424262178409 := by
  unfold tailWord_4630786
  simp only [CollatzResearch.WordTrace]
  refine ⟨42224660250365168032278053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112599094000973781419408141 42224660250365168032278053)
  ·
    refine ⟨7917123796943469006052135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42224660250365168032278053 7917123796943469006052135)
    ·
      refine ⟨11875685695415203509078203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7917123796943469006052135 11875685695415203509078203)
      ·
        refine ⟨17813528543122805263617305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11875685695415203509078203 17813528543122805263617305)
        ·
          refine ⟨13360146407342103947712979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17813528543122805263617305 13360146407342103947712979)
          ·
            refine ⟨20040219611013155921569469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13360146407342103947712979 20040219611013155921569469)
            ·
              refine ⟨7515082354129933470588551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20040219611013155921569469 7515082354129933470588551)
              ·
                refine ⟨11272623531194900205882827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7515082354129933470588551 11272623531194900205882827)
                ·
                  refine ⟨16908935296792350308824241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11272623531194900205882827 16908935296792350308824241)
                  ·
                    refine ⟨12681701472594262731618181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16908935296792350308824241 12681701472594262731618181)
                    ·
                      refine ⟨2377819026111424262178409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12681701472594262731618181 2377819026111424262178409)
                      ·
                        rfl

theorem cell23_4630786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_4630786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630786 prefixEnd_4630786 := by exact prefixLift 4630786
  have htrace : WordTrace (prefixWord ++ tailWord_4630786) baseStart_4630786 baseEnd_4630786 := by
    simpa [prefixWord, tailWord_4630786, baseEnd_4630786] using wordTrace_append hprefix tailTrace_4630786
  have hstable : (prefixWord ++ tailWord_4630786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630786).length < 2 ^ (prefixWord ++ tailWord_4630786).sum := by decide
  have hdescent : baseEnd_4630786 < baseStart_4630786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630799 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 3, 3, 2]
def baseStart_4630799 : Nat := 118140960795 + 4630799 * 2 ^ 59
def prefixEnd_4630799 : Nat := 4983230072969 + 3 ^ 40 * 4630799 * 2
def baseEnd_4630799 : Nat := 2377825701359932711315849

theorem tailTrace_4630799 : CollatzResearch.WordTrace tailWord_4630799 prefixEnd_4630799 2377825701359932711315849 := by
  unfold tailWord_4630799
  simp only [CollatzResearch.WordTrace]
  refine ⟨168899115150413575349335451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112599410100275716899556967 168899115150413575349335451)
  ·
    refine ⟨253348672725620363024003177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168899115150413575349335451 253348672725620363024003177)
    ·
      refine ⟨190011504544215272268002383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253348672725620363024003177 190011504544215272268002383)
      ·
        refine ⟨285017256816322908402003575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190011504544215272268002383 285017256816322908402003575)
        ·
          refine ⟨427525885224484362603005363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285017256816322908402003575 427525885224484362603005363)
          ·
            refine ⟨641288827836726543904508045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427525885224484362603005363 641288827836726543904508045)
            ·
              refine ⟨240483310438772453964190517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 641288827836726543904508045 240483310438772453964190517)
              ·
                refine ⟨22545310353634917559142861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 240483310438772453964190517 22545310353634917559142861)
                ·
                  refine ⟨8454491382613094084678573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22545310353634917559142861 8454491382613094084678573)
                  ·
                    refine ⟨3170434268479910281754465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8454491382613094084678573 3170434268479910281754465)
                    ·
                      refine ⟨2377825701359932711315849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3170434268479910281754465 2377825701359932711315849)
                      ·
                        rfl

theorem cell23_4630799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 3, 2].length) (baseStart_4630799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630799 prefixEnd_4630799 := by exact prefixLift 4630799
  have htrace : WordTrace (prefixWord ++ tailWord_4630799) baseStart_4630799 baseEnd_4630799 := by
    simpa [prefixWord, tailWord_4630799, baseEnd_4630799] using wordTrace_append hprefix tailTrace_4630799
  have hstable : (prefixWord ++ tailWord_4630799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630799).length < 2 ^ (prefixWord ++ tailWord_4630799).sum := by decide
  have hdescent : baseEnd_4630799 < baseStart_4630799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630812 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_4630812 : Nat := 118140960795 + 4630812 * 2 ^ 59
def prefixEnd_4630812 : Nat := 4983230072969 + 3 ^ 40 * 4630812 * 2
def baseEnd_4630812 : Nat := 2377832376608441160453289

theorem tailTrace_4630812 : CollatzResearch.WordTrace tailWord_4630812 prefixEnd_4630812 2377832376608441160453289 := by
  unfold tailWord_4630812
  simp only [CollatzResearch.WordTrace]
  refine ⟨84449794649683239284779345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112599726199577652379705793 84449794649683239284779345)
  ·
    refine ⟨63337345987262429463584509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84449794649683239284779345 63337345987262429463584509)
    ·
      refine ⟨23751504745223411048844191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63337345987262429463584509 23751504745223411048844191)
      ·
        refine ⟨35627257117835116573266287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23751504745223411048844191 35627257117835116573266287)
        ·
          refine ⟨53440885676752674859899431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35627257117835116573266287 53440885676752674859899431)
          ·
            refine ⟨80161328515129012289849147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53440885676752674859899431 80161328515129012289849147)
            ·
              refine ⟨120241992772693518434773721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80161328515129012289849147 120241992772693518434773721)
              ·
                refine ⟨90181494579520138826080291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120241992772693518434773721 90181494579520138826080291)
                ·
                  refine ⟨135272241869280208239120437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90181494579520138826080291 135272241869280208239120437)
                  ·
                    refine ⟨12681772675245019522417541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 135272241869280208239120437 12681772675245019522417541)
                    ·
                      refine ⟨2377832376608441160453289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12681772675245019522417541 2377832376608441160453289)
                      ·
                        rfl

theorem cell23_4630812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_4630812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630812 prefixEnd_4630812 := by exact prefixLift 4630812
  have htrace : WordTrace (prefixWord ++ tailWord_4630812) baseStart_4630812 baseEnd_4630812 := by
    simpa [prefixWord, tailWord_4630812, baseEnd_4630812] using wordTrace_append hprefix tailTrace_4630812
  have hstable : (prefixWord ++ tailWord_4630812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630812).length < 2 ^ (prefixWord ++ tailWord_4630812).sum := by decide
  have hdescent : baseEnd_4630812 < baseStart_4630812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630862 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_4630862 : Nat := 118140960795 + 4630862 * 2 ^ 59
def prefixEnd_4630862 : Nat := 4983230072969 + 3 ^ 40 * 4630862 * 2
def baseEnd_4630862 : Nat := 2377858050641165964828059

theorem tailTrace_4630862 : CollatzResearch.WordTrace tailWord_4630862 prefixEnd_4630862 2377858050641165964828059 := by
  unfold tailWord_4630862
  simp only [CollatzResearch.WordTrace]
  refine ⟨21112676618648167138609855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112600941966123558072585893 21112676618648167138609855)
  ·
    refine ⟨31669014927972250707914783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21112676618648167138609855 31669014927972250707914783)
    ·
      refine ⟨47503522391958376061872175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31669014927972250707914783 47503522391958376061872175)
      ·
        refine ⟨71255283587937564092808263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47503522391958376061872175 71255283587937564092808263)
        ·
          refine ⟨106882925381906346139212395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71255283587937564092808263 106882925381906346139212395)
          ·
            refine ⟨160324388072859519208818593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106882925381906346139212395 160324388072859519208818593)
            ·
              refine ⟨120243291054644639406613945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160324388072859519208818593 120243291054644639406613945)
              ·
                refine ⟨90182468290983479554960459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120243291054644639406613945 90182468290983479554960459)
                ·
                  refine ⟨135273702436475219332440689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90182468290983479554960459 135273702436475219332440689)
                  ·
                    refine ⟨101455276827356414499330517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 135273702436475219332440689 101455276827356414499330517)
                    ·
                      refine ⟨2377858050641165964828059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101455276827356414499330517 2377858050641165964828059)
                      ·
                        rfl

theorem cell23_4630862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_4630862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630862 prefixEnd_4630862 := by exact prefixLift 4630862
  have htrace : WordTrace (prefixWord ++ tailWord_4630862) baseStart_4630862 baseEnd_4630862 := by
    simpa [prefixWord, tailWord_4630862, baseEnd_4630862] using wordTrace_append hprefix tailTrace_4630862
  have hstable : (prefixWord ++ tailWord_4630862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630862).length < 2 ^ (prefixWord ++ tailWord_4630862).sum := by decide
  have hdescent : baseEnd_4630862 < baseStart_4630862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630880 : List Nat := [2, 1, 1, 3, 5, 1, 2, 2, 2, 2, 2]
def baseStart_4630880 : Nat := 118140960795 + 4630880 * 2 ^ 59
def prefixEnd_4630880 : Nat := 4983230072969 + 3 ^ 40 * 4630880 * 2
def baseEnd_4630880 : Nat := 2377867293292946894402977

theorem tailTrace_4630880 : CollatzResearch.WordTrace tailWord_4630880 prefixEnd_4630880 2377867293292946894402977 := by
  unfold tailWord_4630880
  simp only [CollatzResearch.WordTrace]
  refine ⟨84451034731560063091517047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112601379642080084122022729 84451034731560063091517047)
  ·
    refine ⟨126676552097340094637275571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84451034731560063091517047 126676552097340094637275571)
    ·
      refine ⟨190014828146010141955913357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126676552097340094637275571 190014828146010141955913357)
      ·
        refine ⟨71255560554753803233467509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190014828146010141955913357 71255560554753803233467509)
        ·
          refine ⟨6680208802008169053137579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71255560554753803233467509 6680208802008169053137579)
          ·
            refine ⟨10020313203012253579706369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6680208802008169053137579 10020313203012253579706369)
            ·
              refine ⟨7515234902259190184779777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10020313203012253579706369 7515234902259190184779777)
              ·
                refine ⟨5636426176694392638584833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7515234902259190184779777 5636426176694392638584833)
                ·
                  refine ⟨4227319632520794478938625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5636426176694392638584833 4227319632520794478938625)
                  ·
                    refine ⟨3170489724390595859203969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4227319632520794478938625 3170489724390595859203969)
                    ·
                      refine ⟨2377867293292946894402977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3170489724390595859203969 2377867293292946894402977)
                      ·
                        rfl

theorem cell23_4630880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_4630880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630880 prefixEnd_4630880 := by exact prefixLift 4630880
  have htrace : WordTrace (prefixWord ++ tailWord_4630880) baseStart_4630880 baseEnd_4630880 := by
    simpa [prefixWord, tailWord_4630880, baseEnd_4630880] using wordTrace_append hprefix tailTrace_4630880
  have hstable : (prefixWord ++ tailWord_4630880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630880).length < 2 ^ (prefixWord ++ tailWord_4630880).sum := by decide
  have hdescent : baseEnd_4630880 < baseStart_4630880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630889 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 1, 7, 2]
def baseStart_4630889 : Nat := 118140960795 + 4630889 * 2 ^ 59
def prefixEnd_4630889 : Nat := 4983230072969 + 3 ^ 40 * 4630889 * 2
def baseEnd_4630889 : Nat := 2377871914618837359190435

theorem tailTrace_4630889 : CollatzResearch.WordTrace tailWord_4630889 prefixEnd_4630889 2377871914618837359190435 := by
  unfold tailWord_4630889
  simp only [CollatzResearch.WordTrace]
  refine ⟨168902397720087520720111721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112601598480058347146741147 168902397720087520720111721)
  ·
    refine ⟨126676798290065640540083791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168902397720087520720111721 126676798290065640540083791)
    ·
      refine ⟨190015197435098460810125687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126676798290065640540083791 190015197435098460810125687)
      ·
        refine ⟨285022796152647691215188531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190015197435098460810125687 285022796152647691215188531)
        ·
          refine ⟨427534194228971536822782797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285022796152647691215188531 427534194228971536822782797)
          ·
            refine ⟨160325322835864326308543549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 427534194228971536822782797 160325322835864326308543549)
            ·
              refine ⟨60121996063449122365703831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160325322835864326308543549 60121996063449122365703831)
              ·
                refine ⟨90182994095173683548555747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60121996063449122365703831 90182994095173683548555747)
                ·
                  refine ⟨135274491142760525322833621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90182994095173683548555747 135274491142760525322833621)
                  ·
                    refine ⟨3170495886158449812253913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 135274491142760525322833621 3170495886158449812253913)
                    ·
                      refine ⟨2377871914618837359190435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3170495886158449812253913 2377871914618837359190435)
                      ·
                        rfl

theorem cell23_4630889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 7, 2].length) (baseStart_4630889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630889 prefixEnd_4630889 := by exact prefixLift 4630889
  have htrace : WordTrace (prefixWord ++ tailWord_4630889) baseStart_4630889 baseEnd_4630889 := by
    simpa [prefixWord, tailWord_4630889, baseEnd_4630889] using wordTrace_append hprefix tailTrace_4630889
  have hstable : (prefixWord ++ tailWord_4630889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630889).length < 2 ^ (prefixWord ++ tailWord_4630889).sum := by decide
  have hdescent : baseEnd_4630889 < baseStart_4630889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4630919 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_4630919 : Nat := 118140960795 + 4630919 * 2 ^ 59
def prefixEnd_4630919 : Nat := 4983230072969 + 3 ^ 40 * 4630919 * 2
def baseEnd_4630919 : Nat := 2377887319038472241815297

theorem tailTrace_4630919 : CollatzResearch.WordTrace tailWord_4630919 prefixEnd_4630919 2377887319038472241815297 := by
  unfold tailWord_4630919
  simp only [CollatzResearch.WordTrace]
  refine ⟨168903491909978835843703811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112602327939985890562469207 168903491909978835843703811)
  ·
    refine ⟨253355237864968253765555717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168903491909978835843703811 253355237864968253765555717)
    ·
      refine ⟨47504107099681547581041697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 253355237864968253765555717 47504107099681547581041697)
      ·
        refine ⟨35628080324761160685781273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47504107099681547581041697 35628080324761160685781273)
        ·
          refine ⟨26721060243570870514335955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35628080324761160685781273 26721060243570870514335955)
          ·
            refine ⟨40081590365356305771503933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26721060243570870514335955 40081590365356305771503933)
            ·
              refine ⟨15030596387008614664313975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40081590365356305771503933 15030596387008614664313975)
              ·
                refine ⟨22545894580512921996470963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15030596387008614664313975 22545894580512921996470963)
                ·
                  refine ⟨33818841870769382994706445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22545894580512921996470963 33818841870769382994706445)
                  ·
                    refine ⟨12682065701538518623014917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33818841870769382994706445 12682065701538518623014917)
                    ·
                      refine ⟨2377887319038472241815297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12682065701538518623014917 2377887319038472241815297)
                      ·
                        rfl

theorem cell23_4630919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_4630919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4630919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4630919 prefixEnd_4630919 := by exact prefixLift 4630919
  have htrace : WordTrace (prefixWord ++ tailWord_4630919) baseStart_4630919 baseEnd_4630919 := by
    simpa [prefixWord, tailWord_4630919, baseEnd_4630919] using wordTrace_append hprefix tailTrace_4630919
  have hstable : (prefixWord ++ tailWord_4630919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4630919).length < 2 ^ (prefixWord ++ tailWord_4630919).sum := by decide
  have hdescent : baseEnd_4630919 < baseStart_4630919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4630919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631010 : List Nat := [3, 3, 3, 2, 1, 1, 1, 3, 6]
def baseStart_4631010 : Nat := 118140960795 + 4631010 * 2 ^ 59
def prefixEnd_4631010 : Nat := 4983230072969 + 3 ^ 40 * 4631010 * 2
def baseEnd_4631010 : Nat := 264214893975336820641931

theorem tailTrace_4631010 : CollatzResearch.WordTrace tailWord_4631010 prefixEnd_4631010 264214893975336820641931 := by
  unfold tailWord_4631010
  simp only [CollatzResearch.WordTrace]
  refine ⟨42226702738162289596316621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112604540635099438923510989 42226702738162289596316621)
  ·
    refine ⟨15835013526810858598618733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42226702738162289596316621 15835013526810858598618733)
    ·
      refine ⟨5938130072554071974482025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15835013526810858598618733 5938130072554071974482025)
      ·
        refine ⟨4453597554415553980861519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5938130072554071974482025 4453597554415553980861519)
        ·
          refine ⟨6680396331623330971292279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4453597554415553980861519 6680396331623330971292279)
          ·
            refine ⟨10020594497434996456938419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6680396331623330971292279 10020594497434996456938419)
            ·
              refine ⟨15030891746152494685407629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10020594497434996456938419 15030891746152494685407629)
              ·
                refine ⟨5636584404807185507027861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15030891746152494685407629 5636584404807185507027861)
                ·
                  refine ⟨264214893975336820641931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5636584404807185507027861 264214893975336820641931)
                  ·
                    rfl

theorem cell23_4631010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_4631010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631010 prefixEnd_4631010 := by exact prefixLift 4631010
  have htrace : WordTrace (prefixWord ++ tailWord_4631010) baseStart_4631010 baseEnd_4631010 := by
    simpa [prefixWord, tailWord_4631010, baseEnd_4631010] using wordTrace_append hprefix tailTrace_4631010
  have hstable : (prefixWord ++ tailWord_4631010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631010).length < 2 ^ (prefixWord ++ tailWord_4631010).sum := by decide
  have hdescent : baseEnd_4631010 < baseStart_4631010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631019 : List Nat := [1, 1, 1, 1, 2, 3, 4, 3, 1, 6]
def baseStart_4631019 : Nat := 118140960795 + 4631019 * 2 ^ 59
def prefixEnd_4631019 : Nat := 4983230072969 + 3 ^ 40 * 4631019 * 2
def baseEnd_4631019 : Nat := 792646222367973950188279

theorem tailTrace_4631019 : CollatzResearch.WordTrace tailWord_4631019 prefixEnd_4631019 792646222367973950188279 := by
  unfold tailWord_4631019
  simp only [CollatzResearch.WordTrace]
  refine ⟨168907139209616552922344111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112604759473077701948229407 168907139209616552922344111)
  ·
    refine ⟨253360708814424829383516167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168907139209616552922344111 253360708814424829383516167)
    ·
      refine ⟨380041063221637244075274251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253360708814424829383516167 380041063221637244075274251)
      ·
        refine ⟨570061594832455866112911377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380041063221637244075274251 570061594832455866112911377)
        ·
          refine ⟨427546196124341899584683533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 570061594832455866112911377 427546196124341899584683533)
          ·
            refine ⟨160329823546628212344256325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 427546196124341899584683533 160329823546628212344256325)
            ·
              refine ⟨30061841914992789814548061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160329823546628212344256325 30061841914992789814548061)
              ·
                refine ⟨11273190718122296180455523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30061841914992789814548061 11273190718122296180455523)
                ·
                  refine ⟨16909786077183444270683285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11273190718122296180455523 16909786077183444270683285)
                  ·
                    refine ⟨792646222367973950188279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16909786077183444270683285 792646222367973950188279)
                    ·
                      rfl

theorem cell23_4631019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 6].length) (baseStart_4631019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631019 prefixEnd_4631019 := by exact prefixLift 4631019
  have htrace : WordTrace (prefixWord ++ tailWord_4631019) baseStart_4631019 baseEnd_4631019 := by
    simpa [prefixWord, tailWord_4631019, baseEnd_4631019] using wordTrace_append hprefix tailTrace_4631019
  have hstable : (prefixWord ++ tailWord_4631019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631019).length < 2 ^ (prefixWord ++ tailWord_4631019).sum := by decide
  have hdescent : baseEnd_4631019 < baseStart_4631019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631030 : List Nat := [5, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2]
def baseStart_4631030 : Nat := 118140960795 + 4631030 * 2 ^ 59
def prefixEnd_4631030 : Nat := 4983230072969 + 3 ^ 40 * 4631030 * 2
def baseEnd_4631030 : Nat := 2377944315391121307527287

theorem tailTrace_4631030 : CollatzResearch.WordTrace tailWord_4631030 prefixEnd_4631030 2377944315391121307527287 := by
  unfold tailWord_4631030
  simp only [CollatzResearch.WordTrace]
  refine ⟨10556721275786043862562159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112605026941717801200663029 10556721275786043862562159)
  ·
    refine ⟨15835081913679065793843239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10556721275786043862562159 15835081913679065793843239)
    ·
      refine ⟨23752622870518598690764859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15835081913679065793843239 23752622870518598690764859)
      ·
        refine ⟨35628934305777898036147289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23752622870518598690764859 35628934305777898036147289)
        ·
          refine ⟨26721700729333423527110467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35628934305777898036147289 26721700729333423527110467)
          ·
            refine ⟨40082551094000135290665701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26721700729333423527110467 40082551094000135290665701)
            ·
              refine ⟨7515478330125025366999819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40082551094000135290665701 7515478330125025366999819)
              ·
                refine ⟨11273217495187538050499729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7515478330125025366999819 11273217495187538050499729)
                ·
                  refine ⟨8454913121390653537874797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11273217495187538050499729 8454913121390653537874797)
                  ·
                    refine ⟨3170592420521495076703049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8454913121390653537874797 3170592420521495076703049)
                    ·
                      refine ⟨2377944315391121307527287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3170592420521495076703049 2377944315391121307527287)
                      ·
                        rfl

theorem cell23_4631030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_4631030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631030 prefixEnd_4631030 := by exact prefixLift 4631030
  have htrace : WordTrace (prefixWord ++ tailWord_4631030) baseStart_4631030 baseEnd_4631030 := by
    simpa [prefixWord, tailWord_4631030, baseEnd_4631030] using wordTrace_append hprefix tailTrace_4631030
  have hstable : (prefixWord ++ tailWord_4631030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631030).length < 2 ^ (prefixWord ++ tailWord_4631030).sum := by decide
  have hdescent : baseEnd_4631030 < baseStart_4631030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631043 : List Nat := [1, 1, 1, 3, 2, 1, 7, 1, 1, 1, 4]
def baseStart_4631043 : Nat := 118140960795 + 4631043 * 2 ^ 59
def prefixEnd_4631043 : Nat := 4983230072969 + 3 ^ 40 * 4631043 * 2
def baseEnd_4631043 : Nat := 2377950990639629756664727

theorem tailTrace_4631043 : CollatzResearch.WordTrace tailWord_4631043 prefixEnd_4631043 2377950990639629756664727 := by
  unfold tailWord_4631043
  simp only [CollatzResearch.WordTrace]
  refine ⟨168908014561529605021217783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112605343041019736680811855 168908014561529605021217783)
  ·
    refine ⟨253362021842294407531826675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168908014561529605021217783 253362021842294407531826675)
    ·
      refine ⟨380043032763441611297740013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253362021842294407531826675 380043032763441611297740013)
      ·
        refine ⟨142516137286290604236652505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 380043032763441611297740013 142516137286290604236652505)
        ·
          refine ⟨106887102964717953177489379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142516137286290604236652505 106887102964717953177489379)
          ·
            refine ⟨160330654447076929766234069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106887102964717953177489379 160330654447076929766234069)
            ·
              refine ⟨3757749713603365541396111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 160330654447076929766234069 3757749713603365541396111)
              ·
                refine ⟨5636624570405048312094167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3757749713603365541396111 5636624570405048312094167)
                ·
                  refine ⟨8454936855607572468141251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5636624570405048312094167 8454936855607572468141251)
                  ·
                    refine ⟨12682405283411358702211877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8454936855607572468141251 12682405283411358702211877)
                    ·
                      refine ⟨2377950990639629756664727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12682405283411358702211877 2377950990639629756664727)
                      ·
                        rfl

theorem cell23_4631043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 1, 1, 4].length) (baseStart_4631043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631043 prefixEnd_4631043 := by exact prefixLift 4631043
  have htrace : WordTrace (prefixWord ++ tailWord_4631043) baseStart_4631043 baseEnd_4631043 := by
    simpa [prefixWord, tailWord_4631043, baseEnd_4631043] using wordTrace_append hprefix tailTrace_4631043
  have hstable : (prefixWord ++ tailWord_4631043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631043).length < 2 ^ (prefixWord ++ tailWord_4631043).sum := by decide
  have hdescent : baseEnd_4631043 < baseStart_4631043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631054 : List Nat := [4, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3]
def baseStart_4631054 : Nat := 118140960795 + 4631054 * 2 ^ 59
def prefixEnd_4631054 : Nat := 4983230072969 + 3 ^ 40 * 4631054 * 2
def baseEnd_4631054 : Nat := 2377956638926829213627177

theorem tailTrace_4631054 : CollatzResearch.WordTrace tailWord_4631054 prefixEnd_4631054 2377956638926829213627177 := by
  unfold tailWord_4631054
  simp only [CollatzResearch.WordTrace]
  refine ⟨21113551970561219237483527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112605610509659835933245477 21113551970561219237483527)
  ·
    refine ⟨31670327955841828856225291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21113551970561219237483527 31670327955841828856225291)
    ·
      refine ⟨47505491933762743284337937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31670327955841828856225291 47505491933762743284337937)
      ·
        refine ⟨35629118950322057463253453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47505491933762743284337937 35629118950322057463253453)
        ·
          refine ⟨13360919606370771548720045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35629118950322057463253453 13360919606370771548720045)
          ·
            refine ⟨5010344852389039330770017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13360919606370771548720045 5010344852389039330770017)
            ·
              refine ⟨3757758639291779498077513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5010344852389039330770017 3757758639291779498077513)
              ·
                refine ⟨2818318979468834623558135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3757758639291779498077513 2818318979468834623558135)
                ·
                  refine ⟨4227478469203251935337203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2818318979468834623558135 4227478469203251935337203)
                  ·
                    refine ⟨6341217703804877903005805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4227478469203251935337203 6341217703804877903005805)
                    ·
                      refine ⟨2377956638926829213627177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6341217703804877903005805 2377956638926829213627177)
                      ·
                        rfl

theorem cell23_4631054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_4631054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631054 prefixEnd_4631054 := by exact prefixLift 4631054
  have htrace : WordTrace (prefixWord ++ tailWord_4631054) baseStart_4631054 baseEnd_4631054 := by
    simpa [prefixWord, tailWord_4631054, baseEnd_4631054] using wordTrace_append hprefix tailTrace_4631054
  have hstable : (prefixWord ++ tailWord_4631054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631054).length < 2 ^ (prefixWord ++ tailWord_4631054).sum := by decide
  have hdescent : baseEnd_4631054 < baseStart_4631054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
