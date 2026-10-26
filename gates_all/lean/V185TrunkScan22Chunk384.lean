import V185TrunkScan22Chunk383

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3424060 : List Nat := [2, 2, 2, 2, 1, 1, 3, 4, 5]
def baseStart_3424060 : Nat := 118140960795 + 3424060 * 2 ^ 59
def prefixEnd_3424060 : Nat := 4983230072969 + 3 ^ 40 * 3424060 * 2
def baseEnd_3424060 : Nat := 390708571074217462934009

theorem tailTrace_3424060 : CollatzResearch.WordTrace tailWord_3424060 prefixEnd_3424060 390708571074217462934009 := by
  unfold tailWord_3424060
  simp only [CollatzResearch.WordTrace]
  refine ⟨62442863987611438868082817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83257151983481918490777089 62442863987611438868082817)
  ·
    refine ⟨46832147990708579151062113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62442863987611438868082817 46832147990708579151062113)
    ·
      refine ⟨35124110993031434363296585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46832147990708579151062113 35124110993031434363296585)
      ·
        refine ⟨26343083244773575772472439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35124110993031434363296585 26343083244773575772472439)
        ·
          refine ⟨39514624867160363658708659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26343083244773575772472439 39514624867160363658708659)
          ·
            refine ⟨59271937300740545488062989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39514624867160363658708659 59271937300740545488062989)
            ·
              refine ⟨22226976487777704558023621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59271937300740545488062989 22226976487777704558023621)
              ·
                refine ⟨4167558091458319604629429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22226976487777704558023621 4167558091458319604629429)
                ·
                  refine ⟨390708571074217462934009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4167558091458319604629429 390708571074217462934009)
                  ·
                    rfl

theorem cell22_3424060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_3424060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424060 prefixEnd_3424060 := by exact prefixLift 3424060
  have htrace : WordTrace (prefixWord ++ tailWord_3424060) baseStart_3424060 baseEnd_3424060 := by
    simpa [prefixWord, tailWord_3424060, baseEnd_3424060] using wordTrace_append hprefix tailTrace_3424060
  have hstable : (prefixWord ++ tailWord_3424060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424060).length < 2 ^ (prefixWord ++ tailWord_3424060).sum := by decide
  have hdescent : baseEnd_3424060 < baseStart_3424060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424090 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 3, 4]
def baseStart_3424090 : Nat := 118140960795 + 3424090 * 2 ^ 59
def prefixEnd_3424090 : Nat := 4983230072969 + 3 ^ 40 * 3424090 * 2
def baseEnd_3424090 : Nat := 1172135982835742310551935

theorem tailTrace_3424090 : CollatzResearch.WordTrace tailWord_3424090 prefixEnd_3424090 1172135982835742310551935 := by
  unfold tailWord_3424090
  simp only [CollatzResearch.WordTrace]
  refine ⟨31221705541278548214939431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83257881443409461906505149 31221705541278548214939431)
  ·
    refine ⟨46832558311917822322409147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31221705541278548214939431 46832558311917822322409147)
    ·
      refine ⟨70248837467876733483613721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46832558311917822322409147 70248837467876733483613721)
      ·
        refine ⟨52686628100907550112710291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70248837467876733483613721 52686628100907550112710291)
        ·
          refine ⟨79029942151361325169065437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52686628100907550112710291 79029942151361325169065437)
          ·
            refine ⟨29636228306760496938399539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79029942151361325169065437 29636228306760496938399539)
            ·
              refine ⟨44454342460140745407599309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29636228306760496938399539 44454342460140745407599309)
              ·
                refine ⟨16670378422552779527849741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44454342460140745407599309 16670378422552779527849741)
                ·
                  refine ⟨6251391908457292322943653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16670378422552779527849741 6251391908457292322943653)
                  ·
                    refine ⟨1172135982835742310551935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6251391908457292322943653 1172135982835742310551935)
                    ·
                      rfl

theorem cell22_3424090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_3424090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424090 prefixEnd_3424090 := by exact prefixLift 3424090
  have htrace : WordTrace (prefixWord ++ tailWord_3424090) baseStart_3424090 baseEnd_3424090 := by
    simpa [prefixWord, tailWord_3424090, baseEnd_3424090] using wordTrace_append hprefix tailTrace_3424090
  have hstable : (prefixWord ++ tailWord_3424090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424090).length < 2 ^ (prefixWord ++ tailWord_3424090).sum := by decide
  have hdescent : baseEnd_3424090 < baseStart_3424090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424122 : List Nat := [3, 1, 1, 1, 1, 1, 6, 4, 4]
def baseStart_3424122 : Nat := 118140960795 + 3424122 * 2 ^ 59
def prefixEnd_3424122 : Nat := 4983230072969 + 3 ^ 40 * 3424122 * 2
def baseEnd_3424122 : Nat := 390715645696568297917279

theorem tailTrace_3424122 : CollatzResearch.WordTrace tailWord_3424122 prefixEnd_3424122 390715645696568297917279 := by
  unfold tailWord_3424122
  simp only [CollatzResearch.WordTrace]
  refine ⟨31221997325249565581230655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83258659533998841549948413 31221997325249565581230655)
  ·
    refine ⟨46832995987874348371845983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31221997325249565581230655 46832995987874348371845983)
    ·
      refine ⟨70249493981811522557768975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46832995987874348371845983 70249493981811522557768975)
      ·
        refine ⟨105374240972717283836653463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70249493981811522557768975 105374240972717283836653463)
        ·
          refine ⟨158061361459075925754980195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105374240972717283836653463 158061361459075925754980195)
          ·
            refine ⟨237092042188613888632470293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158061361459075925754980195 237092042188613888632470293)
            ·
              refine ⟨11113689477591276029647045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 237092042188613888632470293 11113689477591276029647045)
              ·
                refine ⟨2083816777048364255558821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11113689477591276029647045 2083816777048364255558821)
                ·
                  refine ⟨390715645696568297917279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2083816777048364255558821 390715645696568297917279)
                  ·
                    rfl

theorem cell22_3424122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 4].length) (baseStart_3424122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424122 prefixEnd_3424122 := by exact prefixLift 3424122
  have htrace : WordTrace (prefixWord ++ tailWord_3424122) baseStart_3424122 baseEnd_3424122 := by
    simpa [prefixWord, tailWord_3424122, baseEnd_3424122] using wordTrace_append hprefix tailTrace_3424122
  have hstable : (prefixWord ++ tailWord_3424122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424122).length < 2 ^ (prefixWord ++ tailWord_3424122).sum := by decide
  have hdescent : baseEnd_3424122 < baseStart_3424122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424156 : List Nat := [2, 2, 3, 3, 1, 3, 1, 3, 4]
def baseStart_3424156 : Nat := 118140960795 + 3424156 * 2 ^ 59
def prefixEnd_3424156 : Nat := 4983230072969 + 3 ^ 40 * 3424156 * 2
def baseEnd_3424156 : Nat := 390719525328180046133911

theorem tailTrace_3424156 : CollatzResearch.WordTrace tailWord_3424156 prefixEnd_3424156 390719525328180046133911 := by
  unfold tailWord_3424156
  simp only [CollatzResearch.WordTrace]
  refine ⟨62444614691437543065830161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83259486255250057421106881 62444614691437543065830161)
  ·
    refine ⟨46833461018578157299372621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62444614691437543065830161 46833461018578157299372621)
    ·
      refine ⟨17562547881966808987264733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46833461018578157299372621 17562547881966808987264733)
      ·
        refine ⟨6585955455737553370224275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17562547881966808987264733 6585955455737553370224275)
        ·
          refine ⟨9878933183606330055336413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6585955455737553370224275 9878933183606330055336413)
          ·
            refine ⟨3704599943852373770751155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9878933183606330055336413 3704599943852373770751155)
            ·
              refine ⟨5556899915778560656126733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3704599943852373770751155 5556899915778560656126733)
              ·
                refine ⟨2083837468416960246047525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5556899915778560656126733 2083837468416960246047525)
                ·
                  refine ⟨390719525328180046133911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2083837468416960246047525 390719525328180046133911)
                  ·
                    rfl

theorem cell22_3424156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 4].length) (baseStart_3424156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424156 prefixEnd_3424156 := by exact prefixLift 3424156
  have htrace : WordTrace (prefixWord ++ tailWord_3424156) baseStart_3424156 baseEnd_3424156 := by
    simpa [prefixWord, tailWord_3424156, baseEnd_3424156] using wordTrace_append hprefix tailTrace_3424156
  have hstable : (prefixWord ++ tailWord_3424156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424156).length < 2 ^ (prefixWord ++ tailWord_3424156).sum := by decide
  have hdescent : baseEnd_3424156 < baseStart_3424156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424167 : List Nat := [1, 1, 6, 1, 2, 3, 8]
def baseStart_3424167 : Nat := 118140960795 + 3424167 * 2 ^ 59
def prefixEnd_3424167 : Nat := 4983230072969 + 3 ^ 40 * 3424167 * 2
def baseEnd_3424167 : Nat := 43413420055901473199137

theorem tailTrace_3424167 : CollatzResearch.WordTrace tailWord_3424167 prefixEnd_3424167 43413420055901473199137 := by
  unfold tailWord_3424167
  simp only [CollatzResearch.WordTrace]
  refine ⟨124889630585835235010310755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83259753723890156673540503 124889630585835235010310755)
  ·
    refine ⟨187334445878752852515466133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124889630585835235010310755 187334445878752852515466133)
    ·
      refine ⟨8781302150566539961662475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 187334445878752852515466133 8781302150566539961662475)
      ·
        refine ⟨13171953225849809942493713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8781302150566539961662475 13171953225849809942493713)
        ·
          refine ⟨9878964919387357456870285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13171953225849809942493713 9878964919387357456870285)
          ·
            refine ⟨3704611844770259046326357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9878964919387357456870285 3704611844770259046326357)
            ·
              refine ⟨43413420055901473199137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3704611844770259046326357 43413420055901473199137)
              ·
                rfl

theorem cell22_3424167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 8].length) (baseStart_3424167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424167 prefixEnd_3424167 := by exact prefixLift 3424167
  have htrace : WordTrace (prefixWord ++ tailWord_3424167) baseStart_3424167 baseEnd_3424167 := by
    simpa [prefixWord, tailWord_3424167, baseEnd_3424167] using wordTrace_append hprefix tailTrace_3424167
  have hstable : (prefixWord ++ tailWord_3424167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424167).length < 2 ^ (prefixWord ++ tailWord_3424167).sum := by decide
  have hdescent : baseEnd_3424167 < baseStart_3424167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424257 : List Nat := [1, 2, 4, 1, 2, 1, 3, 2, 6]
def baseStart_3424257 : Nat := 118140960795 + 3424257 * 2 ^ 59
def prefixEnd_3424257 : Nat := 4983230072969 + 3 ^ 40 * 3424257 * 2
def baseEnd_3424257 : Nat := 390731050116203180542141

theorem tailTrace_3424257 : CollatzResearch.WordTrace tailWord_3424257 prefixEnd_3424257 390731050116203180542141 := by
  unfold tailWord_3424257
  simp only [CollatzResearch.WordTrace]
  refine ⟨124892913155509180381087025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83261942103672786920724683 124892913155509180381087025)
  ·
    refine ⟨93669684866631885285815269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124892913155509180381087025 93669684866631885285815269)
    ·
      refine ⟨17563065912493478491090363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93669684866631885285815269 17563065912493478491090363)
      ·
        refine ⟨26344598868740217736635545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17563065912493478491090363 26344598868740217736635545)
        ·
          refine ⟨19758449151555163302476659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26344598868740217736635545 19758449151555163302476659)
          ·
            refine ⟨29637673727332744953714989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19758449151555163302476659 29637673727332744953714989)
            ·
              refine ⟨11114127647749779357643121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29637673727332744953714989 11114127647749779357643121)
              ·
                refine ⟨8335595735812334518232341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11114127647749779357643121 8335595735812334518232341)
                ·
                  refine ⟨390731050116203180542141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8335595735812334518232341 390731050116203180542141)
                  ·
                    rfl

theorem cell22_3424257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 6].length) (baseStart_3424257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424257 prefixEnd_3424257 := by exact prefixLift 3424257
  have htrace : WordTrace (prefixWord ++ tailWord_3424257) baseStart_3424257 baseEnd_3424257 := by
    simpa [prefixWord, tailWord_3424257, baseEnd_3424257] using wordTrace_append hprefix tailTrace_3424257
  have hstable : (prefixWord ++ tailWord_3424257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424257).length < 2 ^ (prefixWord ++ tailWord_3424257).sum := by decide
  have hdescent : baseEnd_3424257 < baseStart_3424257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424272 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 6, 3]
def baseStart_3424272 : Nat := 118140960795 + 3424272 * 2 ^ 59
def prefixEnd_3424272 : Nat := 4983230072969 + 3 ^ 40 * 3424272 * 2
def baseEnd_3424272 : Nat := 1172198285155154502501377

theorem tailTrace_3424272 : CollatzResearch.WordTrace tailWord_3424272 prefixEnd_3424272 1172198285155154502501377 := by
  unfold tailWord_3424272
  simp only [CollatzResearch.WordTrace]
  refine ⟨62446730125227418971441535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83262306833636558628588713 62446730125227418971441535)
  ·
    refine ⟨93670095187841128457162303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62446730125227418971441535 93670095187841128457162303)
    ·
      refine ⟨140505142781761692685743455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93670095187841128457162303 140505142781761692685743455)
      ·
        refine ⟨210757714172642539028615183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140505142781761692685743455 210757714172642539028615183)
        ·
          refine ⟨316136571258963808542922775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210757714172642539028615183 316136571258963808542922775)
          ·
            refine ⟨474204856888445712814384163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316136571258963808542922775 474204856888445712814384163)
            ·
              refine ⟨711307285332668569221576245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474204856888445712814384163 711307285332668569221576245)
              ·
                refine ⟨66685057999937678364522773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 711307285332668569221576245 66685057999937678364522773)
                ·
                  refine ⟨3125862093747078673337005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66685057999937678364522773 3125862093747078673337005)
                  ·
                    refine ⟨1172198285155154502501377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3125862093747078673337005 1172198285155154502501377)
                    ·
                      rfl

theorem cell22_3424272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 6, 3].length) (baseStart_3424272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424272 prefixEnd_3424272 := by exact prefixLift 3424272
  have htrace : WordTrace (prefixWord ++ tailWord_3424272) baseStart_3424272 baseEnd_3424272 := by
    simpa [prefixWord, tailWord_3424272, baseEnd_3424272] using wordTrace_append hprefix tailTrace_3424272
  have hstable : (prefixWord ++ tailWord_3424272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424272).length < 2 ^ (prefixWord ++ tailWord_3424272).sum := by decide
  have hdescent : baseEnd_3424272 < baseStart_3424272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424287 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 4, 4]
def baseStart_3424287 : Nat := 118140960795 + 3424287 * 2 ^ 59
def prefixEnd_3424287 : Nat := 4983230072969 + 3 ^ 40 * 3424287 * 2
def baseEnd_3424287 : Nat := 1172203419961699463376331

theorem tailTrace_3424287 : CollatzResearch.WordTrace tailWord_3424287 prefixEnd_3424287 1172203419961699463376331 := by
  unfold tailWord_3424287
  simp only [CollatzResearch.WordTrace]
  refine ⟨124894007345400495504679115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83262671563600330336452743 124894007345400495504679115)
  ·
    refine ⟨187341011018100743257018673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124894007345400495504679115 187341011018100743257018673)
    ·
      refine ⟨140505758263575557442764005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187341011018100743257018673 140505758263575557442764005)
      ·
        refine ⟨26344829674420417020518251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140505758263575557442764005 26344829674420417020518251)
        ·
          refine ⟨39517244511630625530777377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26344829674420417020518251 39517244511630625530777377)
          ·
            refine ⟨29637933383722969148083033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39517244511630625530777377 29637933383722969148083033)
            ·
              refine ⟨22228450037792226861062275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29637933383722969148083033 22228450037792226861062275)
              ·
                refine ⟨33342675056688340291593413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22228450037792226861062275 33342675056688340291593413)
                ·
                  refine ⟨6251751573129063804673765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33342675056688340291593413 6251751573129063804673765)
                  ·
                    refine ⟨1172203419961699463376331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6251751573129063804673765 1172203419961699463376331)
                    ·
                      rfl

theorem cell22_3424287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 4].length) (baseStart_3424287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424287 prefixEnd_3424287 := by exact prefixLift 3424287
  have htrace : WordTrace (prefixWord ++ tailWord_3424287) baseStart_3424287 baseEnd_3424287 := by
    simpa [prefixWord, tailWord_3424287, baseEnd_3424287] using wordTrace_append hprefix tailTrace_3424287
  have hstable : (prefixWord ++ tailWord_3424287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424287).length < 2 ^ (prefixWord ++ tailWord_3424287).sum := by decide
  have hdescent : baseEnd_3424287 < baseStart_3424287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424317 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_3424317 : Nat := 118140960795 + 3424317 * 2 ^ 59
def prefixEnd_3424317 : Nat := 4983230072969 + 3 ^ 40 * 3424317 * 2
def baseEnd_3424317 : Nat := 1172213689574789385126239

theorem tailTrace_3424317 : CollatzResearch.WordTrace tailWord_3424317 prefixEnd_3424317 1172213689574789385126239 := by
  unfold tailWord_3424317
  simp only [CollatzResearch.WordTrace]
  refine ⟨124895101535291810628271205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83263401023527873752180803 124895101535291810628271205)
  ·
    refine ⟨23417831537867214492800851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124895101535291810628271205 23417831537867214492800851)
    ·
      refine ⟨35126747306800821739201277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23417831537867214492800851 35126747306800821739201277)
      ·
        refine ⟨13172530240050308152200479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35126747306800821739201277 13172530240050308152200479)
        ·
          refine ⟨19758795360075462228300719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13172530240050308152200479 19758795360075462228300719)
          ·
            refine ⟨29638193040113193342451079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19758795360075462228300719 29638193040113193342451079)
            ·
              refine ⟨44457289560169790013676619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29638193040113193342451079 44457289560169790013676619)
              ·
                refine ⟨66685934340254685020514929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44457289560169790013676619 66685934340254685020514929)
                ·
                  refine ⟨50014450755191013765386197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66685934340254685020514929 50014450755191013765386197)
                  ·
                    refine ⟨1172213689574789385126239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50014450755191013765386197 1172213689574789385126239)
                    ·
                      rfl

theorem cell22_3424317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_3424317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424317 prefixEnd_3424317 := by exact prefixLift 3424317
  have htrace : WordTrace (prefixWord ++ tailWord_3424317) baseStart_3424317 baseEnd_3424317 := by
    simpa [prefixWord, tailWord_3424317, baseEnd_3424317] using wordTrace_append hprefix tailTrace_3424317
  have hstable : (prefixWord ++ tailWord_3424317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424317).length < 2 ^ (prefixWord ++ tailWord_3424317).sum := by decide
  have hdescent : baseEnd_3424317 < baseStart_3424317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424364 : List Nat := [2, 2, 1, 1, 3, 4, 1, 3, 5]
def baseStart_3424364 : Nat := 118140960795 + 3424364 * 2 ^ 59
def prefixEnd_3424364 : Nat := 4983230072969 + 3 ^ 40 * 3424364 * 2
def baseEnd_3424364 : Nat := 390743259545098976400365

theorem tailTrace_3424364 : CollatzResearch.WordTrace tailWord_3424364 prefixEnd_3424364 390743259545098976400365 := by
  unfold tailWord_3424364
  simp only [CollatzResearch.WordTrace]
  refine ⟨62448407883060768827616073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83264543844081025103488097 62448407883060768827616073)
  ·
    refine ⟨46836305912295576620712055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62448407883060768827616073 46836305912295576620712055)
    ·
      refine ⟨70254458868443364931068083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46836305912295576620712055 70254458868443364931068083)
      ·
        refine ⟨105381688302665047396602125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70254458868443364931068083 105381688302665047396602125)
        ·
          refine ⟨39518133113499392773725797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105381688302665047396602125 39518133113499392773725797)
          ·
            refine ⟨7409649958781136145073587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39518133113499392773725797 7409649958781136145073587)
            ·
              refine ⟨11114474938171704217610381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7409649958781136145073587 11114474938171704217610381)
              ·
                refine ⟨4167928101814389081603893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11114474938171704217610381 4167928101814389081603893)
                ·
                  refine ⟨390743259545098976400365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4167928101814389081603893 390743259545098976400365)
                  ·
                    rfl

theorem cell22_3424364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_3424364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424364 prefixEnd_3424364 := by exact prefixLift 3424364
  have htrace : WordTrace (prefixWord ++ tailWord_3424364) baseStart_3424364 baseEnd_3424364 := by
    simpa [prefixWord, tailWord_3424364, baseEnd_3424364] using wordTrace_append hprefix tailTrace_3424364
  have hstable : (prefixWord ++ tailWord_3424364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424364).length < 2 ^ (prefixWord ++ tailWord_3424364).sum := by decide
  have hdescent : baseEnd_3424364 < baseStart_3424364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424439 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 1, 6]
def baseStart_3424439 : Nat := 118140960795 + 3424439 * 2 ^ 59
def prefixEnd_3424439 : Nat := 4983230072969 + 3 ^ 40 * 3424439 * 2
def baseEnd_3424439 : Nat := 1172255452668021733575865

theorem tailTrace_3424439 : CollatzResearch.WordTrace tailWord_3424439 prefixEnd_3424439 1172255452668021733575865 := by
  unfold tailWord_3424439
  simp only [CollatzResearch.WordTrace]
  refine ⟨124899551240849825464212371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83266367493899883642808247 124899551240849825464212371)
  ·
    refine ⟨187349326861274738196318557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124899551240849825464212371 187349326861274738196318557)
    ·
      refine ⟨70255997572978026823619459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187349326861274738196318557 70255997572978026823619459)
      ·
        refine ⟨105383996359467040235429189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70255997572978026823619459 105383996359467040235429189)
        ·
          refine ⟨19759499317400070044142973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105383996359467040235429189 19759499317400070044142973)
          ·
            refine ⟨7409812244025026266553615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19759499317400070044142973 7409812244025026266553615)
            ·
              refine ⟨11114718366037539399830423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7409812244025026266553615 11114718366037539399830423)
              ·
                refine ⟨16672077549056309099745635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11114718366037539399830423 16672077549056309099745635)
                ·
                  refine ⟨25008116323584463649618453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16672077549056309099745635 25008116323584463649618453)
                  ·
                    refine ⟨1172255452668021733575865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25008116323584463649618453 1172255452668021733575865)
                    ·
                      rfl

theorem cell22_3424439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_3424439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424439 prefixEnd_3424439 := by exact prefixLift 3424439
  have htrace : WordTrace (prefixWord ++ tailWord_3424439) baseStart_3424439 baseEnd_3424439 := by
    simpa [prefixWord, tailWord_3424439, baseEnd_3424439] using wordTrace_append hprefix tailTrace_3424439
  have hstable : (prefixWord ++ tailWord_3424439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424439).length < 2 ^ (prefixWord ++ tailWord_3424439).sum := by decide
  have hdescent : baseEnd_3424439 < baseStart_3424439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424559 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 3, 5]
def baseStart_3424559 : Nat := 118140960795 + 3424559 * 2 ^ 59
def prefixEnd_3424559 : Nat := 4983230072969 + 3 ^ 40 * 3424559 * 2
def baseEnd_3424559 : Nat := 1172296531120381420575497

theorem tailTrace_3424559 : CollatzResearch.WordTrace tailWord_3424559 prefixEnd_3424559 1172296531120381420575497 := by
  unfold tailWord_3424559
  simp only [CollatzResearch.WordTrace]
  refine ⟨124903928000415085958580731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83269285333610057305720487 124903928000415085958580731)
  ·
    refine ⟨187355892000622628937871097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124903928000415085958580731 187355892000622628937871097)
    ·
      refine ⟨140516919000466971703403323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187355892000622628937871097 140516919000466971703403323)
      ·
        refine ⟨210775378500700457555104985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140516919000466971703403323 210775378500700457555104985)
        ·
          refine ⟨158081533875525343166328739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210775378500700457555104985 158081533875525343166328739)
          ·
            refine ⟨237122300813288014749493109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158081533875525343166328739 237122300813288014749493109)
            ·
              refine ⟨22230215701245751382764979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 237122300813288014749493109 22230215701245751382764979)
              ·
                refine ⟨33345323551868627074147469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22230215701245751382764979 33345323551868627074147469)
                ·
                  refine ⟨12504496331950735152805301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33345323551868627074147469 12504496331950735152805301)
                  ·
                    refine ⟨1172296531120381420575497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12504496331950735152805301 1172296531120381420575497)
                    ·
                      rfl

theorem cell22_3424559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_3424559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424559 prefixEnd_3424559 := by exact prefixLift 3424559
  have htrace : WordTrace (prefixWord ++ tailWord_3424559) baseStart_3424559 baseEnd_3424559 := by
    simpa [prefixWord, tailWord_3424559, baseEnd_3424559] using wordTrace_append hprefix tailTrace_3424559
  have hstable : (prefixWord ++ tailWord_3424559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424559).length < 2 ^ (prefixWord ++ tailWord_3424559).sum := by decide
  have hdescent : baseEnd_3424559 < baseStart_3424559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424563 : List Nat := [1, 1, 1, 2, 5, 1, 5, 1, 1, 4]
def baseStart_3424563 : Nat := 118140960795 + 3424563 * 2 ^ 59
def prefixEnd_3424563 : Nat := 4983230072969 + 3 ^ 40 * 3424563 * 2
def baseEnd_3424563 : Nat := 1172297900402126743475485

theorem tailTrace_3424563 : CollatzResearch.WordTrace tailWord_3424563 prefixEnd_3424563 1172297900402126743475485 := by
  unfold tailWord_3424563
  simp only [CollatzResearch.WordTrace]
  refine ⟨124904073892400594641726343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83269382594933729761150895 124904073892400594641726343)
  ·
    refine ⟨187356110838600891962589515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124904073892400594641726343 187356110838600891962589515)
    ·
      refine ⟨281034166257901337943884273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187356110838600891962589515 281034166257901337943884273)
      ·
        refine ⟨210775624693426003457913205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281034166257901337943884273 210775624693426003457913205)
        ·
          refine ⟨19760214815008687824179363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 210775624693426003457913205 19760214815008687824179363)
          ·
            refine ⟨29640322222513031736269045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19760214815008687824179363 29640322222513031736269045)
            ·
              refine ⟨2778780208360596725275223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29640322222513031736269045 2778780208360596725275223)
              ·
                refine ⟨4168170312540895087912835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2778780208360596725275223 4168170312540895087912835)
                ·
                  refine ⟨6252255468811342631869253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4168170312540895087912835 6252255468811342631869253)
                  ·
                    refine ⟨1172297900402126743475485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6252255468811342631869253 1172297900402126743475485)
                    ·
                      rfl

theorem cell22_3424563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 1, 4].length) (baseStart_3424563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424563 prefixEnd_3424563 := by exact prefixLift 3424563
  have htrace : WordTrace (prefixWord ++ tailWord_3424563) baseStart_3424563 baseEnd_3424563 := by
    simpa [prefixWord, tailWord_3424563, baseEnd_3424563] using wordTrace_append hprefix tailTrace_3424563
  have hstable : (prefixWord ++ tailWord_3424563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424563).length < 2 ^ (prefixWord ++ tailWord_3424563).sum := by decide
  have hdescent : baseEnd_3424563 < baseStart_3424563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424593 : List Nat := [1, 2, 2, 1, 4, 2, 2, 3, 2, 3]
def baseStart_3424593 : Nat := 118140960795 + 3424593 * 2 ^ 59
def prefixEnd_3424593 : Nat := 4983230072969 + 3 ^ 40 * 3424593 * 2
def baseEnd_3424593 : Nat := 1172308170015216665225393

theorem tailTrace_3424593 : CollatzResearch.WordTrace tailWord_3424593 prefixEnd_3424593 1172308170015216665225393 := by
  unfold tailWord_3424593
  simp only [CollatzResearch.WordTrace]
  refine ⟨124905168082291909765318433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83270112054861273176878955 124905168082291909765318433)
  ·
    refine ⟨93678876061718932323988825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124905168082291909765318433 93678876061718932323988825)
    ·
      refine ⟨70259157046289199242991619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93678876061718932323988825 70259157046289199242991619)
      ·
        refine ⟨105388735569433798864487429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70259157046289199242991619 105388735569433798864487429)
        ·
          refine ⟨19760387919268837287091393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105388735569433798864487429 19760387919268837287091393)
          ·
            refine ⟨14820290939451627965318545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19760387919268837287091393 14820290939451627965318545)
            ·
              refine ⟨11115218204588720973988909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14820290939451627965318545 11115218204588720973988909)
              ·
                refine ⟨4168206826720770365245841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11115218204588720973988909 4168206826720770365245841)
                ·
                  refine ⟨3126155120040577773934381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4168206826720770365245841 3126155120040577773934381)
                  ·
                    refine ⟨1172308170015216665225393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3126155120040577773934381 1172308170015216665225393)
                    ·
                      rfl

theorem cell22_3424593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_3424593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424593 prefixEnd_3424593 := by exact prefixLift 3424593
  have htrace : WordTrace (prefixWord ++ tailWord_3424593) baseStart_3424593 baseEnd_3424593 := by
    simpa [prefixWord, tailWord_3424593, baseEnd_3424593] using wordTrace_append hprefix tailTrace_3424593
  have hstable : (prefixWord ++ tailWord_3424593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424593).length < 2 ^ (prefixWord ++ tailWord_3424593).sum := by decide
  have hdescent : baseEnd_3424593 < baseStart_3424593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424619 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 4, 6]
def baseStart_3424619 : Nat := 118140960795 + 3424619 * 2 ^ 59
def prefixEnd_3424619 : Nat := 4983230072969 + 3 ^ 40 * 3424619 * 2
def baseEnd_3424619 : Nat := 1172317070346561264075313

theorem tailTrace_3424619 : CollatzResearch.WordTrace tailWord_3424619 prefixEnd_3424619 1172317070346561264075313 := by
  unfold tailWord_3424619
  simp only [CollatzResearch.WordTrace]
  refine ⟨124906116380197716205764911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83270744253465144137176607 124906116380197716205764911)
  ·
    refine ⟨187359174570296574308647367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124906116380197716205764911 187359174570296574308647367)
    ·
      refine ⟨281038761855444861462971051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187359174570296574308647367 281038761855444861462971051)
      ·
        refine ⟨421558142783167292194456577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281038761855444861462971051 421558142783167292194456577)
        ·
          refine ⟨316168607087375469145842433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421558142783167292194456577 316168607087375469145842433)
          ·
            refine ⟨237126455315531601859381825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316168607087375469145842433 237126455315531601859381825)
            ·
              refine ⟨177844841486648701394536369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237126455315531601859381825 177844841486648701394536369)
              ·
                refine ⟨133383631114986526045902277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177844841486648701394536369 133383631114986526045902277)
                ·
                  refine ⟨25009430834059973633606677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133383631114986526045902277 25009430834059973633606677)
                  ·
                    refine ⟨1172317070346561264075313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25009430834059973633606677 1172317070346561264075313)
                    ·
                      rfl

theorem cell22_3424619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 6].length) (baseStart_3424619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424619 prefixEnd_3424619 := by exact prefixLift 3424619
  have htrace : WordTrace (prefixWord ++ tailWord_3424619) baseStart_3424619 baseEnd_3424619 := by
    simpa [prefixWord, tailWord_3424619, baseEnd_3424619] using wordTrace_append hprefix tailTrace_3424619
  have hstable : (prefixWord ++ tailWord_3424619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424619).length < 2 ^ (prefixWord ++ tailWord_3424619).sum := by decide
  have hdescent : baseEnd_3424619 < baseStart_3424619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424672 : List Nat := [2, 1, 1, 4, 1, 5, 1, 3, 1, 3]
def baseStart_3424672 : Nat := 118140960795 + 3424672 * 2 ^ 59
def prefixEnd_3424672 : Nat := 4983230072969 + 3 ^ 40 * 3424672 * 2
def baseEnd_3424672 : Nat := 1172335213329686792500151

theorem tailTrace_3424672 : CollatzResearch.WordTrace tailWord_3424672 prefixEnd_3424672 1172335213329686792500151 := by
  unfold tailWord_3424672
  simp only [CollatzResearch.WordTrace]
  refine ⟨62454024724502853128722135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83272032966003804171629513 62454024724502853128722135)
  ·
    refine ⟨93681037086754279693083203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62454024724502853128722135 93681037086754279693083203)
    ·
      refine ⟨140521555630131419539624805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93681037086754279693083203 140521555630131419539624805)
      ·
        refine ⟨26347791680649641163679651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140521555630131419539624805 26347791680649641163679651)
        ·
          refine ⟨39521687520974461745519477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26347791680649641163679651 39521687520974461745519477)
          ·
            refine ⟨3705158205091355788642451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39521687520974461745519477 3705158205091355788642451)
            ·
              refine ⟨5557737307637033682963677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3705158205091355788642451 5557737307637033682963677)
              ·
                refine ⟨2084151490363887631111379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5557737307637033682963677 2084151490363887631111379)
                ·
                  refine ⟨3126227235545831446667069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2084151490363887631111379 3126227235545831446667069)
                  ·
                    refine ⟨1172335213329686792500151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3126227235545831446667069 1172335213329686792500151)
                    ·
                      rfl

theorem cell22_3424672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 1, 3].length) (baseStart_3424672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424672 prefixEnd_3424672 := by exact prefixLift 3424672
  have htrace : WordTrace (prefixWord ++ tailWord_3424672) baseStart_3424672 baseEnd_3424672 := by
    simpa [prefixWord, tailWord_3424672, baseEnd_3424672] using wordTrace_append hprefix tailTrace_3424672
  have hstable : (prefixWord ++ tailWord_3424672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424672).length < 2 ^ (prefixWord ++ tailWord_3424672).sum := by decide
  have hdescent : baseEnd_3424672 < baseStart_3424672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424741 : List Nat := [1, 3, 1, 5, 12]
def baseStart_3424741 : Nat := 118140960795 + 3424741 * 2 ^ 59
def prefixEnd_3424741 : Nat := 4983230072969 + 3 ^ 40 * 3424741 * 2
def baseEnd_3424741 : Nat := 4824521948311907870473

theorem tailTrace_3424741 : CollatzResearch.WordTrace tailWord_3424741 prefixEnd_3424741 4824521948311907870473 := by
  unfold tailWord_3424741
  simp only [CollatzResearch.WordTrace]
  refine ⟨124910566085755731041706077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83273710723837154027804051 124910566085755731041706077)
  ·
    refine ⟨46841462282158399140639779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124910566085755731041706077 46841462282158399140639779)
    ·
      refine ⟨70262193423237598710959669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46841462282158399140639779 70262193423237598710959669)
      ·
        refine ⟨6587080633428524879152469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70262193423237598710959669 6587080633428524879152469)
        ·
          refine ⟨4824521948311907870473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6587080633428524879152469 4824521948311907870473)
          ·
            rfl

theorem cell22_3424741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 12].length) (baseStart_3424741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424741 prefixEnd_3424741 := by exact prefixLift 3424741
  have htrace : WordTrace (prefixWord ++ tailWord_3424741) baseStart_3424741 baseEnd_3424741 := by
    simpa [prefixWord, tailWord_3424741, baseEnd_3424741] using wordTrace_append hprefix tailTrace_3424741
  have hstable : (prefixWord ++ tailWord_3424741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424741).length < 2 ^ (prefixWord ++ tailWord_3424741).sum := by decide
  have hdescent : baseEnd_3424741 < baseStart_3424741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424743 : List Nat := [1, 1, 5, 2, 1, 1, 1, 4, 2, 4]
def baseStart_3424743 : Nat := 118140960795 + 3424743 * 2 ^ 59
def prefixEnd_3424743 : Nat := 4983230072969 + 3 ^ 40 * 3424743 * 2
def baseEnd_3424743 : Nat := 1172359518080666273974933

theorem tailTrace_3424743 : CollatzResearch.WordTrace tailWord_3424743 prefixEnd_3424743 1172359518080666273974933 := by
  unfold tailWord_3424743
  simp only [CollatzResearch.WordTrace]
  refine ⟨124910639031748485383278883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83273759354498990255519255 124910639031748485383278883)
  ·
    refine ⟨187365958547622728074918325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124910639031748485383278883 187365958547622728074918325)
    ·
      refine ⟨17565558613839630757023593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187365958547622728074918325 17565558613839630757023593)
      ·
        refine ⟨13174168960379723067767695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17565558613839630757023593 13174168960379723067767695)
        ·
          refine ⟨19761253440569584601651543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13174168960379723067767695 19761253440569584601651543)
          ·
            refine ⟨29641880160854376902477315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19761253440569584601651543 29641880160854376902477315)
            ·
              refine ⟨44462820241281565353715973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29641880160854376902477315 44462820241281565353715973)
              ·
                refine ⟨8336778795240293503821745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44462820241281565353715973 8336778795240293503821745)
                ·
                  refine ⟨6252584096430220127866309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8336778795240293503821745 6252584096430220127866309)
                  ·
                    refine ⟨1172359518080666273974933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6252584096430220127866309 1172359518080666273974933)
                    ·
                      rfl

theorem cell22_3424743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_3424743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424743 prefixEnd_3424743 := by exact prefixLift 3424743
  have htrace : WordTrace (prefixWord ++ tailWord_3424743) baseStart_3424743 baseEnd_3424743 := by
    simpa [prefixWord, tailWord_3424743, baseEnd_3424743] using wordTrace_append hprefix tailTrace_3424743
  have hstable : (prefixWord ++ tailWord_3424743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424743).length < 2 ^ (prefixWord ++ tailWord_3424743).sum := by decide
  have hdescent : baseEnd_3424743 < baseStart_3424743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424771 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 2, 6]
def baseStart_3424771 : Nat := 118140960795 + 3424771 * 2 ^ 59
def prefixEnd_3424771 : Nat := 4983230072969 + 3 ^ 40 * 3424771 * 2
def baseEnd_3424771 : Nat := 1172369103052883534274847

theorem tailTrace_3424771 : CollatzResearch.WordTrace tailWord_3424771 prefixEnd_3424771 1172369103052883534274847 := by
  unfold tailWord_3424771
  simp only [CollatzResearch.WordTrace]
  refine ⟨124911660275647046165298167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83274440183764697443532111 124911660275647046165298167)
  ·
    refine ⟨187367490413470569247947251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124911660275647046165298167 187367490413470569247947251)
    ·
      refine ⟨281051235620205853871920877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187367490413470569247947251 281051235620205853871920877)
      ·
        refine ⟨105394213357577195201970329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281051235620205853871920877 105394213357577195201970329)
        ·
          refine ⟨79045660018182896401477747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105394213357577195201970329 79045660018182896401477747)
          ·
            refine ⟨118568490027274344602216621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79045660018182896401477747 118568490027274344602216621)
            ·
              refine ⟨44463183760227879225831233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118568490027274344602216621 44463183760227879225831233)
              ·
                refine ⟨33347387820170909419373425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44463183760227879225831233 33347387820170909419373425)
                ·
                  refine ⟨25010540865128182064530069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33347387820170909419373425 25010540865128182064530069)
                  ·
                    refine ⟨1172369103052883534274847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25010540865128182064530069 1172369103052883534274847)
                    ·
                      rfl

theorem cell22_3424771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 6].length) (baseStart_3424771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424771 prefixEnd_3424771 := by exact prefixLift 3424771
  have htrace : WordTrace (prefixWord ++ tailWord_3424771) baseStart_3424771 baseEnd_3424771 := by
    simpa [prefixWord, tailWord_3424771, baseEnd_3424771] using wordTrace_append hprefix tailTrace_3424771
  have hstable : (prefixWord ++ tailWord_3424771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424771).length < 2 ^ (prefixWord ++ tailWord_3424771).sum := by decide
  have hdescent : baseEnd_3424771 < baseStart_3424771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424773 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 5, 3]
def baseStart_3424773 : Nat := 118140960795 + 3424773 * 2 ^ 59
def prefixEnd_3424773 : Nat := 4983230072969 + 3 ^ 40 * 3424773 * 2
def baseEnd_3424773 : Nat := 1172369787693756195724841

theorem tailTrace_3424773 : CollatzResearch.WordTrace tailWord_3424773 prefixEnd_3424773 1172369787693756195724841 := by
  unfold tailWord_3424773
  simp only [CollatzResearch.WordTrace]
  refine ⟨124911733221639800506870973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83274488814426533671247315 124911733221639800506870973)
  ·
    refine ⟨46841899958114925190076615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124911733221639800506870973 46841899958114925190076615)
    ·
      refine ⟨70262849937172387785114923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46841899958114925190076615 70262849937172387785114923)
      ·
        refine ⟨105394274905758581677672385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70262849937172387785114923 105394274905758581677672385)
        ·
          refine ⟨79045706179318936258254289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105394274905758581677672385 79045706179318936258254289)
          ·
            refine ⟨59284279634489202193690717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79045706179318936258254289 59284279634489202193690717)
            ·
              refine ⟨22231604862933450822634019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59284279634489202193690717 22231604862933450822634019)
              ·
                refine ⟨33347407294400176233951029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22231604862933450822634019 33347407294400176233951029)
                ·
                  refine ⟨3126319433850016521932909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33347407294400176233951029 3126319433850016521932909)
                  ·
                    refine ⟨1172369787693756195724841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3126319433850016521932909 1172369787693756195724841)
                    ·
                      rfl

theorem cell22_3424773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_3424773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424773 prefixEnd_3424773 := by exact prefixLift 3424773
  have htrace : WordTrace (prefixWord ++ tailWord_3424773) baseStart_3424773 baseEnd_3424773 := by
    simpa [prefixWord, tailWord_3424773, baseEnd_3424773] using wordTrace_append hprefix tailTrace_3424773
  have hstable : (prefixWord ++ tailWord_3424773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424773).length < 2 ^ (prefixWord ++ tailWord_3424773).sum := by decide
  have hdescent : baseEnd_3424773 < baseStart_3424773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424775 : List Nat := [1, 1, 4, 3, 3, 1, 3, 6]
def baseStart_3424775 : Nat := 118140960795 + 3424775 * 2 ^ 59
def prefixEnd_3424775 : Nat := 4983230072969 + 3 ^ 40 * 3424775 * 2
def baseEnd_3424775 : Nat := 130263385814958761908315

theorem tailTrace_3424775 : CollatzResearch.WordTrace tailWord_3424775 prefixEnd_3424775 130263385814958761908315 := by
  unfold tailWord_3424775
  simp only [CollatzResearch.WordTrace]
  refine ⟨124911806167632554848443779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83274537445088369898962519 124911806167632554848443779)
  ·
    refine ⟨187367709251448832272665669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124911806167632554848443779 187367709251448832272665669)
    ·
      refine ⟨35131445484646656051124813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187367709251448832272665669 35131445484646656051124813)
      ·
        refine ⟨13174292056742496019171805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35131445484646656051124813 13174292056742496019171805)
        ·
          refine ⟨4940359521278436007189427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13174292056742496019171805 4940359521278436007189427)
          ·
            refine ⟨7410539281917654010784141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4940359521278436007189427 7410539281917654010784141)
            ·
              refine ⟨2778952230719120254044053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7410539281917654010784141 2778952230719120254044053)
              ·
                refine ⟨130263385814958761908315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2778952230719120254044053 130263385814958761908315)
                ·
                  rfl

theorem cell22_3424775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 6].length) (baseStart_3424775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424775 prefixEnd_3424775 := by exact prefixLift 3424775
  have htrace : WordTrace (prefixWord ++ tailWord_3424775) baseStart_3424775 baseEnd_3424775 := by
    simpa [prefixWord, tailWord_3424775, baseEnd_3424775] using wordTrace_append hprefix tailTrace_3424775
  have hstable : (prefixWord ++ tailWord_3424775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424775).length < 2 ^ (prefixWord ++ tailWord_3424775).sum := by decide
  have hdescent : baseEnd_3424775 < baseStart_3424775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424803 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 7]
def baseStart_3424803 : Nat := 118140960795 + 3424803 * 2 ^ 59
def prefixEnd_3424803 : Nat := 4983230072969 + 3 ^ 40 * 3424803 * 2
def baseEnd_3424803 : Nat := 390793352435615372491583

theorem tailTrace_3424803 : CollatzResearch.WordTrace tailWord_3424803 prefixEnd_3424803 390793352435615372491583 := by
  unfold tailWord_3424803
  simp only [CollatzResearch.WordTrace]
  refine ⟨124912827411531115630463063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83275218274354077086975375 124912827411531115630463063)
  ·
    refine ⟨187369241117296673445694595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124912827411531115630463063 187369241117296673445694595)
    ·
      refine ⟨281053861675945010168541893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187369241117296673445694595 281053861675945010168541893)
      ·
        refine ⟨52697599064239689406601605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281053861675945010168541893 52697599064239689406601605)
        ·
          refine ⟨9880799824544941763737801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52697599064239689406601605 9880799824544941763737801)
          ·
            refine ⟨7410599868408706322803351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9880799824544941763737801 7410599868408706322803351)
            ·
              refine ⟨11115899802613059484205027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7410599868408706322803351 11115899802613059484205027)
              ·
                refine ⟨16673849703919589226307541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11115899802613059484205027 16673849703919589226307541)
                ·
                  refine ⟨390793352435615372491583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16673849703919589226307541 390793352435615372491583)
                  ·
                    rfl

theorem cell22_3424803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 7].length) (baseStart_3424803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424803 prefixEnd_3424803 := by exact prefixLift 3424803
  have htrace : WordTrace (prefixWord ++ tailWord_3424803) baseStart_3424803 baseEnd_3424803 := by
    simpa [prefixWord, tailWord_3424803, baseEnd_3424803] using wordTrace_append hprefix tailTrace_3424803
  have hstable : (prefixWord ++ tailWord_3424803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424803).length < 2 ^ (prefixWord ++ tailWord_3424803).sum := by decide
  have hdescent : baseEnd_3424803 < baseStart_3424803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424813 : List Nat := [1, 5, 4, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3424813 : Nat := 118140960795 + 3424813 * 2 ^ 59
def prefixEnd_3424813 : Nat := 4983230072969 + 3 ^ 40 * 3424813 * 2
def baseEnd_3424813 : Nat := 1172383480511209424724719

theorem tailTrace_3424813 : CollatzResearch.WordTrace tailWord_3424813 prefixEnd_3424813 1172383480511209424724719 := by
  unfold tailWord_3424813
  simp only [CollatzResearch.WordTrace]
  refine ⟨124913192141494887338327093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83275461427663258225551395 124913192141494887338327093)
  ·
    refine ⟨11710611763265145687968165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124913192141494887338327093 11710611763265145687968165)
    ·
      refine ⟨2195739705612214816494031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11710611763265145687968165 2195739705612214816494031)
      ·
        refine ⟨3293609558418322224741047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2195739705612214816494031 3293609558418322224741047)
        ·
          refine ⟨4940414337627483337111571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3293609558418322224741047 4940414337627483337111571)
          ·
            refine ⟨7410621506441225005667357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4940414337627483337111571 7410621506441225005667357)
            ·
              refine ⟨2778983064915459377125259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7410621506441225005667357 2778983064915459377125259)
              ·
                refine ⟨4168474597373189065687889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2778983064915459377125259 4168474597373189065687889)
                ·
                  refine ⟨3126355948029891799265917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4168474597373189065687889 3126355948029891799265917)
                  ·
                    refine ⟨1172383480511209424724719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3126355948029891799265917 1172383480511209424724719)
                    ·
                      rfl

theorem cell22_3424813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3424813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424813 prefixEnd_3424813 := by exact prefixLift 3424813
  have htrace : WordTrace (prefixWord ++ tailWord_3424813) baseStart_3424813 baseEnd_3424813 := by
    simpa [prefixWord, tailWord_3424813, baseEnd_3424813] using wordTrace_append hprefix tailTrace_3424813
  have hstable : (prefixWord ++ tailWord_3424813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424813).length < 2 ^ (prefixWord ++ tailWord_3424813).sum := by decide
  have hdescent : baseEnd_3424813 < baseStart_3424813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424818 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_3424818 : Nat := 118140960795 + 3424818 * 2 ^ 59
def prefixEnd_3424818 : Nat := 4983230072969 + 3 ^ 40 * 3424818 * 2
def baseEnd_3424818 : Nat := 1172385192113391078349703

theorem tailTrace_3424818 : CollatzResearch.WordTrace tailWord_3424818 prefixEnd_3424818 1172385192113391078349703 := by
  unfold tailWord_3424818
  simp only [CollatzResearch.WordTrace]
  refine ⟨31228343626619193298064777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83275583004317848794839405 31228343626619193298064777)
  ·
    refine ⟨23421257719964394973548583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31228343626619193298064777 23421257719964394973548583)
    ·
      refine ⟨35131886579946592460322875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23421257719964394973548583 35131886579946592460322875)
      ·
        refine ⟨52697829869919888690484313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35131886579946592460322875 52697829869919888690484313)
        ·
          refine ⟨39523372402439916517863235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52697829869919888690484313 39523372402439916517863235)
          ·
            refine ⟨59285058603659874776794853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39523372402439916517863235 59285058603659874776794853)
            ·
              refine ⟨11115948488186226520649035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59285058603659874776794853 11115948488186226520649035)
              ·
                refine ⟨16673922732279339780973553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11115948488186226520649035 16673922732279339780973553)
                ·
                  refine ⟨12505442049209504835730165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16673922732279339780973553 12505442049209504835730165)
                  ·
                    refine ⟨1172385192113391078349703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12505442049209504835730165 1172385192113391078349703)
                    ·
                      rfl

theorem cell22_3424818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_3424818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424818 prefixEnd_3424818 := by exact prefixLift 3424818
  have htrace : WordTrace (prefixWord ++ tailWord_3424818) baseStart_3424818 baseEnd_3424818 := by
    simpa [prefixWord, tailWord_3424818, baseEnd_3424818] using wordTrace_append hprefix tailTrace_3424818
  have hstable : (prefixWord ++ tailWord_3424818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424818).length < 2 ^ (prefixWord ++ tailWord_3424818).sum := by decide
  have hdescent : baseEnd_3424818 < baseStart_3424818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424850 : List Nat := [3, 2, 2, 1, 2, 1, 1, 5, 1, 4]
def baseStart_3424850 : Nat := 118140960795 + 3424850 * 2 ^ 59
def prefixEnd_3424850 : Nat := 4983230072969 + 3 ^ 40 * 3424850 * 2
def baseEnd_3424850 : Nat := 1172396146367353661549605

theorem tailTrace_3424850 : CollatzResearch.WordTrace tailWord_3424850 prefixEnd_3424850 1172396146367353661549605 := by
  unfold tailWord_3424850
  simp only [CollatzResearch.WordTrace]
  refine ⟨31228635410590210664356001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83276361094907228438282669 31228635410590210664356001)
  ·
    refine ⟨23421476557942657998267001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31228635410590210664356001 23421476557942657998267001)
    ·
      refine ⟨17566107418456993498700251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23421476557942657998267001 17566107418456993498700251)
      ·
        refine ⟨26349161127685490248050377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17566107418456993498700251 26349161127685490248050377)
        ·
          refine ⟨19761870845764117686037783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26349161127685490248050377 19761870845764117686037783)
          ·
            refine ⟨29642806268646176529056675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19761870845764117686037783 29642806268646176529056675)
            ·
              refine ⟨44464209402969264793585013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29642806268646176529056675 44464209402969264793585013)
              ·
                refine ⟨4168519631528368574398595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44464209402969264793585013 4168519631528368574398595)
                ·
                  refine ⟨6252779447292552861597893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4168519631528368574398595 6252779447292552861597893)
                  ·
                    refine ⟨1172396146367353661549605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6252779447292552861597893 1172396146367353661549605)
                    ·
                      rfl

theorem cell22_3424850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_3424850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424850 prefixEnd_3424850 := by exact prefixLift 3424850
  have htrace : WordTrace (prefixWord ++ tailWord_3424850) baseStart_3424850 baseEnd_3424850 := by
    simpa [prefixWord, tailWord_3424850, baseEnd_3424850] using wordTrace_append hprefix tailTrace_3424850
  have hstable : (prefixWord ++ tailWord_3424850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424850).length < 2 ^ (prefixWord ++ tailWord_3424850).sum := by decide
  have hdescent : baseEnd_3424850 < baseStart_3424850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424865 : List Nat := [1, 2, 3, 1, 1, 6, 1, 1, 6]
def baseStart_3424865 : Nat := 118140960795 + 3424865 * 2 ^ 59
def prefixEnd_3424865 : Nat := 4983230072969 + 3 ^ 40 * 3424865 * 2
def baseEnd_3424865 : Nat := 390800427057966207474853

theorem tailTrace_3424865 : CollatzResearch.WordTrace tailWord_3424865 prefixEnd_3424865 390800427057966207474853 := by
  unfold tailWord_3424865
  simp only [CollatzResearch.WordTrace]
  refine ⟨124915088737306500219220049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83276725824871000146146699 124915088737306500219220049)
  ·
    refine ⟨93686316552979875164415037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124915088737306500219220049 93686316552979875164415037)
    ·
      refine ⟨35132368707367453186655639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93686316552979875164415037 35132368707367453186655639)
      ·
        refine ⟨52698553061051179779983459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35132368707367453186655639 52698553061051179779983459)
        ·
          refine ⟨79047829591576769669975189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52698553061051179779983459 79047829591576769669975189)
          ·
            refine ⟨3705367012105161078280087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 79047829591576769669975189 3705367012105161078280087)
            ·
              refine ⟨5558050518157741617420131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3705367012105161078280087 5558050518157741617420131)
              ·
                refine ⟨8337075777236612426130197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5558050518157741617420131 8337075777236612426130197)
                ·
                  refine ⟨390800427057966207474853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8337075777236612426130197 390800427057966207474853)
                  ·
                    rfl

theorem cell22_3424865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 6].length) (baseStart_3424865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424865 prefixEnd_3424865 := by exact prefixLift 3424865
  have htrace : WordTrace (prefixWord ++ tailWord_3424865) baseStart_3424865 baseEnd_3424865 := by
    simpa [prefixWord, tailWord_3424865, baseEnd_3424865] using wordTrace_append hprefix tailTrace_3424865
  have hstable : (prefixWord ++ tailWord_3424865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424865).length < 2 ^ (prefixWord ++ tailWord_3424865).sum := by decide
  have hdescent : baseEnd_3424865 < baseStart_3424865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424914 : List Nat := [3, 2, 3, 1, 2, 2, 2, 2, 2, 3]
def baseStart_3424914 : Nat := 118140960795 + 3424914 * 2 ^ 59
def prefixEnd_3424914 : Nat := 4983230072969 + 3 ^ 40 * 3424914 * 2
def baseEnd_3424914 : Nat := 1172418054875278827949409

theorem tailTrace_3424914 : CollatzResearch.WordTrace tailWord_3424914 prefixEnd_3424914 1172418054875278827949409 := by
  unfold tailWord_3424914
  simp only [CollatzResearch.WordTrace]
  refine ⟨31229218978532245396938449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83277917276085987725169197 31229218978532245396938449)
  ·
    refine ⟨23421914233899184047703837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31229218978532245396938449 23421914233899184047703837)
    ·
      refine ⟨8783217837712194017888939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23421914233899184047703837 8783217837712194017888939)
      ·
        refine ⟨13174826756568291026833409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8783217837712194017888939 13174826756568291026833409)
        ·
          refine ⟨9881120067426218270125057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13174826756568291026833409 9881120067426218270125057)
          ·
            refine ⟨7410840050569663702593793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9881120067426218270125057 7410840050569663702593793)
            ·
              refine ⟨5558130037927247776945345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7410840050569663702593793 5558130037927247776945345)
              ·
                refine ⟨4168597528445435832709009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5558130037927247776945345 4168597528445435832709009)
                ·
                  refine ⟨3126448146334076874531757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4168597528445435832709009 3126448146334076874531757)
                  ·
                    refine ⟨1172418054875278827949409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3126448146334076874531757 1172418054875278827949409)
                    ·
                      rfl

theorem cell22_3424914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_3424914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424914 prefixEnd_3424914 := by exact prefixLift 3424914
  have htrace : WordTrace (prefixWord ++ tailWord_3424914) baseStart_3424914 baseEnd_3424914 := by
    simpa [prefixWord, tailWord_3424914, baseEnd_3424914] using wordTrace_append hprefix tailTrace_3424914
  have hstable : (prefixWord ++ tailWord_3424914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424914).length < 2 ^ (prefixWord ++ tailWord_3424914).sum := by decide
  have hdescent : baseEnd_3424914 < baseStart_3424914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424916 : List Nat := [2, 4, 2, 2, 1, 3, 2, 2, 4]
def baseStart_3424916 : Nat := 118140960795 + 3424916 * 2 ^ 59
def prefixEnd_3424916 : Nat := 4983230072969 + 3 ^ 40 * 3424916 * 2
def baseEnd_3424916 : Nat := 390806246505383829799801

theorem tailTrace_3424916 : CollatzResearch.WordTrace tailWord_3424916 prefixEnd_3424916 390806246505383829799801 := by
  unfold tailWord_3424916
  simp only [CollatzResearch.WordTrace]
  refine ⟨62458474430060867964663301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83277965906747823952884401 62458474430060867964663301)
  ·
    refine ⟨11710963955636412743374369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62458474430060867964663301 11710963955636412743374369)
    ·
      refine ⟨8783222966727309557530777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11710963955636412743374369 8783222966727309557530777)
      ·
        refine ⟨6587417225045482168148083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8783222966727309557530777 6587417225045482168148083)
        ·
          refine ⟨9881125837568223252222125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6587417225045482168148083 9881125837568223252222125)
          ·
            refine ⟨3705422189088083719583297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9881125837568223252222125 3705422189088083719583297)
            ·
              refine ⟨2779066641816062789687473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3705422189088083719583297 2779066641816062789687473)
              ·
                refine ⟨2084299981362047092265605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2779066641816062789687473 2084299981362047092265605)
                ·
                  refine ⟨390806246505383829799801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2084299981362047092265605 390806246505383829799801)
                  ·
                    rfl

theorem cell22_3424916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_3424916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424916 prefixEnd_3424916 := by exact prefixLift 3424916
  have htrace : WordTrace (prefixWord ++ tailWord_3424916) baseStart_3424916 baseEnd_3424916 := by
    simpa [prefixWord, tailWord_3424916, baseEnd_3424916] using wordTrace_append hprefix tailTrace_3424916
  have hstable : (prefixWord ++ tailWord_3424916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424916).length < 2 ^ (prefixWord ++ tailWord_3424916).sum := by decide
  have hdescent : baseEnd_3424916 < baseStart_3424916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424953 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 3, 7]
def baseStart_3424953 : Nat := 118140960795 + 3424953 * 2 ^ 59
def prefixEnd_3424953 : Nat := 4983230072969 + 3 ^ 40 * 3424953 * 2
def baseEnd_3424953 : Nat := 1172431405372295726224289

theorem tailTrace_3424953 : CollatzResearch.WordTrace tailWord_3424953 prefixEnd_3424953 1172431405372295726224289 := by
  unfold tailWord_3424953
  simp only [CollatzResearch.WordTrace]
  refine ⟨124918298360987691248423513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83278865573991794165615675 124918298360987691248423513)
  ·
    refine ⟨93688723770740768436317635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124918298360987691248423513 93688723770740768436317635)
    ·
      refine ⟨140533085656111152654476453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93688723770740768436317635 140533085656111152654476453)
      ·
        refine ⟨26349953560520841122714335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140533085656111152654476453 26349953560520841122714335)
        ·
          refine ⟨39524930340781261684071503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26349953560520841122714335 39524930340781261684071503)
          ·
            refine ⟨59287395511171892526107255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39524930340781261684071503 59287395511171892526107255)
            ·
              refine ⟨88931093266757838789160883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59287395511171892526107255 88931093266757838789160883)
              ·
                refine ⟨133396639900136758183741325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88931093266757838789160883 133396639900136758183741325)
                ·
                  refine ⟨50023739962551284318902997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133396639900136758183741325 50023739962551284318902997)
                  ·
                    refine ⟨1172431405372295726224289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50023739962551284318902997 1172431405372295726224289)
                    ·
                      rfl

theorem cell22_3424953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_3424953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424953 prefixEnd_3424953 := by exact prefixLift 3424953
  have htrace : WordTrace (prefixWord ++ tailWord_3424953) baseStart_3424953 baseEnd_3424953 := by
    simpa [prefixWord, tailWord_3424953, baseEnd_3424953] using wordTrace_append hprefix tailTrace_3424953
  have hstable : (prefixWord ++ tailWord_3424953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424953).length < 2 ^ (prefixWord ++ tailWord_3424953).sum := by decide
  have hdescent : baseEnd_3424953 < baseStart_3424953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424959 : List Nat := [1, 1, 2, 2, 2, 5, 2, 3, 1, 3]
def baseStart_3424959 : Nat := 118140960795 + 3424959 * 2 ^ 59
def prefixEnd_3424959 : Nat := 4983230072969 + 3 ^ 40 * 3424959 * 2
def baseEnd_3424959 : Nat := 1172433459294913710574271

theorem tailTrace_3424959 : CollatzResearch.WordTrace tailWord_3424959 prefixEnd_3424959 1172433459294913710574271 := by
  unfold tailWord_3424959
  simp only [CollatzResearch.WordTrace]
  refine ⟨124918517198965954273141931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83279011465977302848761287 124918517198965954273141931)
  ·
    refine ⟨187377775798448931409712897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124918517198965954273141931 187377775798448931409712897)
    ·
      refine ⟨140533331848836698557284673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187377775798448931409712897 140533331848836698557284673)
      ·
        refine ⟨105399998886627523917963505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140533331848836698557284673 105399998886627523917963505)
        ·
          refine ⟨79049999164970642938472629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105399998886627523917963505 79049999164970642938472629)
          ·
            refine ⟨7410937421715997775481809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79049999164970642938472629 7410937421715997775481809)
            ·
              refine ⟨5558203066286998331611357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7410937421715997775481809 5558203066286998331611357)
              ·
                refine ⟨2084326149857624374354259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5558203066286998331611357 2084326149857624374354259)
                ·
                  refine ⟨3126489224786436561531389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2084326149857624374354259 3126489224786436561531389)
                  ·
                    refine ⟨1172433459294913710574271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3126489224786436561531389 1172433459294913710574271)
                    ·
                      rfl

theorem cell22_3424959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 1, 3].length) (baseStart_3424959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424959 prefixEnd_3424959 := by exact prefixLift 3424959
  have htrace : WordTrace (prefixWord ++ tailWord_3424959) baseStart_3424959 baseEnd_3424959 := by
    simpa [prefixWord, tailWord_3424959, baseEnd_3424959] using wordTrace_append hprefix tailTrace_3424959
  have hstable : (prefixWord ++ tailWord_3424959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424959).length < 2 ^ (prefixWord ++ tailWord_3424959).sum := by decide
  have hdescent : baseEnd_3424959 < baseStart_3424959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424970 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 2, 5]
def baseStart_3424970 : Nat := 118140960795 + 3424970 * 2 ^ 59
def prefixEnd_3424970 : Nat := 4983230072969 + 3 ^ 40 * 3424970 * 2
def baseEnd_3424970 : Nat := 1172437224819713348549237

theorem tailTrace_3424970 : CollatzResearch.WordTrace tailWord_3424970 prefixEnd_3424970 1172437224819713348549237 := by
  unfold tailWord_3424970
  simp only [CollatzResearch.WordTrace]
  refine ⟨31229729600481525787948091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83279278934617402101194909 31229729600481525787948091)
  ·
    refine ⟨46844594400722288681922137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31229729600481525787948091 46844594400722288681922137)
    ·
      refine ⟨35133445800541716511441603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46844594400722288681922137 35133445800541716511441603)
      ·
        refine ⟨52700168700812574767162405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35133445800541716511441603 52700168700812574767162405)
        ·
          refine ⟨9881281631402357768842951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52700168700812574767162405 9881281631402357768842951)
          ·
            refine ⟨14821922447103536653264427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9881281631402357768842951 14821922447103536653264427)
            ·
              refine ⟨22232883670655304979896641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14821922447103536653264427 22232883670655304979896641)
              ·
                refine ⟨16674662752991478734922481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22232883670655304979896641 16674662752991478734922481)
                ·
                  refine ⟨12505997064743609051191861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16674662752991478734922481 12505997064743609051191861)
                  ·
                    refine ⟨1172437224819713348549237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12505997064743609051191861 1172437224819713348549237)
                    ·
                      rfl

theorem cell22_3424970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_3424970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424970 prefixEnd_3424970 := by exact prefixLift 3424970
  have htrace : WordTrace (prefixWord ++ tailWord_3424970) baseStart_3424970 baseEnd_3424970 := by
    simpa [prefixWord, tailWord_3424970, baseEnd_3424970] using wordTrace_append hprefix tailTrace_3424970
  have hstable : (prefixWord ++ tailWord_3424970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424970).length < 2 ^ (prefixWord ++ tailWord_3424970).sum := by decide
  have hdescent : baseEnd_3424970 < baseStart_3424970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424972 : List Nat := [2, 2, 1, 5, 1, 1, 3, 2, 5]
def baseStart_3424972 : Nat := 118140960795 + 3424972 * 2 ^ 59
def prefixEnd_3424972 : Nat := 4983230072969 + 3 ^ 40 * 3424972 * 2
def baseEnd_3424972 : Nat := 390812636486862003333077

theorem tailTrace_3424972 : CollatzResearch.WordTrace tailWord_3424972 prefixEnd_3424972 390812636486862003333077 := by
  unfold tailWord_3424972
  simp only [CollatzResearch.WordTrace]
  refine ⟨62459495673959428746682585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83279327565279238328910113 62459495673959428746682585)
  ·
    refine ⟨46844621755469571560011939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62459495673959428746682585 46844621755469571560011939)
    ·
      refine ⟨70266932633204357340017909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46844621755469571560011939 70266932633204357340017909)
      ·
        refine ⟨6587524934362908500626679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70266932633204357340017909 6587524934362908500626679)
        ·
          refine ⟨9881287401544362750940019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6587524934362908500626679 9881287401544362750940019)
          ·
            refine ⟨14821931102316544126410029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9881287401544362750940019 14821931102316544126410029)
            ·
              refine ⟨5558224163368704047403761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14821931102316544126410029 5558224163368704047403761)
              ·
                refine ⟨4168668122526528035552821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5558224163368704047403761 4168668122526528035552821)
                ·
                  refine ⟨390812636486862003333077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4168668122526528035552821 390812636486862003333077)
                  ·
                    rfl

theorem cell22_3424972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_3424972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3424972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3424972 prefixEnd_3424972 := by exact prefixLift 3424972
  have htrace : WordTrace (prefixWord ++ tailWord_3424972) baseStart_3424972 baseEnd_3424972 := by
    simpa [prefixWord, tailWord_3424972, baseEnd_3424972] using wordTrace_append hprefix tailTrace_3424972
  have hstable : (prefixWord ++ tailWord_3424972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424972).length < 2 ^ (prefixWord ++ tailWord_3424972).sum := by decide
  have hdescent : baseEnd_3424972 < baseStart_3424972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425032 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 4, 3]
def baseStart_3425032 : Nat := 118140960795 + 3425032 * 2 ^ 59
def prefixEnd_3425032 : Nat := 4983230072969 + 3 ^ 40 * 3425032 * 2
def baseEnd_3425032 : Nat := 1172458448686765853499047

theorem tailTrace_3425032 : CollatzResearch.WordTrace tailWord_3425032 prefixEnd_3425032 1172458448686765853499047 := by
  unfold tailWord_3425032
  simp only [CollatzResearch.WordTrace]
  refine ⟨62460589863850743870274675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83280786485134325160366233 62460589863850743870274675)
  ·
    refine ⟨93690884795776115805412013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62460589863850743870274675 93690884795776115805412013)
    ·
      refine ⟨35134081798416043427029505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93690884795776115805412013 35134081798416043427029505)
      ·
        refine ⟨26350561348812032570272129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35134081798416043427029505 26350561348812032570272129)
        ·
          refine ⟨19762921011609024427704097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26350561348812032570272129 19762921011609024427704097)
          ·
            refine ⟨14822190758706768320778073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19762921011609024427704097 14822190758706768320778073)
            ·
              refine ⟨11116643069030076240583555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14822190758706768320778073 11116643069030076240583555)
              ·
                refine ⟨16674964603545114360875333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11116643069030076240583555 16674964603545114360875333)
                ·
                  refine ⟨3126555863164708942664125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16674964603545114360875333 3126555863164708942664125)
                  ·
                    refine ⟨1172458448686765853499047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3126555863164708942664125 1172458448686765853499047)
                    ·
                      rfl

theorem cell22_3425032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_3425032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425032 prefixEnd_3425032 := by exact prefixLift 3425032
  have htrace : WordTrace (prefixWord ++ tailWord_3425032) baseStart_3425032 baseEnd_3425032 := by
    simpa [prefixWord, tailWord_3425032, baseEnd_3425032] using wordTrace_append hprefix tailTrace_3425032
  have hstable : (prefixWord ++ tailWord_3425032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425032).length < 2 ^ (prefixWord ++ tailWord_3425032).sum := by decide
  have hdescent : baseEnd_3425032 < baseStart_3425032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425034 : List Nat := [3, 1, 2, 2, 1, 2, 5, 2, 4]
def baseStart_3425034 : Nat := 118140960795 + 3425034 * 2 ^ 59
def prefixEnd_3425034 : Nat := 4983230072969 + 3 ^ 40 * 3425034 * 2
def baseEnd_3425034 : Nat := 390819711109212838316347

theorem tailTrace_3425034 : CollatzResearch.WordTrace tailWord_3425034 prefixEnd_3425034 390819711109212838316347 := by
  unfold tailWord_3425034
  simp only [CollatzResearch.WordTrace]
  refine ⟨31230313168423560520530539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83280835115796161388081437 31230313168423560520530539)
  ·
    refine ⟨46845469752635340780795809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31230313168423560520530539 46845469752635340780795809)
    ·
      refine ⟨35134102314476505585596857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46845469752635340780795809 35134102314476505585596857)
      ·
        refine ⟨26350576735857379189197643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35134102314476505585596857 26350576735857379189197643)
        ·
          refine ⟨39525865103786068783796465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26350576735857379189197643 39525865103786068783796465)
          ·
            refine ⟨29644398827839551587847349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39525865103786068783796465 29644398827839551587847349)
            ·
              refine ⟨2779162390109957961360689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29644398827839551587847349 2779162390109957961360689)
              ·
                refine ⟨2084371792582468471020517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2779162390109957961360689 2084371792582468471020517)
                ·
                  refine ⟨390819711109212838316347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2084371792582468471020517 390819711109212838316347)
                  ·
                    rfl

theorem cell22_3425034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 4].length) (baseStart_3425034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425034 prefixEnd_3425034 := by exact prefixLift 3425034
  have htrace : WordTrace (prefixWord ++ tailWord_3425034) baseStart_3425034 baseEnd_3425034 := by
    simpa [prefixWord, tailWord_3425034, baseEnd_3425034] using wordTrace_append hprefix tailTrace_3425034
  have hstable : (prefixWord ++ tailWord_3425034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425034).length < 2 ^ (prefixWord ++ tailWord_3425034).sum := by decide
  have hdescent : baseEnd_3425034 < baseStart_3425034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425045 : List Nat := [1, 3, 2, 1, 2, 2, 4, 7]
def baseStart_3425045 : Nat := 118140960795 + 3425045 * 2 ^ 59
def prefixEnd_3425045 : Nat := 4983230072969 + 3 ^ 40 * 3425045 * 2
def baseEnd_3425045 : Nat := 130273655428048683658223

theorem tailTrace_3425045 : CollatzResearch.WordTrace tailWord_3425045 prefixEnd_3425045 130273655428048683658223 := by
  unfold tailWord_3425045
  simp only [CollatzResearch.WordTrace]
  refine ⟨124921653876654390960772589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83281102584436260640515059 124921653876654390960772589)
  ·
    refine ⟨46845620203745396610289721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124921653876654390960772589 46845620203745396610289721)
    ·
      refine ⟨35134215152809047457717291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46845620203745396610289721 35134215152809047457717291)
      ·
        refine ⟨52701322729213571186575937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35134215152809047457717291 52701322729213571186575937)
        ·
          refine ⟨39525992046910178389931953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52701322729213571186575937 39525992046910178389931953)
          ·
            refine ⟨29644494035182633792448965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39525992046910178389931953 29644494035182633792448965)
            ·
              refine ⟨5558342631596743836084181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29644494035182633792448965 5558342631596743836084181)
              ·
                refine ⟨130273655428048683658223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5558342631596743836084181 130273655428048683658223)
                ·
                  rfl

theorem cell22_3425045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 7].length) (baseStart_3425045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425045 prefixEnd_3425045 := by exact prefixLift 3425045
  have htrace : WordTrace (prefixWord ++ tailWord_3425045) baseStart_3425045 baseEnd_3425045 := by
    simpa [prefixWord, tailWord_3425045, baseEnd_3425045] using wordTrace_append hprefix tailTrace_3425045
  have hstable : (prefixWord ++ tailWord_3425045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425045).length < 2 ^ (prefixWord ++ tailWord_3425045).sum := by decide
  have hdescent : baseEnd_3425045 < baseStart_3425045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425053 : List Nat := [1, 4, 2, 4, 2, 1, 1, 2, 1, 4]
def baseStart_3425053 : Nat := 118140960795 + 3425053 * 2 ^ 59
def prefixEnd_3425053 : Nat := 4983230072969 + 3 ^ 40 * 3425053 * 2
def baseEnd_3425053 : Nat := 1172465637415928798723983

theorem tailTrace_3425053 : CollatzResearch.WordTrace tailWord_3425053 prefixEnd_3425053 1172465637415928798723983 := by
  unfold tailWord_3425053
  simp only [CollatzResearch.WordTrace]
  refine ⟨124921945660625408327063813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83281297107083605551375875 124921945660625408327063813)
  ·
    refine ⟨23422864811367264061324465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124921945660625408327063813 23422864811367264061324465)
    ·
      refine ⟨17567148608525448045993349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23422864811367264061324465 17567148608525448045993349)
      ·
        refine ⟨3293840364098521508623753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17567148608525448045993349 3293840364098521508623753)
        ·
          refine ⟨2470380273073891131467815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3293840364098521508623753 2470380273073891131467815)
          ·
            refine ⟨3705570409610836697201723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2470380273073891131467815 3705570409610836697201723)
            ·
              refine ⟨5558355614416255045802585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3705570409610836697201723 5558355614416255045802585)
              ·
                refine ⟨4168766710812191284351939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5558355614416255045802585 4168766710812191284351939)
                ·
                  refine ⟨6253150066218286926527909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4168766710812191284351939 6253150066218286926527909)
                  ·
                    refine ⟨1172465637415928798723983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6253150066218286926527909 1172465637415928798723983)
                    ·
                      rfl

theorem cell22_3425053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_3425053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425053 prefixEnd_3425053 := by exact prefixLift 3425053
  have htrace : WordTrace (prefixWord ++ tailWord_3425053) baseStart_3425053 baseEnd_3425053 := by
    simpa [prefixWord, tailWord_3425053, baseEnd_3425053] using wordTrace_append hprefix tailTrace_3425053
  have hstable : (prefixWord ++ tailWord_3425053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425053).length < 2 ^ (prefixWord ++ tailWord_3425053).sum := by decide
  have hdescent : baseEnd_3425053 < baseStart_3425053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425186 : List Nat := [3, 3, 1, 2, 2, 1, 3, 3, 4]
def baseStart_3425186 : Nat := 118140960795 + 3425186 * 2 ^ 59
def prefixEnd_3425186 : Nat := 4983230072969 + 3 ^ 40 * 3425186 * 2
def baseEnd_3425186 : Nat := 390837055344653595049525

theorem tailTrace_3425186 : CollatzResearch.WordTrace tailWord_3425186 prefixEnd_3425186 390837055344653595049525 := by
  unfold tailWord_3425186
  simp only [CollatzResearch.WordTrace]
  refine ⟨31231699142285893010413853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83284531046095714694436941 31231699142285893010413853)
  ·
    refine ⟨11711887178357209878905195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31231699142285893010413853 11711887178357209878905195)
    ·
      refine ⟨17567830767535814818357793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11711887178357209878905195 17567830767535814818357793)
      ·
        refine ⟨13175873075651861113768345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17567830767535814818357793 13175873075651861113768345)
        ·
          refine ⟨9881904806738895835326259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13175873075651861113768345 9881904806738895835326259)
          ·
            refine ⟨14822857210108343752989389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9881904806738895835326259 14822857210108343752989389)
            ·
              refine ⟨5558571453790628907371021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14822857210108343752989389 5558571453790628907371021)
              ·
                refine ⟨2084464295171485840264133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5558571453790628907371021 2084464295171485840264133)
                ·
                  refine ⟨390837055344653595049525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2084464295171485840264133 390837055344653595049525)
                  ·
                    rfl

theorem cell22_3425186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_3425186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425186 prefixEnd_3425186 := by exact prefixLift 3425186
  have htrace : WordTrace (prefixWord ++ tailWord_3425186) baseStart_3425186 baseEnd_3425186 := by
    simpa [prefixWord, tailWord_3425186, baseEnd_3425186] using wordTrace_append hprefix tailTrace_3425186
  have hstable : (prefixWord ++ tailWord_3425186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425186).length < 2 ^ (prefixWord ++ tailWord_3425186).sum := by decide
  have hdescent : baseEnd_3425186 < baseStart_3425186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425195 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 1, 9]
def baseStart_3425195 : Nat := 118140960795 + 3425195 * 2 ^ 59
def prefixEnd_3425195 : Nat := 4983230072969 + 3 ^ 40 * 3425195 * 2
def baseEnd_3425195 : Nat := 1172514246917887761673547

theorem tailTrace_3425195 : CollatzResearch.WordTrace tailWord_3425195 prefixEnd_3425195 1172514246917887761673547 := by
  unfold tailWord_3425195
  simp only [CollatzResearch.WordTrace]
  refine ⟨124927124826110966578733039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83284749884073977719155359 124927124826110966578733039)
  ·
    refine ⟨187390687239166449868099559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124927124826110966578733039 187390687239166449868099559)
    ·
      refine ⟨281086030858749674802149339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187390687239166449868099559 281086030858749674802149339)
      ·
        refine ⟨421629046288124512203224009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281086030858749674802149339 421629046288124512203224009)
        ·
          refine ⟨316221784716093384152418007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421629046288124512203224009 316221784716093384152418007)
          ·
            refine ⟨474332677074140076228627011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316221784716093384152418007 474332677074140076228627011)
            ·
              refine ⟨711499015611210114342940517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474332677074140076228627011 711499015611210114342940517)
              ·
                refine ⟨133406065427101896439301347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 711499015611210114342940517 133406065427101896439301347)
                ·
                  refine ⟨200109098140652844658952021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133406065427101896439301347 200109098140652844658952021)
                  ·
                    refine ⟨1172514246917887761673547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 200109098140652844658952021 1172514246917887761673547)
                    ·
                      rfl

theorem cell22_3425195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 9].length) (baseStart_3425195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425195 prefixEnd_3425195 := by exact prefixLift 3425195
  have htrace : WordTrace (prefixWord ++ tailWord_3425195) baseStart_3425195 baseEnd_3425195 := by
    simpa [prefixWord, tailWord_3425195, baseEnd_3425195] using wordTrace_append hprefix tailTrace_3425195
  have hstable : (prefixWord ++ tailWord_3425195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425195).length < 2 ^ (prefixWord ++ tailWord_3425195).sum := by decide
  have hdescent : baseEnd_3425195 < baseStart_3425195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425263 : List Nat := [1, 1, 2, 1, 4, 3, 4, 2, 1, 3]
def baseStart_3425263 : Nat := 118140960795 + 3425263 * 2 ^ 59
def prefixEnd_3425263 : Nat := 4983230072969 + 3 ^ 40 * 3425263 * 2
def baseEnd_3425263 : Nat := 1172537524707558250973339

theorem tailTrace_3425263 : CollatzResearch.WordTrace tailWord_3425263 prefixEnd_3425263 1172537524707558250973339 := by
  unfold tailWord_3425263
  simp only [CollatzResearch.WordTrace]
  refine ⟨124929604989864614192208443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83286403326576409461472295 124929604989864614192208443)
  ·
    refine ⟨187394407484796921288312665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124929604989864614192208443 187394407484796921288312665)
    ·
      refine ⟨140545805613597690966234499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187394407484796921288312665 140545805613597690966234499)
      ·
        refine ⟨210818708420396536449351749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140545805613597690966234499 210818708420396536449351749)
        ·
          refine ⟨39528507828824350584253453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210818708420396536449351749 39528507828824350584253453)
          ·
            refine ⟨14823190435809131469095045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39528507828824350584253453 14823190435809131469095045)
            ·
              refine ⟨2779348206714212150455321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14823190435809131469095045 2779348206714212150455321)
              ·
                refine ⟨2084511155035659112841491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2779348206714212150455321 2084511155035659112841491)
                ·
                  refine ⟨3126766732553488669262237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2084511155035659112841491 3126766732553488669262237)
                  ·
                    refine ⟨1172537524707558250973339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3126766732553488669262237 1172537524707558250973339)
                    ·
                      rfl

theorem cell22_3425263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 1, 3].length) (baseStart_3425263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425263 prefixEnd_3425263 := by exact prefixLift 3425263
  have htrace : WordTrace (prefixWord ++ tailWord_3425263) baseStart_3425263 baseEnd_3425263 := by
    simpa [prefixWord, tailWord_3425263, baseEnd_3425263] using wordTrace_append hprefix tailTrace_3425263
  have hstable : (prefixWord ++ tailWord_3425263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425263).length < 2 ^ (prefixWord ++ tailWord_3425263).sum := by decide
  have hdescent : baseEnd_3425263 < baseStart_3425263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425336 : List Nat := [2, 1, 2, 1, 5, 3, 1, 1, 1, 5]
def baseStart_3425336 : Nat := 118140960795 + 3425336 * 2 ^ 59
def prefixEnd_3425336 : Nat := 4983230072969 + 3 ^ 40 * 3425336 * 2
def baseEnd_3425336 : Nat := 1172562514099410393898115

theorem tailTrace_3425336 : CollatzResearch.WordTrace tailWord_3425336 prefixEnd_3425336 1172562514099410393898115 := by
  unfold tailWord_3425336
  simp only [CollatzResearch.WordTrace]
  refine ⟨62466133759300073829807931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83288178345733431773077241 62466133759300073829807931)
  ·
    refine ⟨93699200638950110744711897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62466133759300073829807931 93699200638950110744711897)
    ·
      refine ⟨70274400479212583058533923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93699200638950110744711897 70274400479212583058533923)
      ·
        refine ⟨105411600718818874587800885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70274400479212583058533923 105411600718818874587800885)
        ·
          refine ⟨9882337567389269492606333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105411600718818874587800885 9882337567389269492606333)
          ·
            refine ⟨3705876587770976059727375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9882337567389269492606333 3705876587770976059727375)
            ·
              refine ⟨5558814881656464089591063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3705876587770976059727375 5558814881656464089591063)
              ·
                refine ⟨8338222322484696134386595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5558814881656464089591063 8338222322484696134386595)
                ·
                  refine ⟨12507333483727044201579893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8338222322484696134386595 12507333483727044201579893)
                  ·
                    refine ⟨1172562514099410393898115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12507333483727044201579893 1172562514099410393898115)
                    ·
                      rfl

theorem cell22_3425336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_3425336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425336 prefixEnd_3425336 := by exact prefixLift 3425336
  have htrace : WordTrace (prefixWord ++ tailWord_3425336) baseStart_3425336 baseEnd_3425336 := by
    simpa [prefixWord, tailWord_3425336, baseEnd_3425336] using wordTrace_append hprefix tailTrace_3425336
  have hstable : (prefixWord ++ tailWord_3425336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425336).length < 2 ^ (prefixWord ++ tailWord_3425336).sum := by decide
  have hdescent : baseEnd_3425336 < baseStart_3425336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425347 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 2, 7]
def baseStart_3425347 : Nat := 118140960795 + 3425347 * 2 ^ 59
def prefixEnd_3425347 : Nat := 4983230072969 + 3 ^ 40 * 3425347 * 2
def baseEnd_3425347 : Nat := 1172566279624210031873081

theorem tailTrace_3425347 : CollatzResearch.WordTrace tailWord_3425347 prefixEnd_3425347 1172566279624210031873081 := by
  unfold tailWord_3425347
  simp only [CollatzResearch.WordTrace]
  refine ⟨124932668721560296538266295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83288445814373531025510863 124932668721560296538266295)
  ·
    refine ⟨187399003082340444807399443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124932668721560296538266295 187399003082340444807399443)
    ·
      refine ⟨281098504623510667211099165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187399003082340444807399443 281098504623510667211099165)
      ·
        refine ⟨105411939233816500204162187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281098504623510667211099165 105411939233816500204162187)
        ·
          refine ⟨158117908850724750306243281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105411939233816500204162187 158117908850724750306243281)
          ·
            refine ⟨118588431638043562729682461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158117908850724750306243281 118588431638043562729682461)
            ·
              refine ⟨44470661864266336023630923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118588431638043562729682461 44470661864266336023630923)
              ·
                refine ⟨66705992796399504035446385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44470661864266336023630923 66705992796399504035446385)
                ·
                  refine ⟨50029494597299628026584789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66705992796399504035446385 50029494597299628026584789)
                  ·
                    refine ⟨1172566279624210031873081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50029494597299628026584789 1172566279624210031873081)
                    ·
                      rfl

theorem cell22_3425347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 7].length) (baseStart_3425347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425347 prefixEnd_3425347 := by exact prefixLift 3425347
  have htrace : WordTrace (prefixWord ++ tailWord_3425347) baseStart_3425347 baseEnd_3425347 := by
    simpa [prefixWord, tailWord_3425347, baseEnd_3425347] using wordTrace_append hprefix tailTrace_3425347
  have hstable : (prefixWord ++ tailWord_3425347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425347).length < 2 ^ (prefixWord ++ tailWord_3425347).sum := by decide
  have hdescent : baseEnd_3425347 < baseStart_3425347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425349 : List Nat := [1, 3, 1, 1, 1, 3, 6, 6]
def baseStart_3425349 : Nat := 118140960795 + 3425349 * 2 ^ 59
def prefixEnd_3425349 : Nat := 4983230072969 + 3 ^ 40 * 3425349 * 2
def baseEnd_3425349 : Nat := 130285218251675854813675

theorem tailTrace_3425349 : CollatzResearch.WordTrace tailWord_3425349 prefixEnd_3425349 130285218251675854813675 := by
  unfold tailWord_3425349
  simp only [CollatzResearch.WordTrace]
  refine ⟨124932741667553050879839101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83288494445035367253226067 124932741667553050879839101)
  ·
    refine ⟨46849778125332394079939663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124932741667553050879839101 46849778125332394079939663)
    ·
      refine ⟨70274667187998591119909495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46849778125332394079939663 70274667187998591119909495)
      ·
        refine ⟨105412000781997886679864243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70274667187998591119909495 105412000781997886679864243)
        ·
          refine ⟨158118001172996830019796365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105412000781997886679864243 158118001172996830019796365)
          ·
            refine ⟨59294250439873811257423637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158118001172996830019796365 59294250439873811257423637)
            ·
              refine ⟨2779417989369084902691733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59294250439873811257423637 2779417989369084902691733)
              ·
                refine ⟨130285218251675854813675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2779417989369084902691733 130285218251675854813675)
                ·
                  rfl

theorem cell22_3425349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 6].length) (baseStart_3425349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425349 prefixEnd_3425349 := by exact prefixLift 3425349
  have htrace : WordTrace (prefixWord ++ tailWord_3425349) baseStart_3425349 baseEnd_3425349 := by
    simpa [prefixWord, tailWord_3425349, baseEnd_3425349] using wordTrace_append hprefix tailTrace_3425349
  have hstable : (prefixWord ++ tailWord_3425349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425349).length < 2 ^ (prefixWord ++ tailWord_3425349).sum := by decide
  have hdescent : baseEnd_3425349 < baseStart_3425349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425432 : List Nat := [2, 1, 2, 4, 2, 3, 2, 2, 1, 3]
def baseStart_3425432 : Nat := 118140960795 + 3425432 * 2 ^ 59
def prefixEnd_3425432 : Nat := 4983230072969 + 3 ^ 40 * 3425432 * 2
def baseEnd_3425432 : Nat := 1172595376861298143497821

theorem tailTrace_3425432 : CollatzResearch.WordTrace tailWord_3425432 prefixEnd_3425432 1172595376861298143497821 := by
  unfold tailWord_3425432
  simp only [CollatzResearch.WordTrace]
  refine ⟨62467884463126178027555275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83290512617501570703407033 62467884463126178027555275)
  ·
    refine ⟨93701826694689267041332913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62467884463126178027555275 93701826694689267041332913)
    ·
      refine ⟨70276370021016950280999685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93701826694689267041332913 70276370021016950280999685)
      ·
        refine ⟨13176819378940678177687441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70276370021016950280999685 13176819378940678177687441)
        ·
          refine ⟨9882614534205508633265581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13176819378940678177687441 9882614534205508633265581)
          ·
            refine ⟨3705980450327065737474593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9882614534205508633265581 3705980450327065737474593)
            ·
              refine ⟨2779485337745299303105945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3705980450327065737474593 2779485337745299303105945)
              ·
                refine ⟨2084614003308974477329459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2779485337745299303105945 2084614003308974477329459)
                ·
                  refine ⟨3126921004963461715994189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2084614003308974477329459 3126921004963461715994189)
                  ·
                    refine ⟨1172595376861298143497821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3126921004963461715994189 1172595376861298143497821)
                    ·
                      rfl

theorem cell22_3425432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 1, 3].length) (baseStart_3425432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425432 prefixEnd_3425432 := by exact prefixLift 3425432
  have htrace : WordTrace (prefixWord ++ tailWord_3425432) baseStart_3425432 baseEnd_3425432 := by
    simpa [prefixWord, tailWord_3425432, baseEnd_3425432] using wordTrace_append hprefix tailTrace_3425432
  have hstable : (prefixWord ++ tailWord_3425432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425432).length < 2 ^ (prefixWord ++ tailWord_3425432).sum := by decide
  have hdescent : baseEnd_3425432 < baseStart_3425432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425505 : List Nat := [1, 2, 3, 1, 3, 3, 3, 1, 2, 3]
def baseStart_3425505 : Nat := 118140960795 + 3425505 * 2 ^ 59
def prefixEnd_3425505 : Nat := 4983230072969 + 3 ^ 40 * 3425505 * 2
def baseEnd_3425505 : Nat := 1172620366253150286422597

theorem tailTrace_3425505 : CollatzResearch.WordTrace tailWord_3425505 prefixEnd_3425505 1172620366253150286422597 := by
  unfold tailWord_3425505
  simp only [CollatzResearch.WordTrace]
  refine ⟨124938431454987889522517969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83292287636658593015011979 124938431454987889522517969)
  ·
    refine ⟨93703823591240917141888477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124938431454987889522517969 93703823591240917141888477)
    ·
      refine ⟨35138933846715343928208179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93703823591240917141888477 35138933846715343928208179)
      ·
        refine ⟨52708400770073015892312269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35138933846715343928208179 52708400770073015892312269)
        ·
          refine ⟨19765650288777380959617101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52708400770073015892312269 19765650288777380959617101)
          ·
            refine ⟨7412118858291517859856413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19765650288777380959617101 7412118858291517859856413)
            ·
              refine ⟨2779544571859319197446155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7412118858291517859856413 2779544571859319197446155)
              ·
                refine ⟨4169316857788978796169233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2779544571859319197446155 4169316857788978796169233)
                ·
                  refine ⟨3126987643341734097126925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4169316857788978796169233 3126987643341734097126925)
                  ·
                    refine ⟨1172620366253150286422597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3126987643341734097126925 1172620366253150286422597)
                    ·
                      rfl

theorem cell22_3425505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_3425505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425505 prefixEnd_3425505 := by exact prefixLift 3425505
  have htrace : WordTrace (prefixWord ++ tailWord_3425505) baseStart_3425505 baseEnd_3425505 := by
    simpa [prefixWord, tailWord_3425505, baseEnd_3425505] using wordTrace_append hprefix tailTrace_3425505
  have hstable : (prefixWord ++ tailWord_3425505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425505).length < 2 ^ (prefixWord ++ tailWord_3425505).sum := by decide
  have hdescent : baseEnd_3425505 < baseStart_3425505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425529 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 9]
def baseStart_3425529 : Nat := 118140960795 + 3425529 * 2 ^ 59
def prefixEnd_3425529 : Nat := 4983230072969 + 3 ^ 40 * 3425529 * 2
def baseEnd_3425529 : Nat := 390876193981207407940841

theorem tailTrace_3425529 : CollatzResearch.WordTrace tailWord_3425529 prefixEnd_3425529 390876193981207407940841 := by
  unfold tailWord_3425529
  simp only [CollatzResearch.WordTrace]
  refine ⟨124939306806900941621391641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83292871204600627747594427 124939306806900941621391641)
  ·
    refine ⟨93704480105175706216043731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124939306806900941621391641 93704480105175706216043731)
    ·
      refine ⟨140556720157763559324065597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93704480105175706216043731 140556720157763559324065597)
      ·
        refine ⟨52708770059161334746524599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140556720157763559324065597 52708770059161334746524599)
        ·
          refine ⟨79063155088742002119786899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52708770059161334746524599 79063155088742002119786899)
          ·
            refine ⟨118594732633113003179680349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79063155088742002119786899 118594732633113003179680349)
            ·
              refine ⟨44473024737417376192380131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118594732633113003179680349 44473024737417376192380131)
              ·
                refine ⟨66709537106126064288570197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44473024737417376192380131 66709537106126064288570197)
                ·
                  refine ⟨390876193981207407940841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66709537106126064288570197 390876193981207407940841)
                  ·
                    rfl

theorem cell22_3425529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 9].length) (baseStart_3425529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425529 prefixEnd_3425529 := by exact prefixLift 3425529
  have htrace : WordTrace (prefixWord ++ tailWord_3425529) baseStart_3425529 baseEnd_3425529 := by
    simpa [prefixWord, tailWord_3425529, baseEnd_3425529] using wordTrace_append hprefix tailTrace_3425529
  have hstable : (prefixWord ++ tailWord_3425529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425529).length < 2 ^ (prefixWord ++ tailWord_3425529).sum := by decide
  have hdescent : baseEnd_3425529 < baseStart_3425529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425546 : List Nat := [3, 1, 2, 2, 1, 1, 1, 6, 5]
def baseStart_3425546 : Nat := 118140960795 + 3425546 * 2 ^ 59
def prefixEnd_3425546 : Nat := 4983230072969 + 3 ^ 40 * 3425546 * 2
def baseEnd_3425546 : Nat := 390878133797013282049157

theorem tailTrace_3425546 : CollatzResearch.WordTrace tailWord_3425546 prefixEnd_3425546 390878133797013282049157 := by
  unfold tailWord_3425546
  simp only [CollatzResearch.WordTrace]
  refine ⟨31234981711959838381190123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83293284565226235683173661 31234981711959838381190123)
  ·
    refine ⟨46852472567939757571785185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31234981711959838381190123 46852472567939757571785185)
    ·
      refine ⟨35139354425954818178838889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46852472567939757571785185 35139354425954818178838889)
      ·
        refine ⟨26354515819466113634129167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35139354425954818178838889 26354515819466113634129167)
        ·
          refine ⟨39531773729199170451193751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26354515819466113634129167 39531773729199170451193751)
          ·
            refine ⟨59297660593798755676790627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39531773729199170451193751 59297660593798755676790627)
            ·
              refine ⟨88946490890698133515185941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59297660593798755676790627 88946490890698133515185941)
              ·
                refine ⟨4169366760501475008524341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88946490890698133515185941 4169366760501475008524341)
                ·
                  refine ⟨390878133797013282049157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4169366760501475008524341 390878133797013282049157)
                  ·
                    rfl

theorem cell22_3425546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_3425546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425546 prefixEnd_3425546 := by exact prefixLift 3425546
  have htrace : WordTrace (prefixWord ++ tailWord_3425546) baseStart_3425546 baseEnd_3425546 := by
    simpa [prefixWord, tailWord_3425546, baseEnd_3425546] using wordTrace_append hprefix tailTrace_3425546
  have hstable : (prefixWord ++ tailWord_3425546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425546).length < 2 ^ (prefixWord ++ tailWord_3425546).sum := by decide
  have hdescent : baseEnd_3425546 < baseStart_3425546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425550 : List Nat := [4, 1, 1, 2, 1, 5, 1, 1, 3, 3]
def baseStart_3425550 : Nat := 118140960795 + 3425550 * 2 ^ 59
def prefixEnd_3425550 : Nat := 4983230072969 + 3 ^ 40 * 3425550 * 2
def baseEnd_3425550 : Nat := 1172635770672785169047459

theorem tailTrace_3425550 : CollatzResearch.WordTrace tailWord_3425550 prefixEnd_3425550 1172635770672785169047459 := by
  unfold tailWord_3425550
  simp only [CollatzResearch.WordTrace]
  refine ⟨15617509092478107775988263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83293381826549908138604069 15617509092478107775988263)
  ·
    refine ⟨23426263638717161663982395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15617509092478107775988263 23426263638717161663982395)
    ·
      refine ⟨35139395458075742495973593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23426263638717161663982395 35139395458075742495973593)
      ·
        refine ⟨26354546593556806871980195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35139395458075742495973593 26354546593556806871980195)
        ·
          refine ⟨39531819890335210307970293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26354546593556806871980195 39531819890335210307970293)
          ·
            refine ⟨3706108114718925966372215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39531819890335210307970293 3706108114718925966372215)
            ·
              refine ⟨5559162172078388949558323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3706108114718925966372215 5559162172078388949558323)
              ·
                refine ⟨8338743258117583424337485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5559162172078388949558323 8338743258117583424337485)
                ·
                  refine ⟨3127028721794093784126557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8338743258117583424337485 3127028721794093784126557)
                  ·
                    refine ⟨1172635770672785169047459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3127028721794093784126557 1172635770672785169047459)
                    ·
                      rfl

theorem cell22_3425550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_3425550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425550 prefixEnd_3425550 := by exact prefixLift 3425550
  have htrace : WordTrace (prefixWord ++ tailWord_3425550) baseStart_3425550 baseEnd_3425550 := by
    simpa [prefixWord, tailWord_3425550, baseEnd_3425550] using wordTrace_append hprefix tailTrace_3425550
  have hstable : (prefixWord ++ tailWord_3425550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425550).length < 2 ^ (prefixWord ++ tailWord_3425550).sum := by decide
  have hdescent : baseEnd_3425550 < baseStart_3425550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425623 : List Nat := [1, 1, 3, 2, 3, 3, 2, 1, 1, 5]
def baseStart_3425623 : Nat := 118140960795 + 3425623 * 2 ^ 59
def prefixEnd_3425623 : Nat := 4983230072969 + 3 ^ 40 * 3425623 * 2
def baseEnd_3425623 : Nat := 1172660760064637311972235

theorem tailTrace_3425623 : CollatzResearch.WordTrace tailWord_3425623 prefixEnd_3425623 1172660760064637311972235 := by
  unfold tailWord_3425623
  simp only [CollatzResearch.WordTrace]
  refine ⟨124942735268560395675313523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83295156845706930450209015 124942735268560395675313523)
  ·
    refine ⟨187414102902840593512970285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124942735268560395675313523 187414102902840593512970285)
    ·
      refine ⟨70280288588565222567363857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187414102902840593512970285 70280288588565222567363857)
      ·
        refine ⟨52710216441423916925522893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70280288588565222567363857 52710216441423916925522893)
        ·
          refine ⟨19766331165533968847071085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52710216441423916925522893 19766331165533968847071085)
          ·
            refine ⟨7412374187075238317651657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19766331165533968847071085 7412374187075238317651657)
            ·
              refine ⟨5559280640306428738238743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7412374187075238317651657 5559280640306428738238743)
              ·
                refine ⟨8338920960459643107358115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5559280640306428738238743 8338920960459643107358115)
                ·
                  refine ⟨12508381440689464661037173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8338920960459643107358115 12508381440689464661037173)
                  ·
                    refine ⟨1172660760064637311972235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12508381440689464661037173 1172660760064637311972235)
                    ·
                      rfl

theorem cell22_3425623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_3425623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425623 prefixEnd_3425623 := by exact prefixLift 3425623
  have htrace : WordTrace (prefixWord ++ tailWord_3425623) baseStart_3425623 baseEnd_3425623 := by
    simpa [prefixWord, tailWord_3425623, baseEnd_3425623] using wordTrace_append hprefix tailTrace_3425623
  have hstable : (prefixWord ++ tailWord_3425623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425623).length < 2 ^ (prefixWord ++ tailWord_3425623).sum := by decide
  have hdescent : baseEnd_3425623 < baseStart_3425623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425642 : List Nat := [3, 1, 3, 3, 2, 1, 2, 3, 4]
def baseStart_3425642 : Nat := 118140960795 + 3425642 * 2 ^ 59
def prefixEnd_3425642 : Nat := 4983230072969 + 3 ^ 40 * 3425642 * 2
def baseEnd_3425642 : Nat := 390889088050975865249059

theorem tailTrace_3425642 : CollatzResearch.WordTrace tailWord_3425642 prefixEnd_3425642 390889088050975865249059 := by
  unfold tailWord_3425642
  simp only [CollatzResearch.WordTrace]
  refine ⟨31235857063872890480063795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83295618836994374613503453 31235857063872890480063795)
  ·
    refine ⟨46853785595809335720095693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31235857063872890480063795 46853785595809335720095693)
    ·
      refine ⟨17570169598428500895035885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46853785595809335720095693 17570169598428500895035885)
      ·
        refine ⟨6588813599410687835638457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17570169598428500895035885 6588813599410687835638457)
        ·
          refine ⟨4941610199558015876728843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6588813599410687835638457 4941610199558015876728843)
          ·
            refine ⟨7412415299337023815093265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4941610199558015876728843 7412415299337023815093265)
            ·
              refine ⟨5559311474502767861319949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7412415299337023815093265 5559311474502767861319949)
              ·
                refine ⟨2084741802938537947994981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5559311474502767861319949 2084741802938537947994981)
                ·
                  refine ⟨390889088050975865249059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2084741802938537947994981 390889088050975865249059)
                  ·
                    rfl

theorem cell22_3425642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 4].length) (baseStart_3425642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425642 prefixEnd_3425642 := by exact prefixLift 3425642
  have htrace : WordTrace (prefixWord ++ tailWord_3425642) baseStart_3425642 baseEnd_3425642 := by
    simpa [prefixWord, tailWord_3425642, baseEnd_3425642] using wordTrace_append hprefix tailTrace_3425642
  have hstable : (prefixWord ++ tailWord_3425642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425642).length < 2 ^ (prefixWord ++ tailWord_3425642).sum := by decide
  have hdescent : baseEnd_3425642 < baseStart_3425642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425653 : List Nat := [1, 3, 4, 1, 3, 1, 9]
def baseStart_3425653 : Nat := 118140960795 + 3425653 * 2 ^ 59
def prefixEnd_3425653 : Nat := 4983230072969 + 3 ^ 40 * 3425653 * 2
def baseEnd_3425653 : Nat := 43432260358434341989709

theorem tailTrace_3425653 : CollatzResearch.WordTrace tailWord_3425653 prefixEnd_3425653 43432260358434341989709 := by
  unfold tailWord_3425653
  simp only [CollatzResearch.WordTrace]
  refine ⟨124943829458451710798905613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83295886305634473865937075 124943829458451710798905613)
  ·
    refine ⟨46853936046919391549589605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124943829458451710798905613 46853936046919391549589605)
    ·
      refine ⟨8785113008797385915548051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46853936046919391549589605 8785113008797385915548051)
      ·
        refine ⟨13177669513196078873322077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8785113008797385915548051 13177669513196078873322077)
        ·
          refine ⟨4941626067448529577495779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13177669513196078873322077 4941626067448529577495779)
          ·
            refine ⟨7412439101172794366243669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4941626067448529577495779 7412439101172794366243669)
            ·
              refine ⟨43432260358434341989709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7412439101172794366243669 43432260358434341989709)
              ·
                rfl

theorem cell22_3425653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 9].length) (baseStart_3425653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425653 prefixEnd_3425653 := by exact prefixLift 3425653
  have htrace : WordTrace (prefixWord ++ tailWord_3425653) baseStart_3425653 baseEnd_3425653 := by
    simpa [prefixWord, tailWord_3425653, baseEnd_3425653] using wordTrace_append hprefix tailTrace_3425653
  have hstable : (prefixWord ++ tailWord_3425653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425653).length < 2 ^ (prefixWord ++ tailWord_3425653).sum := by decide
  have hdescent : baseEnd_3425653 < baseStart_3425653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425698 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 7]
def baseStart_3425698 : Nat := 118140960795 + 3425698 * 2 ^ 59
def prefixEnd_3425698 : Nat := 4983230072969 + 3 ^ 40 * 3425698 * 2
def baseEnd_3425698 : Nat := 390895478032454038782335

theorem tailTrace_3425698 : CollatzResearch.WordTrace tailWord_3425698 prefixEnd_3425698 390895478032454038782335 := by
  unfold tailWord_3425698
  simp only [CollatzResearch.WordTrace]
  refine ⟨31236367685822170871073437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83296980495525788989529165 31236367685822170871073437)
  ·
    refine ⟨11713637882183314076652539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31236367685822170871073437 11713637882183314076652539)
    ·
      refine ⟨17570456823274971114978809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11713637882183314076652539 17570456823274971114978809)
      ·
        refine ⟨13177842617456228336234107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17570456823274971114978809 13177842617456228336234107)
        ·
          refine ⟨19766763926184342504351161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13177842617456228336234107 19766763926184342504351161)
          ·
            refine ⟨14825072944638256878263371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19766763926184342504351161 14825072944638256878263371)
            ·
              refine ⟨22237609416957385317395057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14825072944638256878263371 22237609416957385317395057)
              ·
                refine ⟨16678207062718038988046293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22237609416957385317395057 16678207062718038988046293)
                ·
                  refine ⟨390895478032454038782335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16678207062718038988046293 390895478032454038782335)
                  ·
                    rfl

theorem cell22_3425698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_3425698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425698 prefixEnd_3425698 := by exact prefixLift 3425698
  have htrace : WordTrace (prefixWord ++ tailWord_3425698) baseStart_3425698 baseEnd_3425698 := by
    simpa [prefixWord, tailWord_3425698, baseEnd_3425698] using wordTrace_append hprefix tailTrace_3425698
  have hstable : (prefixWord ++ tailWord_3425698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425698).length < 2 ^ (prefixWord ++ tailWord_3425698).sum := by decide
  have hdescent : baseEnd_3425698 < baseStart_3425698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425732 : List Nat := [2, 3, 3, 2, 1, 1, 4, 1, 5]
def baseStart_3425732 : Nat := 118140960795 + 3425732 * 2 ^ 59
def prefixEnd_3425732 : Nat := 4983230072969 + 3 ^ 40 * 3425732 * 2
def baseEnd_3425732 : Nat := 390899357664065786998967

theorem tailTrace_3425732 : CollatzResearch.WordTrace tailWord_3425732 prefixEnd_3425732 390899357664065786998967 := by
  unfold tailWord_3425732
  simp only [CollatzResearch.WordTrace]
  refine ⟨62473355412582753645515725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83297807216777004860687633 62473355412582753645515725)
  ·
    refine ⟨23427508279718532617068397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62473355412582753645515725 23427508279718532617068397)
    ·
      refine ⟨8785315604894449731400649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23427508279718532617068397 8785315604894449731400649)
      ·
        refine ⟨6588986703670837298550487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8785315604894449731400649 6588986703670837298550487)
        ·
          refine ⟨9883480055506255947825731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6588986703670837298550487 9883480055506255947825731)
          ·
            refine ⟨14825220083259383921738597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9883480055506255947825731 14825220083259383921738597)
            ·
              refine ⟨2779728765611134485325987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14825220083259383921738597 2779728765611134485325987)
              ·
                refine ⟨4169593148416701727988981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2779728765611134485325987 4169593148416701727988981)
                ·
                  refine ⟨390899357664065786998967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4169593148416701727988981 390899357664065786998967)
                  ·
                    rfl

theorem cell22_3425732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_3425732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425732 prefixEnd_3425732 := by exact prefixLift 3425732
  have htrace : WordTrace (prefixWord ++ tailWord_3425732) baseStart_3425732 baseEnd_3425732 := by
    simpa [prefixWord, tailWord_3425732, baseEnd_3425732] using wordTrace_append hprefix tailTrace_3425732
  have hstable : (prefixWord ++ tailWord_3425732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425732).length < 2 ^ (prefixWord ++ tailWord_3425732).sum := by decide
  have hdescent : baseEnd_3425732 < baseStart_3425732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425775 : List Nat := [1, 1, 2, 1, 4, 1, 3, 4, 2, 3]
def baseStart_3425775 : Nat := 118140960795 + 3425775 * 2 ^ 59
def prefixEnd_3425775 : Nat := 4983230072969 + 3 ^ 40 * 3425775 * 2
def baseEnd_3425775 : Nat := 1172712792770959582171769

theorem tailTrace_3425775 : CollatzResearch.WordTrace tailWord_3425775 prefixEnd_3425775 1172712792770959582171769 := by
  unfold tailWord_3425775
  simp only [CollatzResearch.WordTrace]
  refine ⟨124948279164009725634846779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83298852776006483756564519 124948279164009725634846779)
  ·
    refine ⟨187422418746014588452270169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124948279164009725634846779 187422418746014588452270169)
    ·
      refine ⟨140566814059510941339202627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187422418746014588452270169 140566814059510941339202627)
      ·
        refine ⟨210850221089266412008803941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140566814059510941339202627 210850221089266412008803941)
        ·
          refine ⟨39534416454237452251650739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210850221089266412008803941 39534416454237452251650739)
          ·
            refine ⟨59301624681356178377476109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39534416454237452251650739 59301624681356178377476109)
            ·
              refine ⟨22238109255508566891553541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59301624681356178377476109 22238109255508566891553541)
              ·
                refine ⟨4169645485407856292166289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22238109255508566891553541 4169645485407856292166289)
                ·
                  refine ⟨3127234114055892219124717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4169645485407856292166289 3127234114055892219124717)
                  ·
                    refine ⟨1172712792770959582171769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3127234114055892219124717 1172712792770959582171769)
                    ·
                      rfl

theorem cell22_3425775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 3].length) (baseStart_3425775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425775 prefixEnd_3425775 := by exact prefixLift 3425775
  have htrace : WordTrace (prefixWord ++ tailWord_3425775) baseStart_3425775 baseEnd_3425775 := by
    simpa [prefixWord, tailWord_3425775, baseEnd_3425775] using wordTrace_append hprefix tailTrace_3425775
  have hstable : (prefixWord ++ tailWord_3425775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425775).length < 2 ^ (prefixWord ++ tailWord_3425775).sum := by decide
  have hdescent : baseEnd_3425775 < baseStart_3425775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425777 : List Nat := [1, 2, 2, 2, 3, 2, 4, 2, 4]
def baseStart_3425777 : Nat := 118140960795 + 3425777 * 2 ^ 59
def prefixEnd_3425777 : Nat := 4983230072969 + 3 ^ 40 * 3425777 * 2
def baseEnd_3425777 : Nat := 390904492470610747873921

theorem tailTrace_3425777 : CollatzResearch.WordTrace tailWord_3425777 prefixEnd_3425777 390904492470610747873921 := by
  unfold tailWord_3425777
  simp only [CollatzResearch.WordTrace]
  refine ⟨124948352110002479976419585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83298901406668319984279723 124948352110002479976419585)
  ·
    refine ⟨93711264082501859982314689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124948352110002479976419585 93711264082501859982314689)
    ·
      refine ⟨70283448061876394986736017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93711264082501859982314689 70283448061876394986736017)
      ·
        refine ⟨52712586046407296240052013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70283448061876394986736017 52712586046407296240052013)
        ·
          refine ⟨19767219767402736090019505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52712586046407296240052013 19767219767402736090019505)
          ·
            refine ⟨14825414825552052067514629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19767219767402736090019505 14825414825552052067514629)
            ·
              refine ⟨2779765279791009762658993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14825414825552052067514629 2779765279791009762658993)
              ·
                refine ⟨2084823959843257321994245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2779765279791009762658993 2084823959843257321994245)
                ·
                  refine ⟨390904492470610747873921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2084823959843257321994245 390904492470610747873921)
                  ·
                    rfl

theorem cell22_3425777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 4].length) (baseStart_3425777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425777 prefixEnd_3425777 := by exact prefixLift 3425777
  have htrace : WordTrace (prefixWord ++ tailWord_3425777) baseStart_3425777 baseEnd_3425777 := by
    simpa [prefixWord, tailWord_3425777, baseEnd_3425777] using wordTrace_append hprefix tailTrace_3425777
  have hstable : (prefixWord ++ tailWord_3425777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425777).length < 2 ^ (prefixWord ++ tailWord_3425777).sum := by decide
  have hdescent : baseEnd_3425777 < baseStart_3425777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425788 : List Nat := [2, 2, 2, 1, 2, 1, 5, 7]
def baseStart_3425788 : Nat := 118140960795 + 3425788 * 2 ^ 59
def prefixEnd_3425788 : Nat := 4983230072969 + 3 ^ 40 * 3425788 * 2
def baseEnd_3425788 : Nat := 130301915881847986844081

theorem tailTrace_3425788 : CollatzResearch.WordTrace tailWord_3425788 prefixEnd_3425788 130301915881847986844081 := by
  unfold tailWord_3425788
  simp only [CollatzResearch.WordTrace]
  refine ⟨62474376656481314427535009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83299168875308419236713345 62474376656481314427535009)
  ·
    refine ⟨46855782492360985820651257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62474376656481314427535009 46855782492360985820651257)
    ·
      refine ⟨35141836869270739365488443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46855782492360985820651257 35141836869270739365488443)
      ·
        refine ⟨52712755303906109048232665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35141836869270739365488443 52712755303906109048232665)
        ·
          refine ⟨39534566477929581786174499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52712755303906109048232665 39534566477929581786174499)
          ·
            refine ⟨59301849716894372679261749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39534566477929581786174499 59301849716894372679261749)
            ·
              refine ⟨5559548410958847438680789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59301849716894372679261749 5559548410958847438680789)
              ·
                refine ⟨130301915881847986844081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5559548410958847438680789 130301915881847986844081)
                ·
                  rfl

theorem cell22_3425788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 7].length) (baseStart_3425788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425788 prefixEnd_3425788 := by exact prefixLift 3425788
  have htrace : WordTrace (prefixWord ++ tailWord_3425788) baseStart_3425788 baseEnd_3425788 := by
    simpa [prefixWord, tailWord_3425788, baseEnd_3425788] using wordTrace_append hprefix tailTrace_3425788
  have hstable : (prefixWord ++ tailWord_3425788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425788).length < 2 ^ (prefixWord ++ tailWord_3425788).sum := by decide
  have hdescent : baseEnd_3425788 < baseStart_3425788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425820 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 5, 3]
def baseStart_3425820 : Nat := 118140960795 + 3425820 * 2 ^ 59
def prefixEnd_3425820 : Nat := 4983230072969 + 3 ^ 40 * 3425820 * 2
def baseEnd_3425820 : Nat := 1172728197190594464796631

theorem tailTrace_3425820 : CollatzResearch.WordTrace tailWord_3425820 prefixEnd_3425820 1172728197190594464796631 := by
  unfold tailWord_3425820
  simp only [CollatzResearch.WordTrace]
  refine ⟨62474960224423349160117457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83299946965897798880156609 62474960224423349160117457)
  ·
    refine ⟨46856220168317511870088093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62474960224423349160117457 46856220168317511870088093)
    ·
      refine ⟨17571082563119066951283035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46856220168317511870088093 17571082563119066951283035)
      ·
        refine ⟨26356623844678600426924553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17571082563119066951283035 26356623844678600426924553)
        ·
          refine ⟨19767467883508950320193415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26356623844678600426924553 19767467883508950320193415)
          ·
            refine ⟨29651201825263425480290123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19767467883508950320193415 29651201825263425480290123)
            ·
              refine ⟨44476802737895138220435185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29651201825263425480290123 44476802737895138220435185)
              ·
                refine ⟨33357602053421353665326389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44476802737895138220435185 33357602053421353665326389)
                ·
                  refine ⟨3127275192508251906124349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33357602053421353665326389 3127275192508251906124349)
                  ·
                    refine ⟨1172728197190594464796631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3127275192508251906124349 1172728197190594464796631)
                    ·
                      rfl

theorem cell22_3425820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_3425820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425820 prefixEnd_3425820 := by exact prefixLift 3425820
  have htrace : WordTrace (prefixWord ++ tailWord_3425820) baseStart_3425820 baseEnd_3425820 := by
    simpa [prefixWord, tailWord_3425820, baseEnd_3425820] using wordTrace_append hprefix tailTrace_3425820
  have hstable : (prefixWord ++ tailWord_3425820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425820).length < 2 ^ (prefixWord ++ tailWord_3425820).sum := by decide
  have hdescent : baseEnd_3425820 < baseStart_3425820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425895 : List Nat := [1, 1, 5, 1, 1, 1, 5, 1, 6]
def baseStart_3425895 : Nat := 118140960795 + 3425895 * 2 ^ 59
def prefixEnd_3425895 : Nat := 4983230072969 + 3 ^ 40 * 3425895 * 2
def baseEnd_3425895 : Nat := 390917957074439756390467

theorem tailTrace_3425895 : CollatzResearch.WordTrace tailWord_3425895 prefixEnd_3425895 390917957074439756390467 := by
  unfold tailWord_3425895
  simp only [CollatzResearch.WordTrace]
  refine ⟨124952655923574986129215139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83301770615716657419476759 124952655923574986129215139)
  ·
    refine ⟨187428983885362479193822709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124952655923574986129215139 187428983885362479193822709)
    ·
      refine ⟨17571467239252732424420879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187428983885362479193822709 17571467239252732424420879)
      ·
        refine ⟨26357200858879098636631319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17571467239252732424420879 26357200858879098636631319)
        ·
          refine ⟨39535801288318647954946979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26357200858879098636631319 39535801288318647954946979)
          ·
            refine ⟨59303701932477971932420469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39535801288318647954946979 59303701932477971932420469)
            ·
              refine ⟨5559722056169809868664419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59303701932477971932420469 5559722056169809868664419)
              ·
                refine ⟨8339583084254714802996629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5559722056169809868664419 8339583084254714802996629)
                ·
                  refine ⟨390917957074439756390467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8339583084254714802996629 390917957074439756390467)
                  ·
                    rfl

theorem cell22_3425895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 6].length) (baseStart_3425895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425895 prefixEnd_3425895 := by exact prefixLift 3425895
  have htrace : WordTrace (prefixWord ++ tailWord_3425895) baseStart_3425895 baseEnd_3425895 := by
    simpa [prefixWord, tailWord_3425895, baseEnd_3425895] using wordTrace_append hprefix tailTrace_3425895
  have hstable : (prefixWord ++ tailWord_3425895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425895).length < 2 ^ (prefixWord ++ tailWord_3425895).sum := by decide
  have hdescent : baseEnd_3425895 < baseStart_3425895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425901 : List Nat := [1, 5, 1, 1, 5, 1, 2, 1, 5]
def baseStart_3425901 : Nat := 118140960795 + 3425901 * 2 ^ 59
def prefixEnd_3425901 : Nat := 4983230072969 + 3 ^ 40 * 3425901 * 2
def baseEnd_3425901 : Nat := 390918641715312417840461

theorem tailTrace_3425901 : CollatzResearch.WordTrace tailWord_3425901 prefixEnd_3425901 390918641715312417840461 := by
  unfold tailWord_3425901
  simp only [CollatzResearch.WordTrace]
  refine ⟨124952874761553249153933557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83301916507702166102622371 124952874761553249153933557)
  ·
    refine ⟨11714332008895617108181271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124952874761553249153933557 11714332008895617108181271)
    ·
      refine ⟨17571498013343425662271907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11714332008895617108181271 17571498013343425662271907)
      ·
        refine ⟨26357247020015138493407861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17571498013343425662271907 26357247020015138493407861)
        ·
          refine ⟨2470991908126419233756987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26357247020015138493407861 2470991908126419233756987)
          ·
            refine ⟨3706487862189628850635481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2470991908126419233756987 3706487862189628850635481)
            ·
              refine ⟨2779865896642221637976611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3706487862189628850635481 2779865896642221637976611)
              ·
                refine ⟨4169798844963332456964917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2779865896642221637976611 4169798844963332456964917)
                ·
                  refine ⟨390918641715312417840461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4169798844963332456964917 390918641715312417840461)
                  ·
                    rfl

theorem cell22_3425901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_3425901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425901 prefixEnd_3425901 := by exact prefixLift 3425901
  have htrace : WordTrace (prefixWord ++ tailWord_3425901) baseStart_3425901 baseEnd_3425901 := by
    simpa [prefixWord, tailWord_3425901, baseEnd_3425901] using wordTrace_append hprefix tailTrace_3425901
  have hstable : (prefixWord ++ tailWord_3425901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425901).length < 2 ^ (prefixWord ++ tailWord_3425901).sum := by decide
  have hdescent : baseEnd_3425901 < baseStart_3425901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425940 : List Nat := [2, 4, 2, 2, 12]
def baseStart_3425940 : Nat := 118140960795 + 3425940 * 2 ^ 59
def prefixEnd_3425940 : Nat := 4983230072969 + 3 ^ 40 * 3425940 * 2
def baseEnd_3425940 : Nat := 4826211010876354534141

theorem tailTrace_3425940 : CollatzResearch.WordTrace tailWord_3425940 prefixEnd_3425940 4826211010876354534141 := by
  unfold tailWord_3425940
  simp only [CollatzResearch.WordTrace]
  refine ⟨62477148604205979407301637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83302864805607972543068849 62477148604205979407301637)
  ·
    refine ⟨11714465363288621138869057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62477148604205979407301637 11714465363288621138869057)
    ·
      refine ⟨8785849022466465854151793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11714465363288621138869057 8785849022466465854151793)
      ·
        refine ⟨6589386766849849390613845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8785849022466465854151793 6589386766849849390613845)
        ·
          refine ⟨4826211010876354534141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6589386766849849390613845 4826211010876354534141)
          ·
            rfl

theorem cell22_3425940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 12].length) (baseStart_3425940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425940 prefixEnd_3425940 := by exact prefixLift 3425940
  have htrace : WordTrace (prefixWord ++ tailWord_3425940) baseStart_3425940 baseEnd_3425940 := by
    simpa [prefixWord, tailWord_3425940, baseEnd_3425940] using wordTrace_append hprefix tailTrace_3425940
  have hstable : (prefixWord ++ tailWord_3425940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425940).length < 2 ^ (prefixWord ++ tailWord_3425940).sum := by decide
  have hdescent : baseEnd_3425940 < baseStart_3425940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425944 : List Nat := [2, 1, 2, 4, 1, 3, 2, 2, 2, 3]
def baseStart_3425944 : Nat := 118140960795 + 3425944 * 2 ^ 59
def prefixEnd_3425944 : Nat := 4983230072969 + 3 ^ 40 * 3425944 * 2
def baseEnd_3425944 : Nat := 1172770644924699474696251

theorem tailTrace_3425944 : CollatzResearch.WordTrace tailWord_3425944 prefixEnd_3425944 1172770644924699474696251 := by
  unfold tailWord_3425944
  simp only [CollatzResearch.WordTrace]
  refine ⟨62477221550198733748874443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83302962066931644998499257 62477221550198733748874443)
  ·
    refine ⟨93715832325298100623311665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62477221550198733748874443 93715832325298100623311665)
    ·
      refine ⟨70286874243973575467483749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93715832325298100623311665 70286874243973575467483749)
      ·
        refine ⟨13178788920745045400153203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70286874243973575467483749 13178788920745045400153203)
        ·
          refine ⟨19768183381117568100229805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13178788920745045400153203 19768183381117568100229805)
          ·
            refine ⟨7413068767919088037586177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19768183381117568100229805 7413068767919088037586177)
            ·
              refine ⟨5559801575939316028189633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7413068767919088037586177 5559801575939316028189633)
              ·
                refine ⟨4169851181954487021142225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5559801575939316028189633 4169851181954487021142225)
                ·
                  refine ⟨3127388386465865265856669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4169851181954487021142225 3127388386465865265856669)
                  ·
                    refine ⟨1172770644924699474696251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3127388386465865265856669 1172770644924699474696251)
                    ·
                      rfl

theorem cell22_3425944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_3425944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3425944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3425944 prefixEnd_3425944 := by exact prefixLift 3425944
  have htrace : WordTrace (prefixWord ++ tailWord_3425944) baseStart_3425944 baseEnd_3425944 := by
    simpa [prefixWord, tailWord_3425944, baseEnd_3425944] using wordTrace_append hprefix tailTrace_3425944
  have hstable : (prefixWord ++ tailWord_3425944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425944).length < 2 ^ (prefixWord ++ tailWord_3425944).sum := by decide
  have hdescent : baseEnd_3425944 < baseStart_3425944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426002 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 7]
def baseStart_3426002 : Nat := 118140960795 + 3426002 * 2 ^ 59
def prefixEnd_3426002 : Nat := 4983230072969 + 3 ^ 40 * 3426002 * 2
def baseEnd_3426002 : Nat := 390930166503335552248691

theorem tailTrace_3426002 : CollatzResearch.WordTrace tailWord_3426002 prefixEnd_3426002 390930166503335552248691 := by
  unfold tailWord_3426002
  simp only [CollatzResearch.WordTrace]
  refine ⟨31239139633546835850840065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83304372356124895602240173 31239139633546835850840065)
  ·
    refine ⟨23429354725160126888130049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31239139633546835850840065 23429354725160126888130049)
    ·
      refine ⟨17572016043870095166097537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23429354725160126888130049 17572016043870095166097537)
      ·
        refine ⟨13179012032902571374573153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17572016043870095166097537 13179012032902571374573153)
        ·
          refine ⟨9884259024676928530929865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13179012032902571374573153 9884259024676928530929865)
          ·
            refine ⟨7413194268507696398197399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9884259024676928530929865 7413194268507696398197399)
            ·
              refine ⟨11119791402761544597296099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7413194268507696398197399 11119791402761544597296099)
              ·
                refine ⟨16679687104142316895944149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11119791402761544597296099 16679687104142316895944149)
                ·
                  refine ⟨390930166503335552248691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16679687104142316895944149 390930166503335552248691)
                  ·
                    rfl

theorem cell22_3426002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_3426002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426002 prefixEnd_3426002 := by exact prefixLift 3426002
  have htrace : WordTrace (prefixWord ++ tailWord_3426002) baseStart_3426002 baseEnd_3426002 := by
    simpa [prefixWord, tailWord_3426002, baseEnd_3426002] using wordTrace_append hprefix tailTrace_3426002
  have hstable : (prefixWord ++ tailWord_3426002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426002).length < 2 ^ (prefixWord ++ tailWord_3426002).sum := by decide
  have hdescent : baseEnd_3426002 < baseStart_3426002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426079 : List Nat := [1, 1, 2, 4, 2, 1, 3, 3, 2, 3]
def baseStart_3426079 : Nat := 118140960795 + 3426079 * 2 ^ 59
def prefixEnd_3426079 : Nat := 4983230072969 + 3 ^ 40 * 3426079 * 2
def baseEnd_3426079 : Nat := 1172816858183604122570837

theorem tailTrace_3426079 : CollatzResearch.WordTrace tailWord_3426079 prefixEnd_3426079 1172816858183604122570837 := by
  unfold tailWord_3426079
  simp only [CollatzResearch.WordTrace]
  refine ⟨124959366954908385553913291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83306244636605590369275527 124959366954908385553913291)
  ·
    refine ⟨187439050432362578330869937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124959366954908385553913291 187439050432362578330869937)
    ·
      refine ⟨140579287824271933748152453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187439050432362578330869937 140579287824271933748152453)
      ·
        refine ⟨26358616467050987577778585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140579287824271933748152453 26358616467050987577778585)
        ·
          refine ⟨19768962350288240683333939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26358616467050987577778585 19768962350288240683333939)
          ·
            refine ⟨29653443525432361025000909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19768962350288240683333939 29653443525432361025000909)
            ·
              refine ⟨11120041322037135384375341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29653443525432361025000909 11120041322037135384375341)
              ·
                refine ⟨4170015495763925769140753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11120041322037135384375341 4170015495763925769140753)
                ·
                  refine ⟨3127511621822944326855565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4170015495763925769140753 3127511621822944326855565)
                  ·
                    refine ⟨1172816858183604122570837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3127511621822944326855565 1172816858183604122570837)
                    ·
                      rfl

theorem cell22_3426079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 3].length) (baseStart_3426079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426079 prefixEnd_3426079 := by exact prefixLift 3426079
  have htrace : WordTrace (prefixWord ++ tailWord_3426079) baseStart_3426079 baseEnd_3426079 := by
    simpa [prefixWord, tailWord_3426079, baseEnd_3426079] using wordTrace_append hprefix tailTrace_3426079
  have hstable : (prefixWord ++ tailWord_3426079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426079).length < 2 ^ (prefixWord ++ tailWord_3426079).sum := by decide
  have hdescent : baseEnd_3426079 < baseStart_3426079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426137 : List Nat := [1, 2, 1, 2, 2, 3, 1, 5, 5]
def baseStart_3426137 : Nat := 118140960795 + 3426137 * 2 ^ 59
def prefixEnd_3426137 : Nat := 4983230072969 + 3 ^ 40 * 3426137 * 2
def baseEnd_3426137 : Nat := 390945570922970434873553

theorem tailTrace_3426137 : CollatzResearch.WordTrace tailWord_3426137 prefixEnd_3426137 390945570922970434873553 := by
  unfold tailWord_3426137
  simp only [CollatzResearch.WordTrace]
  refine ⟨124961482388698261459524665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83307654925798840973016443 124961482388698261459524665)
  ·
    refine ⟨93721111791523696094643499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124961482388698261459524665 93721111791523696094643499)
    ·
      refine ⟨140581667687285544141965249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93721111791523696094643499 140581667687285544141965249)
      ·
        refine ⟨105436250765464158106473937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140581667687285544141965249 105436250765464158106473937)
        ·
          refine ⟨79077188074098118579855453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105436250765464158106473937 79077188074098118579855453)
          ·
            refine ⟨29653945527786794467445795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79077188074098118579855453 29653945527786794467445795)
            ·
              refine ⟨44480918291680191701168693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29653945527786794467445795 44480918291680191701168693)
              ·
                refine ⟨4170086089845017971984565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44480918291680191701168693 4170086089845017971984565)
                ·
                  refine ⟨390945570922970434873553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4170086089845017971984565 390945570922970434873553)
                  ·
                    rfl

theorem cell22_3426137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 5].length) (baseStart_3426137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426137 prefixEnd_3426137 := by exact prefixLift 3426137
  have htrace : WordTrace (prefixWord ++ tailWord_3426137) baseStart_3426137 baseEnd_3426137 := by
    simpa [prefixWord, tailWord_3426137, baseEnd_3426137] using wordTrace_append hprefix tailTrace_3426137
  have hstable : (prefixWord ++ tailWord_3426137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426137).length < 2 ^ (prefixWord ++ tailWord_3426137).sum := by decide
  have hdescent : baseEnd_3426137 < baseStart_3426137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426152 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 1, 7]
def baseStart_3426152 : Nat := 118140960795 + 3426152 * 2 ^ 59
def prefixEnd_3426152 : Nat := 4983230072969 + 3 ^ 40 * 3426152 * 2
def baseEnd_3426152 : Nat := 1172841847575456265495613

theorem tailTrace_3426152 : CollatzResearch.WordTrace tailWord_3426152 prefixEnd_3426152 1172841847575456265495613 := by
  unfold tailWord_3426152
  simp only [CollatzResearch.WordTrace]
  refine ⟨62481014741821959510660355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83308019655762612680880473 62481014741821959510660355)
  ·
    refine ⟨93721522112732939265990533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62481014741821959510660355 93721522112732939265990533)
    ·
      refine ⟨17572785396137426112373225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93721522112732939265990533 17572785396137426112373225)
      ·
        refine ⟨13179589047103069584279919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17572785396137426112373225 13179589047103069584279919)
        ·
          refine ⟨19769383570654604376419879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13179589047103069584279919 19769383570654604376419879)
          ·
            refine ⟨29654075355981906564629819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19769383570654604376419879 29654075355981906564629819)
            ·
              refine ⟨44481113033972859846944729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29654075355981906564629819 44481113033972859846944729)
              ·
                refine ⟨33360834775479644885208547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44481113033972859846944729 33360834775479644885208547)
                ·
                  refine ⟨50041252163219467327812821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33360834775479644885208547 50041252163219467327812821)
                  ·
                    refine ⟨1172841847575456265495613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50041252163219467327812821 1172841847575456265495613)
                    ·
                      rfl

theorem cell22_3426152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_3426152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426152 prefixEnd_3426152 := by exact prefixLift 3426152
  have htrace : WordTrace (prefixWord ++ tailWord_3426152) baseStart_3426152 baseEnd_3426152 := by
    simpa [prefixWord, tailWord_3426152, baseEnd_3426152] using wordTrace_append hprefix tailTrace_3426152
  have hstable : (prefixWord ++ tailWord_3426152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426152).length < 2 ^ (prefixWord ++ tailWord_3426152).sum := by decide
  have hdescent : baseEnd_3426152 < baseStart_3426152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426158 : List Nat := [4, 1, 2, 3, 1, 1, 1, 5, 1, 3]
def baseStart_3426158 : Nat := 118140960795 + 3426158 * 2 ^ 59
def prefixEnd_3426158 : Nat := 4983230072969 + 3 ^ 40 * 3426158 * 2
def baseEnd_3426158 : Nat := 1172843901498074249845595

theorem tailTrace_3426158 : CollatzResearch.WordTrace tailWord_3426158 prefixEnd_3426158 1172843901498074249845595 := by
  unfold tailWord_3426158
  simp only [CollatzResearch.WordTrace]
  refine ⟨15620281040202772755754891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83308165547748121364026085 15620281040202772755754891)
  ·
    refine ⟨23430421560304159133632337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15620281040202772755754891 23430421560304159133632337)
    ·
      refine ⟨17572816170228119350224253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23430421560304159133632337 17572816170228119350224253)
      ·
        refine ⟨6589806063835544756334095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17572816170228119350224253 6589806063835544756334095)
        ·
          refine ⟨9884709095753317134501143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6589806063835544756334095 9884709095753317134501143)
          ·
            refine ⟨14827063643629975701751715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9884709095753317134501143 14827063643629975701751715)
            ·
              refine ⟨22240595465444963552627573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14827063643629975701751715 22240595465444963552627573)
              ·
                refine ⟨2085055824885465333058835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22240595465444963552627573 2085055824885465333058835)
                ·
                  refine ⟨3127583737328197999588253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2085055824885465333058835 3127583737328197999588253)
                  ·
                    refine ⟨1172843901498074249845595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3127583737328197999588253 1172843901498074249845595)
                    ·
                      rfl

theorem cell22_3426158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_3426158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426158 prefixEnd_3426158 := by exact prefixLift 3426158
  have htrace : WordTrace (prefixWord ++ tailWord_3426158) baseStart_3426158 baseEnd_3426158 := by
    simpa [prefixWord, tailWord_3426158, baseEnd_3426158] using wordTrace_append hprefix tailTrace_3426158
  have hstable : (prefixWord ++ tailWord_3426158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426158).length < 2 ^ (prefixWord ++ tailWord_3426158).sum := by decide
  have hdescent : baseEnd_3426158 < baseStart_3426158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426229 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 4, 4]
def baseStart_3426229 : Nat := 118140960795 + 3426229 * 2 ^ 59
def prefixEnd_3426229 : Nat := 4983230072969 + 3 ^ 40 * 3426229 * 2
def baseEnd_3426229 : Nat := 1172868206249053731320377

theorem tailTrace_3426229 : CollatzResearch.WordTrace tailWord_3426229 prefixEnd_3426229 1172868206249053731320377 := by
  unfold tailWord_3426229
  simp only [CollatzResearch.WordTrace]
  refine ⟨124964837904364961171873741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83309891936243307447915827 124964837904364961171873741)
  ·
    refine ⟨46861814214136860439452653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124964837904364961171873741 46861814214136860439452653)
    ·
      refine ⟨17573180330301322664794745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46861814214136860439452653 17573180330301322664794745)
      ·
        refine ⟨13179885247725991998596059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17573180330301322664794745 13179885247725991998596059)
        ·
          refine ⟨19769827871588987997894089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13179885247725991998596059 19769827871588987997894089)
          ·
            refine ⟨14827370903691740998420567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19769827871588987997894089 14827370903691740998420567)
            ·
              refine ⟨22241056355537611497630851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14827370903691740998420567 22241056355537611497630851)
              ·
                refine ⟨33361584533306417246446277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22241056355537611497630851 33361584533306417246446277)
                ·
                  refine ⟨6255297099994953233708677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33361584533306417246446277 6255297099994953233708677)
                  ·
                    refine ⟨1172868206249053731320377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6255297099994953233708677 1172868206249053731320377)
                    ·
                      rfl

theorem cell22_3426229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_3426229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426229 prefixEnd_3426229 := by exact prefixLift 3426229
  have htrace : WordTrace (prefixWord ++ tailWord_3426229) baseStart_3426229 baseEnd_3426229 := by
    simpa [prefixWord, tailWord_3426229, baseEnd_3426229] using wordTrace_append hprefix tailTrace_3426229
  have hstable : (prefixWord ++ tailWord_3426229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426229).length < 2 ^ (prefixWord ++ tailWord_3426229).sum := by decide
  have hdescent : baseEnd_3426229 < baseStart_3426229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426248 : List Nat := [2, 1, 3, 1, 4, 1, 4, 1, 2, 3]
def baseStart_3426248 : Nat := 118140960795 + 3426248 * 2 ^ 59
def prefixEnd_3426248 : Nat := 4983230072969 + 3 ^ 40 * 3426248 * 2
def baseEnd_3426248 : Nat := 1172874710337344015095319

theorem tailTrace_3426248 : CollatzResearch.WordTrace tailWord_3426248 prefixEnd_3426248 1172874710337344015095319 := by
  unfold tailWord_3426248
  simp only [CollatzResearch.WordTrace]
  refine ⟨62482765445648063708407699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83310353927530751611210265 62482765445648063708407699)
  ·
    refine ⟨93724148168472095562611549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62482765445648063708407699 93724148168472095562611549)
    ·
      refine ⟨35146555563177035835979331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93724148168472095562611549 35146555563177035835979331)
      ·
        refine ⟨52719833344765553753968997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35146555563177035835979331 52719833344765553753968997)
        ·
          refine ⟨9884968752143541328869187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52719833344765553753968997 9884968752143541328869187)
          ·
            refine ⟨14827453128215311993303781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9884968752143541328869187 14827453128215311993303781)
            ·
              refine ⟨2780147461540370998744459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14827453128215311993303781 2780147461540370998744459)
              ·
                refine ⟨4170221192310556498116689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2780147461540370998744459 4170221192310556498116689)
                ·
                  refine ⟨3127665894232917373587517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4170221192310556498116689 3127665894232917373587517)
                  ·
                    refine ⟨1172874710337344015095319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3127665894232917373587517 1172874710337344015095319)
                    ·
                      rfl

theorem cell22_3426248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_3426248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426248 prefixEnd_3426248 := by exact prefixLift 3426248
  have htrace : WordTrace (prefixWord ++ tailWord_3426248) baseStart_3426248 baseEnd_3426248 := by
    simpa [prefixWord, tailWord_3426248, baseEnd_3426248] using wordTrace_append hprefix tailTrace_3426248
  have hstable : (prefixWord ++ tailWord_3426248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426248).length < 2 ^ (prefixWord ++ tailWord_3426248).sum := by decide
  have hdescent : baseEnd_3426248 < baseStart_3426248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426257 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 4, 6]
def baseStart_3426257 : Nat := 118140960795 + 3426257 * 2 ^ 59
def prefixEnd_3426257 : Nat := 4983230072969 + 3 ^ 40 * 3426257 * 2
def baseEnd_3426257 : Nat := 1172877791221270991620291

theorem tailTrace_3426257 : CollatzResearch.WordTrace tailWord_3426257 prefixEnd_3426257 1172877791221270991620291 := by
  unfold tailWord_3426257
  simp only [CollatzResearch.WordTrace]
  refine ⟨124965859148263521953893025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83310572765509014635928683 124965859148263521953893025)
  ·
    refine ⟨93724394361197641465419769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124965859148263521953893025 93724394361197641465419769)
    ·
      refine ⟨70293295770898231099064827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93724394361197641465419769 70293295770898231099064827)
      ·
        refine ⟨105439943656347346648597241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70293295770898231099064827 105439943656347346648597241)
        ·
          refine ⟨79079957742260509986447931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105439943656347346648597241 79079957742260509986447931)
          ·
            refine ⟨118619936613390764979671897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79079957742260509986447931 118619936613390764979671897)
            ·
              refine ⟨88964952460043073734753923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118619936613390764979671897 88964952460043073734753923)
              ·
                refine ⟨133447428690064610602130885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88964952460043073734753923 133447428690064610602130885)
                ·
                  refine ⟨25021392879387114487899541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133447428690064610602130885 25021392879387114487899541)
                  ·
                    refine ⟨1172877791221270991620291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25021392879387114487899541 1172877791221270991620291)
                    ·
                      rfl

theorem cell22_3426257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_3426257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426257 prefixEnd_3426257 := by exact prefixLift 3426257
  have htrace : WordTrace (prefixWord ++ tailWord_3426257) baseStart_3426257 baseEnd_3426257 := by
    simpa [prefixWord, tailWord_3426257, baseEnd_3426257] using wordTrace_append hprefix tailTrace_3426257
  have hstable : (prefixWord ++ tailWord_3426257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426257).length < 2 ^ (prefixWord ++ tailWord_3426257).sum := by decide
  have hdescent : baseEnd_3426257 < baseStart_3426257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426272 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 9]
def baseStart_3426272 : Nat := 118140960795 + 3426272 * 2 ^ 59
def prefixEnd_3426272 : Nat := 4983230072969 + 3 ^ 40 * 3426272 * 2
def baseEnd_3426272 : Nat := 390960975342605317498415

theorem tailTrace_3426272 : CollatzResearch.WordTrace tailWord_3426272 prefixEnd_3426272 390960975342605317498415 := by
  unfold tailWord_3426272
  simp only [CollatzResearch.WordTrace]
  refine ⟨62483203121604589757844535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83310937495472786343792713 62483203121604589757844535)
  ·
    refine ⟨93724804682406884636766803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62483203121604589757844535 93724804682406884636766803)
    ·
      refine ⟨140587207023610326955150205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93724804682406884636766803 140587207023610326955150205)
      ·
        refine ⟨52720202633853872608181327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140587207023610326955150205 52720202633853872608181327)
        ·
          refine ⟨79080303950780808912271991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52720202633853872608181327 79080303950780808912271991)
          ·
            refine ⟨118620455926171213368407987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79080303950780808912271991 118620455926171213368407987)
            ·
              refine ⟨177930683889256820052611981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118620455926171213368407987 177930683889256820052611981)
              ·
                refine ⟨66724006458471307519729493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177930683889256820052611981 66724006458471307519729493)
                ·
                  refine ⟨390960975342605317498415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66724006458471307519729493 390960975342605317498415)
                  ·
                    rfl

theorem cell22_3426272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 9].length) (baseStart_3426272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426272 prefixEnd_3426272 := by exact prefixLift 3426272
  have htrace : WordTrace (prefixWord ++ tailWord_3426272) baseStart_3426272 baseEnd_3426272 := by
    simpa [prefixWord, tailWord_3426272, baseEnd_3426272] using wordTrace_append hprefix tailTrace_3426272
  have hstable : (prefixWord ++ tailWord_3426272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426272).length < 2 ^ (prefixWord ++ tailWord_3426272).sum := by decide
  have hdescent : baseEnd_3426272 < baseStart_3426272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426340 : List Nat := [2, 3, 1, 4, 3, 1, 1, 2, 5]
def baseStart_3426340 : Nat := 118140960795 + 3426340 * 2 ^ 59
def prefixEnd_3426340 : Nat := 4983230072969 + 3 ^ 40 * 3426340 * 2
def baseEnd_3426340 : Nat := 390968734605828813931679

theorem tailTrace_3426340 : CollatzResearch.WordTrace tailWord_3426340 prefixEnd_3426340 390968734605828813931679 := by
  unfold tailWord_3426340
  simp only [CollatzResearch.WordTrace]
  refine ⟨62484443203481413564582237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83312590937975218086109649 62484443203481413564582237)
  ·
    refine ⟨23431666201305530086718339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62484443203481413564582237 23431666201305530086718339)
    ·
      refine ⟨35147499301958295130077509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23431666201305530086718339 35147499301958295130077509)
      ·
        refine ⟨6590156119117180336889533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35147499301958295130077509 6590156119117180336889533)
        ·
          refine ⟨2471308544668942626333575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6590156119117180336889533 2471308544668942626333575)
          ·
            refine ⟨3706962817003413939500363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2471308544668942626333575 3706962817003413939500363)
            ·
              refine ⟨5560444225505120909250545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3706962817003413939500363 5560444225505120909250545)
              ·
                refine ⟨4170333169128840681937909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5560444225505120909250545 4170333169128840681937909)
                ·
                  refine ⟨390968734605828813931679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4170333169128840681937909 390968734605828813931679)
                  ·
                    rfl

theorem cell22_3426340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_3426340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426340 prefixEnd_3426340 := by exact prefixLift 3426340
  have htrace : WordTrace (prefixWord ++ tailWord_3426340) baseStart_3426340 baseEnd_3426340 := by
    simpa [prefixWord, tailWord_3426340, baseEnd_3426340] using wordTrace_append hprefix tailTrace_3426340
  have hstable : (prefixWord ++ tailWord_3426340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426340).length < 2 ^ (prefixWord ++ tailWord_3426340).sum := by decide
  have hdescent : baseEnd_3426340 < baseStart_3426340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426364 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 3, 6]
def baseStart_3426364 : Nat := 118140960795 + 3426364 * 2 ^ 59
def prefixEnd_3426364 : Nat := 4983230072969 + 3 ^ 40 * 3426364 * 2
def baseEnd_3426364 : Nat := 1172914419507958379194963

theorem tailTrace_3426364 : CollatzResearch.WordTrace tailWord_3426364 prefixEnd_3426364 1172914419507958379194963 := by
  unfold tailWord_3426364
  simp only [CollatzResearch.WordTrace]
  refine ⟨62484880879437939614019073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83313174505917252818692097 62484880879437939614019073)
  ·
    refine ⟨46863660659578454710514305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62484880879437939614019073 46863660659578454710514305)
    ·
      refine ⟨35147745494683841032885729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46863660659578454710514305 35147745494683841032885729)
      ·
        refine ⟨26360809121012880774664297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35147745494683841032885729 26360809121012880774664297)
        ·
          refine ⟨19770606840759660580998223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26360809121012880774664297 19770606840759660580998223)
          ·
            refine ⟨29655910261139490871497335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19770606840759660580998223 29655910261139490871497335)
            ·
              refine ⟨44483865391709236307246003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29655910261139490871497335 44483865391709236307246003)
              ·
                refine ⟨66725798087563854460869005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44483865391709236307246003 66725798087563854460869005)
                ·
                  refine ⟨25022174282836445422825877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66725798087563854460869005 25022174282836445422825877)
                  ·
                    refine ⟨1172914419507958379194963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25022174282836445422825877 1172914419507958379194963)
                    ·
                      rfl

theorem cell22_3426364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_3426364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426364 prefixEnd_3426364 := by exact prefixLift 3426364
  have htrace : WordTrace (prefixWord ++ tailWord_3426364) baseStart_3426364 baseEnd_3426364 := by
    simpa [prefixWord, tailWord_3426364, baseEnd_3426364] using wordTrace_append hprefix tailTrace_3426364
  have hstable : (prefixWord ++ tailWord_3426364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426364).length < 2 ^ (prefixWord ++ tailWord_3426364).sum := by decide
  have hdescent : baseEnd_3426364 < baseStart_3426364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426381 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_3426381 : Nat := 118140960795 + 3426381 * 2 ^ 59
def prefixEnd_3426381 : Nat := 4983230072969 + 3 ^ 40 * 3426381 * 2
def baseEnd_3426381 : Nat := 1172920238955376001519911

theorem tailTrace_3426381 : CollatzResearch.WordTrace tailWord_3426381 prefixEnd_3426381 1172920238955376001519911 := by
  unfold tailWord_3426381
  simp only [CollatzResearch.WordTrace]
  refine ⟨124970381799814291131406997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83313587866542860754271331 124970381799814291131406997)
  ·
    refine ⟨5857986646866294896784703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 124970381799814291131406997 5857986646866294896784703)
    ·
      refine ⟨8786979970299442345177055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5857986646866294896784703 8786979970299442345177055)
      ·
        refine ⟨13180469955449163517765583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8786979970299442345177055 13180469955449163517765583)
        ·
          refine ⟨19770704933173745276648375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13180469955449163517765583 19770704933173745276648375)
          ·
            refine ⟨29656057399760617914972563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19770704933173745276648375 29656057399760617914972563)
            ·
              refine ⟨44484086099640926872458845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29656057399760617914972563 44484086099640926872458845)
              ·
                refine ⟨16681532287365347577172067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44484086099640926872458845 16681532287365347577172067)
                ·
                  refine ⟨25022298431048021365758101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16681532287365347577172067 25022298431048021365758101)
                  ·
                    refine ⟨1172920238955376001519911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25022298431048021365758101 1172920238955376001519911)
                    ·
                      rfl

theorem cell22_3426381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_3426381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426381 prefixEnd_3426381 := by exact prefixLift 3426381
  have htrace : WordTrace (prefixWord ++ tailWord_3426381) baseStart_3426381 baseEnd_3426381 := by
    simpa [prefixWord, tailWord_3426381, baseEnd_3426381] using wordTrace_append hprefix tailTrace_3426381
  have hstable : (prefixWord ++ tailWord_3426381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426381).length < 2 ^ (prefixWord ++ tailWord_3426381).sum := by decide
  have hdescent : baseEnd_3426381 < baseStart_3426381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426396 : List Nat := [2, 2, 4, 1, 1, 4, 8]
def baseStart_3426396 : Nat := 118140960795 + 3426396 * 2 ^ 59
def prefixEnd_3426396 : Nat := 4983230072969 + 3 ^ 40 * 3426396 * 2
def baseEnd_3426396 : Nat := 43441680509700776384995

theorem tailTrace_3426396 : CollatzResearch.WordTrace tailWord_3426396 prefixEnd_3426396 43441680509700776384995 := by
  unfold tailWord_3426396
  simp only [CollatzResearch.WordTrace]
  refine ⟨62485464447379974346601521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83313952596506632462135361 62485464447379974346601521)
  ·
    refine ⟨46864098335534980759951141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62485464447379974346601521 46864098335534980759951141)
    ·
      refine ⟨8787018437912808892490839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46864098335534980759951141 8787018437912808892490839)
      ·
        refine ⟨13180527656869213338736259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8787018437912808892490839 13180527656869213338736259)
        ·
          refine ⟨19770791485303820008104389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13180527656869213338736259 19770791485303820008104389)
          ·
            refine ⟨3707023403494466251519573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19770791485303820008104389 3707023403494466251519573)
            ·
              refine ⟨43441680509700776384995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3707023403494466251519573 43441680509700776384995)
              ·
                rfl

theorem cell22_3426396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 8].length) (baseStart_3426396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426396 prefixEnd_3426396 := by exact prefixLift 3426396
  have htrace : WordTrace (prefixWord ++ tailWord_3426396) baseStart_3426396 baseEnd_3426396 := by
    simpa [prefixWord, tailWord_3426396, baseEnd_3426396] using wordTrace_append hprefix tailTrace_3426396
  have hstable : (prefixWord ++ tailWord_3426396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426396).length < 2 ^ (prefixWord ++ tailWord_3426396).sum := by decide
  have hdescent : baseEnd_3426396 < baseStart_3426396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426402 : List Nat := [3, 3, 2, 2, 2, 1, 3, 2, 4]
def baseStart_3426402 : Nat := 118140960795 + 3426402 * 2 ^ 59
def prefixEnd_3426402 : Nat := 4983230072969 + 3 ^ 40 * 3426402 * 2
def baseEnd_3426402 : Nat := 390975809228179648914949

theorem tailTrace_3426402 : CollatzResearch.WordTrace tailWord_3426402 prefixEnd_3426402 390975809228179648914949 := by
  unfold tailWord_3426402
  simp only [CollatzResearch.WordTrace]
  refine ⟨31242786933184552929480365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83314098488492141145280973 31242786933184552929480365)
  ·
    refine ⟨11716045099944207348555137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31242786933184552929480365 11716045099944207348555137)
    ·
      refine ⟨8787033824958155511416353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11716045099944207348555137 8787033824958155511416353)
      ·
        refine ⟨6590275368718616633562265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8787033824958155511416353 6590275368718616633562265)
        ·
          refine ⟨4942706526538962475171699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6590275368718616633562265 4942706526538962475171699)
          ·
            refine ⟨7414059789808443712757549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4942706526538962475171699 7414059789808443712757549)
            ·
              refine ⟨2780272421178166392284081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7414059789808443712757549 2780272421178166392284081)
              ·
                refine ⟨2085204315883624794213061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2780272421178166392284081 2085204315883624794213061)
                ·
                  refine ⟨390975809228179648914949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2085204315883624794213061 390975809228179648914949)
                  ·
                    rfl

theorem cell22_3426402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_3426402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426402 prefixEnd_3426402 := by exact prefixLift 3426402
  have htrace : WordTrace (prefixWord ++ tailWord_3426402) baseStart_3426402 baseEnd_3426402 := by
    simpa [prefixWord, tailWord_3426402, baseEnd_3426402] using wordTrace_append hprefix tailTrace_3426402
  have hstable : (prefixWord ++ tailWord_3426402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426402).length < 2 ^ (prefixWord ++ tailWord_3426402).sum := by decide
  have hdescent : baseEnd_3426402 < baseStart_3426402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426409 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 2, 6]
def baseStart_3426409 : Nat := 118140960795 + 3426409 * 2 ^ 59
def prefixEnd_3426409 : Nat := 4983230072969 + 3 ^ 40 * 3426409 * 2
def baseEnd_3426409 : Nat := 1172929823927593261819825

theorem tailTrace_3426409 : CollatzResearch.WordTrace tailWord_3426409 prefixEnd_3426409 1172929823927593261819825 := by
  unfold tailWord_3426409
  simp only [CollatzResearch.WordTrace]
  refine ⟨124971403043712851913426281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83314268695808567942284187 124971403043712851913426281)
  ·
    refine ⟨93728552282784638935069711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124971403043712851913426281 93728552282784638935069711)
    ·
      refine ⟨140592828424176958402604567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93728552282784638935069711 140592828424176958402604567)
      ·
        refine ⟨210889242636265437603906851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140592828424176958402604567 210889242636265437603906851)
        ·
          refine ⟨316333863954398156405860277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210889242636265437603906851 316333863954398156405860277)
          ·
            refine ⟨29656299745724827163049401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 316333863954398156405860277 29656299745724827163049401)
            ·
              refine ⟨22242224809293620372287051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29656299745724827163049401 22242224809293620372287051)
              ·
                refine ⟨33363337213940430558430577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22242224809293620372287051 33363337213940430558430577)
                ·
                  refine ⟨25022502910455322918822933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33363337213940430558430577 25022502910455322918822933)
                  ·
                    refine ⟨1172929823927593261819825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25022502910455322918822933 1172929823927593261819825)
                    ·
                      rfl

theorem cell22_3426409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_3426409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426409 prefixEnd_3426409 := by exact prefixLift 3426409
  have htrace : WordTrace (prefixWord ++ tailWord_3426409) baseStart_3426409 baseEnd_3426409 := by
    simpa [prefixWord, tailWord_3426409, baseEnd_3426409] using wordTrace_append hprefix tailTrace_3426409
  have hstable : (prefixWord ++ tailWord_3426409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426409).length < 2 ^ (prefixWord ++ tailWord_3426409).sum := by decide
  have hdescent : baseEnd_3426409 < baseStart_3426409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426501 : List Nat := [1, 3, 1, 1, 1, 1, 6, 2, 1, 5]
def baseStart_3426501 : Nat := 118140960795 + 3426501 * 2 ^ 59
def prefixEnd_3426501 : Nat := 4983230072969 + 3 ^ 40 * 3426501 * 2
def baseEnd_3426501 : Nat := 1172961317407735688519543

theorem tailTrace_3426501 : CollatzResearch.WordTrace tailWord_3426501 prefixEnd_3426501 1172961317407735688519543 := by
  unfold tailWord_3426501
  simp only [CollatzResearch.WordTrace]
  refine ⟨124974758559379551625775357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83316505706253034417183571 124974758559379551625775357)
  ·
    refine ⟨46865534459767331859665759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124974758559379551625775357 46865534459767331859665759)
    ·
      refine ⟨70298301689650997789498639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46865534459767331859665759 70298301689650997789498639)
      ·
        refine ⟨105447452534476496684247959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70298301689650997789498639 105447452534476496684247959)
        ·
          refine ⟨158171178801714745026371939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105447452534476496684247959 158171178801714745026371939)
          ·
            refine ⟨237256768202572117539557909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158171178801714745026371939 237256768202572117539557909)
            ·
              refine ⟨11121411009495568009666777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 237256768202572117539557909 11121411009495568009666777)
              ·
                refine ⟨8341058257121676007250083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11121411009495568009666777 8341058257121676007250083)
                ·
                  refine ⟨12511587385682514010875125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8341058257121676007250083 12511587385682514010875125)
                  ·
                    refine ⟨1172961317407735688519543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12511587385682514010875125 1172961317407735688519543)
                    ·
                      rfl

theorem cell22_3426501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_3426501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426501 prefixEnd_3426501 := by exact prefixLift 3426501
  have htrace : WordTrace (prefixWord ++ tailWord_3426501) baseStart_3426501 baseEnd_3426501 := by
    simpa [prefixWord, tailWord_3426501, baseEnd_3426501] using wordTrace_append hprefix tailTrace_3426501
  have hstable : (prefixWord ++ tailWord_3426501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426501).length < 2 ^ (prefixWord ++ tailWord_3426501).sum := by decide
  have hdescent : baseEnd_3426501 < baseStart_3426501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426535 : List Nat := [1, 1, 5, 3, 1, 3, 1, 1, 1, 5]
def baseStart_3426535 : Nat := 118140960795 + 3426535 * 2 ^ 59
def prefixEnd_3426535 : Nat := 4983230072969 + 3 ^ 40 * 3426535 * 2
def baseEnd_3426535 : Nat := 1172972956302570933169439

theorem tailTrace_3426535 : CollatzResearch.WordTrace tailWord_3426535 prefixEnd_3426535 1172972956302570933169439 := by
  unfold tailWord_3426535
  simp only [CollatzResearch.WordTrace]
  refine ⟨124975998641256375432513059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83317332427504250288342039 124975998641256375432513059)
  ·
    refine ⟨187463997961884563148769589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124975998641256375432513059 187463997961884563148769589)
    ·
      refine ⟨17574749808926677795197149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187463997961884563148769589 17574749808926677795197149)
      ·
        refine ⟨6590531178347504173198931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17574749808926677795197149 6590531178347504173198931)
        ·
          refine ⟨9885796767521256259798397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6590531178347504173198931 9885796767521256259798397)
          ·
            refine ⟨3707173787820471097424399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9885796767521256259798397 3707173787820471097424399)
            ·
              refine ⟨5560760681730706646136599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3707173787820471097424399 5560760681730706646136599)
              ·
                refine ⟨8341141022596059969204899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5560760681730706646136599 8341141022596059969204899)
                ·
                  refine ⟨12511711533894089953807349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8341141022596059969204899 12511711533894089953807349)
                  ·
                    refine ⟨1172972956302570933169439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12511711533894089953807349 1172972956302570933169439)
                    ·
                      rfl

theorem cell22_3426535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_3426535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426535 prefixEnd_3426535 := by exact prefixLift 3426535
  have htrace : WordTrace (prefixWord ++ tailWord_3426535) baseStart_3426535 baseEnd_3426535 := by
    simpa [prefixWord, tailWord_3426535, baseEnd_3426535] using wordTrace_append hprefix tailTrace_3426535
  have hstable : (prefixWord ++ tailWord_3426535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426535).length < 2 ^ (prefixWord ++ tailWord_3426535).sum := by decide
  have hdescent : baseEnd_3426535 < baseStart_3426535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426717 : List Nat := [1, 4, 2, 1, 4, 2, 2, 6]
def baseStart_3426717 : Nat := 118140960795 + 3426717 * 2 ^ 59
def prefixEnd_3426717 : Nat := 4983230072969 + 3 ^ 40 * 3426717 * 2
def baseEnd_3426717 : Nat := 130337250957998125013209

theorem tailTrace_3426717 : CollatzResearch.WordTrace tailWord_3426717 prefixEnd_3426717 130337250957998125013209 := by
  unfold tailWord_3426717
  simp only [CollatzResearch.WordTrace]
  refine ⟨124982636726597020515638405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83321757817731347010425603 124982636726597020515638405)
  ·
    refine ⟨23434244386236941346682201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124982636726597020515638405 23434244386236941346682201)
    ·
      refine ⟨17575683289677706010011651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23434244386236941346682201 17575683289677706010011651)
      ·
        refine ⟨26363524934516559015017477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17575683289677706010011651 26363524934516559015017477)
        ·
          refine ⟨4943160925221854815315777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26363524934516559015017477 4943160925221854815315777)
          ·
            refine ⟨3707370693916391111486833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4943160925221854815315777 3707370693916391111486833)
            ·
              refine ⟨2780528020437293333615125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3707370693916391111486833 2780528020437293333615125)
              ·
                refine ⟨130337250957998125013209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2780528020437293333615125 130337250957998125013209)
                ·
                  rfl

theorem cell22_3426717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 6].length) (baseStart_3426717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426717 prefixEnd_3426717 := by exact prefixLift 3426717
  have htrace : WordTrace (prefixWord ++ tailWord_3426717) baseStart_3426717 baseEnd_3426717 := by
    simpa [prefixWord, tailWord_3426717, baseEnd_3426717] using wordTrace_append hprefix tailTrace_3426717
  have hstable : (prefixWord ++ tailWord_3426717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426717).length < 2 ^ (prefixWord ++ tailWord_3426717).sum := by decide
  have hdescent : baseEnd_3426717 < baseStart_3426717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426833 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 1, 9]
def baseStart_3426833 : Nat := 118140960795 + 3426833 * 2 ^ 59
def prefixEnd_3426833 : Nat := 4983230072969 + 3 ^ 40 * 3426833 * 2
def baseEnd_3426833 : Nat := 1173074967792597489218525

theorem tailTrace_3426833 : CollatzResearch.WordTrace tailWord_3426833 prefixEnd_3426833 1173074967792597489218525 := by
  unfold tailWord_3426833
  simp only [CollatzResearch.WordTrace]
  refine ⟨124986867594176772326861153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83324578396117848217907435 124986867594176772326861153)
  ·
    refine ⟨93740150695632579245145865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124986867594176772326861153 93740150695632579245145865)
    ·
      refine ⟨70305113021724434433859399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93740150695632579245145865 70305113021724434433859399)
      ·
        refine ⟨105457669532586651650789099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70305113021724434433859399 105457669532586651650789099)
        ·
          refine ⟨158186504298879977476183649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105457669532586651650789099 158186504298879977476183649)
          ·
            refine ⟨118639878224159983107137737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158186504298879977476183649 118639878224159983107137737)
            ·
              refine ⟨88979908668119987330353303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118639878224159983107137737 88979908668119987330353303)
              ·
                refine ⟨133469863002179980995529955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88979908668119987330353303 133469863002179980995529955)
                ·
                  refine ⟨200204794503269971493294933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133469863002179980995529955 200204794503269971493294933)
                  ·
                    refine ⟨1173074967792597489218525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 200204794503269971493294933 1173074967792597489218525)
                    ·
                      rfl

theorem cell22_3426833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_3426833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426833 prefixEnd_3426833 := by exact prefixLift 3426833
  have htrace : WordTrace (prefixWord ++ tailWord_3426833) baseStart_3426833 baseEnd_3426833 := by
    simpa [prefixWord, tailWord_3426833, baseEnd_3426833] using wordTrace_append hprefix tailTrace_3426833
  have hstable : (prefixWord ++ tailWord_3426833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426833).length < 2 ^ (prefixWord ++ tailWord_3426833).sum := by decide
  have hdescent : baseEnd_3426833 < baseStart_3426833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426835 : List Nat := [1, 1, 1, 2, 1, 5, 5, 6]
def baseStart_3426835 : Nat := 118140960795 + 3426835 * 2 ^ 59
def prefixEnd_3426835 : Nat := 4983230072969 + 3 ^ 40 * 3426835 * 2
def baseEnd_3426835 : Nat := 130341739159274461185391

theorem tailTrace_3426835 : CollatzResearch.WordTrace tailWord_3426835 prefixEnd_3426835 130341739159274461185391 := by
  unfold tailWord_3426835
  simp only [CollatzResearch.WordTrace]
  refine ⟨124986940540169526668433959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83324627026779684445622639 124986940540169526668433959)
  ·
    refine ⟨187480410810254290002650939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124986940540169526668433959 187480410810254290002650939)
    ·
      refine ⟨281220616215381435003976409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187480410810254290002650939 281220616215381435003976409)
      ·
        refine ⟨210915462161536076252982307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281220616215381435003976409 210915462161536076252982307)
        ·
          refine ⟨316373193242304114379473461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210915462161536076252982307 316373193242304114379473461)
          ·
            refine ⟨29659986866466010723075637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 316373193242304114379473461 29659986866466010723075637)
            ·
              refine ⟨2780623768731188505288341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29659986866466010723075637 2780623768731188505288341)
              ·
                refine ⟨130341739159274461185391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2780623768731188505288341 130341739159274461185391)
                ·
                  rfl

theorem cell22_3426835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 6].length) (baseStart_3426835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426835 prefixEnd_3426835 := by exact prefixLift 3426835
  have htrace : WordTrace (prefixWord ++ tailWord_3426835) baseStart_3426835 baseEnd_3426835 := by
    simpa [prefixWord, tailWord_3426835, baseEnd_3426835] using wordTrace_append hprefix tailTrace_3426835
  have hstable : (prefixWord ++ tailWord_3426835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426835).length < 2 ^ (prefixWord ++ tailWord_3426835).sum := by decide
  have hdescent : baseEnd_3426835 < baseStart_3426835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426852 : List Nat := [2, 3, 1, 5, 1, 1, 9]
def baseStart_3426852 : Nat := 118140960795 + 3426852 * 2 ^ 59
def prefixEnd_3426852 : Nat := 4983230072969 + 3 ^ 40 * 3426852 * 2
def baseEnd_3426852 : Nat := 43447461921514361962721

theorem tailTrace_3426852 : CollatzResearch.WordTrace tailWord_3426852 prefixEnd_3426852 43447461921514361962721 := by
  unfold tailWord_3426852
  simp only [CollatzResearch.WordTrace]
  refine ⟨62493780290553969285901405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83325040387405292381201873 62493780290553969285901405)
  ·
    refine ⟨23435167608957738482213027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62493780290553969285901405 23435167608957738482213027)
    ·
      refine ⟨35152751413436607723319541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23435167608957738482213027 35152751413436607723319541)
      ·
        refine ⟨3295570445009681974061207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35152751413436607723319541 3295570445009681974061207)
        ·
          refine ⟨4943355667514522961091811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3295570445009681974061207 4943355667514522961091811)
          ·
            refine ⟨7415033501271784441637717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4943355667514522961091811 7415033501271784441637717)
            ·
              refine ⟨43447461921514361962721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7415033501271784441637717 43447461921514361962721)
              ·
                rfl

theorem cell22_3426852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 9].length) (baseStart_3426852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426852 prefixEnd_3426852 := by exact prefixLift 3426852
  have htrace : WordTrace (prefixWord ++ tailWord_3426852) baseStart_3426852 baseEnd_3426852 := by
    simpa [prefixWord, tailWord_3426852, baseEnd_3426852] using wordTrace_append hprefix tailTrace_3426852
  have hstable : (prefixWord ++ tailWord_3426852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426852).length < 2 ^ (prefixWord ++ tailWord_3426852).sum := by decide
  have hdescent : baseEnd_3426852 < baseStart_3426852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426856 : List Nat := [2, 1, 5, 2, 1, 3, 1, 2, 2, 3]
def baseStart_3426856 : Nat := 118140960795 + 3426856 * 2 ^ 59
def prefixEnd_3426856 : Nat := 4983230072969 + 3 ^ 40 * 3426856 * 2
def baseEnd_3426856 : Nat := 1173082841162633095893455

theorem tailTrace_3426856 : CollatzResearch.WordTrace tailWord_3426856 prefixEnd_3426856 1173082841162633095893455 := by
  unfold tailWord_3426856
  simp only [CollatzResearch.WordTrace]
  refine ⟨62493853236546723627474211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83325137648728964836632281 62493853236546723627474211)
  ·
    refine ⟨93740779854820085441211317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62493853236546723627474211 93740779854820085441211317)
    ·
      refine ⟨8788198111389383010113561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93740779854820085441211317 8788198111389383010113561)
      ·
        refine ⟨6591148583542037257585171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8788198111389383010113561 6591148583542037257585171)
        ·
          refine ⟨9886722875313055886377757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6591148583542037257585171 9886722875313055886377757)
          ·
            refine ⟨3707521078242395957391659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9886722875313055886377757 3707521078242395957391659)
            ·
              refine ⟨5561281617363593936087489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3707521078242395957391659 5561281617363593936087489)
              ·
                refine ⟨4170961213022695452065617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5561281617363593936087489 4170961213022695452065617)
                ·
                  refine ⟨3128220909767021589049213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4170961213022695452065617 3128220909767021589049213)
                  ·
                    refine ⟨1173082841162633095893455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3128220909767021589049213 1173082841162633095893455)
                    ·
                      rfl

theorem cell22_3426856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_3426856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426856 prefixEnd_3426856 := by exact prefixLift 3426856
  have htrace : WordTrace (prefixWord ++ tailWord_3426856) baseStart_3426856 baseEnd_3426856 := by
    simpa [prefixWord, tailWord_3426856, baseEnd_3426856] using wordTrace_append hprefix tailTrace_3426856
  have hstable : (prefixWord ++ tailWord_3426856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426856).length < 2 ^ (prefixWord ++ tailWord_3426856).sum := by decide
  have hdescent : baseEnd_3426856 < baseStart_3426856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426867 : List Nat := [1, 1, 1, 2, 4, 2, 4, 1, 3, 3]
def baseStart_3426867 : Nat := 118140960795 + 3426867 * 2 ^ 59
def prefixEnd_3426867 : Nat := 4983230072969 + 3 ^ 40 * 3426867 * 2
def baseEnd_3426867 : Nat := 1173086606687432733868421

theorem tailTrace_3426867 : CollatzResearch.WordTrace tailWord_3426867 prefixEnd_3426867 1173086606687432733868421 := by
  unfold tailWord_3426867
  simp only [CollatzResearch.WordTrace]
  refine ⟨124988107676053596133598855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83325405117369064089065903 124988107676053596133598855)
  ·
    refine ⟨187482161514080394200398283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124988107676053596133598855 187482161514080394200398283)
    ·
      refine ⟨281223242271120591300597425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187482161514080394200398283 281223242271120591300597425)
      ·
        refine ⟨210917431703340443475448069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281223242271120591300597425 210917431703340443475448069)
        ·
          refine ⟨39547018444376333151646513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210917431703340443475448069 39547018444376333151646513)
          ·
            refine ⟨29660263833282249863734885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39547018444376333151646513 29660263833282249863734885)
            ·
              refine ⟨5561299468740421849450291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29660263833282249863734885 5561299468740421849450291)
              ·
                refine ⟨8341949203110632774175437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5561299468740421849450291 8341949203110632774175437)
                ·
                  refine ⟨3128230951166487290315789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8341949203110632774175437 3128230951166487290315789)
                  ·
                    refine ⟨1173086606687432733868421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3128230951166487290315789 1173086606687432733868421)
                    ·
                      rfl

theorem cell22_3426867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 3].length) (baseStart_3426867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426867 prefixEnd_3426867 := by exact prefixLift 3426867
  have htrace : WordTrace (prefixWord ++ tailWord_3426867) baseStart_3426867 baseEnd_3426867 := by
    simpa [prefixWord, tailWord_3426867, baseEnd_3426867] using wordTrace_append hprefix tailTrace_3426867
  have hstable : (prefixWord ++ tailWord_3426867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426867).length < 2 ^ (prefixWord ++ tailWord_3426867).sum := by decide
  have hdescent : baseEnd_3426867 < baseStart_3426867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426880 : List Nat := [2, 1, 1, 2, 2, 2, 2, 5, 5]
def baseStart_3426880 : Nat := 118140960795 + 3426880 * 2 ^ 59
def prefixEnd_3426880 : Nat := 4983230072969 + 3 ^ 40 * 3426880 * 2
def baseEnd_3426880 : Nat := 391030352284368344431127

theorem tailTrace_3426880 : CollatzResearch.WordTrace tailWord_3426880 prefixEnd_3426880 391030352284368344431127 := by
  unfold tailWord_3426880
  simp only [CollatzResearch.WordTrace]
  refine ⟨62494290912503249676911047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83325721216670999569214729 62494290912503249676911047)
  ·
    refine ⟨93741436368754874515366571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62494290912503249676911047 93741436368754874515366571)
    ·
      refine ⟨140612154553132311773049857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93741436368754874515366571 140612154553132311773049857)
      ·
        refine ⟨105459115914849233829787393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140612154553132311773049857 105459115914849233829787393)
        ·
          refine ⟨79094336936136925372340545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105459115914849233829787393 79094336936136925372340545)
          ·
            refine ⟨59320752702102694029255409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79094336936136925372340545 59320752702102694029255409)
            ·
              refine ⟨44490564526577020521941557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59320752702102694029255409 44490564526577020521941557)
              ·
                refine ⟨4170990424366595673932021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44490564526577020521941557 4170990424366595673932021)
                ·
                  refine ⟨391030352284368344431127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4170990424366595673932021 391030352284368344431127)
                  ·
                    rfl

theorem cell22_3426880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 5].length) (baseStart_3426880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426880 prefixEnd_3426880 := by exact prefixLift 3426880
  have htrace : WordTrace (prefixWord ++ tailWord_3426880) baseStart_3426880 baseEnd_3426880 := by
    simpa [prefixWord, tailWord_3426880, baseEnd_3426880] using wordTrace_append hprefix tailTrace_3426880
  have hstable : (prefixWord ++ tailWord_3426880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426880).length < 2 ^ (prefixWord ++ tailWord_3426880).sum := by decide
  have hdescent : baseEnd_3426880 < baseStart_3426880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426886 : List Nat := [6, 1, 1, 1, 2, 3, 2, 6]
def baseStart_3426886 : Nat := 118140960795 + 3426886 * 2 ^ 59
def prefixEnd_3426886 : Nat := 4983230072969 + 3 ^ 40 * 3426886 * 2
def baseEnd_3426886 : Nat := 130343678975080335293707

theorem tailTrace_3426886 : CollatzResearch.WordTrace tailWord_3426886 prefixEnd_3426886 130343678975080335293707 := by
  unfold tailWord_3426886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3905900020718273824329391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83325867108656508252360341 3905900020718273824329391)
  ·
    refine ⟨5858850031077410736494087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3905900020718273824329391 5858850031077410736494087)
    ·
      refine ⟨8788275046616116104741131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5858850031077410736494087 8788275046616116104741131)
      ·
        refine ⟨13182412569924174157111697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8788275046616116104741131 13182412569924174157111697)
        ·
          refine ⟨9886809427443130617833773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13182412569924174157111697 9886809427443130617833773)
          ·
            refine ⟨3707553535291173981687665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9886809427443130617833773 3707553535291173981687665)
            ·
              refine ⟨2780665151468380486265749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3707553535291173981687665 2780665151468380486265749)
              ·
                refine ⟨130343678975080335293707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2780665151468380486265749 130343678975080335293707)
                ·
                  rfl

theorem cell22_3426886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_3426886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426886 prefixEnd_3426886 := by exact prefixLift 3426886
  have htrace : WordTrace (prefixWord ++ tailWord_3426886) baseStart_3426886 baseEnd_3426886 := by
    simpa [prefixWord, tailWord_3426886, baseEnd_3426886] using wordTrace_append hprefix tailTrace_3426886
  have hstable : (prefixWord ++ tailWord_3426886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426886).length < 2 ^ (prefixWord ++ tailWord_3426886).sum := by decide
  have hdescent : baseEnd_3426886 < baseStart_3426886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426944 : List Nat := [2, 1, 1, 2, 1, 7, 1, 2, 1, 4]
def baseStart_3426944 : Nat := 118140960795 + 3426944 * 2 ^ 59
def prefixEnd_3426944 : Nat := 4983230072969 + 3 ^ 40 * 3426944 * 2
def baseEnd_3426944 : Nat := 1173112965361030199693185

theorem tailTrace_3426944 : CollatzResearch.WordTrace tailWord_3426944 prefixEnd_3426944 1173112965361030199693185 := by
  unfold tailWord_3426944
  simp only [CollatzResearch.WordTrace]
  refine ⟨62495458048387319142075943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83327277397849758856101257 62495458048387319142075943)
  ·
    refine ⟨93743187072580978713113915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62495458048387319142075943 93743187072580978713113915)
    ·
      refine ⟨140614780608871468069670873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93743187072580978713113915 140614780608871468069670873)
      ·
        refine ⟨105461085456653601052253155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140614780608871468069670873 105461085456653601052253155)
        ·
          refine ⟨158191628184980401578379733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105461085456653601052253155 158191628184980401578379733)
          ·
            refine ⟨3707616285585478161993275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 158191628184980401578379733 3707616285585478161993275)
            ·
              refine ⟨5561424428378217242989913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3707616285585478161993275 5561424428378217242989913)
              ·
                refine ⟨4171068321283662932242435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5561424428378217242989913 4171068321283662932242435)
                ·
                  refine ⟨6256602481925494398363653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4171068321283662932242435 6256602481925494398363653)
                  ·
                    refine ⟨1173112965361030199693185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6256602481925494398363653 1173112965361030199693185)
                    ·
                      rfl

theorem cell22_3426944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 1, 4].length) (baseStart_3426944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3426944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3426944 prefixEnd_3426944 := by exact prefixLift 3426944
  have htrace : WordTrace (prefixWord ++ tailWord_3426944) baseStart_3426944 baseEnd_3426944 := by
    simpa [prefixWord, tailWord_3426944, baseEnd_3426944] using wordTrace_append hprefix tailTrace_3426944
  have hstable : (prefixWord ++ tailWord_3426944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426944).length < 2 ^ (prefixWord ++ tailWord_3426944).sum := by decide
  have hdescent : baseEnd_3426944 < baseStart_3426944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427032 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 7]
def baseStart_3427032 : Nat := 118140960795 + 3427032 * 2 ^ 59
def prefixEnd_3427032 : Nat := 4983230072969 + 3 ^ 40 * 3427032 * 2
def baseEnd_3427032 : Nat := 391047696519809101164305

theorem tailTrace_3427032 : CollatzResearch.WordTrace tailWord_3427032 prefixEnd_3427032 391047696519809101164305 := by
  unfold tailWord_3427032
  simp only [CollatzResearch.WordTrace]
  refine ⟨62497062860227914656677675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83329417146970552875570233 62497062860227914656677675)
  ·
    refine ⟨93745594290341871985016513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62497062860227914656677675 93745594290341871985016513)
    ·
      refine ⟨70309195717756403988762385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93745594290341871985016513 70309195717756403988762385)
      ·
        refine ⟨52731896788317302991571789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70309195717756403988762385 52731896788317302991571789)
        ·
          refine ⟨19774461295618988621839421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52731896788317302991571789 19774461295618988621839421)
          ·
            refine ⟨7415422985857120733189783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19774461295618988621839421 7415422985857120733189783)
            ·
              refine ⟨11123134478785681099784675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7415422985857120733189783 11123134478785681099784675)
              ·
                refine ⟨16684701718178521649677013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11123134478785681099784675 16684701718178521649677013)
                ·
                  refine ⟨391047696519809101164305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16684701718178521649677013 391047696519809101164305)
                  ·
                    rfl

theorem cell22_3427032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 7].length) (baseStart_3427032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427032 prefixEnd_3427032 := by exact prefixLift 3427032
  have htrace : WordTrace (prefixWord ++ tailWord_3427032) baseStart_3427032 baseEnd_3427032 := by
    simpa [prefixWord, tailWord_3427032, baseEnd_3427032] using wordTrace_append hprefix tailTrace_3427032
  have hstable : (prefixWord ++ tailWord_3427032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427032).length < 2 ^ (prefixWord ++ tailWord_3427032).sum := by decide
  have hdescent : baseEnd_3427032 < baseStart_3427032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427036 : List Nat := [2, 2, 5, 1, 1, 1, 1, 3, 3, 3]
def baseStart_3427036 : Nat := 118140960795 + 3427036 * 2 ^ 59
def prefixEnd_3427036 : Nat := 4983230072969 + 3 ^ 40 * 3427036 * 2
def baseEnd_3427036 : Nat := 1173144458841172626392903

theorem tailTrace_3427036 : CollatzResearch.WordTrace tailWord_3427036 prefixEnd_3427036 1173144458841172626392903 := by
  unfold tailWord_3427036
  simp only [CollatzResearch.WordTrace]
  refine ⟨62497135806220668998250481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83329514408294225331000641 62497135806220668998250481)
  ·
    refine ⟨46872851854665501748687861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62497135806220668998250481 46872851854665501748687861)
    ·
      refine ⟨4394329861374890788939487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46872851854665501748687861 4394329861374890788939487)
      ·
        refine ⟨6591494792062336183409231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4394329861374890788939487 6591494792062336183409231)
        ·
          refine ⟨9887242188093504275113847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6591494792062336183409231 9887242188093504275113847)
          ·
            refine ⟨14830863282140256412670771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9887242188093504275113847 14830863282140256412670771)
            ·
              refine ⟨22246294923210384619006157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14830863282140256412670771 22246294923210384619006157)
              ·
                refine ⟨8342360596203894232127309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22246294923210384619006157 8342360596203894232127309)
                ·
                  refine ⟨3128385223576460337047741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8342360596203894232127309 3128385223576460337047741)
                  ·
                    refine ⟨1173144458841172626392903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3128385223576460337047741 1173144458841172626392903)
                    ·
                      rfl

theorem cell22_3427036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_3427036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427036 prefixEnd_3427036 := by exact prefixLift 3427036
  have htrace : WordTrace (prefixWord ++ tailWord_3427036) baseStart_3427036 baseEnd_3427036 := by
    simpa [prefixWord, tailWord_3427036, baseEnd_3427036] using wordTrace_append hprefix tailTrace_3427036
  have hstable : (prefixWord ++ tailWord_3427036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427036).length < 2 ^ (prefixWord ++ tailWord_3427036).sum := by decide
  have hdescent : baseEnd_3427036 < baseStart_3427036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427070 : List Nat := [4, 2, 2, 1, 2, 3, 1, 3, 1, 3]
def baseStart_3427070 : Nat := 118140960795 + 3427070 * 2 ^ 59
def prefixEnd_3427070 : Nat := 4983230072969 + 3 ^ 40 * 3427070 * 2
def baseEnd_3427070 : Nat := 1173156097736007871042799

theorem tailTrace_3427070 : CollatzResearch.WordTrace tailWord_3427070 prefixEnd_3427070 1173156097736007871042799 := by
  unfold tailWord_3427070
  simp only [CollatzResearch.WordTrace]
  refine ⟨15624438961789770225404833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83330341129545441202159109 15624438961789770225404833)
  ·
    refine ⟨11718329221342327669053625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15624438961789770225404833 11718329221342327669053625)
    ·
      refine ⟨8788746916006745751790219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11718329221342327669053625 8788746916006745751790219)
      ·
        refine ⟨13183120374010118627685329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8788746916006745751790219 13183120374010118627685329)
        ·
          refine ⟨9887340280507588970763997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13183120374010118627685329 9887340280507588970763997)
          ·
            refine ⟨3707752605190345864036499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9887340280507588970763997 3707752605190345864036499)
            ·
              refine ⟨5561628907785518796054749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3707752605190345864036499 5561628907785518796054749)
              ·
                refine ⟨2085610840419569548520531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5561628907785518796054749 2085610840419569548520531)
                ·
                  refine ⟨3128416260629354322780797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2085610840419569548520531 3128416260629354322780797)
                  ·
                    refine ⟨1173156097736007871042799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3128416260629354322780797 1173156097736007871042799)
                    ·
                      rfl

theorem cell22_3427070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_3427070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427070 prefixEnd_3427070 := by exact prefixLift 3427070
  have htrace : WordTrace (prefixWord ++ tailWord_3427070) baseStart_3427070 baseEnd_3427070 := by
    simpa [prefixWord, tailWord_3427070, baseEnd_3427070] using wordTrace_append hprefix tailTrace_3427070
  have hstable : (prefixWord ++ tailWord_3427070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427070).length < 2 ^ (prefixWord ++ tailWord_3427070).sum := by decide
  have hdescent : baseEnd_3427070 < baseStart_3427070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427107 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 6, 4]
def baseStart_3427107 : Nat := 118140960795 + 3427107 * 2 ^ 59
def prefixEnd_3427107 : Nat := 4983230072969 + 3 ^ 40 * 3427107 * 2
def baseEnd_3427107 : Nat := 1173168763592152107867685

theorem tailTrace_3427107 : CollatzResearch.WordTrace tailWord_3427107 prefixEnd_3427107 1173168763592152107867685 := by
  unfold tailWord_3427107
  simp only [CollatzResearch.WordTrace]
  refine ⟨124996861195184117122335575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83331240796789411414890383 124996861195184117122335575)
  ·
    refine ⟨187495291792776175683503363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124996861195184117122335575 187495291792776175683503363)
    ·
      refine ⟨281242937689164263525255045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187495291792776175683503363 281242937689164263525255045)
      ·
        refine ⟨52733050816718299410985321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281242937689164263525255045 52733050816718299410985321)
        ·
          refine ⟨39549788112538724558238991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52733050816718299410985321 39549788112538724558238991)
          ·
            refine ⟨59324682168808086837358487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39549788112538724558238991 59324682168808086837358487)
            ·
              refine ⟨88987023253212130256037731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59324682168808086837358487 88987023253212130256037731)
              ·
                refine ⟨133480534879818195384056597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88987023253212130256037731 133480534879818195384056597)
                ·
                  refine ⟨6256900072491477908627653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 133480534879818195384056597 6256900072491477908627653)
                  ·
                    refine ⟨1173168763592152107867685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6256900072491477908627653 1173168763592152107867685)
                    ·
                      rfl

theorem cell22_3427107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 4].length) (baseStart_3427107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427107 prefixEnd_3427107 := by exact prefixLift 3427107
  have htrace : WordTrace (prefixWord ++ tailWord_3427107) baseStart_3427107 baseEnd_3427107 := by
    simpa [prefixWord, tailWord_3427107, baseEnd_3427107] using wordTrace_append hprefix tailTrace_3427107
  have hstable : (prefixWord ++ tailWord_3427107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427107).length < 2 ^ (prefixWord ++ tailWord_3427107).sum := by decide
  have hdescent : baseEnd_3427107 < baseStart_3427107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427122 : List Nat := [3, 2, 1, 1, 3, 1, 1, 10]
def baseStart_3427122 : Nat := 118140960795 + 3427122 * 2 ^ 59
def prefixEnd_3427122 : Nat := 4983230072969 + 3 ^ 40 * 3427122 * 2
def baseEnd_3427122 : Nat := 130352655377633007638071

theorem tailTrace_3427122 : CollatzResearch.WordTrace tailWord_3427122 prefixEnd_3427122 130352655377633007638071 := by
  unfold tailWord_3427122
  simp only [CollatzResearch.WordTrace]
  refine ⟨31249352072532443671032905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83331605526753183122754413 31249352072532443671032905)
  ·
    refine ⟨23437014054399332753274679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31249352072532443671032905 23437014054399332753274679)
    ·
      refine ⟨35155521081598999129912019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23437014054399332753274679 35155521081598999129912019)
      ·
        refine ⟨52733281622398498694868029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35155521081598999129912019 52733281622398498694868029)
        ·
          refine ⟨19774980608399437010575511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52733281622398498694868029 19774980608399437010575511)
          ·
            refine ⟨29662470912599155515863267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19774980608399437010575511 29662470912599155515863267)
            ·
              refine ⟨44493706368898733273794901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29662470912599155515863267 44493706368898733273794901)
              ·
                refine ⟨130352655377633007638071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44493706368898733273794901 130352655377633007638071)
                ·
                  rfl

theorem cell22_3427122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 10].length) (baseStart_3427122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427122 prefixEnd_3427122 := by exact prefixLift 3427122
  have htrace : WordTrace (prefixWord ++ tailWord_3427122) baseStart_3427122 baseEnd_3427122 := by
    simpa [prefixWord, tailWord_3427122, baseEnd_3427122] using wordTrace_append hprefix tailTrace_3427122
  have hstable : (prefixWord ++ tailWord_3427122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427122).length < 2 ^ (prefixWord ++ tailWord_3427122).sum := by decide
  have hdescent : baseEnd_3427122 < baseStart_3427122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427152 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 2, 6]
def baseStart_3427152 : Nat := 118140960795 + 3427152 * 2 ^ 59
def prefixEnd_3427152 : Nat := 4983230072969 + 3 ^ 40 * 3427152 * 2
def baseEnd_3427152 : Nat := 1173184168011786990492547

theorem tailTrace_3427152 : CollatzResearch.WordTrace tailWord_3427152 prefixEnd_3427152 1173184168011786990492547 := by
  unfold tailWord_3427152
  simp only [CollatzResearch.WordTrace]
  refine ⟨62499251240010544903861855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83332334986680726538482473 62499251240010544903861855)
  ·
    refine ⟨93748876860015817355792783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62499251240010544903861855 93748876860015817355792783)
    ·
      refine ⟨140623315290023726033689175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93748876860015817355792783 140623315290023726033689175)
      ·
        refine ⟨210934972935035589050533763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140623315290023726033689175 210934972935035589050533763)
        ·
          refine ⟨316402459402553383575800645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210934972935035589050533763 316402459402553383575800645)
          ·
            refine ⟨59325461137978759420462621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 316402459402553383575800645 59325461137978759420462621)
            ·
              refine ⟨22247047926742034782673483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59325461137978759420462621 22247047926742034782673483)
              ·
                refine ⟨33370571890113052174010225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22247047926742034782673483 33370571890113052174010225)
                ·
                  refine ⟨25027928917584789130507669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33370571890113052174010225 25027928917584789130507669)
                  ·
                    refine ⟨1173184168011786990492547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25027928917584789130507669 1173184168011786990492547)
                    ·
                      rfl

theorem cell22_3427152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_3427152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427152 prefixEnd_3427152 := by exact prefixLift 3427152
  have htrace : WordTrace (prefixWord ++ tailWord_3427152) baseStart_3427152 baseEnd_3427152 := by
    simpa [prefixWord, tailWord_3427152, baseEnd_3427152] using wordTrace_append hprefix tailTrace_3427152
  have hstable : (prefixWord ++ tailWord_3427152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427152).length < 2 ^ (prefixWord ++ tailWord_3427152).sum := by decide
  have hdescent : baseEnd_3427152 < baseStart_3427152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427156 : List Nat := [2, 4, 1, 1, 4, 2, 1, 7]
def baseStart_3427156 : Nat := 118140960795 + 3427156 * 2 ^ 59
def prefixEnd_3427156 : Nat := 4983230072969 + 3 ^ 40 * 3427156 * 2
def baseEnd_3427156 : Nat := 130353948588170257043615

theorem tailTrace_3427156 : CollatzResearch.WordTrace tailWord_3427156 prefixEnd_3427156 130353948588170257043615 := by
  unfold tailWord_3427156
  simp only [CollatzResearch.WordTrace]
  refine ⟨62499324186003299245434661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83332432248004398993912881 62499324186003299245434661)
  ·
    refine ⟨11718623284875618608518999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62499324186003299245434661 11718623284875618608518999)
    ·
      refine ⟨17577934927313427912778499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11718623284875618608518999 17577934927313427912778499)
      ·
        refine ⟨26366902390970141869167749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17577934927313427912778499 26366902390970141869167749)
        ·
          refine ⟨4943794198306901600468953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26366902390970141869167749 4943794198306901600468953)
          ·
            refine ⟨3707845648730176200351715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4943794198306901600468953 3707845648730176200351715)
            ·
              refine ⟨5561768473095264300527573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3707845648730176200351715 5561768473095264300527573)
              ·
                refine ⟨130353948588170257043615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5561768473095264300527573 130353948588170257043615)
                ·
                  rfl

theorem cell22_3427156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 7].length) (baseStart_3427156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427156 prefixEnd_3427156 := by exact prefixLift 3427156
  have htrace : WordTrace (prefixWord ++ tailWord_3427156) baseStart_3427156 baseEnd_3427156 := by
    simpa [prefixWord, tailWord_3427156, baseEnd_3427156] using wordTrace_append hprefix tailTrace_3427156
  have hstable : (prefixWord ++ tailWord_3427156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427156).length < 2 ^ (prefixWord ++ tailWord_3427156).sum := by decide
  have hdescent : baseEnd_3427156 < baseStart_3427156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427171 : List Nat := [1, 1, 1, 5, 3, 2, 1, 2, 3, 3]
def baseStart_3427171 : Nat := 118140960795 + 3427171 * 2 ^ 59
def prefixEnd_3427171 : Nat := 4983230072969 + 3 ^ 40 * 3427171 * 2
def baseEnd_3427171 : Nat := 1173190672100077274267489

theorem tailTrace_3427171 : CollatzResearch.WordTrace tailWord_3427171 prefixEnd_3427171 1173190672100077274267489 := by
  unfold tailWord_3427171
  simp only [CollatzResearch.WordTrace]
  refine ⟨124999195466952256052665367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83332796977968170701776911 124999195466952256052665367)
  ·
    refine ⟨187498793200428384078998051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124999195466952256052665367 187498793200428384078998051)
    ·
      refine ⟨281248189800642576118497077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187498793200428384078998051 281248189800642576118497077)
      ·
        refine ⟨26367017793810241511109101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 281248189800642576118497077 26367017793810241511109101)
        ·
          refine ⟨9887631672678840566665913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26367017793810241511109101 9887631672678840566665913)
          ·
            refine ⟨7415723754509130424999435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9887631672678840566665913 7415723754509130424999435)
            ·
              refine ⟨11123585631763695637499153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7415723754509130424999435 11123585631763695637499153)
              ·
                refine ⟨8342689223822771728124365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11123585631763695637499153 8342689223822771728124365)
                ·
                  refine ⟨3128508458933539398046637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8342689223822771728124365 3128508458933539398046637)
                  ·
                    refine ⟨1173190672100077274267489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3128508458933539398046637 1173190672100077274267489)
                    ·
                      rfl

theorem cell22_3427171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 3].length) (baseStart_3427171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427171 prefixEnd_3427171 := by exact prefixLift 3427171
  have htrace : WordTrace (prefixWord ++ tailWord_3427171) baseStart_3427171 baseEnd_3427171 := by
    simpa [prefixWord, tailWord_3427171, baseEnd_3427171] using wordTrace_append hprefix tailTrace_3427171
  have hstable : (prefixWord ++ tailWord_3427171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427171).length < 2 ^ (prefixWord ++ tailWord_3427171).sum := by decide
  have hdescent : baseEnd_3427171 < baseStart_3427171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427229 : List Nat := [1, 4, 2, 1, 2, 1, 1, 4, 6]
def baseStart_3427229 : Nat := 118140960795 + 3427229 * 2 ^ 59
def prefixEnd_3427229 : Nat := 4983230072969 + 3 ^ 40 * 3427229 * 2
def baseEnd_3427229 : Nat := 391070175561794818772437

theorem tailTrace_3427229 : CollatzResearch.WordTrace tailWord_3427229 prefixEnd_3427229 391070175561794818772437 := by
  unfold tailWord_3427229
  simp only [CollatzResearch.WordTrace]
  refine ⟨125001310900742131958276741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83334207267161421305517827 125001310900742131958276741)
  ·
    refine ⟨23437745793889149742176889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125001310900742131958276741 23437745793889149742176889)
    ·
      refine ⟨17578309345416862306632667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23437745793889149742176889 17578309345416862306632667)
      ·
        refine ⟨26367464018125293459949001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17578309345416862306632667 26367464018125293459949001)
        ·
          refine ⟨19775598013593970094961751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26367464018125293459949001 19775598013593970094961751)
          ·
            refine ⟨29663397020390955142442627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19775598013593970094961751 29663397020390955142442627)
            ·
              refine ⟨44495095530586432713663941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29663397020390955142442627 44495095530586432713663941)
              ·
                refine ⟨8342830411984956133811989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44495095530586432713663941 8342830411984956133811989)
                ·
                  refine ⟨391070175561794818772437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8342830411984956133811989 391070175561794818772437)
                  ·
                    rfl

theorem cell22_3427229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_3427229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427229 prefixEnd_3427229 := by exact prefixLift 3427229
  have htrace : WordTrace (prefixWord ++ tailWord_3427229) baseStart_3427229 baseEnd_3427229 := by
    simpa [prefixWord, tailWord_3427229, baseEnd_3427229] using wordTrace_append hprefix tailTrace_3427229
  have hstable : (prefixWord ++ tailWord_3427229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427229).length < 2 ^ (prefixWord ++ tailWord_3427229).sum := by decide
  have hdescent : baseEnd_3427229 < baseStart_3427229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427231 : List Nat := [1, 1, 2, 5, 2, 1, 1, 4, 1, 4]
def baseStart_3427231 : Nat := 118140960795 + 3427231 * 2 ^ 59
def prefixEnd_3427231 : Nat := 4983230072969 + 3 ^ 40 * 3427231 * 2
def baseEnd_3427231 : Nat := 1173211211326257117767305

theorem tailTrace_3427231 : CollatzResearch.WordTrace tailWord_3427231 prefixEnd_3427231 1173211211326257117767305 := by
  unfold tailWord_3427231
  simp only [CollatzResearch.WordTrace]
  refine ⟨125001383846734886299849547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83334255897823257533233031 125001383846734886299849547)
  ·
    refine ⟨187502075770102329449774321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125001383846734886299849547 187502075770102329449774321)
    ·
      refine ⟨140626556827576747087330741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187502075770102329449774321 140626556827576747087330741)
      ·
        refine ⟨13183739702585320039437257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140626556827576747087330741 13183739702585320039437257)
        ·
          refine ⟨9887804776938990029577943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13183739702585320039437257 9887804776938990029577943)
          ·
            refine ⟨14831707165408485044366915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9887804776938990029577943 14831707165408485044366915)
            ·
              refine ⟨22247560748112727566550373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14831707165408485044366915 22247560748112727566550373)
              ·
                refine ⟨4171417640271136418728195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22247560748112727566550373 4171417640271136418728195)
                ·
                  refine ⟨6257126460406704628092293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4171417640271136418728195 6257126460406704628092293)
                  ·
                    refine ⟨1173211211326257117767305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6257126460406704628092293 1173211211326257117767305)
                    ·
                      rfl

theorem cell22_3427231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 4].length) (baseStart_3427231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427231 prefixEnd_3427231 := by exact prefixLift 3427231
  have htrace : WordTrace (prefixWord ++ tailWord_3427231) baseStart_3427231 baseEnd_3427231 := by
    simpa [prefixWord, tailWord_3427231, baseEnd_3427231] using wordTrace_append hprefix tailTrace_3427231
  have hstable : (prefixWord ++ tailWord_3427231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427231).length < 2 ^ (prefixWord ++ tailWord_3427231).sum := by decide
  have hdescent : baseEnd_3427231 < baseStart_3427231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427278 : List Nat := [4, 1, 1, 1, 2, 4, 1, 3, 2, 3]
def baseStart_3427278 : Nat := 118140960795 + 3427278 * 2 ^ 59
def prefixEnd_3427278 : Nat := 4983230072969 + 3 ^ 40 * 3427278 * 2
def baseEnd_3427278 : Nat := 1173227300386764661842161

theorem tailTrace_3427278 : CollatzResearch.WordTrace tailWord_3427278 prefixEnd_3427278 1173227300386764661842161 := by
  unfold tailWord_3427278
  simp only [CollatzResearch.WordTrace]
  refine ⟨15625387259695576665851311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83335398718376408884540325 15625387259695576665851311)
  ·
    refine ⟨23438080889543364998776967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15625387259695576665851311 23438080889543364998776967)
    ·
      refine ⟨35157121334315047498165451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23438080889543364998776967 35157121334315047498165451)
      ·
        refine ⟨52735682001472571247248177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35157121334315047498165451 52735682001472571247248177)
        ·
          refine ⟨39551761501104428435436133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52735682001472571247248177 39551761501104428435436133)
          ·
            refine ⟨7415955281457080331644275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39551761501104428435436133 7415955281457080331644275)
            ·
              refine ⟨11123932922185620497466413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7415955281457080331644275 11123932922185620497466413)
              ·
                refine ⟨4171474845819607686549905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11123932922185620497466413 4171474845819607686549905)
                ·
                  refine ⟨3128606134364705764912429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4171474845819607686549905 3128606134364705764912429)
                  ·
                    refine ⟨1173227300386764661842161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3128606134364705764912429 1173227300386764661842161)
                    ·
                      rfl

theorem cell22_3427278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_3427278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427278 prefixEnd_3427278 := by exact prefixLift 3427278
  have htrace : WordTrace (prefixWord ++ tailWord_3427278) baseStart_3427278 baseEnd_3427278 := by
    simpa [prefixWord, tailWord_3427278, baseEnd_3427278] using wordTrace_append hprefix tailTrace_3427278
  have hstable : (prefixWord ++ tailWord_3427278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427278).length < 2 ^ (prefixWord ++ tailWord_3427278).sum := by decide
  have hdescent : baseEnd_3427278 < baseStart_3427278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427293 : List Nat := [1, 4, 3, 1, 2, 2, 2, 1, 2, 4]
def baseStart_3427293 : Nat := 118140960795 + 3427293 * 2 ^ 59
def prefixEnd_3427293 : Nat := 4983230072969 + 3 ^ 40 * 3427293 * 2
def baseEnd_3427293 : Nat := 1173232435193309622717115

theorem tailTrace_3427293 : CollatzResearch.WordTrace tailWord_3427293 prefixEnd_3427293 1173232435193309622717115 := by
  unfold tailWord_3427293
  simp only [CollatzResearch.WordTrace]
  refine ⟨125003645172510270888606533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83335763448340180592404355 125003645172510270888606533)
  ·
    refine ⟨23438183469845675791613725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125003645172510270888606533 23438183469845675791613725)
    ·
      refine ⟨8789318801192128421855147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23438183469845675791613725 8789318801192128421855147)
      ·
        refine ⟨13183978201788192632782721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8789318801192128421855147 13183978201788192632782721)
        ·
          refine ⟨9887983651341144474587041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13183978201788192632782721 9887983651341144474587041)
          ·
            refine ⟨7415987738505858355940281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9887983651341144474587041 7415987738505858355940281)
            ·
              refine ⟨5561990803879393766955211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7415987738505858355940281 5561990803879393766955211)
              ·
                refine ⟨8342986205819090650432817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5561990803879393766955211 8342986205819090650432817)
                ·
                  refine ⟨6257239654364317987824613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8342986205819090650432817 6257239654364317987824613)
                  ·
                    refine ⟨1173232435193309622717115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6257239654364317987824613 1173232435193309622717115)
                    ·
                      rfl

theorem cell22_3427293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_3427293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427293 prefixEnd_3427293 := by exact prefixLift 3427293
  have htrace : WordTrace (prefixWord ++ tailWord_3427293) baseStart_3427293 baseEnd_3427293 := by
    simpa [prefixWord, tailWord_3427293, baseEnd_3427293] using wordTrace_append hprefix tailTrace_3427293
  have hstable : (prefixWord ++ tailWord_3427293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427293).length < 2 ^ (prefixWord ++ tailWord_3427293).sum := by decide
  have hdescent : baseEnd_3427293 < baseStart_3427293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427314 : List Nat := [3, 2, 1, 5, 2, 1, 2, 2, 4]
def baseStart_3427314 : Nat := 118140960795 + 3427314 * 2 ^ 59
def prefixEnd_3427314 : Nat := 4983230072969 + 3 ^ 40 * 3427314 * 2
def baseEnd_3427314 : Nat := 391079874640824189314017

theorem tailTrace_3427314 : CollatzResearch.WordTrace tailWord_3427314 prefixEnd_3427314 391079874640824189314017 := by
  unfold tailWord_3427314
  simp only [CollatzResearch.WordTrace]
  refine ⟨31251102776358547868780249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83336274070289460983413997 31251102776358547868780249)
  ·
    refine ⟨23438327082268910901585187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31251102776358547868780249 23438327082268910901585187)
    ·
      refine ⟨35157490623403366352377781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23438327082268910901585187 35157490623403366352377781)
      ·
        refine ⟨3296014745944065595535417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35157490623403366352377781 3296014745944065595535417)
        ·
          refine ⟨2472011059458049196651563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3296014745944065595535417 2472011059458049196651563)
          ·
            refine ⟨3708016589187073794977345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472011059458049196651563 3708016589187073794977345)
            ·
              refine ⟨2781012441890305346233009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3708016589187073794977345 2781012441890305346233009)
              ·
                refine ⟨2085759331417729009674757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2781012441890305346233009 2085759331417729009674757)
                ·
                  refine ⟨391079874640824189314017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2085759331417729009674757 391079874640824189314017)
                  ·
                    rfl

theorem cell22_3427314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_3427314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427314 prefixEnd_3427314 := by exact prefixLift 3427314
  have htrace : WordTrace (prefixWord ++ tailWord_3427314) baseStart_3427314 baseEnd_3427314 := by
    simpa [prefixWord, tailWord_3427314, baseEnd_3427314] using wordTrace_append hprefix tailTrace_3427314
  have hstable : (prefixWord ++ tailWord_3427314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427314).length < 2 ^ (prefixWord ++ tailWord_3427314).sum := by decide
  have hdescent : baseEnd_3427314 < baseStart_3427314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427336 : List Nat := [2, 1, 3, 2, 1, 3, 2, 3, 5]
def baseStart_3427336 : Nat := 118140960795 + 3427336 * 2 ^ 59
def prefixEnd_3427336 : Nat := 4983230072969 + 3 ^ 40 * 3427336 * 2
def baseEnd_3427336 : Nat := 391082384990690614630661

theorem tailTrace_3427336 : CollatzResearch.WordTrace tailWord_3427336 prefixEnd_3427336 391082384990690614630661 := by
  unfold tailWord_3427336
  simp only [CollatzResearch.WordTrace]
  refine ⟨62502606755677244616210931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83336809007569659488281241 62502606755677244616210931)
  ·
    refine ⟨93753910133515866924316397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62502606755677244616210931 93753910133515866924316397)
    ·
      refine ⟨35157716300068450096618649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93753910133515866924316397 35157716300068450096618649)
      ·
        refine ⟨26368287225051337572463987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35157716300068450096618649 26368287225051337572463987)
        ·
          refine ⟨39552430837577006358695981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26368287225051337572463987 39552430837577006358695981)
          ·
            refine ⟨14832161564091377384510993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39552430837577006358695981 14832161564091377384510993)
            ·
              refine ⟨11124121173068533038383245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14832161564091377384510993 11124121173068533038383245)
              ·
                refine ⟨4171545439900699889393717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11124121173068533038383245 4171545439900699889393717)
                ·
                  refine ⟨391082384990690614630661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4171545439900699889393717 391082384990690614630661)
                  ·
                    rfl

theorem cell22_3427336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 5].length) (baseStart_3427336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427336 prefixEnd_3427336 := by exact prefixLift 3427336
  have htrace : WordTrace (prefixWord ++ tailWord_3427336) baseStart_3427336 baseEnd_3427336 := by
    simpa [prefixWord, tailWord_3427336, baseEnd_3427336] using wordTrace_append hprefix tailTrace_3427336
  have hstable : (prefixWord ++ tailWord_3427336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427336).length < 2 ^ (prefixWord ++ tailWord_3427336).sum := by decide
  have hdescent : baseEnd_3427336 < baseStart_3427336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427357 : List Nat := [1, 4, 2, 2, 3, 1, 2, 3, 1, 3]
def baseStart_3427357 : Nat := 118140960795 + 3427357 * 2 ^ 59
def prefixEnd_3427357 : Nat := 4983230072969 + 3 ^ 40 * 3427357 * 2
def baseEnd_3427357 : Nat := 1173254343701234789116919

theorem tailTrace_3427357 : CollatzResearch.WordTrace tailWord_3427357 prefixEnd_3427357 1173254343701234789116919 := by
  unfold tailWord_3427357
  simp only [CollatzResearch.WordTrace]
  refine ⟨125005979444278409818936325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83337319629518939879290883 125005979444278409818936325)
  ·
    refine ⟨23438621145802201841050561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125005979444278409818936325 23438621145802201841050561)
    ·
      refine ⟨17578965859351651380787921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23438621145802201841050561 17578965859351651380787921)
      ·
        refine ⟨13184224394513738535590941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17578965859351651380787921 13184224394513738535590941)
        ·
          refine ⟨4944084147942651950846603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13184224394513738535590941 4944084147942651950846603)
          ·
            refine ⟨7416126221913977926269905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4944084147942651950846603 7416126221913977926269905)
            ·
              refine ⟨5562094666435483444702429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7416126221913977926269905 5562094666435483444702429)
              ·
                refine ⟨2085785499913306291763411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5562094666435483444702429 2085785499913306291763411)
                ·
                  refine ⟨3128678249869959437645117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2085785499913306291763411 3128678249869959437645117)
                  ·
                    refine ⟨1173254343701234789116919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3128678249869959437645117 1173254343701234789116919)
                    ·
                      rfl

theorem cell22_3427357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_3427357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427357 prefixEnd_3427357 := by exact prefixLift 3427357
  have htrace : WordTrace (prefixWord ++ tailWord_3427357) baseStart_3427357 baseEnd_3427357 := by
    simpa [prefixWord, tailWord_3427357, baseEnd_3427357] using wordTrace_append hprefix tailTrace_3427357
  have hstable : (prefixWord ++ tailWord_3427357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427357).length < 2 ^ (prefixWord ++ tailWord_3427357).sum := by decide
  have hdescent : baseEnd_3427357 < baseStart_3427357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427370 : List Nat := [3, 1, 4, 1, 3, 2, 1, 2, 5]
def baseStart_3427370 : Nat := 118140960795 + 3427370 * 2 ^ 59
def prefixEnd_3427370 : Nat := 4983230072969 + 3 ^ 40 * 3427370 * 2
def baseEnd_3427370 : Nat := 391086264622302362847293

theorem tailTrace_3427370 : CollatzResearch.WordTrace tailWord_3427370 prefixEnd_3427370 391086264622302362847293 := by
  unfold tailWord_3427370
  simp only [CollatzResearch.WordTrace]
  refine ⟨31251613398307828259789891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83337635728820875359439709 31251613398307828259789891)
  ·
    refine ⟨46877420097461742389684837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31251613398307828259789891 46877420097461742389684837)
    ·
      refine ⟨8789516268274076698065907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46877420097461742389684837 8789516268274076698065907)
      ·
        refine ⟨13184274402411115047098861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8789516268274076698065907 13184274402411115047098861)
        ·
          refine ⟨4944102900904168142662073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13184274402411115047098861 4944102900904168142662073)
          ·
            refine ⟨3708077175678126106996555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4944102900904168142662073 3708077175678126106996555)
            ·
              refine ⟨5562115763517189160494833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3708077175678126106996555 5562115763517189160494833)
              ·
                refine ⟨4171586822637891870371125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5562115763517189160494833 4171586822637891870371125)
                ·
                  refine ⟨391086264622302362847293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4171586822637891870371125 391086264622302362847293)
                  ·
                    rfl

theorem cell22_3427370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_3427370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427370 prefixEnd_3427370 := by exact prefixLift 3427370
  have htrace : WordTrace (prefixWord ++ tailWord_3427370) baseStart_3427370 baseEnd_3427370 := by
    simpa [prefixWord, tailWord_3427370, baseEnd_3427370] using wordTrace_append hprefix tailTrace_3427370
  have hstable : (prefixWord ++ tailWord_3427370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427370).length < 2 ^ (prefixWord ++ tailWord_3427370).sum := by decide
  have hdescent : baseEnd_3427370 < baseStart_3427370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427432 : List Nat := [2, 1, 4, 4, 2, 1, 1, 1, 6]
def baseStart_3427432 : Nat := 118140960795 + 3427432 * 2 ^ 59
def prefixEnd_3427432 : Nat := 4983230072969 + 3 ^ 40 * 3427432 * 2
def baseEnd_3427432 : Nat := 391093339244653197830563

theorem tailTrace_3427432 : CollatzResearch.WordTrace tailWord_3427432 prefixEnd_3427432 391093339244653197830563 := by
  unfold tailWord_3427432
  simp only [CollatzResearch.WordTrace]
  refine ⟨62504357459503348813958275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83339143279337798418611033 62504357459503348813958275)
  ·
    refine ⟨93756536189255023220937413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62504357459503348813958275 93756536189255023220937413)
    ·
      refine ⟨17579350535485316853925765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93756536189255023220937413 17579350535485316853925765)
      ·
        refine ⟨3296128225403496910111081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17579350535485316853925765 3296128225403496910111081)
        ·
          refine ⟨2472096169052622682583311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3296128225403496910111081 2472096169052622682583311)
          ·
            refine ⟨3708144253578934023874967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472096169052622682583311 3708144253578934023874967)
            ·
              refine ⟨5562216380368401035812451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3708144253578934023874967 5562216380368401035812451)
              ·
                refine ⟨8343324570552601553718677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5562216380368401035812451 8343324570552601553718677)
                ·
                  refine ⟨391093339244653197830563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8343324570552601553718677 391093339244653197830563)
                  ·
                    rfl

theorem cell22_3427432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 6].length) (baseStart_3427432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427432 prefixEnd_3427432 := by exact prefixLift 3427432
  have htrace : WordTrace (prefixWord ++ tailWord_3427432) baseStart_3427432 baseEnd_3427432 := by
    simpa [prefixWord, tailWord_3427432, baseEnd_3427432] using wordTrace_append hprefix tailTrace_3427432
  have hstable : (prefixWord ++ tailWord_3427432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427432).length < 2 ^ (prefixWord ++ tailWord_3427432).sum := by decide
  have hdescent : baseEnd_3427432 < baseStart_3427432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427488 : List Nat := [2, 1, 1, 4, 2, 1, 4, 2, 5]
def baseStart_3427488 : Nat := 118140960795 + 3427488 * 2 ^ 59
def prefixEnd_3427488 : Nat := 4983230072969 + 3 ^ 40 * 3427488 * 2
def baseEnd_3427488 : Nat := 391099729226131371363839

theorem tailTrace_3427488 : CollatzResearch.WordTrace tailWord_3427488 prefixEnd_3427488 391099729226131371363839 := by
  unfold tailWord_3427488
  simp only [CollatzResearch.WordTrace]
  refine ⟨62505378703401909595977559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83340504937869212794636745 62505378703401909595977559)
  ·
    refine ⟨93758068055102864393966339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62505378703401909595977559 93758068055102864393966339)
    ·
      refine ⟨140637102082654296590949509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93758068055102864393966339 140637102082654296590949509)
      ·
        refine ⟨26369456640497680610803033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140637102082654296590949509 26369456640497680610803033)
        ·
          refine ⟨19777092480373260458102275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26369456640497680610803033 19777092480373260458102275)
          ·
            refine ⟨29665638720559890687153413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19777092480373260458102275 29665638720559890687153413)
            ·
              refine ⟨5562307260104979503841265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29665638720559890687153413 5562307260104979503841265)
              ·
                refine ⟨4171730445078734627880949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5562307260104979503841265 4171730445078734627880949)
                ·
                  refine ⟨391099729226131371363839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4171730445078734627880949 391099729226131371363839)
                  ·
                    rfl

theorem cell22_3427488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 5].length) (baseStart_3427488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427488 prefixEnd_3427488 := by exact prefixLift 3427488
  have htrace : WordTrace (prefixWord ++ tailWord_3427488) baseStart_3427488 baseEnd_3427488 := by
    simpa [prefixWord, tailWord_3427488, baseEnd_3427488] using wordTrace_append hprefix tailTrace_3427488
  have hstable : (prefixWord ++ tailWord_3427488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427488).length < 2 ^ (prefixWord ++ tailWord_3427488).sum := by decide
  have hdescent : baseEnd_3427488 < baseStart_3427488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427492 : List Nat := [2, 3, 1, 2, 3, 2, 1, 4, 1, 3]
def baseStart_3427492 : Nat := 118140960795 + 3427492 * 2 ^ 59
def prefixEnd_3427492 : Nat := 4983230072969 + 3 ^ 40 * 3427492 * 2
def baseEnd_3427492 : Nat := 1173300556960139436991505

theorem tailTrace_3427492 : CollatzResearch.WordTrace tailWord_3427492 prefixEnd_3427492 1173300556960139436991505 := by
  unfold tailWord_3427492
  simp only [CollatzResearch.WordTrace]
  refine ⟨62505451649394663937550365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83340602199192885250067153 62505451649394663937550365)
  ·
    refine ⟨23439544368522998976581387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62505451649394663937550365 23439544368522998976581387)
    ·
      refine ⟨35159316552784498464872081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23439544368522998976581387 35159316552784498464872081)
      ·
        refine ⟨26369487414588373848654061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35159316552784498464872081 26369487414588373848654061)
        ·
          refine ⟨9888557780470640193245273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26369487414588373848654061 9888557780470640193245273)
          ·
            refine ⟨7416418335352980144933955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9888557780470640193245273 7416418335352980144933955)
            ·
              refine ⟨11124627503029470217400933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7416418335352980144933955 11124627503029470217400933)
              ·
                refine ⟨2085867656818025665762675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11124627503029470217400933 2085867656818025665762675)
                ·
                  refine ⟨3128801485227038498644013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2085867656818025665762675 3128801485227038498644013)
                  ·
                    refine ⟨1173300556960139436991505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3128801485227038498644013 1173300556960139436991505)
                    ·
                      rfl

theorem cell22_3427492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_3427492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427492 prefixEnd_3427492 := by exact prefixLift 3427492
  have htrace : WordTrace (prefixWord ++ tailWord_3427492) baseStart_3427492 baseEnd_3427492 := by
    simpa [prefixWord, tailWord_3427492, baseEnd_3427492] using wordTrace_append hprefix tailTrace_3427492
  have hstable : (prefixWord ++ tailWord_3427492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427492).length < 2 ^ (prefixWord ++ tailWord_3427492).sum := by decide
  have hdescent : baseEnd_3427492 < baseStart_3427492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427531 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 3, 5]
def baseStart_3427531 : Nat := 118140960795 + 3427531 * 2 ^ 59
def prefixEnd_3427531 : Nat := 4983230072969 + 3 ^ 40 * 3427531 * 2
def baseEnd_3427531 : Nat := 1173313907457156335266385

theorem tailTrace_3427531 : CollatzResearch.WordTrace tailWord_3427531 prefixEnd_3427531 1173313907457156335266385 := by
  unfold tailWord_3427531
  simp only [CollatzResearch.WordTrace]
  refine ⟨125012325745648037535770447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83341550497098691690513631 125012325745648037535770447)
  ·
    refine ⟨187518488618472056303655671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125012325745648037535770447 187518488618472056303655671)
    ·
      refine ⟨281277732927708084455483507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187518488618472056303655671 281277732927708084455483507)
      ·
        refine ⟨421916599391562126683225261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281277732927708084455483507 421916599391562126683225261)
        ·
          refine ⟨158218724771835797506209473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421916599391562126683225261 158218724771835797506209473)
          ·
            refine ⟨118664043578876848129657105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158218724771835797506209473 118664043578876848129657105)
            ·
              refine ⟨88998032684157636097242829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118664043578876848129657105 88998032684157636097242829)
              ·
                refine ⟨33374262256559113536466061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88998032684157636097242829 33374262256559113536466061)
                ·
                  refine ⟨12515348346209667576174773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33374262256559113536466061 12515348346209667576174773)
                  ·
                    refine ⟨1173313907457156335266385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12515348346209667576174773 1173313907457156335266385)
                    ·
                      rfl

theorem cell22_3427531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 5].length) (baseStart_3427531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427531 prefixEnd_3427531 := by exact prefixLift 3427531
  have htrace : WordTrace (prefixWord ++ tailWord_3427531) baseStart_3427531 baseEnd_3427531 := by
    simpa [prefixWord, tailWord_3427531, baseEnd_3427531] using wordTrace_append hprefix tailTrace_3427531
  have hstable : (prefixWord ++ tailWord_3427531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427531).length < 2 ^ (prefixWord ++ tailWord_3427531).sum := by decide
  have hdescent : baseEnd_3427531 < baseStart_3427531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427565 : List Nat := [1, 5, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_3427565 : Nat := 118140960795 + 3427565 * 2 ^ 59
def prefixEnd_3427565 : Nat := 4983230072969 + 3 ^ 40 * 3427565 * 2
def baseEnd_3427565 : Nat := 1173325546351991579916281

theorem tailTrace_3427565 : CollatzResearch.WordTrace tailWord_3427565 prefixEnd_3427565 1173325546351991579916281 := by
  unfold tailWord_3427565
  simp only [CollatzResearch.WordTrace]
  refine ⟨125013565827524861342508149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83342377218349907561672099 125013565827524861342508149)
  ·
    refine ⟨11720021796330455750860139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125013565827524861342508149 11720021796330455750860139)
    ·
      refine ⟨17580032694495683626290209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11720021796330455750860139 17580032694495683626290209)
      ·
        refine ⟨13185024520871762719717657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17580032694495683626290209 13185024520871762719717657)
        ·
          refine ⟨9888768390653822039788243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13185024520871762719717657 9888768390653822039788243)
          ·
            refine ⟨14833152585980733059682365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9888768390653822039788243 14833152585980733059682365)
            ·
              refine ⟨5562432219742774897380887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14833152585980733059682365 5562432219742774897380887)
              ·
                refine ⟨8343648329614162346071331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5562432219742774897380887 8343648329614162346071331)
                ·
                  refine ⟨12515472494421243519106997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8343648329614162346071331 12515472494421243519106997)
                  ·
                    refine ⟨1173325546351991579916281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12515472494421243519106997 1173325546351991579916281)
                    ·
                      rfl

theorem cell22_3427565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_3427565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427565 prefixEnd_3427565 := by exact prefixLift 3427565
  have htrace : WordTrace (prefixWord ++ tailWord_3427565) baseStart_3427565 baseEnd_3427565 := by
    simpa [prefixWord, tailWord_3427565, baseEnd_3427565] using wordTrace_append hprefix tailTrace_3427565
  have hstable : (prefixWord ++ tailWord_3427565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427565).length < 2 ^ (prefixWord ++ tailWord_3427565).sum := by decide
  have hdescent : baseEnd_3427565 < baseStart_3427565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427616 : List Nat := [2, 1, 1, 5, 4, 1, 2, 1, 2, 3]
def baseStart_3427616 : Nat := 118140960795 + 3427616 * 2 ^ 59
def prefixEnd_3427616 : Nat := 4983230072969 + 3 ^ 40 * 3427616 * 2
def baseEnd_3427616 : Nat := 1173343004694244446891125

theorem tailTrace_3427616 : CollatzResearch.WordTrace tailWord_3427616 prefixEnd_3427616 1173343004694244446891125 := by
  unfold tailWord_3427616
  simp only [CollatzResearch.WordTrace]
  refine ⟨62507712975170048526307351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83343617300226731368409801 62507712975170048526307351)
  ·
    refine ⟨93761569462755072789461027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62507712975170048526307351 93761569462755072789461027)
    ·
      refine ⟨140642354194132609184191541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93761569462755072789461027 140642354194132609184191541)
      ·
        refine ⟨13185220705699932111017957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140642354194132609184191541 13185220705699932111017957)
        ·
          refine ⟨2472228882318737270815867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13185220705699932111017957 2472228882318737270815867)
          ·
            refine ⟨3708343323478105906223801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472228882318737270815867 3708343323478105906223801)
            ·
              refine ⟨2781257492608579429667851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3708343323478105906223801 2781257492608579429667851)
              ·
                refine ⟨4171886238912869144501777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2781257492608579429667851 4171886238912869144501777)
                ·
                  refine ⟨3128914679184651858376333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4171886238912869144501777 3128914679184651858376333)
                  ·
                    refine ⟨1173343004694244446891125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3128914679184651858376333 1173343004694244446891125)
                    ·
                      rfl

theorem cell22_3427616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 2, 3].length) (baseStart_3427616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427616 prefixEnd_3427616 := by exact prefixLift 3427616
  have htrace : WordTrace (prefixWord ++ tailWord_3427616) baseStart_3427616 baseEnd_3427616 := by
    simpa [prefixWord, tailWord_3427616, baseEnd_3427616] using wordTrace_append hprefix tailTrace_3427616
  have hstable : (prefixWord ++ tailWord_3427616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427616).length < 2 ^ (prefixWord ++ tailWord_3427616).sum := by decide
  have hdescent : baseEnd_3427616 < baseStart_3427616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427717 : List Nat := [1, 3, 1, 1, 3, 1, 5, 2, 2, 3]
def baseStart_3427717 : Nat := 118140960795 + 3427717 * 2 ^ 59
def prefixEnd_3427717 : Nat := 4983230072969 + 3 ^ 40 * 3427717 * 2
def baseEnd_3427717 : Nat := 1173377579058313850115815

theorem tailTrace_3427717 : CollatzResearch.WordTrace tailWord_3427717 prefixEnd_3427717 1173377579058313850115815 := by
  unfold tailWord_3427717
  simp only [CollatzResearch.WordTrace]
  refine ⟨125019109722974191302041405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83346073148649460868027603 125019109722974191302041405)
  ·
    refine ⟨46882166146115321738265527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125019109722974191302041405 46882166146115321738265527)
    ·
      refine ⟨70323249219172982607398291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46882166146115321738265527 70323249219172982607398291)
      ·
        refine ⟨105484873828759473911097437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70323249219172982607398291 105484873828759473911097437)
        ·
          refine ⟨39556827685784802716661539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105484873828759473911097437 39556827685784802716661539)
          ·
            refine ⟨59335241528677204074992309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39556827685784802716661539 59335241528677204074992309)
            ·
              refine ⟨5562678893313487882030529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59335241528677204074992309 5562678893313487882030529)
              ·
                refine ⟨4172009169985115911522897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5562678893313487882030529 4172009169985115911522897)
                ·
                  refine ⟨3129006877488836933642173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4172009169985115911522897 3129006877488836933642173)
                  ·
                    refine ⟨1173377579058313850115815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3129006877488836933642173 1173377579058313850115815)
                    ·
                      rfl

theorem cell22_3427717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_3427717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427717 prefixEnd_3427717 := by exact prefixLift 3427717
  have htrace : WordTrace (prefixWord ++ tailWord_3427717) baseStart_3427717 baseEnd_3427717 := by
    simpa [prefixWord, tailWord_3427717, baseEnd_3427717] using wordTrace_append hprefix tailTrace_3427717
  have hstable : (prefixWord ++ tailWord_3427717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427717).length < 2 ^ (prefixWord ++ tailWord_3427717).sum := by decide
  have hdescent : baseEnd_3427717 < baseStart_3427717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427790 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_3427790 : Nat := 118140960795 + 3427790 * 2 ^ 59
def prefixEnd_3427790 : Nat := 4983230072969 + 3 ^ 40 * 3427790 * 2
def baseEnd_3427790 : Nat := 1173402568450165993040591

theorem tailTrace_3427790 : CollatzResearch.WordTrace tailWord_3427790 prefixEnd_3427790 1173402568450165993040591 := by
  unfold tailWord_3427790
  simp only [CollatzResearch.WordTrace]
  refine ⟨15627721531463715596181103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83347848167806483179632549 15627721531463715596181103)
  ·
    refine ⟨23441582297195573394271655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15627721531463715596181103 23441582297195573394271655)
    ·
      refine ⟨35162373445793360091407483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23441582297195573394271655 35162373445793360091407483)
      ·
        refine ⟨52743560168690040137111225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35162373445793360091407483 52743560168690040137111225)
        ·
          refine ⟨39557670126517530102833419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52743560168690040137111225 39557670126517530102833419)
          ·
            refine ⟨59336505189776295154250129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39557670126517530102833419 59336505189776295154250129)
            ·
              refine ⟨44502378892332221365687597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59336505189776295154250129 44502378892332221365687597)
              ·
                refine ⟨16688392084624583012132849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44502378892332221365687597 16688392084624583012132849)
                ·
                  refine ⟨12516294063468437259099637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16688392084624583012132849 12516294063468437259099637)
                  ·
                    refine ⟨1173402568450165993040591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12516294063468437259099637 1173402568450165993040591)
                    ·
                      rfl

theorem cell22_3427790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_3427790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427790 prefixEnd_3427790 := by exact prefixLift 3427790
  have htrace : WordTrace (prefixWord ++ tailWord_3427790) baseStart_3427790 baseEnd_3427790 := by
    simpa [prefixWord, tailWord_3427790, baseEnd_3427790] using wordTrace_append hprefix tailTrace_3427790
  have hstable : (prefixWord ++ tailWord_3427790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427790).length < 2 ^ (prefixWord ++ tailWord_3427790).sum := by decide
  have hdescent : baseEnd_3427790 < baseStart_3427790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427886 : List Nat := [4, 1, 3, 1, 2, 1, 3, 2, 2, 3]
def baseStart_3427886 : Nat := 118140960795 + 3427886 * 2 ^ 59
def prefixEnd_3427886 : Nat := 4983230072969 + 3 ^ 40 * 3427886 * 2
def baseEnd_3427886 : Nat := 1173435431212053742640297

theorem tailTrace_3427886 : CollatzResearch.WordTrace tailWord_3427886 prefixEnd_3427886 1173435431212053742640297 := by
  unfold tailWord_3427886
  simp only [CollatzResearch.WordTrace]
  refine ⟨15628159207420241645617939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83350182439574622109962341 15628159207420241645617939)
  ·
    refine ⟨23442238811130362468426909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15628159207420241645617939 23442238811130362468426909)
    ·
      refine ⟨8790839554173885925660091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23442238811130362468426909 8790839554173885925660091)
      ·
        refine ⟨13186259331260828888490137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8790839554173885925660091 13186259331260828888490137)
        ·
          refine ⟨9889694498445621666367603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13186259331260828888490137 9889694498445621666367603)
          ·
            refine ⟨14834541747668432499551405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9889694498445621666367603 14834541747668432499551405)
            ·
              refine ⟨5562953155375662187331777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14834541747668432499551405 5562953155375662187331777)
              ·
                refine ⟨4172214866531746640498833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5562953155375662187331777 4172214866531746640498833)
                ·
                  refine ⟨3129161149898809980374125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4172214866531746640498833 3129161149898809980374125)
                  ·
                    refine ⟨1173435431212053742640297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3129161149898809980374125 1173435431212053742640297)
                    ·
                      rfl

theorem cell22_3427886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_3427886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427886 prefixEnd_3427886 := by exact prefixLift 3427886
  have htrace : WordTrace (prefixWord ++ tailWord_3427886) baseStart_3427886 baseEnd_3427886 := by
    simpa [prefixWord, tailWord_3427886, baseEnd_3427886] using wordTrace_append hprefix tailTrace_3427886
  have hstable : (prefixWord ++ tailWord_3427886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427886).length < 2 ^ (prefixWord ++ tailWord_3427886).sum := by decide
  have hdescent : baseEnd_3427886 < baseStart_3427886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427991 : List Nat := [1, 1, 3, 3, 2, 3, 3, 1, 1, 4]
def baseStart_3427991 : Nat := 118140960795 + 3427991 * 2 ^ 59
def prefixEnd_3427991 : Nat := 4983230072969 + 3 ^ 40 * 3427991 * 2
def baseEnd_3427991 : Nat := 1173471374857868468764975

theorem tailTrace_3427991 : CollatzResearch.WordTrace tailWord_3427991 prefixEnd_3427991 1173471374857868468764975 := by
  unfold tailWord_3427991
  simp only [CollatzResearch.WordTrace]
  refine ⟨125029103323981536097515827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83352735549321024065010551 125029103323981536097515827)
  ·
    refine ⟨187543654985972304146273741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125029103323981536097515827 187543654985972304146273741)
    ·
      refine ⟨70328870619739614054852653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187543654985972304146273741 70328870619739614054852653)
      ·
        refine ⟨26373326482402355270569745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70328870619739614054852653 26373326482402355270569745)
        ·
          refine ⟨19779994861801766452927309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26373326482402355270569745 19779994861801766452927309)
          ·
            refine ⟨7417498073175662419847741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19779994861801766452927309 7417498073175662419847741)
            ·
              refine ⟨2781561777440873407442903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7417498073175662419847741 2781561777440873407442903)
              ·
                refine ⟨4172342666161310111164355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2781561777440873407442903 4172342666161310111164355)
                ·
                  refine ⟨6258513999241965166746533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4172342666161310111164355 6258513999241965166746533)
                  ·
                    refine ⟨1173471374857868468764975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6258513999241965166746533 1173471374857868468764975)
                    ·
                      rfl

theorem cell22_3427991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 1, 4].length) (baseStart_3427991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3427991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3427991 prefixEnd_3427991 := by exact prefixLift 3427991
  have htrace : WordTrace (prefixWord ++ tailWord_3427991) baseStart_3427991 baseEnd_3427991 := by
    simpa [prefixWord, tailWord_3427991, baseEnd_3427991] using wordTrace_append hprefix tailTrace_3427991
  have hstable : (prefixWord ++ tailWord_3427991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427991).length < 2 ^ (prefixWord ++ tailWord_3427991).sum := by decide
  have hdescent : baseEnd_3427991 < baseStart_3427991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428021 : List Nat := [1, 3, 3, 3, 2, 1, 2, 1, 1, 5]
def baseStart_3428021 : Nat := 118140960795 + 3428021 * 2 ^ 59
def prefixEnd_3428021 : Nat := 4983230072969 + 3 ^ 40 * 3428021 * 2
def baseEnd_3428021 : Nat := 1173481644470958390514883

theorem tailTrace_3428021 : CollatzResearch.WordTrace tailWord_3428021 prefixEnd_3428021 1173481644470958390514883 := by
  unfold tailWord_3428021
  simp only [CollatzResearch.WordTrace]
  refine ⟨125030197513872851221107917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83353465009248567480738611 125030197513872851221107917)
  ·
    refine ⟨46886324067702319207915469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125030197513872851221107917 46886324067702319207915469)
    ·
      refine ⟨17582371525388369702968301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46886324067702319207915469 17582371525388369702968301)
      ·
        refine ⟨6593389322020638638613113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17582371525388369702968301 6593389322020638638613113)
        ·
          refine ⟨4945041991515478978959835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6593389322020638638613113 4945041991515478978959835)
          ·
            refine ⟨7417562987273218468439753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4945041991515478978959835 7417562987273218468439753)
            ·
              refine ⟨5563172240454913851329815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7417562987273218468439753 5563172240454913851329815)
              ·
                refine ⟨8344758360682370776994723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5563172240454913851329815 8344758360682370776994723)
                ·
                  refine ⟨12517137541023556165492085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8344758360682370776994723 12517137541023556165492085)
                  ·
                    refine ⟨1173481644470958390514883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12517137541023556165492085 1173481644470958390514883)
                    ·
                      rfl

theorem cell22_3428021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_3428021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428021 prefixEnd_3428021 := by exact prefixLift 3428021
  have htrace : WordTrace (prefixWord ++ tailWord_3428021) baseStart_3428021 baseEnd_3428021 := by
    simpa [prefixWord, tailWord_3428021, baseEnd_3428021] using wordTrace_append hprefix tailTrace_3428021
  have hstable : (prefixWord ++ tailWord_3428021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428021).length < 2 ^ (prefixWord ++ tailWord_3428021).sum := by decide
  have hdescent : baseEnd_3428021 < baseStart_3428021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428038 : List Nat := [6, 1, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3428038 : Nat := 118140960795 + 3428038 * 2 ^ 59
def prefixEnd_3428038 : Nat := 4983230072969 + 3 ^ 40 * 3428038 * 2
def baseEnd_3428038 : Nat := 1173487463918376012839831

theorem tailTrace_3428038 : CollatzResearch.WordTrace tailWord_3428038 prefixEnd_3428038 1173487463918376012839831 := by
  unfold tailWord_3428038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3907213048587851972639899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83353878369874175416317845 3907213048587851972639899)
  ·
    refine ⟨5860819572881777958959849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3907213048587851972639899 5860819572881777958959849)
    ·
      refine ⟨4395614679661333469219887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5860819572881777958959849 4395614679661333469219887)
      ·
        refine ⟨6593422019492000203829831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4395614679661333469219887 6593422019492000203829831)
        ·
          refine ⟨9890133029238000305744747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6593422019492000203829831 9890133029238000305744747)
          ·
            refine ⟨14835199543857000458617121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9890133029238000305744747 14835199543857000458617121)
            ·
              refine ⟨11126399657892750343962841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14835199543857000458617121 11126399657892750343962841)
              ·
                refine ⟨8344799743419562757972131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11126399657892750343962841 8344799743419562757972131)
                ·
                  refine ⟨12517199615129344136958197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8344799743419562757972131 12517199615129344136958197)
                  ·
                    refine ⟨1173487463918376012839831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12517199615129344136958197 1173487463918376012839831)
                    ·
                      rfl

theorem cell22_3428038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3428038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428038 prefixEnd_3428038 := by exact prefixLift 3428038
  have htrace : WordTrace (prefixWord ++ tailWord_3428038) baseStart_3428038 baseEnd_3428038 := by
    simpa [prefixWord, tailWord_3428038, baseEnd_3428038] using wordTrace_append hprefix tailTrace_3428038
  have hstable : (prefixWord ++ tailWord_3428038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428038).length < 2 ^ (prefixWord ++ tailWord_3428038).sum := by decide
  have hdescent : baseEnd_3428038 < baseStart_3428038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428100 : List Nat := [2, 3, 2, 2, 1, 4, 1, 3, 1, 3]
def baseStart_3428100 : Nat := 118140960795 + 3428100 * 2 ^ 59
def prefixEnd_3428100 : Nat := 4983230072969 + 3 ^ 40 * 3428100 * 2
def baseEnd_3428100 : Nat := 1173508687785428517789641

theorem tailTrace_3428100 : CollatzResearch.WordTrace tailWord_3428100 prefixEnd_3428100 1173508687785428517789641 := by
  unfold tailWord_3428100
  simp only [CollatzResearch.WordTrace]
  refine ⟨62516539440293323856616877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83355385920391098475489169 62516539440293323856616877)
  ·
    refine ⟨23443702290109996446231329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62516539440293323856616877 23443702290109996446231329)
    ·
      refine ⟨17582776717582497334673497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23443702290109996446231329 17582776717582497334673497)
      ·
        refine ⟨13187082538186873001005123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17582776717582497334673497 13187082538186873001005123)
        ·
          refine ⟨19780623807280309501507685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13187082538186873001005123 19780623807280309501507685)
          ·
            refine ⟨3708866963865058031532691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19780623807280309501507685 3708866963865058031532691)
            ·
              refine ⟨5563300445797587047299037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3708866963865058031532691 5563300445797587047299037)
              ·
                refine ⟨2086237667174095142737139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5563300445797587047299037 2086237667174095142737139)
                ·
                  refine ⟨3129356500761142714105709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2086237667174095142737139 3129356500761142714105709)
                  ·
                    refine ⟨1173508687785428517789641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3129356500761142714105709 1173508687785428517789641)
                    ·
                      rfl

theorem cell22_3428100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_3428100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428100 prefixEnd_3428100 := by exact prefixLift 3428100
  have htrace : WordTrace (prefixWord ++ tailWord_3428100) baseStart_3428100 baseEnd_3428100 := by
    simpa [prefixWord, tailWord_3428100, baseEnd_3428100] using wordTrace_append hprefix tailTrace_3428100
  have hstable : (prefixWord ++ tailWord_3428100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428100).length < 2 ^ (prefixWord ++ tailWord_3428100).sum := by decide
  have hdescent : baseEnd_3428100 < baseStart_3428100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428102 : List Nat := [6, 2, 2, 1, 1, 2, 8]
def baseStart_3428102 : Nat := 118140960795 + 3428102 * 2 ^ 59
def prefixEnd_3428102 : Nat := 4983230072969 + 3 ^ 40 * 3428102 * 2
def baseEnd_3428102 : Nat := 43463310089863006638505

theorem tailTrace_3428102 : CollatzResearch.WordTrace tailWord_3428102 prefixEnd_3428102 43463310089863006638505 := by
  unfold tailWord_3428102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3907285994580606314212705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83355434551052934703204373 3907285994580606314212705)
  ·
    refine ⟨2930464495935454735659529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3907285994580606314212705 2930464495935454735659529)
    ·
      refine ⟨2197848371951591051744647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2930464495935454735659529 2197848371951591051744647)
      ·
        refine ⟨3296772557927386577616971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2197848371951591051744647 3296772557927386577616971)
        ·
          refine ⟨4945158836891079866425457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3296772557927386577616971 4945158836891079866425457)
          ·
            refine ⟨3708869127668309899819093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4945158836891079866425457 3708869127668309899819093)
            ·
              refine ⟨43463310089863006638505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3708869127668309899819093 43463310089863006638505)
              ·
                rfl

theorem cell22_3428102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 8].length) (baseStart_3428102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428102 prefixEnd_3428102 := by exact prefixLift 3428102
  have htrace : WordTrace (prefixWord ++ tailWord_3428102) baseStart_3428102 baseEnd_3428102 := by
    simpa [prefixWord, tailWord_3428102, baseEnd_3428102] using wordTrace_append hprefix tailTrace_3428102
  have hstable : (prefixWord ++ tailWord_3428102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428102).length < 2 ^ (prefixWord ++ tailWord_3428102).sum := by decide
  have hdescent : baseEnd_3428102 < baseStart_3428102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428107 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 8]
def baseStart_3428107 : Nat := 118140960795 + 3428107 * 2 ^ 59
def prefixEnd_3428107 : Nat := 4983230072969 + 3 ^ 40 * 3428107 * 2
def baseEnd_3428107 : Nat := 391170361342827610954873

theorem tailTrace_3428107 : CollatzResearch.WordTrace tailWord_3428107 prefixEnd_3428107 391170361342827610954873 := by
  unfold tailWord_3428107
  simp only [CollatzResearch.WordTrace]
  refine ⟨125033334191561287908738575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83355556127707525272492383 125033334191561287908738575)
  ·
    refine ⟨187550001287341931863107863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125033334191561287908738575 187550001287341931863107863)
    ·
      refine ⟨281325001931012897794661795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187550001287341931863107863 281325001931012897794661795)
      ·
        refine ⟨421987502896519346691992693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281325001931012897794661795 421987502896519346691992693)
        ·
          refine ⟨39561328396548688752374315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 421987502896519346691992693 39561328396548688752374315)
          ·
            refine ⟨59341992594823033128561473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39561328396548688752374315 59341992594823033128561473)
            ·
              refine ⟨44506494446117274846421105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59341992594823033128561473 44506494446117274846421105)
              ·
                refine ⟨33379870834587956134815829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44506494446117274846421105 33379870834587956134815829)
                ·
                  refine ⟨391170361342827610954873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33379870834587956134815829 391170361342827610954873)
                  ·
                    rfl

theorem cell22_3428107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 8].length) (baseStart_3428107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428107 prefixEnd_3428107 := by exact prefixLift 3428107
  have htrace : WordTrace (prefixWord ++ tailWord_3428107) baseStart_3428107 baseEnd_3428107 := by
    simpa [prefixWord, tailWord_3428107, baseEnd_3428107] using wordTrace_append hprefix tailTrace_3428107
  have hstable : (prefixWord ++ tailWord_3428107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428107).length < 2 ^ (prefixWord ++ tailWord_3428107).sum := by decide
  have hdescent : baseEnd_3428107 < baseStart_3428107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428199 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 2, 6]
def baseStart_3428199 : Nat := 118140960795 + 3428199 * 2 ^ 59
def prefixEnd_3428199 : Nat := 4983230072969 + 3 ^ 40 * 3428199 * 2
def baseEnd_3428199 : Nat := 1173542577508625259564337

theorem tailTrace_3428199 : CollatzResearch.WordTrace tailWord_3428199 prefixEnd_3428199 1173542577508625259564337 := by
  unfold tailWord_3428199
  simp only [CollatzResearch.WordTrace]
  refine ⟨125036689707227987621087651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83357793138151991747391767 125036689707227987621087651)
  ·
    refine ⟨187555034560841981431631477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125036689707227987621087651 187555034560841981431631477)
    ·
      refine ⟨17583284490078935759215451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187555034560841981431631477 17583284490078935759215451)
      ·
        refine ⟨26374926735118403638823177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17583284490078935759215451 26374926735118403638823177)
        ·
          refine ⟨19781195051338802729117383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26374926735118403638823177 19781195051338802729117383)
          ·
            refine ⟨29671792577008204093676075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19781195051338802729117383 29671792577008204093676075)
            ·
              refine ⟨44507688865512306140514113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29671792577008204093676075 44507688865512306140514113)
              ·
                refine ⟨33380766649134229605385585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44507688865512306140514113 33380766649134229605385585)
                ·
                  refine ⟨25035574986850672204039189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33380766649134229605385585 25035574986850672204039189)
                  ·
                    refine ⟨1173542577508625259564337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25035574986850672204039189 1173542577508625259564337)
                    ·
                      rfl

theorem cell22_3428199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_3428199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428199 prefixEnd_3428199 := by exact prefixLift 3428199
  have htrace : WordTrace (prefixWord ++ tailWord_3428199) baseStart_3428199 baseEnd_3428199 := by
    simpa [prefixWord, tailWord_3428199, baseEnd_3428199] using wordTrace_append hprefix tailTrace_3428199
  have hstable : (prefixWord ++ tailWord_3428199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428199).length < 2 ^ (prefixWord ++ tailWord_3428199).sum := by decide
  have hdescent : baseEnd_3428199 < baseStart_3428199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428218 : List Nat := [3, 1, 1, 1, 1, 1, 5, 5, 1, 3]
def baseStart_3428218 : Nat := 118140960795 + 3428218 * 2 ^ 59
def prefixEnd_3428218 : Nat := 4983230072969 + 3 ^ 40 * 3428218 * 2
def baseEnd_3428218 : Nat := 1173549081596915543339279

theorem tailTrace_3428218 : CollatzResearch.WordTrace tailWord_3428218 prefixEnd_3428218 1173549081596915543339279 := by
  unfold tailWord_3428218
  simp only [CollatzResearch.WordTrace]
  refine ⟨31259345673539788466507327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83358255129439435910686205 31259345673539788466507327)
  ·
    refine ⟨46889018510309682699760991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31259345673539788466507327 46889018510309682699760991)
    ·
      refine ⟨70333527765464524049641487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46889018510309682699760991 70333527765464524049641487)
      ·
        refine ⟨105500291648196786074462231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70333527765464524049641487 105500291648196786074462231)
        ·
          refine ⟨158250437472295179111693347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105500291648196786074462231 158250437472295179111693347)
          ·
            refine ⟨237375656208442768667540021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158250437472295179111693347 237375656208442768667540021)
            ·
              refine ⟨22253967769541509562581877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 237375656208442768667540021 22253967769541509562581877)
              ·
                refine ⟨2086309478394516521492051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22253967769541509562581877 2086309478394516521492051)
                ·
                  refine ⟨3129464217591774782238077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2086309478394516521492051 3129464217591774782238077)
                  ·
                    refine ⟨1173549081596915543339279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3129464217591774782238077 1173549081596915543339279)
                    ·
                      rfl

theorem cell22_3428218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 1, 3].length) (baseStart_3428218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428218 prefixEnd_3428218 := by exact prefixLift 3428218
  have htrace : WordTrace (prefixWord ++ tailWord_3428218) baseStart_3428218 baseEnd_3428218 := by
    simpa [prefixWord, tailWord_3428218, baseEnd_3428218] using wordTrace_append hprefix tailTrace_3428218
  have hstable : (prefixWord ++ tailWord_3428218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428218).length < 2 ^ (prefixWord ++ tailWord_3428218).sum := by decide
  have hdescent : baseEnd_3428218 < baseStart_3428218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428229 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 4, 5]
def baseStart_3428229 : Nat := 118140960795 + 3428229 * 2 ^ 59
def prefixEnd_3428229 : Nat := 4983230072969 + 3 ^ 40 * 3428229 * 2
def baseEnd_3428229 : Nat := 1173552847121715181314245

theorem tailTrace_3428229 : CollatzResearch.WordTrace tailWord_3428229 prefixEnd_3428229 1173552847121715181314245 := by
  unfold tailWord_3428229
  simp only [CollatzResearch.WordTrace]
  refine ⟨125037783897119302744679741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83358522598079535163119827 125037783897119302744679741)
  ·
    refine ⟨46889168961419738529254903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125037783897119302744679741 46889168961419738529254903)
    ·
      refine ⟨70333753442129607793882355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46889168961419738529254903 70333753442129607793882355)
      ·
        refine ⟨105500630163194411690823533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70333753442129607793882355 105500630163194411690823533)
        ·
          refine ⟨39562736311197904384058825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105500630163194411690823533 39562736311197904384058825)
          ·
            refine ⟨29672052233398428288044119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39562736311197904384058825 29672052233398428288044119)
            ·
              refine ⟨44508078350097642432066179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29672052233398428288044119 44508078350097642432066179)
              ·
                refine ⟨66762117525146463648099269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44508078350097642432066179 66762117525146463648099269)
                ·
                  refine ⟨12517897035964961934018613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66762117525146463648099269 12517897035964961934018613)
                  ·
                    refine ⟨1173552847121715181314245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12517897035964961934018613 1173552847121715181314245)
                    ·
                      rfl

theorem cell22_3428229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_3428229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428229 prefixEnd_3428229 := by exact prefixLift 3428229
  have htrace : WordTrace (prefixWord ++ tailWord_3428229) baseStart_3428229 baseEnd_3428229 := by
    simpa [prefixWord, tailWord_3428229, baseEnd_3428229] using wordTrace_append hprefix tailTrace_3428229
  have hstable : (prefixWord ++ tailWord_3428229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428229).length < 2 ^ (prefixWord ++ tailWord_3428229).sum := by decide
  have hdescent : baseEnd_3428229 < baseStart_3428229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428231 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 7]
def baseStart_3428231 : Nat := 118140960795 + 3428231 * 2 ^ 59
def prefixEnd_3428231 : Nat := 4983230072969 + 3 ^ 40 * 3428231 * 2
def baseEnd_3428231 : Nat := 391184510587529280921413

theorem tailTrace_3428231 : CollatzResearch.WordTrace tailWord_3428231 prefixEnd_3428231 391184510587529280921413 := by
  unfold tailWord_3428231
  simp only [CollatzResearch.WordTrace]
  refine ⟨125037856843112057086252547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83358571228741371390835031 125037856843112057086252547)
  ·
    refine ⟨187556785264668085629378821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125037856843112057086252547 187556785264668085629378821)
    ·
      refine ⟨35166897237125266055508529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187556785264668085629378821 35166897237125266055508529)
      ·
        refine ⟨26375172927843949541631397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35166897237125266055508529 26375172927843949541631397)
        ·
          refine ⟨4945344923970740539055887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26375172927843949541631397 4945344923970740539055887)
          ·
            refine ⟨7418017385956110808583831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4945344923970740539055887 7418017385956110808583831)
            ·
              refine ⟨11127026078934166212875747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7418017385956110808583831 11127026078934166212875747)
              ·
                refine ⟨16690539118401249319313621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11127026078934166212875747 16690539118401249319313621)
                ·
                  refine ⟨391184510587529280921413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16690539118401249319313621 391184510587529280921413)
                  ·
                    rfl

theorem cell22_3428231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 7].length) (baseStart_3428231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428231 prefixEnd_3428231 := by exact prefixLift 3428231
  have htrace : WordTrace (prefixWord ++ tailWord_3428231) baseStart_3428231 baseEnd_3428231 := by
    simpa [prefixWord, tailWord_3428231, baseEnd_3428231] using wordTrace_append hprefix tailTrace_3428231
  have hstable : (prefixWord ++ tailWord_3428231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428231).length < 2 ^ (prefixWord ++ tailWord_3428231).sum := by decide
  have hdescent : baseEnd_3428231 < baseStart_3428231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428304 : List Nat := [2, 1, 1, 1, 1, 2, 5, 9]
def baseStart_3428304 : Nat := 118140960795 + 3428304 * 2 ^ 59
def prefixEnd_3428304 : Nat := 4983230072969 + 3 ^ 40 * 3428304 * 2
def baseEnd_3428304 : Nat := 130397613461604442854335

theorem tailTrace_3428304 : CollatzResearch.WordTrace tailWord_3428304 prefixEnd_3428304 130397613461604442854335 := by
  unfold tailWord_3428304
  simp only [CollatzResearch.WordTrace]
  refine ⟨62520259685923795276829983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83360346247898393702439977 62520259685923795276829983)
  ·
    refine ⟨93780389528885692915244975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62520259685923795276829983 93780389528885692915244975)
    ·
      refine ⟨140670584293328539372867463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93780389528885692915244975 140670584293328539372867463)
      ·
        refine ⟨211005876439992809059301195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140670584293328539372867463 211005876439992809059301195)
        ·
          refine ⟨316508814659989213588951793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211005876439992809059301195 316508814659989213588951793)
          ·
            refine ⟨237381610994991910191713845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316508814659989213588951793 237381610994991910191713845)
            ·
              refine ⟨22254526030780491580473173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 237381610994991910191713845 22254526030780491580473173)
              ·
                refine ⟨130397613461604442854335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22254526030780491580473173 130397613461604442854335)
                ·
                  rfl

theorem cell22_3428304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 9].length) (baseStart_3428304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428304 prefixEnd_3428304 := by exact prefixLift 3428304
  have htrace : WordTrace (prefixWord ++ tailWord_3428304) baseStart_3428304 baseEnd_3428304 := by
    simpa [prefixWord, tailWord_3428304, baseEnd_3428304] using wordTrace_append hprefix tailTrace_3428304
  have hstable : (prefixWord ++ tailWord_3428304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428304).length < 2 ^ (prefixWord ++ tailWord_3428304).sum := by decide
  have hdescent : baseEnd_3428304 < baseStart_3428304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428323 : List Nat := [1, 1, 1, 6, 1, 3, 2, 1, 2, 4]
def baseStart_3428323 : Nat := 118140960795 + 3428323 * 2 ^ 59
def prefixEnd_3428323 : Nat := 4983230072969 + 3 ^ 40 * 3428323 * 2
def baseEnd_3428323 : Nat := 1173585025242730269463957

theorem tailTrace_3428323 : CollatzResearch.WordTrace tailWord_3428323 prefixEnd_3428323 1173585025242730269463957 := by
  unfold tailWord_3428323
  simp only [CollatzResearch.WordTrace]
  refine ⟨125041212358778756798601623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83360808239185837865734415 125041212358778756798601623)
  ·
    refine ⟨187561818538168135197902435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125041212358778756798601623 187561818538168135197902435)
    ·
      refine ⟨281342727807252202796853653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187561818538168135197902435 281342727807252202796853653)
      ·
        refine ⟨13187940365964947006102515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 281342727807252202796853653 13187940365964947006102515)
        ·
          refine ⟨19781910548947420509153773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13187940365964947006102515 19781910548947420509153773)
          ·
            refine ⟨7418216455855282690932665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19781910548947420509153773 7418216455855282690932665)
            ·
              refine ⟨5563662341891462018199499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7418216455855282690932665 5563662341891462018199499)
              ·
                refine ⟨8345493512837193027299249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5563662341891462018199499 8345493512837193027299249)
                ·
                  refine ⟨6259120134627894770474437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8345493512837193027299249 6259120134627894770474437)
                  ·
                    refine ⟨1173585025242730269463957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6259120134627894770474437 1173585025242730269463957)
                    ·
                      rfl

theorem cell22_3428323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 4].length) (baseStart_3428323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428323 prefixEnd_3428323 := by exact prefixLift 3428323
  have htrace : WordTrace (prefixWord ++ tailWord_3428323) baseStart_3428323 baseEnd_3428323 := by
    simpa [prefixWord, tailWord_3428323, baseEnd_3428323] using wordTrace_append hprefix tailTrace_3428323
  have hstable : (prefixWord ++ tailWord_3428323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428323).length < 2 ^ (prefixWord ++ tailWord_3428323).sum := by decide
  have hdescent : baseEnd_3428323 < baseStart_3428323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428342 : List Nat := [5, 1, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_3428342 : Nat := 118140960795 + 3428342 * 2 ^ 59
def prefixEnd_3428342 : Nat := 4983230072969 + 3 ^ 40 * 3428342 * 2
def baseEnd_3428342 : Nat := 1173591529331020553238899

theorem tailTrace_3428342 : CollatzResearch.WordTrace tailWord_3428342 prefixEnd_3428342 1173591529331020553238899 := by
  unfold tailWord_3428342
  simp only [CollatzResearch.WordTrace]
  refine ⟨7815119084106870190221455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83361270230473282029028853 7815119084106870190221455)
  ·
    refine ⟨11722678626160305285332183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7815119084106870190221455 11722678626160305285332183)
    ·
      refine ⟨17584017939240457927998275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11722678626160305285332183 17584017939240457927998275)
      ·
        refine ⟨26376026908860686891997413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17584017939240457927998275 26376026908860686891997413)
        ·
          refine ⟨4945505045411378792249515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26376026908860686891997413 4945505045411378792249515)
          ·
            refine ⟨7418257568117068188374273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4945505045411378792249515 7418257568117068188374273)
            ·
              refine ⟨5563693176087801141280705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7418257568117068188374273 5563693176087801141280705)
              ·
                refine ⟨4172769882065850855960529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5563693176087801141280705 4172769882065850855960529)
                ·
                  refine ⟨3129577411549388141970397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4172769882065850855960529 3129577411549388141970397)
                  ·
                    refine ⟨1173591529331020553238899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3129577411549388141970397 1173591529331020553238899)
                    ·
                      rfl

theorem cell22_3428342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_3428342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428342 prefixEnd_3428342 := by exact prefixLift 3428342
  have htrace : WordTrace (prefixWord ++ tailWord_3428342) baseStart_3428342 baseEnd_3428342 := by
    simpa [prefixWord, tailWord_3428342, baseEnd_3428342] using wordTrace_append hprefix tailTrace_3428342
  have hstable : (prefixWord ++ tailWord_3428342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428342).length < 2 ^ (prefixWord ++ tailWord_3428342).sum := by decide
  have hdescent : baseEnd_3428342 < baseStart_3428342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428353 : List Nat := [1, 2, 4, 1, 2, 1, 2, 3, 3, 3]
def baseStart_3428353 : Nat := 118140960795 + 3428353 * 2 ^ 59
def prefixEnd_3428353 : Nat := 4983230072969 + 3 ^ 40 * 3428353 * 2
def baseEnd_3428353 : Nat := 1173595294855820191213865

theorem tailTrace_3428353 : CollatzResearch.WordTrace tailWord_3428353 prefixEnd_3428353 1173595294855820191213865 := by
  unfold tailWord_3428353
  simp only [CollatzResearch.WordTrace]
  refine ⟨125042306548670071922193713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83361537699113381281462475 125042306548670071922193713)
  ·
    refine ⟨93781729911502553941645285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125042306548670071922193713 93781729911502553941645285)
    ·
      refine ⟨17584074358406728864058491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93781729911502553941645285 17584074358406728864058491)
      ·
        refine ⟨26376111537610093296087737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17584074358406728864058491 26376111537610093296087737)
        ·
          refine ⟨19782083653207569972065803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26376111537610093296087737 19782083653207569972065803)
          ·
            refine ⟨29673125479811354958098705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19782083653207569972065803 29673125479811354958098705)
            ·
              refine ⟨22254844109858516218574029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29673125479811354958098705 22254844109858516218574029)
              ·
                refine ⟨8345566541196943581965261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22254844109858516218574029 8345566541196943581965261)
                ·
                  refine ⟨3129587452948853843236973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8345566541196943581965261 3129587452948853843236973)
                  ·
                    refine ⟨1173595294855820191213865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3129587452948853843236973 1173595294855820191213865)
                    ·
                      rfl

theorem cell22_3428353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_3428353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428353 prefixEnd_3428353 := by exact prefixLift 3428353
  have htrace : WordTrace (prefixWord ++ tailWord_3428353) baseStart_3428353 baseEnd_3428353 := by
    simpa [prefixWord, tailWord_3428353, baseEnd_3428353] using wordTrace_append hprefix tailTrace_3428353
  have hstable : (prefixWord ++ tailWord_3428353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428353).length < 2 ^ (prefixWord ++ tailWord_3428353).sum := by decide
  have hdescent : baseEnd_3428353 < baseStart_3428353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428372 : List Nat := [2, 4, 3, 2, 1, 1, 3, 6]
def baseStart_3428372 : Nat := 118140960795 + 3428372 * 2 ^ 59
def prefixEnd_3428372 : Nat := 4983230072969 + 3 ^ 40 * 3428372 * 2
def baseEnd_3428372 : Nat := 130400199882678941665423

theorem tailTrace_3428372 : CollatzResearch.WordTrace tailWord_3428372 prefixEnd_3428372 130400199882678941665423 := by
  unfold tailWord_3428372
  simp only [CollatzResearch.WordTrace]
  refine ⟨62521499767800619083567685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83361999690400825444756913 62521499767800619083567685)
  ·
    refine ⟨11722781206462616078168941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62521499767800619083567685 11722781206462616078168941)
    ·
      refine ⟨4396042952423481029313353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11722781206462616078168941 4396042952423481029313353)
      ·
        refine ⟨3297032214317610771985015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4396042952423481029313353 3297032214317610771985015)
        ·
          refine ⟨4945548321476416157977523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3297032214317610771985015 4945548321476416157977523)
          ·
            refine ⟨7418322482214624236966285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4945548321476416157977523 7418322482214624236966285)
            ·
              refine ⟨2781870930830484088862357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7418322482214624236966285 2781870930830484088862357)
              ·
                refine ⟨130400199882678941665423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2781870930830484088862357 130400199882678941665423)
                ·
                  rfl

theorem cell22_3428372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 6].length) (baseStart_3428372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428372 prefixEnd_3428372 := by exact prefixLift 3428372
  have htrace : WordTrace (prefixWord ++ tailWord_3428372) baseStart_3428372 baseEnd_3428372 := by
    simpa [prefixWord, tailWord_3428372, baseEnd_3428372] using wordTrace_append hprefix tailTrace_3428372
  have hstable : (prefixWord ++ tailWord_3428372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428372).length < 2 ^ (prefixWord ++ tailWord_3428372).sum := by decide
  have hdescent : baseEnd_3428372 < baseStart_3428372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428396 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 5, 4]
def baseStart_3428396 : Nat := 118140960795 + 3428396 * 2 ^ 59
def prefixEnd_3428396 : Nat := 4983230072969 + 3 ^ 40 * 3428396 * 2
def baseEnd_3428396 : Nat := 1173610014634582412388733

theorem tailTrace_3428396 : CollatzResearch.WordTrace tailWord_3428396 prefixEnd_3428396 1173610014634582412388733 := by
  unfold tailWord_3428396
  simp only [CollatzResearch.WordTrace]
  refine ⟨62521937443757145133004521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83362583258342860177339361 62521937443757145133004521)
  ·
    refine ⟨46891453082817858849753391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62521937443757145133004521 46891453082817858849753391)
    ·
      refine ⟨70337179624226788274630087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46891453082817858849753391 70337179624226788274630087)
      ·
        refine ⟨105505769436340182411945131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70337179624226788274630087 105505769436340182411945131)
        ·
          refine ⟨158258654154510273617917697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105505769436340182411945131 158258654154510273617917697)
          ·
            refine ⟨118693990615882705213438273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158258654154510273617917697 118693990615882705213438273)
            ·
              refine ⟨89020492961912028910078705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118693990615882705213438273 89020492961912028910078705)
              ·
                refine ⟨66765369721434021682559029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89020492961912028910078705 66765369721434021682559029)
                ·
                  refine ⟨6259253411384439532739909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66765369721434021682559029 6259253411384439532739909)
                  ·
                    refine ⟨1173610014634582412388733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6259253411384439532739909 1173610014634582412388733)
                    ·
                      rfl

theorem cell22_3428396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_3428396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428396 prefixEnd_3428396 := by exact prefixLift 3428396
  have htrace : WordTrace (prefixWord ++ tailWord_3428396) baseStart_3428396 baseEnd_3428396 := by
    simpa [prefixWord, tailWord_3428396, baseEnd_3428396] using wordTrace_append hprefix tailTrace_3428396
  have hstable : (prefixWord ++ tailWord_3428396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428396).length < 2 ^ (prefixWord ++ tailWord_3428396).sum := by decide
  have hdescent : baseEnd_3428396 < baseStart_3428396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428398 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_3428398 : Nat := 118140960795 + 3428398 * 2 ^ 59
def prefixEnd_3428398 : Nat := 4983230072969 + 3 ^ 40 * 3428398 * 2
def baseEnd_3428398 : Nat := 1173610699275455073838727

theorem tailTrace_3428398 : CollatzResearch.WordTrace tailWord_3428398 prefixEnd_3428398 1173610699275455073838727 := by
  unfold tailWord_3428398
  simp only [CollatzResearch.WordTrace]
  refine ⟨15630493479188380575947731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83362631889004696405054565 15630493479188380575947731)
  ·
    refine ⟨23445740218782570863921597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15630493479188380575947731 23445740218782570863921597)
    ·
      refine ⟨8792152582043464073970599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23445740218782570863921597 8792152582043464073970599)
      ·
        refine ⟨13188228873065196110955899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8792152582043464073970599 13188228873065196110955899)
        ·
          refine ⟨19782343309597794166433849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13188228873065196110955899 19782343309597794166433849)
          ·
            refine ⟨14836757482198345624825387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19782343309597794166433849 14836757482198345624825387)
            ·
              refine ⟨22255136223297518437238081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14836757482198345624825387 22255136223297518437238081)
              ·
                refine ⟨16691352167473138827928561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22255136223297518437238081 16691352167473138827928561)
                ·
                  refine ⟨12518514125604854120946421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16691352167473138827928561 12518514125604854120946421)
                  ·
                    refine ⟨1173610699275455073838727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12518514125604854120946421 1173610699275455073838727)
                    ·
                      rfl

theorem cell22_3428398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_3428398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428398 prefixEnd_3428398 := by exact prefixLift 3428398
  have htrace : WordTrace (prefixWord ++ tailWord_3428398) baseStart_3428398 baseEnd_3428398 := by
    simpa [prefixWord, tailWord_3428398, baseEnd_3428398] using wordTrace_append hprefix tailTrace_3428398
  have hstable : (prefixWord ++ tailWord_3428398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428398).length < 2 ^ (prefixWord ++ tailWord_3428398).sum := by decide
  have hdescent : baseEnd_3428398 < baseStart_3428398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428430 : List Nat := [4, 1, 1, 1, 1, 5, 2, 2, 1, 4]
def baseStart_3428430 : Nat := 118140960795 + 3428430 * 2 ^ 59
def prefixEnd_3428430 : Nat := 4983230072969 + 3 ^ 40 * 3428430 * 2
def baseEnd_3428430 : Nat := 1173621653529417657038629

theorem tailTrace_3428430 : CollatzResearch.WordTrace tailWord_3428430 prefixEnd_3428430 1173621653529417657038629 := by
  unfold tailWord_3428430
  simp only [CollatzResearch.WordTrace]
  refine ⟨15630639371173889259093343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83363409979594076048497829 15630639371173889259093343)
  ·
    refine ⟨23445959056760833888640015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15630639371173889259093343 23445959056760833888640015)
    ·
      refine ⟨35168938585141250832960023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23445959056760833888640015 35168938585141250832960023)
      ·
        refine ⟨52753407877711876249440035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35168938585141250832960023 52753407877711876249440035)
        ·
          refine ⟨79130111816567814374160053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52753407877711876249440035 79130111816567814374160053)
          ·
            refine ⟨7418447982803232597577505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79130111816567814374160053 7418447982803232597577505)
            ·
              refine ⟨5563835987102424448183129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7418447982803232597577505 5563835987102424448183129)
              ·
                refine ⟨4172876990326818336137347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5563835987102424448183129 4172876990326818336137347)
                ·
                  refine ⟨6259315485490227504206021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4172876990326818336137347 6259315485490227504206021)
                  ·
                    refine ⟨1173621653529417657038629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6259315485490227504206021 1173621653529417657038629)
                    ·
                      rfl

theorem cell22_3428430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_3428430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428430 prefixEnd_3428430 := by exact prefixLift 3428430
  have htrace : WordTrace (prefixWord ++ tailWord_3428430) baseStart_3428430 baseEnd_3428430 := by
    simpa [prefixWord, tailWord_3428430, baseEnd_3428430] using wordTrace_append hprefix tailTrace_3428430
  have hstable : (prefixWord ++ tailWord_3428430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428430).length < 2 ^ (prefixWord ++ tailWord_3428430).sum := by decide
  have hdescent : baseEnd_3428430 < baseStart_3428430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428441 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 1, 6]
def baseStart_3428441 : Nat := 118140960795 + 3428441 * 2 ^ 59
def prefixEnd_3428441 : Nat := 4983230072969 + 3 ^ 40 * 3428441 * 2
def baseEnd_3428441 : Nat := 1173625419054217295013595

theorem tailTrace_3428441 : CollatzResearch.WordTrace tailWord_3428441 prefixEnd_3428441 1173625419054217295013595 := by
  unfold tailWord_3428441
  simp only [CollatzResearch.WordTrace]
  refine ⟨125045516172351262951397177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83363677448234175300931451 125045516172351262951397177)
  ·
    refine ⟨93784137129263447213547883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125045516172351262951397177 93784137129263447213547883)
    ·
      refine ⟨140676205693895170820321825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93784137129263447213547883 140676205693895170820321825)
      ·
        refine ⟨105507154270421378115241369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140676205693895170820321825 105507154270421378115241369)
        ·
          refine ⟨79130365702816033586431027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105507154270421378115241369 79130365702816033586431027)
          ·
            refine ⟨118695548554224050379646541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79130365702816033586431027 118695548554224050379646541)
            ·
              refine ⟨44510830707834018892367453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118695548554224050379646541 44510830707834018892367453)
              ·
                refine ⟨16691561515437757084637795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44510830707834018892367453 16691561515437757084637795)
                ·
                  refine ⟨25037342273156635626956693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16691561515437757084637795 25037342273156635626956693)
                  ·
                    refine ⟨1173625419054217295013595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25037342273156635626956693 1173625419054217295013595)
                    ·
                      rfl

theorem cell22_3428441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_3428441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428441 prefixEnd_3428441 := by exact prefixLift 3428441
  have htrace : WordTrace (prefixWord ++ tailWord_3428441) baseStart_3428441 baseEnd_3428441 := by
    simpa [prefixWord, tailWord_3428441, baseEnd_3428441] using wordTrace_append hprefix tailTrace_3428441
  have hstable : (prefixWord ++ tailWord_3428441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428441).length < 2 ^ (prefixWord ++ tailWord_3428441).sum := by decide
  have hdescent : baseEnd_3428441 < baseStart_3428441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428462 : List Nat := [4, 1, 2, 2, 1, 1, 5, 2, 4]
def baseStart_3428462 : Nat := 118140960795 + 3428462 * 2 ^ 59
def prefixEnd_3428462 : Nat := 4983230072969 + 3 ^ 40 * 3428462 * 2
def baseEnd_3428462 : Nat := 391210869261126746746177

theorem tailTrace_3428462 : CollatzResearch.WordTrace tailWord_3428462 prefixEnd_3428462 391210869261126746746177 := by
  unfold tailWord_3428462
  simp only [CollatzResearch.WordTrace]
  refine ⟨15630785263159397942238955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83364188070183455691941093 15630785263159397942238955)
  ·
    refine ⟨23446177894739096913358433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15630785263159397942238955 23446177894739096913358433)
    ·
      refine ⟨17584633421054322685018825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23446177894739096913358433 17584633421054322685018825)
      ·
        refine ⟨13188475065790742013764119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17584633421054322685018825 13188475065790742013764119)
        ·
          refine ⟨19782712598686113020646179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13188475065790742013764119 19782712598686113020646179)
          ·
            refine ⟨29674068898029169530969269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19782712598686113020646179 29674068898029169530969269)
            ·
              refine ⟨2781943959190234643528369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29674068898029169530969269 2781943959190234643528369)
              ·
                refine ⟨2086457969392675982646277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2781943959190234643528369 2086457969392675982646277)
                ·
                  refine ⟨391210869261126746746177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2086457969392675982646277 391210869261126746746177)
                  ·
                    rfl

theorem cell22_3428462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_3428462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428462 prefixEnd_3428462 := by exact prefixLift 3428462
  have htrace : WordTrace (prefixWord ++ tailWord_3428462) baseStart_3428462 baseEnd_3428462 := by
    simpa [prefixWord, tailWord_3428462, baseEnd_3428462] using wordTrace_append hprefix tailTrace_3428462
  have hstable : (prefixWord ++ tailWord_3428462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428462).length < 2 ^ (prefixWord ++ tailWord_3428462).sum := by decide
  have hdescent : baseEnd_3428462 < baseStart_3428462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428473 : List Nat := [1, 2, 1, 3, 4, 2, 2, 7]
def baseStart_3428473 : Nat := 118140960795 + 3428473 * 2 ^ 59
def prefixEnd_3428473 : Nat := 4983230072969 + 3 ^ 40 * 3428473 * 2
def baseEnd_3428473 : Nat := 130404041478686653134833

theorem tailTrace_3428473 : CollatzResearch.WordTrace tailWord_3428473 prefixEnd_3428473 130404041478686653134833 := by
  unfold tailWord_3428473
  simp only [CollatzResearch.WordTrace]
  refine ⟨125046683308235332416562073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83364455538823554944374715 125046683308235332416562073)
  ·
    refine ⟨93785012481176499312421555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125046683308235332416562073 93785012481176499312421555)
    ·
      refine ⟨140677518721764748968632333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93785012481176499312421555 140677518721764748968632333)
      ·
        refine ⟨52754069520661780863237125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140677518721764748968632333 52754069520661780863237125)
        ·
          refine ⟨9891388035124083911856961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52754069520661780863237125 9891388035124083911856961)
          ·
            refine ⟨7418541026343062933892721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9891388035124083911856961 7418541026343062933892721)
            ·
              refine ⟨5563905769757297200419541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7418541026343062933892721 5563905769757297200419541)
              ·
                refine ⟨130404041478686653134833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5563905769757297200419541 130404041478686653134833)
                ·
                  rfl

theorem cell22_3428473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 7].length) (baseStart_3428473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428473 prefixEnd_3428473 := by exact prefixLift 3428473
  have htrace : WordTrace (prefixWord ++ tailWord_3428473) baseStart_3428473 baseEnd_3428473 := by
    simpa [prefixWord, tailWord_3428473, baseEnd_3428473] using wordTrace_append hprefix tailTrace_3428473
  have hstable : (prefixWord ++ tailWord_3428473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428473).length < 2 ^ (prefixWord ++ tailWord_3428473).sum := by decide
  have hdescent : baseEnd_3428473 < baseStart_3428473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428477 : List Nat := [1, 4, 1, 1, 3, 2, 4, 1, 2, 3]
def baseStart_3428477 : Nat := 118140960795 + 3428477 * 2 ^ 59
def prefixEnd_3428477 : Nat := 4983230072969 + 3 ^ 40 * 3428477 * 2
def baseEnd_3428477 : Nat := 1173637742589925201113485

theorem tailTrace_3428477 : CollatzResearch.WordTrace tailWord_3428477 prefixEnd_3428477 1173637742589925201113485 := by
  unfold tailWord_3428477
  simp only [CollatzResearch.WordTrace]
  refine ⟨125046829200220841099707685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83364552800147227399805123 125046829200220841099707685)
  ·
    refine ⟨23446280475041407706195191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125046829200220841099707685 23446280475041407706195191)
    ·
      refine ⟨35169420712562111559292787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23446280475041407706195191 35169420712562111559292787)
      ·
        refine ⟨52754131068843167338939181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35169420712562111559292787 52754131068843167338939181)
        ·
          refine ⟨19782799150816187752102193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52754131068843167338939181 19782799150816187752102193)
          ·
            refine ⟨14837099363112140814076645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19782799150816187752102193 14837099363112140814076645)
            ·
              refine ⟨2781956130583526402639371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14837099363112140814076645 2781956130583526402639371)
              ·
                refine ⟨4172934195875289603959057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2781956130583526402639371 4172934195875289603959057)
                ·
                  refine ⟨3129700646906467202969293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4172934195875289603959057 3129700646906467202969293)
                  ·
                    refine ⟨1173637742589925201113485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3129700646906467202969293 1173637742589925201113485)
                    ·
                      rfl

theorem cell22_3428477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_3428477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428477 prefixEnd_3428477 := by exact prefixLift 3428477
  have htrace : WordTrace (prefixWord ++ tailWord_3428477) baseStart_3428477 baseEnd_3428477 := by
    simpa [prefixWord, tailWord_3428477, baseEnd_3428477] using wordTrace_append hprefix tailTrace_3428477
  have hstable : (prefixWord ++ tailWord_3428477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428477).length < 2 ^ (prefixWord ++ tailWord_3428477).sum := by decide
  have hdescent : baseEnd_3428477 < baseStart_3428477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428556 : List Nat := [2, 2, 1, 6, 1, 1, 2, 3, 1, 3]
def baseStart_3428556 : Nat := 118140960795 + 3428556 * 2 ^ 59
def prefixEnd_3428556 : Nat := 4983230072969 + 3 ^ 40 * 3428556 * 2
def baseEnd_3428556 : Nat := 1173664785904395328388243

theorem tailTrace_3428556 : CollatzResearch.WordTrace tailWord_3428556 prefixEnd_3428556 1173664785904395328388243 := by
  unfold tailWord_3428556
  simp only [CollatzResearch.WordTrace]
  refine ⟨62524855283467318795916761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83366473711289758394555681 62524855283467318795916761)
  ·
    refine ⟨46893641462600489096937571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62524855283467318795916761 46893641462600489096937571)
    ·
      refine ⟨70340462193900733645406357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46893641462600489096937571 70340462193900733645406357)
      ·
        refine ⟨3297209165339096889628423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70340462193900733645406357 3297209165339096889628423)
        ·
          refine ⟨4945813748008645334442635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3297209165339096889628423 4945813748008645334442635)
          ·
            refine ⟨7418720622012968001663953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4945813748008645334442635 7418720622012968001663953)
            ·
              refine ⟨5564040466509726001247965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7418720622012968001663953 5564040466509726001247965)
              ·
                refine ⟨2086515174941147250467987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5564040466509726001247965 2086515174941147250467987)
                ·
                  refine ⟨3129772762411720875701981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2086515174941147250467987 3129772762411720875701981)
                  ·
                    refine ⟨1173664785904395328388243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3129772762411720875701981 1173664785904395328388243)
                    ·
                      rfl

theorem cell22_3428556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 1, 3].length) (baseStart_3428556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428556 prefixEnd_3428556 := by exact prefixLift 3428556
  have htrace : WordTrace (prefixWord ++ tailWord_3428556) baseStart_3428556 baseEnd_3428556 := by
    simpa [prefixWord, tailWord_3428556, baseEnd_3428556] using wordTrace_append hprefix tailTrace_3428556
  have hstable : (prefixWord ++ tailWord_3428556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428556).length < 2 ^ (prefixWord ++ tailWord_3428556).sum := by decide
  have hdescent : baseEnd_3428556 < baseStart_3428556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428593 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 1, 6]
def baseStart_3428593 : Nat := 118140960795 + 3428593 * 2 ^ 59
def prefixEnd_3428593 : Nat := 4983230072969 + 3 ^ 40 * 3428593 * 2
def baseEnd_3428593 : Nat := 1173677451760539565213129

theorem tailTrace_3428593 : CollatzResearch.WordTrace tailWord_3428593 prefixEnd_3428593 1173677451760539565213129 := by
  unfold tailWord_3428593
  simp only [CollatzResearch.WordTrace]
  refine ⟨125051060067800592910930433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83367373378533728607286955 125051060067800592910930433)
  ·
    refine ⟨93788295050850444683197825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125051060067800592910930433 93788295050850444683197825)
    ·
      refine ⟨70341221288137833512398369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93788295050850444683197825 70341221288137833512398369)
      ·
        refine ⟨52755915966103375134298777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70341221288137833512398369 52755915966103375134298777)
        ·
          refine ⟨39566936974577531350724083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52755915966103375134298777 39566936974577531350724083)
          ·
            refine ⟨59350405461866297026086125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39566936974577531350724083 59350405461866297026086125)
            ·
              refine ⟨22256402048199861384782297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59350405461866297026086125 22256402048199861384782297)
              ·
                refine ⟨16692301536149896038586723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22256402048199861384782297 16692301536149896038586723)
                ·
                  refine ⟨25038452304224844057880085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16692301536149896038586723 25038452304224844057880085)
                  ·
                    refine ⟨1173677451760539565213129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25038452304224844057880085 1173677451760539565213129)
                    ·
                      rfl

theorem cell22_3428593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_3428593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428593 prefixEnd_3428593 := by exact prefixLift 3428593
  have htrace : WordTrace (prefixWord ++ tailWord_3428593) baseStart_3428593 baseEnd_3428593 := by
    simpa [prefixWord, tailWord_3428593, baseEnd_3428593] using wordTrace_append hprefix tailTrace_3428593
  have hstable : (prefixWord ++ tailWord_3428593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428593).length < 2 ^ (prefixWord ++ tailWord_3428593).sum := by decide
  have hdescent : baseEnd_3428593 < baseStart_3428593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428717 : List Nat := [1, 5, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_3428717 : Nat := 118140960795 + 3428717 * 2 ^ 59
def prefixEnd_3428717 : Nat := 4983230072969 + 3 ^ 40 * 3428717 * 2
def baseEnd_3428717 : Nat := 1173719899494644575112749

theorem tailTrace_3428717 : CollatzResearch.WordTrace tailWord_3428717 prefixEnd_3428717 1173719899494644575112749 := by
  unfold tailWord_3428717
  simp only [CollatzResearch.WordTrace]
  refine ⟨125055582719351362088444405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83370388479567574725629603 125055582719351362088444405)
  ·
    refine ⟨11723960879939190195791663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125055582719351362088444405 11723960879939190195791663)
    ·
      refine ⟨17585941319908785293687495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11723960879939190195791663 17585941319908785293687495)
      ·
        refine ⟨26378911979863177940531243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17585941319908785293687495 26378911979863177940531243)
        ·
          refine ⟨39568367969794766910796865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26378911979863177940531243 39568367969794766910796865)
          ·
            refine ⟨29676275977346075183097649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39568367969794766910796865 29676275977346075183097649)
            ·
              refine ⟨22257206983009556387323237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29676275977346075183097649 22257206983009556387323237)
              ·
                refine ⟨4173226309314291822623107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22257206983009556387323237 4173226309314291822623107)
                ·
                  refine ⟨6259839463971437733934661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4173226309314291822623107 6259839463971437733934661)
                  ·
                    refine ⟨1173719899494644575112749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6259839463971437733934661 1173719899494644575112749)
                    ·
                      rfl

theorem cell22_3428717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_3428717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428717 prefixEnd_3428717 := by exact prefixLift 3428717
  have htrace : WordTrace (prefixWord ++ tailWord_3428717) baseStart_3428717 baseEnd_3428717 := by
    simpa [prefixWord, tailWord_3428717, baseEnd_3428717] using wordTrace_append hprefix tailTrace_3428717
  have hstable : (prefixWord ++ tailWord_3428717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428717).length < 2 ^ (prefixWord ++ tailWord_3428717).sum := by decide
  have hdescent : baseEnd_3428717 < baseStart_3428717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428738 : List Nat := [3, 4, 2, 1, 3, 1, 1, 2, 5]
def baseStart_3428738 : Nat := 118140960795 + 3428738 * 2 ^ 59
def prefixEnd_3428738 : Nat := 4983230072969 + 3 ^ 40 * 3428738 * 2
def baseEnd_3428738 : Nat := 391242362741269173445895

theorem tailTrace_3428738 : CollatzResearch.WordTrace tailWord_3428738 prefixEnd_3428738 391242362741269173445895 := by
  unfold tailWord_3428738
  simp only [CollatzResearch.WordTrace]
  refine ⟨31264087163068820668739717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83370899101516855116639245 31264087163068820668739717)
  ·
    refine ⟨5862016343075403875388697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31264087163068820668739717 5862016343075403875388697)
    ·
      refine ⟨4396512257306552906541523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5862016343075403875388697 4396512257306552906541523)
      ·
        refine ⟨6594768385959829359812285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4396512257306552906541523 6594768385959829359812285)
        ·
          refine ⟨2473038144734936009929607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6594768385959829359812285 2473038144734936009929607)
          ·
            refine ⟨3709557217102404014894411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2473038144734936009929607 3709557217102404014894411)
            ·
              refine ⟨5564335825653606022341617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3709557217102404014894411 5564335825653606022341617)
              ·
                refine ⟨4173251869240204516756213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5564335825653606022341617 4173251869240204516756213)
                ·
                  refine ⟨391242362741269173445895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4173251869240204516756213 391242362741269173445895)
                  ·
                    rfl

theorem cell22_3428738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_3428738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428738 prefixEnd_3428738 := by exact prefixLift 3428738
  have htrace : WordTrace (prefixWord ++ tailWord_3428738) baseStart_3428738 baseEnd_3428738 := by
    simpa [prefixWord, tailWord_3428738, baseEnd_3428738] using wordTrace_append hprefix tailTrace_3428738
  have hstable : (prefixWord ++ tailWord_3428738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428738).length < 2 ^ (prefixWord ++ tailWord_3428738).sum := by decide
  have hdescent : baseEnd_3428738 < baseStart_3428738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428747 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 4, 3]
def baseStart_3428747 : Nat := 118140960795 + 3428747 * 2 ^ 59
def prefixEnd_3428747 : Nat := 4983230072969 + 3 ^ 40 * 3428747 * 2
def baseEnd_3428747 : Nat := 1173730169107734496862657

theorem tailTrace_3428747 : CollatzResearch.WordTrace tailWord_3428747 prefixEnd_3428747 1173730169107734496862657 := by
  unfold tailWord_3428747
  simp only [CollatzResearch.WordTrace]
  refine ⟨125056676909242677212036495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83371117939495118141357663 125056676909242677212036495)
  ·
    refine ⟨187585015363864015818054743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125056676909242677212036495 187585015363864015818054743)
    ·
      refine ⟨281377523045796023727082115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187585015363864015818054743 281377523045796023727082115)
      ·
        refine ⟨422066284568694035590623173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281377523045796023727082115 422066284568694035590623173)
        ·
          refine ⟨79137428356630131673241845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 422066284568694035590623173 79137428356630131673241845)
          ·
            refine ⟨7419133908434074844366423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79137428356630131673241845 7419133908434074844366423)
            ·
              refine ⟨11128700862651112266549635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7419133908434074844366423 11128700862651112266549635)
              ·
                refine ⟨16693051293976668399824453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11128700862651112266549635 16693051293976668399824453)
                ·
                  refine ⟨3129947117620625324967085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16693051293976668399824453 3129947117620625324967085)
                  ·
                    refine ⟨1173730169107734496862657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3129947117620625324967085 1173730169107734496862657)
                    ·
                      rfl

theorem cell22_3428747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 3].length) (baseStart_3428747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428747 prefixEnd_3428747 := by exact prefixLift 3428747
  have htrace : WordTrace (prefixWord ++ tailWord_3428747) baseStart_3428747 baseEnd_3428747 := by
    simpa [prefixWord, tailWord_3428747, baseEnd_3428747] using wordTrace_append hprefix tailTrace_3428747
  have hstable : (prefixWord ++ tailWord_3428747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428747).length < 2 ^ (prefixWord ++ tailWord_3428747).sum := by decide
  have hdescent : baseEnd_3428747 < baseStart_3428747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428809 : List Nat := [1, 2, 1, 1, 2, 1, 4, 6, 1, 3]
def baseStart_3428809 : Nat := 118140960795 + 3428809 * 2 ^ 59
def prefixEnd_3428809 : Nat := 4983230072969 + 3 ^ 40 * 3428809 * 2
def baseEnd_3428809 : Nat := 1173751392974787001812467

theorem tailTrace_3428809 : CollatzResearch.WordTrace tailWord_3428809 prefixEnd_3428809 1173751392974787001812467 := by
  unfold tailWord_3428809
  simp only [CollatzResearch.WordTrace]
  refine ⟨125058938235018061800793481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83372625490012041200528987 125058938235018061800793481)
  ·
    refine ⟨93794203676263546350595111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125058938235018061800793481 93794203676263546350595111)
    ·
      refine ⟨140691305514395319525892667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93794203676263546350595111 140691305514395319525892667)
      ·
        refine ⟨211036958271592979288839001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140691305514395319525892667 211036958271592979288839001)
        ·
          refine ⟨158277718703694734466629251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211036958271592979288839001 158277718703694734466629251)
          ·
            refine ⟨237416578055542101699943877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158277718703694734466629251 237416578055542101699943877)
            ·
              refine ⟨44515608385414144068739477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 237416578055542101699943877 44515608385414144068739477)
              ·
                refine ⟨2086669143066288003222163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44515608385414144068739477 2086669143066288003222163)
                ·
                  refine ⟨3130003714599432004833245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2086669143066288003222163 3130003714599432004833245)
                  ·
                    refine ⟨1173751392974787001812467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3130003714599432004833245 1173751392974787001812467)
                    ·
                      rfl

theorem cell22_3428809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 1, 3].length) (baseStart_3428809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428809 prefixEnd_3428809 := by exact prefixLift 3428809
  have htrace : WordTrace (prefixWord ++ tailWord_3428809) baseStart_3428809 baseEnd_3428809 := by
    simpa [prefixWord, tailWord_3428809, baseEnd_3428809] using wordTrace_append hprefix tailTrace_3428809
  have hstable : (prefixWord ++ tailWord_3428809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428809).length < 2 ^ (prefixWord ++ tailWord_3428809).sum := by decide
  have hdescent : baseEnd_3428809 < baseStart_3428809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428880 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 2, 10]
def baseStart_3428880 : Nat := 118140960795 + 3428880 * 2 ^ 59
def prefixEnd_3428880 : Nat := 4983230072969 + 3 ^ 40 * 3428880 * 2
def baseEnd_3428880 : Nat := 1173775697725766483287249

theorem tailTrace_3428880 : CollatzResearch.WordTrace tailWord_3428880 prefixEnd_3428880 1173775697725766483287249 := by
  unfold tailWord_3428880
  simp only [CollatzResearch.WordTrace]
  refine ⟨62530763908880420463314047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83374351878507227284418729 62530763908880420463314047)
  ·
    refine ⟨93796145863320630694971071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62530763908880420463314047 93796145863320630694971071)
    ·
      refine ⟨140694218794980946042456607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93796145863320630694971071 140694218794980946042456607)
      ·
        refine ⟨211041328192471419063684911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140694218794980946042456607 211041328192471419063684911)
        ·
          refine ⟨316561992288707128595527367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211041328192471419063684911 316561992288707128595527367)
          ·
            refine ⟨474842988433060692893291051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316561992288707128595527367 474842988433060692893291051)
            ·
              refine ⟨712264482649591039339936577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474842988433060692893291051 712264482649591039339936577)
              ·
                refine ⟨534198361987193279504952433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 712264482649591039339936577 534198361987193279504952433)
                ·
                  refine ⟨400648771490394959628714325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534198361987193279504952433 400648771490394959628714325)
                  ·
                    refine ⟨1173775697725766483287249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 400648771490394959628714325 1173775697725766483287249)
                    ·
                      rfl

theorem cell22_3428880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_3428880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428880 prefixEnd_3428880 := by exact prefixLift 3428880
  have htrace : WordTrace (prefixWord ++ tailWord_3428880) baseStart_3428880 baseEnd_3428880 := by
    simpa [prefixWord, tailWord_3428880, baseEnd_3428880] using wordTrace_append hprefix tailTrace_3428880
  have hstable : (prefixWord ++ tailWord_3428880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428880).length < 2 ^ (prefixWord ++ tailWord_3428880).sum := by decide
  have hdescent : baseEnd_3428880 < baseStart_3428880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428884 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 8]
def baseStart_3428884 : Nat := 118140960795 + 3428884 * 2 ^ 59
def prefixEnd_3428884 : Nat := 4983230072969 + 3 ^ 40 * 3428884 * 2
def baseEnd_3428884 : Nat := 391259022335837268729079

theorem tailTrace_3428884 : CollatzResearch.WordTrace tailWord_3428884 prefixEnd_3428884 391259022335837268729079 := by
  unfold tailWord_3428884
  simp only [CollatzResearch.WordTrace]
  refine ⟨62530836854873174804886853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83374449139830899739849137 62530836854873174804886853)
  ·
    refine ⟨11724531910288720275916285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62530836854873174804886853 11724531910288720275916285)
    ·
      refine ⟨4396699466358270103468607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11724531910288720275916285 4396699466358270103468607)
      ·
        refine ⟨6595049199537405155202911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4396699466358270103468607 6595049199537405155202911)
        ·
          refine ⟨9892573799306107732804367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6595049199537405155202911 9892573799306107732804367)
          ·
            refine ⟨14838860698959161599206551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9892573799306107732804367 14838860698959161599206551)
            ·
              refine ⟨22258291048438742398809827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14838860698959161599206551 22258291048438742398809827)
              ·
                refine ⟨33387436572658113598214741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22258291048438742398809827 33387436572658113598214741)
                ·
                  refine ⟨391259022335837268729079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33387436572658113598214741 391259022335837268729079)
                  ·
                    rfl

theorem cell22_3428884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_3428884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428884 prefixEnd_3428884 := by exact prefixLift 3428884
  have htrace : WordTrace (prefixWord ++ tailWord_3428884) baseStart_3428884 baseEnd_3428884 := by
    simpa [prefixWord, tailWord_3428884, baseEnd_3428884] using wordTrace_append hprefix tailTrace_3428884
  have hstable : (prefixWord ++ tailWord_3428884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428884).length < 2 ^ (prefixWord ++ tailWord_3428884).sum := by decide
  have hdescent : baseEnd_3428884 < baseStart_3428884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428897 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 1, 6]
def baseStart_3428897 : Nat := 118140960795 + 3428897 * 2 ^ 59
def prefixEnd_3428897 : Nat := 4983230072969 + 3 ^ 40 * 3428897 * 2
def baseEnd_3428897 : Nat := 1173781517173184105612197

theorem tailTrace_3428897 : CollatzResearch.WordTrace tailWord_3428897 prefixEnd_3428897 1173781517173184105612197 := by
  unfold tailWord_3428897
  simp only [CollatzResearch.WordTrace]
  refine ⟨125062147858699252829996945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83374765239132835219997963 125062147858699252829996945)
  ·
    refine ⟨93796610894024439622497709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125062147858699252829996945 93796610894024439622497709)
    ·
      refine ⟨35173729085259164858436641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93796610894024439622497709 35173729085259164858436641)
      ·
        refine ⟨26380296813944373643827481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35173729085259164858436641 26380296813944373643827481)
        ·
          refine ⟨19785222610458280232870611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26380296813944373643827481 19785222610458280232870611)
          ·
            refine ⟨29677833915687420349305917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19785222610458280232870611 29677833915687420349305917)
            ·
              refine ⟨11129187718382782630989719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29677833915687420349305917 11129187718382782630989719)
              ·
                refine ⟨16693781577574173946484579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11129187718382782630989719 16693781577574173946484579)
                ·
                  refine ⟨25040672366361260919726869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16693781577574173946484579 25040672366361260919726869)
                  ·
                    refine ⟨1173781517173184105612197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25040672366361260919726869 1173781517173184105612197)
                    ·
                      rfl

theorem cell22_3428897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_3428897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428897 prefixEnd_3428897 := by exact prefixLift 3428897
  have htrace : WordTrace (prefixWord ++ tailWord_3428897) baseStart_3428897 baseEnd_3428897 := by
    simpa [prefixWord, tailWord_3428897, baseEnd_3428897] using wordTrace_append hprefix tailTrace_3428897
  have hstable : (prefixWord ++ tailWord_3428897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428897).length < 2 ^ (prefixWord ++ tailWord_3428897).sum := by decide
  have hdescent : baseEnd_3428897 < baseStart_3428897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428903 : List Nat := [1, 1, 7, 2, 1, 1, 1, 3, 1, 4]
def baseStart_3428903 : Nat := 118140960795 + 3428903 * 2 ^ 59
def prefixEnd_3428903 : Nat := 4983230072969 + 3 ^ 40 * 3428903 * 2
def baseEnd_3428903 : Nat := 1173783571095802089962179

theorem tailTrace_3428903 : CollatzResearch.WordTrace tailWord_3428903 prefixEnd_3428903 1173783571095802089962179 := by
  unfold tailWord_3428903
  simp only [CollatzResearch.WordTrace]
  refine ⟨125062366696677515854715363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83374911131118343903143575 125062366696677515854715363)
  ·
    refine ⟨187593550045016273782073045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125062366696677515854715363 187593550045016273782073045)
    ·
      refine ⟨4396723829180068916767337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 187593550045016273782073045 4396723829180068916767337)
      ·
        refine ⟨3297542871885051687575503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4396723829180068916767337 3297542871885051687575503)
        ·
          refine ⟨4946314307827577531363255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3297542871885051687575503 4946314307827577531363255)
          ·
            refine ⟨7419471461741366297044883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4946314307827577531363255 7419471461741366297044883)
            ·
              refine ⟨11129207192612049445567325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7419471461741366297044883 11129207192612049445567325)
              ·
                refine ⟨4173452697229518542087747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11129207192612049445567325 4173452697229518542087747)
                ·
                  refine ⟨6260179045844277813131621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4173452697229518542087747 6260179045844277813131621)
                  ·
                    refine ⟨1173783571095802089962179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6260179045844277813131621 1173783571095802089962179)
                    ·
                      rfl

theorem cell22_3428903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_3428903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428903 prefixEnd_3428903 := by exact prefixLift 3428903
  have htrace : WordTrace (prefixWord ++ tailWord_3428903) baseStart_3428903 baseEnd_3428903 := by
    simpa [prefixWord, tailWord_3428903, baseEnd_3428903] using wordTrace_append hprefix tailTrace_3428903
  have hstable : (prefixWord ++ tailWord_3428903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428903).length < 2 ^ (prefixWord ++ tailWord_3428903).sum := by decide
  have hdescent : baseEnd_3428903 < baseStart_3428903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428942 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_3428942 : Nat := 118140960795 + 3428942 * 2 ^ 59
def prefixEnd_3428942 : Nat := 4983230072969 + 3 ^ 40 * 3428942 * 2
def baseEnd_3428942 : Nat := 1173796921592818988237059

theorem tailTrace_3428942 : CollatzResearch.WordTrace tailWord_3428942 prefixEnd_3428942 1173796921592818988237059 := by
  unfold tailWord_3428942
  simp only [CollatzResearch.WordTrace]
  refine ⟨15632973642942028189423135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83375859429024150343590053 15632973642942028189423135)
  ·
    refine ⟨23449460464413042284134703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15632973642942028189423135 23449460464413042284134703)
    ·
      refine ⟨35174190696619563426202055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23449460464413042284134703 35174190696619563426202055)
      ·
        refine ⟨52761286044929345139303083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35174190696619563426202055 52761286044929345139303083)
        ·
          refine ⟨79141929067394017708954625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52761286044929345139303083 79141929067394017708954625)
          ·
            refine ⟨59356446800545513281715969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79141929067394017708954625 59356446800545513281715969)
            ·
              refine ⟨44517335100409134961286977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59356446800545513281715969 44517335100409134961286977)
              ·
                refine ⟨33388001325306851220965233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44517335100409134961286977 33388001325306851220965233)
                ·
                  refine ⟨25041000993980138415723925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33388001325306851220965233 25041000993980138415723925)
                  ·
                    refine ⟨1173796921592818988237059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25041000993980138415723925 1173796921592818988237059)
                    ·
                      rfl

theorem cell22_3428942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_3428942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428942 prefixEnd_3428942 := by exact prefixLift 3428942
  have htrace : WordTrace (prefixWord ++ tailWord_3428942) baseStart_3428942 baseEnd_3428942 := by
    simpa [prefixWord, tailWord_3428942, baseEnd_3428942] using wordTrace_append hprefix tailTrace_3428942
  have hstable : (prefixWord ++ tailWord_3428942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428942).length < 2 ^ (prefixWord ++ tailWord_3428942).sum := by decide
  have hdescent : baseEnd_3428942 < baseStart_3428942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428972 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 4, 5]
def baseStart_3428972 : Nat := 118140960795 + 3428972 * 2 ^ 59
def prefixEnd_3428972 : Nat := 4983230072969 + 3 ^ 40 * 3428972 * 2
def baseEnd_3428972 : Nat := 1173807191205908909986967

theorem tailTrace_3428972 : CollatzResearch.WordTrace tailWord_3428972 prefixEnd_3428972 1173807191205908909986967 := by
  unfold tailWord_3428972
  simp only [CollatzResearch.WordTrace]
  refine ⟨62532441666713770319488585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83376588888951693759318113 62532441666713770319488585)
  ·
    refine ⟨46899331250035327739616439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62532441666713770319488585 46899331250035327739616439)
    ·
      refine ⟨70348996875052991609424659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46899331250035327739616439 70348996875052991609424659)
      ·
        refine ⟨105523495312579487414136989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70348996875052991609424659 105523495312579487414136989)
        ·
          refine ⟨39571310742217307780301371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105523495312579487414136989 39571310742217307780301371)
          ·
            refine ⟨59356966113325961670452057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39571310742217307780301371 59356966113325961670452057)
            ·
              refine ⟨44517724584994471252839043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59356966113325961670452057 44517724584994471252839043)
              ·
                refine ⟨66776586877491706879258565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44517724584994471252839043 66776586877491706879258565)
                ·
                  refine ⟨12520610039529695039860981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66776586877491706879258565 12520610039529695039860981)
                  ·
                    refine ⟨1173807191205908909986967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12520610039529695039860981 1173807191205908909986967)
                    ·
                      rfl

theorem cell22_3428972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_3428972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428972 prefixEnd_3428972 := by exact prefixLift 3428972
  have htrace : WordTrace (prefixWord ++ tailWord_3428972) baseStart_3428972 baseEnd_3428972 := by
    simpa [prefixWord, tailWord_3428972, baseEnd_3428972] using wordTrace_append hprefix tailTrace_3428972
  have hstable : (prefixWord ++ tailWord_3428972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428972).length < 2 ^ (prefixWord ++ tailWord_3428972).sum := by decide
  have hdescent : baseEnd_3428972 < baseStart_3428972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428974 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 7]
def baseStart_3428974 : Nat := 118140960795 + 3428974 * 2 ^ 59
def prefixEnd_3428974 : Nat := 4983230072969 + 3 ^ 40 * 3428974 * 2
def baseEnd_3428974 : Nat := 391269291948927190478987

theorem tailTrace_3428974 : CollatzResearch.WordTrace tailWord_3428974 prefixEnd_3428974 391269291948927190478987 := by
  unfold tailWord_3428974
  simp only [CollatzResearch.WordTrace]
  refine ⟨15633119534927536872568747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83376637519613529987033317 15633119534927536872568747)
  ·
    refine ⟨23449679302391305308853121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15633119534927536872568747 23449679302391305308853121)
    ·
      refine ⟨17587259476793478981639841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23449679302391305308853121 17587259476793478981639841)
      ·
        refine ⟨13190444607595109236229881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17587259476793478981639841 13190444607595109236229881)
        ·
          refine ⟨9892833455696331927172411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13190444607595109236229881 9892833455696331927172411)
          ·
            refine ⟨14839250183544497890758617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9892833455696331927172411 14839250183544497890758617)
            ·
              refine ⟨11129437637658373418068963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14839250183544497890758617 11129437637658373418068963)
              ·
                refine ⟨16694156456487560127103445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11129437637658373418068963 16694156456487560127103445)
                ·
                  refine ⟨391269291948927190478987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16694156456487560127103445 391269291948927190478987)
                  ·
                    rfl

theorem cell22_3428974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_3428974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428974 prefixEnd_3428974 := by exact prefixLift 3428974
  have htrace : WordTrace (prefixWord ++ tailWord_3428974) baseStart_3428974 baseEnd_3428974 := by
    simpa [prefixWord, tailWord_3428974, baseEnd_3428974] using wordTrace_append hprefix tailTrace_3428974
  have hstable : (prefixWord ++ tailWord_3428974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428974).length < 2 ^ (prefixWord ++ tailWord_3428974).sum := by decide
  have hdescent : baseEnd_3428974 < baseStart_3428974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428978 : List Nat := [3, 2, 1, 2, 4, 2, 1, 1, 3, 3]
def baseStart_3428978 : Nat := 118140960795 + 3428978 * 2 ^ 59
def prefixEnd_3428978 : Nat := 4983230072969 + 3 ^ 40 * 3428978 * 2
def baseEnd_3428978 : Nat := 1173809245128526894336949

theorem tailTrace_3428978 : CollatzResearch.WordTrace tailWord_3428978 prefixEnd_3428978 1173809245128526894336949 := by
  unfold tailWord_3428978
  simp only [CollatzResearch.WordTrace]
  refine ⟨31266275542851450915923897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83376734780937202442463725 31266275542851450915923897)
  ·
    refine ⟨23449706657138588186942923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31266275542851450915923897 23449706657138588186942923)
    ·
      refine ⟨35174559985707882280414385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23449706657138588186942923 35174559985707882280414385)
      ·
        refine ⟨26380919989280911710310789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35174559985707882280414385 26380919989280911710310789)
        ·
          refine ⟨4946422497990170945683273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26380919989280911710310789 4946422497990170945683273)
          ·
            refine ⟨3709816873492628209262455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4946422497990170945683273 3709816873492628209262455)
            ·
              refine ⟨5564725310238942313893683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3709816873492628209262455 5564725310238942313893683)
              ·
                refine ⟨8347087965358413470840525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5564725310238942313893683 8347087965358413470840525)
                ·
                  refine ⟨3130157987009405051565197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8347087965358413470840525 3130157987009405051565197)
                  ·
                    refine ⟨1173809245128526894336949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3130157987009405051565197 1173809245128526894336949)
                    ·
                      rfl

theorem cell22_3428978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_3428978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3428978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3428978 prefixEnd_3428978 := by exact prefixLift 3428978
  have htrace : WordTrace (prefixWord ++ tailWord_3428978) baseStart_3428978 baseEnd_3428978 := by
    simpa [prefixWord, tailWord_3428978, baseEnd_3428978] using wordTrace_append hprefix tailTrace_3428978
  have hstable : (prefixWord ++ tailWord_3428978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428978).length < 2 ^ (prefixWord ++ tailWord_3428978).sum := by decide
  have hdescent : baseEnd_3428978 < baseStart_3428978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429004 : List Nat := [2, 2, 1, 2, 1, 1, 2, 6, 1, 4]
def baseStart_3429004 : Nat := 118140960795 + 3429004 * 2 ^ 59
def prefixEnd_3429004 : Nat := 4983230072969 + 3 ^ 40 * 3429004 * 2
def baseEnd_3429004 : Nat := 1173818145459871493186869

theorem tailTrace_3429004 : CollatzResearch.WordTrace tailWord_3429004 prefixEnd_3429004 1173818145459871493186869 := by
  unfold tailWord_3429004
  simp only [CollatzResearch.WordTrace]
  refine ⟨62533025234655805052071033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83377366979541073402761377 62533025234655805052071033)
  ·
    refine ⟨46899768925991853789053275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62533025234655805052071033 46899768925991853789053275)
    ·
      refine ⟨70349653388987780683579913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46899768925991853789053275 70349653388987780683579913)
      ·
        refine ⟨52762240041740835512684935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70349653388987780683579913 52762240041740835512684935)
        ·
          refine ⟨79143360062611253269027403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52762240041740835512684935 79143360062611253269027403)
          ·
            refine ⟨118715040093916879903541105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79143360062611253269027403 118715040093916879903541105)
            ·
              refine ⟨89036280070437659927655829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118715040093916879903541105 89036280070437659927655829)
              ·
                refine ⟨4173575628301765309108867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89036280070437659927655829 4173575628301765309108867)
                ·
                  refine ⟨6260363442452647963663301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4173575628301765309108867 6260363442452647963663301)
                  ·
                    refine ⟨1173818145459871493186869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6260363442452647963663301 1173818145459871493186869)
                    ·
                      rfl

theorem cell22_3429004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_3429004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429004 prefixEnd_3429004 := by exact prefixLift 3429004
  have htrace : WordTrace (prefixWord ++ tailWord_3429004) baseStart_3429004 baseEnd_3429004 := by
    simpa [prefixWord, tailWord_3429004, baseEnd_3429004] using wordTrace_append hprefix tailTrace_3429004
  have hstable : (prefixWord ++ tailWord_3429004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429004).length < 2 ^ (prefixWord ++ tailWord_3429004).sum := by decide
  have hdescent : baseEnd_3429004 < baseStart_3429004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429066 : List Nat := [3, 1, 2, 1, 4, 1, 3, 1, 2, 4]
def baseStart_3429066 : Nat := 118140960795 + 3429066 * 2 ^ 59
def prefixEnd_3429066 : Nat := 4983230072969 + 3 ^ 40 * 3429066 * 2
def baseEnd_3429066 : Nat := 1173839369326923998136679

theorem tailTrace_3429066 : CollatzResearch.WordTrace tailWord_3429066 prefixEnd_3429066 1173839369326923998136679 := by
  unfold tailWord_3429066
  simp only [CollatzResearch.WordTrace]
  refine ⟨31267077948771748673224763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83378874530057996461932701 31267077948771748673224763)
  ·
    refine ⟨46900616923157623009837145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31267077948771748673224763 46900616923157623009837145)
    ·
      refine ⟨35175462692368217257377859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46900616923157623009837145 35175462692368217257377859)
      ·
        refine ⟨52763194038552325886066789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35175462692368217257377859 52763194038552325886066789)
        ·
          refine ⟨9893098882228561103637523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52763194038552325886066789 9893098882228561103637523)
          ·
            refine ⟨14839648323342841655456285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9893098882228561103637523 14839648323342841655456285)
            ·
              refine ⟨5564868121253565620796107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14839648323342841655456285 5564868121253565620796107)
              ·
                refine ⟨8347302181880348431194161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5564868121253565620796107 8347302181880348431194161)
                ·
                  refine ⟨6260476636410261323395621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8347302181880348431194161 6260476636410261323395621)
                  ·
                    refine ⟨1173839369326923998136679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6260476636410261323395621 1173839369326923998136679)
                    ·
                      rfl

theorem cell22_3429066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_3429066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429066 prefixEnd_3429066 := by exact prefixLift 3429066
  have htrace : WordTrace (prefixWord ++ tailWord_3429066) baseStart_3429066 baseEnd_3429066 := by
    simpa [prefixWord, tailWord_3429066, baseEnd_3429066] using wordTrace_append hprefix tailTrace_3429066
  have hstable : (prefixWord ++ tailWord_3429066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429066).length < 2 ^ (prefixWord ++ tailWord_3429066).sum := by decide
  have hdescent : baseEnd_3429066 < baseStart_3429066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429173 : List Nat := [1, 3, 3, 1, 3, 1, 3, 2, 1, 4]
def baseStart_3429173 : Nat := 118140960795 + 3429173 * 2 ^ 59
def prefixEnd_3429173 : Nat := 4983230072969 + 3 ^ 40 * 3429173 * 2
def baseEnd_3429173 : Nat := 1173875997613611385711351

theorem tailTrace_3429173 : CollatzResearch.WordTrace tailWord_3429173 prefixEnd_3429173 1173875997613611385711351 := by
  unfold tailWord_3429173
  simp only [CollatzResearch.WordTrace]
  refine ⟨125072214405699351967044173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83381476270466234644696115 125072214405699351967044173)
  ·
    refine ⟨46902080402137256987641565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125072214405699351967044173 46902080402137256987641565)
    ·
      refine ⟨17588280150801471370365587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46902080402137256987641565 17588280150801471370365587)
      ·
        refine ⟨26382420226202207055548381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17588280150801471370365587 26382420226202207055548381)
        ·
          refine ⟨9893407584825827645830643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26382420226202207055548381 9893407584825827645830643)
          ·
            refine ⟨14840111377238741468745965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9893407584825827645830643 14840111377238741468745965)
            ·
              refine ⟨5565041766464528050779737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14840111377238741468745965 5565041766464528050779737)
              ·
                refine ⟨4173781324848396038084803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5565041766464528050779737 4173781324848396038084803)
                ·
                  refine ⟨6260671987272594057127205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4173781324848396038084803 6260671987272594057127205)
                  ·
                    refine ⟨1173875997613611385711351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6260671987272594057127205 1173875997613611385711351)
                    ·
                      rfl

theorem cell22_3429173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_3429173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429173 prefixEnd_3429173 := by exact prefixLift 3429173
  have htrace : WordTrace (prefixWord ++ tailWord_3429173) baseStart_3429173 baseEnd_3429173 := by
    simpa [prefixWord, tailWord_3429173, baseEnd_3429173] using wordTrace_append hprefix tailTrace_3429173
  have hstable : (prefixWord ++ tailWord_3429173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429173).length < 2 ^ (prefixWord ++ tailWord_3429173).sum := by decide
  have hdescent : baseEnd_3429173 < baseStart_3429173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429184 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 1, 6]
def baseStart_3429184 : Nat := 118140960795 + 3429184 * 2 ^ 59
def prefixEnd_3429184 : Nat := 4983230072969 + 3 ^ 40 * 3429184 * 2
def baseEnd_3429184 : Nat := 1173879763138411023686317

theorem tailTrace_3429184 : CollatzResearch.WordTrace tailWord_3429184 prefixEnd_3429184 1173879763138411023686317 := by
  unfold tailWord_3429184
  simp only [CollatzResearch.WordTrace]
  refine ⟨62536307804329750422847303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83381743739106333897129737 62536307804329750422847303)
  ·
    refine ⟨93804461706494625634270955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62536307804329750422847303 93804461706494625634270955)
    ·
      refine ⟨140706692559741938451406433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93804461706494625634270955 140706692559741938451406433)
      ·
        refine ⟨105530019419806453838554825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140706692559741938451406433 105530019419806453838554825)
        ·
          refine ⟨79147514564854840378916119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105530019419806453838554825 79147514564854840378916119)
          ·
            refine ⟨118721271847282260568374179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79147514564854840378916119 118721271847282260568374179)
            ·
              refine ⟨178081907770923390852561269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118721271847282260568374179 178081907770923390852561269)
              ·
                refine ⟨16695178853524067892427619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178081907770923390852561269 16695178853524067892427619)
                ·
                  refine ⟨25042768280286101838641429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16695178853524067892427619 25042768280286101838641429)
                  ·
                    refine ⟨1173879763138411023686317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25042768280286101838641429 1173879763138411023686317)
                    ·
                      rfl

theorem cell22_3429184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_3429184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429184 prefixEnd_3429184 := by exact prefixLift 3429184
  have htrace : WordTrace (prefixWord ++ tailWord_3429184) baseStart_3429184 baseEnd_3429184 := by
    simpa [prefixWord, tailWord_3429184, baseEnd_3429184] using wordTrace_append hprefix tailTrace_3429184
  have hstable : (prefixWord ++ tailWord_3429184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429184).length < 2 ^ (prefixWord ++ tailWord_3429184).sum := by decide
  have hdescent : baseEnd_3429184 < baseStart_3429184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429250 : List Nat := [3, 4, 2, 2, 1, 1, 9]
def baseStart_3429250 : Nat := 118140960795 + 3429250 * 2 ^ 59
def prefixEnd_3429250 : Nat := 4983230072969 + 3 ^ 40 * 3429250 * 2
def baseEnd_3429250 : Nat := 43477865047674401908745

theorem tailTrace_3429250 : CollatzResearch.WordTrace tailWord_3429250 prefixEnd_3429250 43477865047674401908745 := by
  unfold tailWord_3429250
  simp only [CollatzResearch.WordTrace]
  refine ⟨31268755706605098529399301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83383348550946929411731469 31268755706605098529399301)
  ·
    refine ⟨5862891694988455974262369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31268755706605098529399301 5862891694988455974262369)
    ·
      refine ⟨4397168771241341980696777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5862891694988455974262369 4397168771241341980696777)
      ·
        refine ⟨3297876578431006485522583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4397168771241341980696777 3297876578431006485522583)
        ·
          refine ⟨4946814867646509728283875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3297876578431006485522583 4946814867646509728283875)
          ·
            refine ⟨7420222301469764592425813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4946814867646509728283875 7420222301469764592425813)
            ·
              refine ⟨43477865047674401908745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7420222301469764592425813 43477865047674401908745)
              ·
                rfl

theorem cell22_3429250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 9].length) (baseStart_3429250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429250 prefixEnd_3429250 := by exact prefixLift 3429250
  have htrace : WordTrace (prefixWord ++ tailWord_3429250) baseStart_3429250 baseEnd_3429250 := by
    simpa [prefixWord, tailWord_3429250, baseEnd_3429250] using wordTrace_append hprefix tailTrace_3429250
  have hstable : (prefixWord ++ tailWord_3429250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429250).length < 2 ^ (prefixWord ++ tailWord_3429250).sum := by decide
  have hdescent : baseEnd_3429250 < baseStart_3429250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429316 : List Nat := [2, 3, 3, 3, 1, 1, 3, 2, 1, 3]
def baseStart_3429316 : Nat := 118140960795 + 3429316 * 2 ^ 59
def prefixEnd_3429316 : Nat := 4983230072969 + 3 ^ 40 * 3429316 * 2
def baseEnd_3429316 : Nat := 1173924949436006679385913

theorem tailTrace_3429316 : CollatzResearch.WordTrace tailWord_3429316 prefixEnd_3429316 1173924949436006679385913 := by
  unfold tailWord_3429316
  simp only [CollatzResearch.WordTrace]
  refine ⟨62538715022090643694749901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83384953362787524926333201 62538715022090643694749901)
  ·
    refine ⟨23452018133283991385531213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62538715022090643694749901 23452018133283991385531213)
    ·
      refine ⟨8794506799981496769574205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23452018133283991385531213 8794506799981496769574205)
      ·
        refine ⟨3297940049993061288590327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8794506799981496769574205 3297940049993061288590327)
        ·
          refine ⟨4946910074989591932885491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3297940049993061288590327 4946910074989591932885491)
          ·
            refine ⟨7420365112484387899328237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4946910074989591932885491 7420365112484387899328237)
            ·
              refine ⟨2782636917181645462248089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7420365112484387899328237 2782636917181645462248089)
              ·
                refine ⟨2086977687886234096686067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2782636917181645462248089 2086977687886234096686067)
                ·
                  refine ⟨3130466531829351145029101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2086977687886234096686067 3130466531829351145029101)
                  ·
                    refine ⟨1173924949436006679385913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3130466531829351145029101 1173924949436006679385913)
                    ·
                      rfl

theorem cell22_3429316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_3429316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429316 prefixEnd_3429316 := by exact prefixLift 3429316
  have htrace : WordTrace (prefixWord ++ tailWord_3429316) baseStart_3429316 baseEnd_3429316 := by
    simpa [prefixWord, tailWord_3429316, baseEnd_3429316] using wordTrace_append hprefix tailTrace_3429316
  have hstable : (prefixWord ++ tailWord_3429316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429316).length < 2 ^ (prefixWord ++ tailWord_3429316).sum := by decide
  have hdescent : baseEnd_3429316 < baseStart_3429316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429323 : List Nat := [1, 1, 1, 1, 3, 7, 1, 1, 6]
def baseStart_3429323 : Nat := 118140960795 + 3429323 * 2 ^ 59
def prefixEnd_3429323 : Nat := 4983230072969 + 3 ^ 40 * 3429323 * 2
def baseEnd_3429323 : Nat := 391309115226353664820297

theorem tailTrace_3429323 : CollatzResearch.WordTrace tailWord_3429323 prefixEnd_3429323 391309115226353664820297 := by
  unfold tailWord_3429323
  simp only [CollatzResearch.WordTrace]
  refine ⟨125077685355155927585004623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83385123570103951723336415 125077685355155927585004623)
  ·
    refine ⟨187616528032733891377506935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125077685355155927585004623 187616528032733891377506935)
    ·
      refine ⟨281424792049100837066260403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187616528032733891377506935 281424792049100837066260403)
      ·
        refine ⟨422137188073651255599390605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281424792049100837066260403 422137188073651255599390605)
        ·
          refine ⟨158301445527619220849771477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 422137188073651255599390605 158301445527619220849771477)
          ·
            refine ⟨3710190129553575488666519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 158301445527619220849771477 3710190129553575488666519)
            ·
              refine ⟨5565285194330363232999779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3710190129553575488666519 5565285194330363232999779)
              ·
                refine ⟨8347927791495544849499669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5565285194330363232999779 8347927791495544849499669)
                ·
                  refine ⟨391309115226353664820297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8347927791495544849499669 391309115226353664820297)
                  ·
                    rfl

theorem cell22_3429323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 6].length) (baseStart_3429323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429323 prefixEnd_3429323 := by exact prefixLift 3429323
  have htrace : WordTrace (prefixWord ++ tailWord_3429323) baseStart_3429323 baseEnd_3429323 := by
    simpa [prefixWord, tailWord_3429323, baseEnd_3429323] using wordTrace_append hprefix tailTrace_3429323
  have hstable : (prefixWord ++ tailWord_3429323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429323).length < 2 ^ (prefixWord ++ tailWord_3429323).sum := by decide
  have hdescent : baseEnd_3429323 < baseStart_3429323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429381 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 1, 8]
def baseStart_3429381 : Nat := 118140960795 + 3429381 * 2 ^ 59
def prefixEnd_3429381 : Nat := 4983230072969 + 3 ^ 40 * 3429381 * 2
def baseEnd_3429381 : Nat := 1173947200264368176510713

theorem tailTrace_3429381 : CollatzResearch.WordTrace tailWord_3429381 prefixEnd_3429381 1173947200264368176510713 := by
  unfold tailWord_3429381
  simp only [CollatzResearch.WordTrace]
  refine ⟨125079800788945803490615997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83386533859297202327077331 125079800788945803490615997)
  ·
    refine ⟨46904925295854676308980999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125079800788945803490615997 46904925295854676308980999)
    ·
      refine ⟨70357387943782014463471499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46904925295854676308980999 70357387943782014463471499)
      ·
        refine ⟨105536081915673021695207249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70357387943782014463471499 105536081915673021695207249)
        ·
          refine ⟨79152061436754766271405437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105536081915673021695207249 79152061436754766271405437)
          ·
            refine ⟨29682023038783037351777039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79152061436754766271405437 29682023038783037351777039)
            ·
              refine ⟨44523034558174556027665559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29682023038783037351777039 44523034558174556027665559)
              ·
                refine ⟨66784551837261834041498339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44523034558174556027665559 66784551837261834041498339)
                ·
                  refine ⟨100176827755892751062247509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66784551837261834041498339 100176827755892751062247509)
                  ·
                    refine ⟨1173947200264368176510713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100176827755892751062247509 1173947200264368176510713)
                    ·
                      rfl

theorem cell22_3429381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_3429381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429381 prefixEnd_3429381 := by exact prefixLift 3429381
  have htrace : WordTrace (prefixWord ++ tailWord_3429381) baseStart_3429381 baseEnd_3429381 := by
    simpa [prefixWord, tailWord_3429381, baseEnd_3429381] using wordTrace_append hprefix tailTrace_3429381
  have hstable : (prefixWord ++ tailWord_3429381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429381).length < 2 ^ (prefixWord ++ tailWord_3429381).sum := by decide
  have hdescent : baseEnd_3429381 < baseStart_3429381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429400 : List Nat := [2, 1, 2, 3, 2, 3, 1, 2, 3, 3]
def baseStart_3429400 : Nat := 118140960795 + 3429400 * 2 ^ 59
def prefixEnd_3429400 : Nat := 4983230072969 + 3 ^ 40 * 3429400 * 2
def baseEnd_3429400 : Nat := 1173953704352658460285655

theorem tailTrace_3429400 : CollatzResearch.WordTrace tailWord_3429400 prefixEnd_3429400 1173953704352658460285655 := by
  unfold tailWord_3429400
  simp only [CollatzResearch.WordTrace]
  refine ⟨62540246887938484867778827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83386995850584646490371769 62540246887938484867778827)
  ·
    refine ⟨93810370331907727301668241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62540246887938484867778827 93810370331907727301668241)
    ·
      refine ⟨70357777748930795476251181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93810370331907727301668241 70357777748930795476251181)
      ·
        refine ⟨26384166655849048303594193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70357777748930795476251181 26384166655849048303594193)
        ·
          refine ⟨19788124991886786227695645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26384166655849048303594193 19788124991886786227695645)
          ·
            refine ⟨7420546871957544835385867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19788124991886786227695645 7420546871957544835385867)
            ·
              refine ⟨11130820307936317253078801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7420546871957544835385867 11130820307936317253078801)
              ·
                refine ⟨8348115230952237939809101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11130820307936317253078801 8348115230952237939809101)
                ·
                  refine ⟨3130543211607089227428413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8348115230952237939809101 3130543211607089227428413)
                  ·
                    refine ⟨1173953704352658460285655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3130543211607089227428413 1173953704352658460285655)
                    ·
                      rfl

theorem cell22_3429400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_3429400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429400 prefixEnd_3429400 := by exact prefixLift 3429400
  have htrace : WordTrace (prefixWord ++ tailWord_3429400) baseStart_3429400 baseEnd_3429400 := by
    simpa [prefixWord, tailWord_3429400, baseEnd_3429400] using wordTrace_append hprefix tailTrace_3429400
  have hstable : (prefixWord ++ tailWord_3429400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429400).length < 2 ^ (prefixWord ++ tailWord_3429400).sum := by decide
  have hdescent : baseEnd_3429400 < baseStart_3429400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429430 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_3429430 : Nat := 118140960795 + 3429430 * 2 ^ 59
def prefixEnd_3429430 : Nat := 4983230072969 + 3 ^ 40 * 3429430 * 2
def baseEnd_3429430 : Nat := 391321324655249460678521

theorem tailTrace_3429430 : CollatzResearch.WordTrace tailWord_3429430 prefixEnd_3429430 391321324655249460678521 := by
  unfold tailWord_3429430
  simp only [CollatzResearch.WordTrace]
  refine ⟨7817599247860517803696859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83387725310512189906099829 7817599247860517803696859)
  ·
    refine ⟨11726398871790776705545289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7817599247860517803696859 11726398871790776705545289)
    ·
      refine ⟨8794799153843082529158967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11726398871790776705545289 8794799153843082529158967)
      ·
        refine ⟨13192198730764623793738451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8794799153843082529158967 13192198730764623793738451)
        ·
          refine ⟨19788298096146935690607677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13192198730764623793738451 19788298096146935690607677)
          ·
            refine ⟨7420611786055100883977879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19788298096146935690607677 7420611786055100883977879)
            ·
              refine ⟨11130917679082651325966819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7420611786055100883977879 11130917679082651325966819)
              ·
                refine ⟨16696376518623976988950229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11130917679082651325966819 16696376518623976988950229)
                ·
                  refine ⟨391321324655249460678521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16696376518623976988950229 391321324655249460678521)
                  ·
                    rfl

theorem cell22_3429430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_3429430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429430 prefixEnd_3429430 := by exact prefixLift 3429430
  have htrace : WordTrace (prefixWord ++ tailWord_3429430) baseStart_3429430 baseEnd_3429430 := by
    simpa [prefixWord, tailWord_3429430, baseEnd_3429430] using wordTrace_append hprefix tailTrace_3429430
  have hstable : (prefixWord ++ tailWord_3429430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429430).length < 2 ^ (prefixWord ++ tailWord_3429430).sum := by decide
  have hdescent : baseEnd_3429430 < baseStart_3429430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429460 : List Nat := [2, 4, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_3429460 : Nat := 118140960795 + 3429460 * 2 ^ 59
def prefixEnd_3429460 : Nat := 4983230072969 + 3 ^ 40 * 3429460 * 2
def baseEnd_3429460 : Nat := 1173974243578838303785471

theorem tailTrace_3429460 : CollatzResearch.WordTrace tailWord_3429460 prefixEnd_3429460 1173974243578838303785471 := by
  unfold tailWord_3429460
  simp only [CollatzResearch.WordTrace]
  refine ⟨62541341077829799991370917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83388454770439733321827889 62541341077829799991370917)
  ·
    refine ⟨11726501452093087498382047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62541341077829799991370917 11726501452093087498382047)
    ·
      refine ⟨17589752178139631247573071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11726501452093087498382047 17589752178139631247573071)
      ·
        refine ⟨26384628267209446871359607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17589752178139631247573071 26384628267209446871359607)
        ·
          refine ⟨39576942400814170307039411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26384628267209446871359607 39576942400814170307039411)
          ·
            refine ⟨59365413601221255460559117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39576942400814170307039411 59365413601221255460559117)
            ·
              refine ⟨22262030100457970797709669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59365413601221255460559117 22262030100457970797709669)
              ·
                refine ⟨4174130643835869524570563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22262030100457970797709669 4174130643835869524570563)
                ·
                  refine ⟨6261195965753804286855845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4174130643835869524570563 6261195965753804286855845)
                  ·
                    refine ⟨1173974243578838303785471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6261195965753804286855845 1173974243578838303785471)
                    ·
                      rfl

theorem cell22_3429460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_3429460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429460 prefixEnd_3429460 := by exact prefixLift 3429460
  have htrace : WordTrace (prefixWord ++ tailWord_3429460) baseStart_3429460 baseEnd_3429460 := by
    simpa [prefixWord, tailWord_3429460, baseEnd_3429460] using wordTrace_append hprefix tailTrace_3429460
  have hstable : (prefixWord ++ tailWord_3429460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429460).length < 2 ^ (prefixWord ++ tailWord_3429460).sum := by decide
  have hdescent : baseEnd_3429460 < baseStart_3429460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429473 : List Nat := [1, 2, 3, 1, 1, 2, 2, 4, 1, 5]
def baseStart_3429473 : Nat := 118140960795 + 3429473 * 2 ^ 59
def prefixEnd_3429473 : Nat := 4983230072969 + 3 ^ 40 * 3429473 * 2
def baseEnd_3429473 : Nat := 1173978693744510603210431

theorem tailTrace_3429473 : CollatzResearch.WordTrace tailWord_3429473 prefixEnd_3429473 1173978693744510603210431 := by
  unfold tailWord_3429473
  simp only [CollatzResearch.WordTrace]
  refine ⟨125083156304612503202965073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83388770869741668801976715 125083156304612503202965073)
  ·
    refine ⟨93812367228459377402223805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125083156304612503202965073 93812367228459377402223805)
    ·
      refine ⟨35179637710672266525833927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93812367228459377402223805 35179637710672266525833927)
      ·
        refine ⟨52769456566008399788750891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35179637710672266525833927 52769456566008399788750891)
        ·
          refine ⟨79154184849012599683126337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52769456566008399788750891 79154184849012599683126337)
          ·
            refine ⟨59365638636759449762344753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79154184849012599683126337 59365638636759449762344753)
            ·
              refine ⟨44524228977569587321758565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59365638636759449762344753 44524228977569587321758565)
              ·
                refine ⟨8348292933294297622829731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44524228977569587321758565 8348292933294297622829731)
                ·
                  refine ⟨12522439399941446434244597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8348292933294297622829731 12522439399941446434244597)
                  ·
                    refine ⟨1173978693744510603210431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12522439399941446434244597 1173978693744510603210431)
                    ·
                      rfl

theorem cell22_3429473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_3429473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429473 prefixEnd_3429473 := by exact prefixLift 3429473
  have htrace : WordTrace (prefixWord ++ tailWord_3429473) baseStart_3429473 baseEnd_3429473 := by
    simpa [prefixWord, tailWord_3429473, baseEnd_3429473] using wordTrace_append hprefix tailTrace_3429473
  have hstable : (prefixWord ++ tailWord_3429473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429473).length < 2 ^ (prefixWord ++ tailWord_3429473).sum := by decide
  have hdescent : baseEnd_3429473 < baseStart_3429473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429490 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 4, 3]
def baseStart_3429490 : Nat := 118140960795 + 3429490 * 2 ^ 59
def prefixEnd_3429490 : Nat := 4983230072969 + 3 ^ 40 * 3429490 * 2
def baseEnd_3429490 : Nat := 1173984513191928225535379

theorem tailTrace_3429490 : CollatzResearch.WordTrace tailWord_3429490 prefixEnd_3429490 1173984513191928225535379 := by
  unfold tailWord_3429490
  simp only [CollatzResearch.WordTrace]
  refine ⟨31270944086387728776583481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83389184230367276737555949 31270944086387728776583481)
  ·
    refine ⟨23453208064790796582437611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31270944086387728776583481 23453208064790796582437611)
    ·
      refine ⟨35179812097186194873656417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23453208064790796582437611 35179812097186194873656417)
      ·
        refine ⟨26384859072889646155242313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35179812097186194873656417 26384859072889646155242313)
        ·
          refine ⟨19788644304667234616431735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26384859072889646155242313 19788644304667234616431735)
          ·
            refine ⟨29682966457000851924647603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19788644304667234616431735 29682966457000851924647603)
            ·
              refine ⟨44524449685501277886971405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29682966457000851924647603 44524449685501277886971405)
              ·
                refine ⟨16696668632062979207614277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44524449685501277886971405 16696668632062979207614277)
                ·
                  refine ⟨3130625368511808601427677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16696668632062979207614277 3130625368511808601427677)
                  ·
                    refine ⟨1173984513191928225535379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3130625368511808601427677 1173984513191928225535379)
                    ·
                      rfl

theorem cell22_3429490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_3429490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429490 prefixEnd_3429490 := by exact prefixLift 3429490
  have htrace : WordTrace (prefixWord ++ tailWord_3429490) baseStart_3429490 baseEnd_3429490 := by
    simpa [prefixWord, tailWord_3429490, baseEnd_3429490] using wordTrace_append hprefix tailTrace_3429490
  have hstable : (prefixWord ++ tailWord_3429490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429490).length < 2 ^ (prefixWord ++ tailWord_3429490).sum := by decide
  have hdescent : baseEnd_3429490 < baseStart_3429490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429522 : List Nat := [3, 2, 3, 1, 1, 3, 2, 1, 2, 4]
def baseStart_3429522 : Nat := 118140960795 + 3429522 * 2 ^ 59
def prefixEnd_3429522 : Nat := 4983230072969 + 3 ^ 40 * 3429522 * 2
def baseEnd_3429522 : Nat := 1173995467445890808735281

theorem tailTrace_3429522 : CollatzResearch.WordTrace tailWord_3429522 prefixEnd_3429522 1173995467445890808735281 := by
  unfold tailWord_3429522
  simp only [CollatzResearch.WordTrace]
  refine ⟨31271235870358746142874705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83389962320956656380999213 31271235870358746142874705)
  ·
    refine ⟨23453426902769059607156029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31271235870358746142874705 23453426902769059607156029)
    ·
      refine ⟨8795035088538397352683511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23453426902769059607156029 8795035088538397352683511)
      ·
        refine ⟨13192552632807596029025267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8795035088538397352683511 13192552632807596029025267)
        ·
          refine ⟨19788828949211394043537901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13192552632807596029025267 19788828949211394043537901)
          ·
            refine ⟨7420810855954272766326713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19788828949211394043537901 7420810855954272766326713)
            ·
              refine ⟨5565608141965704574745035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7420810855954272766326713 5565608141965704574745035)
              ·
                refine ⟨8348412212948556862117553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5565608141965704574745035 8348412212948556862117553)
                ·
                  refine ⟨6261309159711417646588165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8348412212948556862117553 6261309159711417646588165)
                  ·
                    refine ⟨1173995467445890808735281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6261309159711417646588165 1173995467445890808735281)
                    ·
                      rfl

theorem cell22_3429522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_3429522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429522 prefixEnd_3429522 := by exact prefixLift 3429522
  have htrace : WordTrace (prefixWord ++ tailWord_3429522) baseStart_3429522 baseEnd_3429522 := by
    simpa [prefixWord, tailWord_3429522, baseEnd_3429522] using wordTrace_append hprefix tailTrace_3429522
  have hstable : (prefixWord ++ tailWord_3429522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429522).length < 2 ^ (prefixWord ++ tailWord_3429522).sum := by decide
  have hdescent : baseEnd_3429522 < baseStart_3429522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429552 : List Nat := [2, 1, 1, 1, 2, 1, 2, 8, 1, 3]
def baseStart_3429552 : Nat := 118140960795 + 3429552 * 2 ^ 59
def prefixEnd_3429552 : Nat := 4983230072969 + 3 ^ 40 * 3429552 * 2
def baseEnd_3429552 : Nat := 1174005737058980730485189

theorem tailTrace_3429552 : CollatzResearch.WordTrace tailWord_3429552 prefixEnd_3429552 1174005737058980730485189 := by
  unfold tailWord_3429552
  simp only [CollatzResearch.WordTrace]
  refine ⟨62543018835663149847545455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83390691780884199796727273 62543018835663149847545455)
  ·
    refine ⟨93814528253494724771318183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62543018835663149847545455 93814528253494724771318183)
    ·
      refine ⟨140721792380242087156977275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93814528253494724771318183 140721792380242087156977275)
      ·
        refine ⟨211082688570363130735465913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140721792380242087156977275 211082688570363130735465913)
        ·
          refine ⟨158312016427772348051599435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211082688570363130735465913 158312016427772348051599435)
          ·
            refine ⟨237468024641658522077399153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158312016427772348051599435 237468024641658522077399153)
            ·
              refine ⟨178101018481243891558049365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237468024641658522077399153 178101018481243891558049365)
              ·
                refine ⟨2087121310327076854195891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 178101018481243891558049365 2087121310327076854195891)
                ·
                  refine ⟨3130681965490615281293837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2087121310327076854195891 3130681965490615281293837)
                  ·
                    refine ⟨1174005737058980730485189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3130681965490615281293837 1174005737058980730485189)
                    ·
                      rfl

theorem cell22_3429552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 1, 3].length) (baseStart_3429552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429552 prefixEnd_3429552 := by exact prefixLift 3429552
  have htrace : WordTrace (prefixWord ++ tailWord_3429552) baseStart_3429552 baseEnd_3429552 := by
    simpa [prefixWord, tailWord_3429552, baseEnd_3429552] using wordTrace_append hprefix tailTrace_3429552
  have hstable : (prefixWord ++ tailWord_3429552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429552).length < 2 ^ (prefixWord ++ tailWord_3429552).sum := by decide
  have hdescent : baseEnd_3429552 < baseStart_3429552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429565 : List Nat := [1, 4, 1, 2, 1, 1, 4, 3, 5]
def baseStart_3429565 : Nat := 118140960795 + 3429565 * 2 ^ 59
def prefixEnd_3429565 : Nat := 4983230072969 + 3 ^ 40 * 3429565 * 2
def baseEnd_3429565 : Nat := 391336729074884343303383

theorem tailTrace_3429565 : CollatzResearch.WordTrace tailWord_3429565 prefixEnd_3429565 391336729074884343303383 := by
  unfold tailWord_3429565
  simp only [CollatzResearch.WordTrace]
  refine ⟨125086511820279202915314149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83391007880186135276876099 125086511820279202915314149)
  ·
    refine ⟨23453720966302350546621403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125086511820279202915314149 23453720966302350546621403)
    ·
      refine ⟨35180581449453525819932105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23453720966302350546621403 35180581449453525819932105)
      ·
        refine ⟨26385436087090144364949079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35180581449453525819932105 26385436087090144364949079)
        ·
          refine ⟨39578154130635216547423619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26385436087090144364949079 39578154130635216547423619)
          ·
            refine ⟨59367231195952824821135429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39578154130635216547423619 59367231195952824821135429)
            ·
              refine ⟨11131355849241154653962893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59367231195952824821135429 11131355849241154653962893)
              ·
                refine ⟨4174258443465432995236085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11131355849241154653962893 4174258443465432995236085)
                ·
                  refine ⟨391336729074884343303383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4174258443465432995236085 391336729074884343303383)
                  ·
                    rfl

theorem cell22_3429565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_3429565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429565 prefixEnd_3429565 := by exact prefixLift 3429565
  have htrace : WordTrace (prefixWord ++ tailWord_3429565) baseStart_3429565 baseEnd_3429565 := by
    simpa [prefixWord, tailWord_3429565, baseEnd_3429565] using wordTrace_append hprefix tailTrace_3429565
  have hstable : (prefixWord ++ tailWord_3429565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429565).length < 2 ^ (prefixWord ++ tailWord_3429565).sum := by decide
  have hdescent : baseEnd_3429565 < baseStart_3429565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429569 : List Nat := [1, 2, 6, 1, 1, 2, 1, 2, 3, 3]
def baseStart_3429569 : Nat := 118140960795 + 3429569 * 2 ^ 59
def prefixEnd_3429569 : Nat := 4983230072969 + 3 ^ 40 * 3429569 * 2
def baseEnd_3429569 : Nat := 1174011556506398352810137

theorem tailTrace_3429569 : CollatzResearch.WordTrace tailWord_3429569 prefixEnd_3429569 1174011556506398352810137 := by
  unfold tailWord_3429569
  simp only [CollatzResearch.WordTrace]
  refine ⟨125086657712264711598459761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83391105141509807732306507 125086657712264711598459761)
  ·
    refine ⟨93814993284198533698844821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125086657712264711598459761 93814993284198533698844821)
    ·
      refine ⟨4397577810196806267133351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93814993284198533698844821 4397577810196806267133351)
      ·
        refine ⟨6596366715295209400700027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4397577810196806267133351 6596366715295209400700027)
        ·
          refine ⟨9894550072942814101050041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6596366715295209400700027 9894550072942814101050041)
          ·
            refine ⟨7420912554707110575787531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9894550072942814101050041 7420912554707110575787531)
            ·
              refine ⟨11131368832060665863681297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7420912554707110575787531 11131368832060665863681297)
              ·
                refine ⟨8348526624045499397760973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11131368832060665863681297 8348526624045499397760973)
                ·
                  refine ⟨3130697484017062274160365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8348526624045499397760973 3130697484017062274160365)
                  ·
                    refine ⟨1174011556506398352810137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3130697484017062274160365 1174011556506398352810137)
                    ·
                      rfl

theorem cell22_3429569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_3429569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429569 prefixEnd_3429569 := by exact prefixLift 3429569
  have htrace : WordTrace (prefixWord ++ tailWord_3429569) baseStart_3429569 baseEnd_3429569 := by
    simpa [prefixWord, tailWord_3429569, baseEnd_3429569] using wordTrace_append hprefix tailTrace_3429569
  have hstable : (prefixWord ++ tailWord_3429569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429569).length < 2 ^ (prefixWord ++ tailWord_3429569).sum := by decide
  have hdescent : baseEnd_3429569 < baseStart_3429569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429593 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 10]
def baseStart_3429593 : Nat := 118140960795 + 3429593 * 2 ^ 59
def prefixEnd_3429593 : Nat := 4983230072969 + 3 ^ 40 * 3429593 * 2
def baseEnd_3429593 : Nat := 391339924065623430070021

theorem tailTrace_3429593 : CollatzResearch.WordTrace tailWord_3429593 prefixEnd_3429593 391339924065623430070021 := by
  unfold tailWord_3429593
  simp only [CollatzResearch.WordTrace]
  refine ⟨125087533064177763697333433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83391688709451842464888955 125087533064177763697333433)
  ·
    refine ⟨93815649798133322773000075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125087533064177763697333433 93815649798133322773000075)
    ·
      refine ⟨140723474697199984159500113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93815649798133322773000075 140723474697199984159500113)
      ·
        refine ⟨105542606022899988119625085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140723474697199984159500113 105542606022899988119625085)
        ·
          refine ⟨39578477258587495544859407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105542606022899988119625085 39578477258587495544859407)
          ·
            refine ⟨59367715887881243317289111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39578477258587495544859407 59367715887881243317289111)
            ·
              refine ⟨89051573831821864975933667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59367715887881243317289111 89051573831821864975933667)
              ·
                refine ⟨133577360747732797463900501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89051573831821864975933667 133577360747732797463900501)
                ·
                  refine ⟨391339924065623430070021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 133577360747732797463900501 391339924065623430070021)
                  ·
                    rfl

theorem cell22_3429593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 10].length) (baseStart_3429593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429593 prefixEnd_3429593 := by exact prefixLift 3429593
  have htrace : WordTrace (prefixWord ++ tailWord_3429593) baseStart_3429593 baseEnd_3429593 := by
    simpa [prefixWord, tailWord_3429593, baseEnd_3429593] using wordTrace_append hprefix tailTrace_3429593
  have hstable : (prefixWord ++ tailWord_3429593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429593).length < 2 ^ (prefixWord ++ tailWord_3429593).sum := by decide
  have hdescent : baseEnd_3429593 < baseStart_3429593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429610 : List Nat := [3, 1, 3, 1, 1, 3, 1, 3, 6]
def baseStart_3429610 : Nat := 118140960795 + 3429610 * 2 ^ 59
def prefixEnd_3429610 : Nat := 4983230072969 + 3 ^ 40 * 3429610 * 2
def baseEnd_3429610 : Nat := 391341863881429304178337

theorem tailTrace_3429610 : CollatzResearch.WordTrace tailWord_3429610 prefixEnd_3429610 391341863881429304178337 := by
  unfold tailWord_3429610
  simp only [CollatzResearch.WordTrace]
  refine ⟨31272038276279043900175571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83392102070077450400468189 31272038276279043900175571)
  ·
    refine ⟨46908057414418565850263357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31272038276279043900175571 46908057414418565850263357)
    ·
      refine ⟨17590521530406962193848759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46908057414418565850263357 17590521530406962193848759)
      ·
        refine ⟨26385782295610443290773139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17590521530406962193848759 26385782295610443290773139)
        ·
          refine ⟨39578673443415664936159709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26385782295610443290773139 39578673443415664936159709)
          ·
            refine ⟨14842002541280874351059891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39578673443415664936159709 14842002541280874351059891)
            ·
              refine ⟨22263003811921311526589837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14842002541280874351059891 22263003811921311526589837)
              ·
                refine ⟨8348626429470491822471189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22263003811921311526589837 8348626429470491822471189)
                ·
                  refine ⟨391341863881429304178337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8348626429470491822471189 391341863881429304178337)
                  ·
                    rfl

theorem cell22_3429610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_3429610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429610 prefixEnd_3429610 := by exact prefixLift 3429610
  have htrace : WordTrace (prefixWord ++ tailWord_3429610) baseStart_3429610 baseEnd_3429610 := by
    simpa [prefixWord, tailWord_3429610, baseEnd_3429610] using wordTrace_append hprefix tailTrace_3429610
  have hstable : (prefixWord ++ tailWord_3429610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429610).length < 2 ^ (prefixWord ++ tailWord_3429610).sum := by decide
  have hdescent : baseEnd_3429610 < baseStart_3429610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429644 : List Nat := [2, 2, 1, 2, 2, 5, 1, 3, 4]
def baseStart_3429644 : Nat := 118140960795 + 3429644 * 2 ^ 59
def prefixEnd_3429644 : Nat := 4983230072969 + 3 ^ 40 * 3429644 * 2
def baseEnd_3429644 : Nat := 391345743513041052394969

theorem tailTrace_3429644 : CollatzResearch.WordTrace tailWord_3429644 prefixEnd_3429644 391345743513041052394969 := by
  unfold tailWord_3429644
  simp only [CollatzResearch.WordTrace]
  refine ⟨62544696593496499703719993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83392928791328666271626657 62544696593496499703719993)
  ·
    refine ⟨46908522445122374777789995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62544696593496499703719993 46908522445122374777789995)
    ·
      refine ⟨70362783667683562166684993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46908522445122374777789995 70362783667683562166684993)
      ·
        refine ⟨52772087750762671625013745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70362783667683562166684993 52772087750762671625013745)
        ·
          refine ⟨39579065813072003718760309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52772087750762671625013745 39579065813072003718760309)
          ·
            refine ⟨3710537419975500348633779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39579065813072003718760309 3710537419975500348633779)
            ·
              refine ⟨5565806129963250522950669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3710537419975500348633779 5565806129963250522950669)
              ·
                refine ⟨2087177298736218946106501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5565806129963250522950669 2087177298736218946106501)
                ·
                  refine ⟨391345743513041052394969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2087177298736218946106501 391345743513041052394969)
                  ·
                    rfl

theorem cell22_3429644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 4].length) (baseStart_3429644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429644 prefixEnd_3429644 := by exact prefixLift 3429644
  have htrace : WordTrace (prefixWord ++ tailWord_3429644) baseStart_3429644 baseEnd_3429644 := by
    simpa [prefixWord, tailWord_3429644, baseEnd_3429644] using wordTrace_append hprefix tailTrace_3429644
  have hstable : (prefixWord ++ tailWord_3429644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429644).length < 2 ^ (prefixWord ++ tailWord_3429644).sum := by decide
  have hdescent : baseEnd_3429644 < baseStart_3429644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429661 : List Nat := [1, 4, 2, 3, 1, 2, 3, 2, 4]
def baseStart_3429661 : Nat := 118140960795 + 3429661 * 2 ^ 59
def prefixEnd_3429661 : Nat := 4983230072969 + 3 ^ 40 * 3429661 * 2
def baseEnd_3429661 : Nat := 391347683328846926503285

theorem tailTrace_3429661 : CollatzResearch.WordTrace tailWord_3429661 prefixEnd_3429661 391347683328846926503285 := by
  unfold tailWord_3429661
  simp only [CollatzResearch.WordTrace]
  refine ⟨125090013227931411310808837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83393342151954274207205891 125090013227931411310808837)
  ·
    refine ⟨23454377480237139620776657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125090013227931411310808837 23454377480237139620776657)
    ·
      refine ⟨17590783110177854715582493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23454377480237139620776657 17590783110177854715582493)
      ·
        refine ⟨6596543666316695518343435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17590783110177854715582493 6596543666316695518343435)
        ·
          refine ⟨9894815499475043277515153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6596543666316695518343435 9894815499475043277515153)
          ·
            refine ⟨7421111624606282458136365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9894815499475043277515153 7421111624606282458136365)
            ·
              refine ⟨2782916859227355921801137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7421111624606282458136365 2782916859227355921801137)
              ·
                refine ⟨2087187644420516941350853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2782916859227355921801137 2087187644420516941350853)
                ·
                  refine ⟨391347683328846926503285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2087187644420516941350853 391347683328846926503285)
                  ·
                    rfl

theorem cell22_3429661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_3429661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429661 prefixEnd_3429661 := by exact prefixLift 3429661
  have htrace : WordTrace (prefixWord ++ tailWord_3429661) baseStart_3429661 baseEnd_3429661 := by
    simpa [prefixWord, tailWord_3429661, baseEnd_3429661] using wordTrace_append hprefix tailTrace_3429661
  have hstable : (prefixWord ++ tailWord_3429661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429661).length < 2 ^ (prefixWord ++ tailWord_3429661).sum := by decide
  have hdescent : baseEnd_3429661 < baseStart_3429661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429672 : List Nat := [2, 1, 5, 1, 2, 2, 2, 7]
def baseStart_3429672 : Nat := 118140960795 + 3429672 * 2 ^ 59
def prefixEnd_3429672 : Nat := 4983230072969 + 3 ^ 40 * 3429672 * 2
def baseEnd_3429672 : Nat := 130449646167926713053869

theorem tailTrace_3429672 : CollatzResearch.WordTrace tailWord_3429672 prefixEnd_3429672 130449646167926713053869 := by
  unfold tailWord_3429672
  simp only [CollatzResearch.WordTrace]
  refine ⟨62545207215445780094729635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83393609620594373459639513 62545207215445780094729635)
  ·
    refine ⟨93817810823168670142094453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62545207215445780094729635 93817810823168670142094453)
    ·
      refine ⟨8795419764672062825821355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93817810823168670142094453 8795419764672062825821355)
      ·
        refine ⟨13193129647008094238732033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8795419764672062825821355 13193129647008094238732033)
        ·
          refine ⟨9894847235256070679049025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13193129647008094238732033 9894847235256070679049025)
          ·
            refine ⟨7421135426442053009286769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9894847235256070679049025 7421135426442053009286769)
            ·
              refine ⟨5565851569831539756965077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7421135426442053009286769 5565851569831539756965077)
              ·
                refine ⟨130449646167926713053869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5565851569831539756965077 130449646167926713053869)
                ·
                  rfl

theorem cell22_3429672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 7].length) (baseStart_3429672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429672 prefixEnd_3429672 := by exact prefixLift 3429672
  have htrace : WordTrace (prefixWord ++ tailWord_3429672) baseStart_3429672 baseEnd_3429672 := by
    simpa [prefixWord, tailWord_3429672, baseEnd_3429672] using wordTrace_append hprefix tailTrace_3429672
  have hstable : (prefixWord ++ tailWord_3429672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429672).length < 2 ^ (prefixWord ++ tailWord_3429672).sum := by decide
  have hdescent : baseEnd_3429672 < baseStart_3429672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429704 : List Nat := [2, 1, 3, 1, 1, 2, 1, 7, 1, 3]
def baseStart_3429704 : Nat := 118140960795 + 3429704 * 2 ^ 59
def prefixEnd_3429704 : Nat := 4983230072969 + 3 ^ 40 * 3429704 * 2
def baseEnd_3429704 : Nat := 1174057769765303000684723

theorem tailTrace_3429704 : CollatzResearch.WordTrace tailWord_3429704 prefixEnd_3429704 1174057769765303000684723 := by
  unfold tailWord_3429704
  simp only [CollatzResearch.WordTrace]
  refine ⟨62545790783387814827312083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83394387711183753103082777 62545790783387814827312083)
  ·
    refine ⟨93818686175081722240968125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62545790783387814827312083 93818686175081722240968125)
    ·
      refine ⟨35182007315655645840363047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93818686175081722240968125 35182007315655645840363047)
      ·
        refine ⟨52773010973483468760544571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35182007315655645840363047 52773010973483468760544571)
        ·
          refine ⟨79159516460225203140816857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52773010973483468760544571 79159516460225203140816857)
          ·
            refine ⟨59369637345168902355612643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79159516460225203140816857 59369637345168902355612643)
            ·
              refine ⟨89054456017753353533418965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59369637345168902355612643 89054456017753353533418965)
              ·
                refine ⟨2087213812916094223439507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 89054456017753353533418965 2087213812916094223439507)
                ·
                  refine ⟨3130820719374141335159261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2087213812916094223439507 3130820719374141335159261)
                  ·
                    refine ⟨1174057769765303000684723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3130820719374141335159261 1174057769765303000684723)
                    ·
                      rfl

theorem cell22_3429704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_3429704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429704 prefixEnd_3429704 := by exact prefixLift 3429704
  have htrace : WordTrace (prefixWord ++ tailWord_3429704) baseStart_3429704 baseEnd_3429704 := by
    simpa [prefixWord, tailWord_3429704, baseEnd_3429704] using wordTrace_append hprefix tailTrace_3429704
  have hstable : (prefixWord ++ tailWord_3429704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429704).length < 2 ^ (prefixWord ++ tailWord_3429704).sum := by decide
  have hdescent : baseEnd_3429704 < baseStart_3429704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429715 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 2, 5]
def baseStart_3429715 : Nat := 118140960795 + 3429715 * 2 ^ 59
def prefixEnd_3429715 : Nat := 4983230072969 + 3 ^ 40 * 3429715 * 2
def baseEnd_3429715 : Nat := 1174061535290102638659689

theorem tailTrace_3429715 : CollatzResearch.WordTrace tailWord_3429715 prefixEnd_3429715 1174061535290102638659689 := by
  unfold tailWord_3429715
  simp only [CollatzResearch.WordTrace]
  refine ⟨125091982769735778533274599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83394655179823852355516399 125091982769735778533274599)
  ·
    refine ⟨187637974154603667799911899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125091982769735778533274599 187637974154603667799911899)
    ·
      refine ⟨281456961231905501699867849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187637974154603667799911899 281456961231905501699867849)
      ·
        refine ⟨211092720923929126274900887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281456961231905501699867849 211092720923929126274900887)
        ·
          refine ⟨316639081385893689412351331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211092720923929126274900887 316639081385893689412351331)
          ·
            refine ⟨474958622078840534118526997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316639081385893689412351331 474958622078840534118526997)
            ·
              refine ⟨22263685409945650036805953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 474958622078840534118526997 22263685409945650036805953)
              ·
                refine ⟨16697764057459237527604465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22263685409945650036805953 16697764057459237527604465)
                ·
                  refine ⟨12523323043094428145703349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16697764057459237527604465 12523323043094428145703349)
                  ·
                    refine ⟨1174061535290102638659689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12523323043094428145703349 1174061535290102638659689)
                    ·
                      rfl

theorem cell22_3429715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 5].length) (baseStart_3429715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429715 prefixEnd_3429715 := by exact prefixLift 3429715
  have htrace : WordTrace (prefixWord ++ tailWord_3429715) baseStart_3429715 baseEnd_3429715 := by
    simpa [prefixWord, tailWord_3429715, baseEnd_3429715] using wordTrace_append hprefix tailTrace_3429715
  have hstable : (prefixWord ++ tailWord_3429715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429715).length < 2 ^ (prefixWord ++ tailWord_3429715).sum := by decide
  have hdescent : baseEnd_3429715 < baseStart_3429715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429717 : List Nat := [1, 3, 2, 2, 3, 1, 1, 4, 5]
def baseStart_3429717 : Nat := 118140960795 + 3429717 * 2 ^ 59
def prefixEnd_3429717 : Nat := 4983230072969 + 3 ^ 40 * 3429717 * 2
def baseEnd_3429717 : Nat := 391354073310325100036561

theorem tailTrace_3429717 : CollatzResearch.WordTrace tailWord_3429717 prefixEnd_3429717 391354073310325100036561 := by
  unfold tailWord_3429717
  simp only [CollatzResearch.WordTrace]
  refine ⟨125092055715728532874847405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83394703810485688583231603 125092055715728532874847405)
  ·
    refine ⟨46909520893398199828067777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125092055715728532874847405 46909520893398199828067777)
    ·
      refine ⟨35182140670048649871050833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46909520893398199828067777 35182140670048649871050833)
      ·
        refine ⟨26386605502536487403288125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35182140670048649871050833 26386605502536487403288125)
        ·
          refine ⟨9894977063451182776233047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26386605502536487403288125 9894977063451182776233047)
          ·
            refine ⟨14842465595176774164349571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9894977063451182776233047 14842465595176774164349571)
            ·
              refine ⟨22263698392765161246524357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14842465595176774164349571 22263698392765161246524357)
              ·
                refine ⟨4174443448643467733723317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22263698392765161246524357 4174443448643467733723317)
                ·
                  refine ⟨391354073310325100036561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4174443448643467733723317 391354073310325100036561)
                  ·
                    rfl

theorem cell22_3429717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_3429717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429717 prefixEnd_3429717 := by exact prefixLift 3429717
  have htrace : WordTrace (prefixWord ++ tailWord_3429717) baseStart_3429717 baseEnd_3429717 := by
    simpa [prefixWord, tailWord_3429717, baseEnd_3429717] using wordTrace_append hprefix tailTrace_3429717
  have hstable : (prefixWord ++ tailWord_3429717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429717).length < 2 ^ (prefixWord ++ tailWord_3429717).sum := by decide
  have hdescent : baseEnd_3429717 < baseStart_3429717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429721 : List Nat := [1, 2, 1, 2, 2, 2, 6, 2, 1, 3]
def baseStart_3429721 : Nat := 118140960795 + 3429721 * 2 ^ 59
def prefixEnd_3429721 : Nat := 4983230072969 + 3 ^ 40 * 3429721 * 2
def baseEnd_3429721 : Nat := 1174063589212720623009671

theorem tailTrace_3429721 : CollatzResearch.WordTrace tailWord_3429721 prefixEnd_3429721 1174063589212720623009671 := by
  unfold tailWord_3429721
  simp only [CollatzResearch.WordTrace]
  refine ⟨125092201607714041557993017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83394801071809361038662011 125092201607714041557993017)
  ·
    refine ⟨93819151205785531168494763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125092201607714041557993017 93819151205785531168494763)
    ·
      refine ⟨140728726808678296752742145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93819151205785531168494763 140728726808678296752742145)
      ·
        refine ⟨105546545106508722564556609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140728726808678296752742145 105546545106508722564556609)
        ·
          refine ⟨79159908829881541923417457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105546545106508722564556609 79159908829881541923417457)
          ·
            refine ⟨59369931622411156442563093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79159908829881541923417457 59369931622411156442563093)
            ·
              refine ⟨2782965544800522958245145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59369931622411156442563093 2782965544800522958245145)
              ·
                refine ⟨2087224158600392218683859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2782965544800522958245145 2087224158600392218683859)
                ·
                  refine ⟨3130836237900588328025789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2087224158600392218683859 3130836237900588328025789)
                  ·
                    refine ⟨1174063589212720623009671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3130836237900588328025789 1174063589212720623009671)
                    ·
                      rfl

theorem cell22_3429721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 1, 3].length) (baseStart_3429721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429721 prefixEnd_3429721 := by exact prefixLift 3429721
  have htrace : WordTrace (prefixWord ++ tailWord_3429721) baseStart_3429721 baseEnd_3429721 := by
    simpa [prefixWord, tailWord_3429721, baseEnd_3429721] using wordTrace_append hprefix tailTrace_3429721
  have hstable : (prefixWord ++ tailWord_3429721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429721).length < 2 ^ (prefixWord ++ tailWord_3429721).sum := by decide
  have hdescent : baseEnd_3429721 < baseStart_3429721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429732 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_3429732 : Nat := 118140960795 + 3429732 * 2 ^ 59
def prefixEnd_3429732 : Nat := 4983230072969 + 3 ^ 40 * 3429732 * 2
def baseEnd_3429732 : Nat := 1174067354737520260984637

theorem tailTrace_3429732 : CollatzResearch.WordTrace tailWord_3429732 prefixEnd_3429732 1174067354737520260984637 := by
  unfold tailWord_3429732
  simp only [CollatzResearch.WordTrace]
  refine ⟨62546301405337095218321725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83395068540449460291095633 62546301405337095218321725)
  ·
    refine ⟨23454863027001410706870647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62546301405337095218321725 23454863027001410706870647)
    ·
      refine ⟨35182294540502116060305971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23454863027001410706870647 35182294540502116060305971)
      ·
        refine ⟨52773441810753174090458957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35182294540502116060305971 52773441810753174090458957)
        ·
          refine ⟨19790040679032440283922109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52773441810753174090458957 19790040679032440283922109)
          ·
            refine ⟨7421265254637165106470791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19790040679032440283922109 7421265254637165106470791)
            ·
              refine ⟨11131897881955747659706187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7421265254637165106470791 11131897881955747659706187)
              ·
                refine ⟨16697846822933621489559281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11131897881955747659706187 16697846822933621489559281)
                ·
                  refine ⟨12523385117200216117169461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16697846822933621489559281 12523385117200216117169461)
                  ·
                    refine ⟨1174067354737520260984637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12523385117200216117169461 1174067354737520260984637)
                    ·
                      rfl

theorem cell22_3429732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_3429732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429732 prefixEnd_3429732 := by exact prefixLift 3429732
  have htrace : WordTrace (prefixWord ++ tailWord_3429732) baseStart_3429732 baseEnd_3429732 := by
    simpa [prefixWord, tailWord_3429732, baseEnd_3429732] using wordTrace_append hprefix tailTrace_3429732
  have hstable : (prefixWord ++ tailWord_3429732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429732).length < 2 ^ (prefixWord ++ tailWord_3429732).sum := by decide
  have hdescent : baseEnd_3429732 < baseStart_3429732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429745 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 8]
def baseStart_3429745 : Nat := 118140960795 + 3429745 * 2 ^ 59
def prefixEnd_3429745 : Nat := 4983230072969 + 3 ^ 40 * 3429745 * 2
def baseEnd_3429745 : Nat := 391357268301064186803199

theorem tailTrace_3429745 : CollatzResearch.WordTrace tailWord_3429745 prefixEnd_3429745 391357268301064186803199 := by
  unfold tailWord_3429745
  simp only [CollatzResearch.WordTrace]
  refine ⟨125093076959627093656866689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83395384639751395771244459 125093076959627093656866689)
  ·
    refine ⟨93819807719720320242650017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125093076959627093656866689 93819807719720320242650017)
    ·
      refine ⟨70364855789790240181987513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93819807719720320242650017 70364855789790240181987513)
      ·
        refine ⟨52773641842342680136490635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70364855789790240181987513 52773641842342680136490635)
        ·
          refine ⟨79160462763514020204735953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52773641842342680136490635 79160462763514020204735953)
          ·
            refine ⟨59370347072635515153551965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79160462763514020204735953 59370347072635515153551965)
            ·
              refine ⟨22263880152238318182581987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59370347072635515153551965 22263880152238318182581987)
              ·
                refine ⟨33395820228357477273872981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22263880152238318182581987 33395820228357477273872981)
                ·
                  refine ⟨391357268301064186803199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33395820228357477273872981 391357268301064186803199)
                  ·
                    rfl

theorem cell22_3429745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 8].length) (baseStart_3429745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429745 prefixEnd_3429745 := by exact prefixLift 3429745
  have htrace : WordTrace (prefixWord ++ tailWord_3429745) baseStart_3429745 baseEnd_3429745 := by
    simpa [prefixWord, tailWord_3429745, baseEnd_3429745] using wordTrace_append hprefix tailTrace_3429745
  have hstable : (prefixWord ++ tailWord_3429745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429745).length < 2 ^ (prefixWord ++ tailWord_3429745).sum := by decide
  have hdescent : baseEnd_3429745 < baseStart_3429745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429764 : List Nat := [2, 3, 2, 1, 1, 4, 1, 3, 1, 4]
def baseStart_3429764 : Nat := 118140960795 + 3429764 * 2 ^ 59
def prefixEnd_3429764 : Nat := 4983230072969 + 3 ^ 40 * 3429764 * 2
def baseEnd_3429764 : Nat := 1174078308991482844184539

theorem tailTrace_3429764 : CollatzResearch.WordTrace tailWord_3429764 prefixEnd_3429764 1174078308991482844184539 := by
  unfold tailWord_3429764
  simp only [CollatzResearch.WordTrace]
  refine ⟨62546884973279129950904173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83395846631038839934538897 62546884973279129950904173)
  ·
    refine ⟨23455081864979673731589065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62546884973279129950904173 23455081864979673731589065)
    ·
      refine ⟨17591311398734755298691799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23455081864979673731589065 17591311398734755298691799)
      ·
        refine ⟨26386967098102132948037699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17591311398734755298691799 26386967098102132948037699)
        ·
          refine ⟨39580450647153199422056549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26386967098102132948037699 39580450647153199422056549)
          ·
            refine ⟨7421334496341224891635603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39580450647153199422056549 7421334496341224891635603)
            ·
              refine ⟨11132001744511837337453405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7421334496341224891635603 11132001744511837337453405)
              ·
                refine ⟨4174500654191939001545027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11132001744511837337453405 4174500654191939001545027)
                ·
                  refine ⟨6261750981287908502317541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4174500654191939001545027 6261750981287908502317541)
                  ·
                    refine ⟨1174078308991482844184539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6261750981287908502317541 1174078308991482844184539)
                    ·
                      rfl

theorem cell22_3429764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_3429764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429764 prefixEnd_3429764 := by exact prefixLift 3429764
  have htrace : WordTrace (prefixWord ++ tailWord_3429764) baseStart_3429764 baseEnd_3429764 := by
    simpa [prefixWord, tailWord_3429764, baseEnd_3429764] using wordTrace_append hprefix tailTrace_3429764
  have hstable : (prefixWord ++ tailWord_3429764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429764).length < 2 ^ (prefixWord ++ tailWord_3429764).sum := by decide
  have hdescent : baseEnd_3429764 < baseStart_3429764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429777 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 4, 3]
def baseStart_3429777 : Nat := 118140960795 + 3429777 * 2 ^ 59
def prefixEnd_3429777 : Nat := 4983230072969 + 3 ^ 40 * 3429777 * 2
def baseEnd_3429777 : Nat := 1174082759157155143609499

theorem tailTrace_3429777 : CollatzResearch.WordTrace tailWord_3429777 prefixEnd_3429777 1174082759157155143609499 := by
  unfold tailWord_3429777
  simp only [CollatzResearch.WordTrace]
  refine ⟨125094244095511163122031585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83396162730340775414687723 125094244095511163122031585)
  ·
    refine ⟨93820683071633372341523689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125094244095511163122031585 93820683071633372341523689)
    ·
      refine ⟨70365512303725029256142767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93820683071633372341523689 70365512303725029256142767)
      ·
        refine ⟨105548268455587543884214151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70365512303725029256142767 105548268455587543884214151)
        ·
          refine ⟨158322402683381315826321227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105548268455587543884214151 158322402683381315826321227)
          ·
            refine ⟨237483604025071973739481841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158322402683381315826321227 237483604025071973739481841)
            ·
              refine ⟨178112703018803980304611381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237483604025071973739481841 178112703018803980304611381)
              ·
                refine ⟨16698065908012873153557317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178112703018803980304611381 16698065908012873153557317)
                ·
                  refine ⟨3130887357752413716291997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16698065908012873153557317 3130887357752413716291997)
                  ·
                    refine ⟨1174082759157155143609499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3130887357752413716291997 1174082759157155143609499)
                    ·
                      rfl

theorem cell22_3429777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_3429777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429777 prefixEnd_3429777 := by exact prefixLift 3429777
  have htrace : WordTrace (prefixWord ++ tailWord_3429777) baseStart_3429777 baseEnd_3429777 := by
    simpa [prefixWord, tailWord_3429777, baseEnd_3429777] using wordTrace_append hprefix tailTrace_3429777
  have hstable : (prefixWord ++ tailWord_3429777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429777).length < 2 ^ (prefixWord ++ tailWord_3429777).sum := by decide
  have hdescent : baseEnd_3429777 < baseStart_3429777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429794 : List Nat := [3, 3, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_3429794 : Nat := 118140960795 + 3429794 * 2 ^ 59
def prefixEnd_3429794 : Nat := 4983230072969 + 3 ^ 40 * 3429794 * 2
def baseEnd_3429794 : Nat := 1174088578604572765934447

theorem tailTrace_3429794 : CollatzResearch.WordTrace tailWord_3429794 prefixEnd_3429794 1174088578604572765934447 := by
  unfold tailWord_3429794
  simp only [CollatzResearch.WordTrace]
  refine ⟨31273716034112393756350109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83396576090966383350266957 31273716034112393756350109)
  ·
    refine ⟨11727643512792147658631291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31273716034112393756350109 11727643512792147658631291)
    ·
      refine ⟨17591465269188221487946937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11727643512792147658631291 17591465269188221487946937)
      ·
        refine ⟨13193598951891166115960203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17591465269188221487946937 13193598951891166115960203)
        ·
          refine ⟨19790398427836749173940305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13193598951891166115960203 19790398427836749173940305)
          ·
            refine ⟨14842798820877561880455229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19790398427836749173940305 14842798820877561880455229)
            ·
              refine ⟨5566049557829085705170711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14842798820877561880455229 5566049557829085705170711)
              ·
                refine ⟨8349074336743628557756067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5566049557829085705170711 8349074336743628557756067)
                ·
                  refine ⟨12523611505115442836634101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8349074336743628557756067 12523611505115442836634101)
                  ·
                    refine ⟨1174088578604572765934447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12523611505115442836634101 1174088578604572765934447)
                    ·
                      rfl

theorem cell22_3429794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_3429794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429794 prefixEnd_3429794 := by exact prefixLift 3429794
  have htrace : WordTrace (prefixWord ++ tailWord_3429794) baseStart_3429794 baseEnd_3429794 := by
    simpa [prefixWord, tailWord_3429794, baseEnd_3429794] using wordTrace_append hprefix tailTrace_3429794
  have hstable : (prefixWord ++ tailWord_3429794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429794).length < 2 ^ (prefixWord ++ tailWord_3429794).sum := by decide
  have hdescent : baseEnd_3429794 < baseStart_3429794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429839 : List Nat := [1, 1, 2, 1, 1, 4, 5, 1, 3, 3]
def baseStart_3429839 : Nat := 118140960795 + 3429839 * 2 ^ 59
def prefixEnd_3429839 : Nat := 4983230072969 + 3 ^ 40 * 3429839 * 2
def baseEnd_3429839 : Nat := 1174103983024207648559309

theorem tailTrace_3429839 : CollatzResearch.WordTrace tailWord_3429839 prefixEnd_3429839 1174103983024207648559309 := by
  unfold tailWord_3429839
  simp only [CollatzResearch.WordTrace]
  refine ⟨125096505421286547710788571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83397670280857698473859047 125096505421286547710788571)
  ·
    refine ⟨187644758131929821566182857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125096505421286547710788571 187644758131929821566182857)
    ·
      refine ⟨140733568598947366174637143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187644758131929821566182857 140733568598947366174637143)
      ·
        refine ⟨211100352898421049261955715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140733568598947366174637143 211100352898421049261955715)
        ·
          refine ⟨316650529347631573892933573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211100352898421049261955715 316650529347631573892933573)
          ·
            refine ⟨59371974252680920104925045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 316650529347631573892933573 59371974252680920104925045)
            ·
              refine ⟨5566122586188836259836723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59371974252680920104925045 5566122586188836259836723)
              ·
                refine ⟨8349183879283254389755085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5566122586188836259836723 8349183879283254389755085)
                ·
                  refine ⟨3130943954731220396158157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8349183879283254389755085 3130943954731220396158157)
                  ·
                    refine ⟨1174103983024207648559309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3130943954731220396158157 1174103983024207648559309)
                    ·
                      rfl

theorem cell22_3429839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 3].length) (baseStart_3429839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429839 prefixEnd_3429839 := by exact prefixLift 3429839
  have htrace : WordTrace (prefixWord ++ tailWord_3429839) baseStart_3429839 baseEnd_3429839 := by
    simpa [prefixWord, tailWord_3429839, baseEnd_3429839] using wordTrace_append hprefix tailTrace_3429839
  have hstable : (prefixWord ++ tailWord_3429839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429839).length < 2 ^ (prefixWord ++ tailWord_3429839).sum := by decide
  have hdescent : baseEnd_3429839 < baseStart_3429839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429890 : List Nat := [3, 4, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_3429890 : Nat := 118140960795 + 3429890 * 2 ^ 59
def prefixEnd_3429890 : Nat := 4983230072969 + 3 ^ 40 * 3429890 * 2
def baseEnd_3429890 : Nat := 1174121441366460515534153

theorem tailTrace_3429890 : CollatzResearch.WordTrace tailWord_3429890 prefixEnd_3429890 1174121441366460515534153 := by
  unfold tailWord_3429890
  simp only [CollatzResearch.WordTrace]
  refine ⟨31274591386025445855223781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83398910362734522280596749 31274591386025445855223781)
  ·
    refine ⟨5863985884879771097854459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31274591386025445855223781 5863985884879771097854459)
    ·
      refine ⟨8795978827319656646781689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5863985884879771097854459 8795978827319656646781689)
      ·
        refine ⟨6596984120489742485086267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8795978827319656646781689 6596984120489742485086267)
        ·
          refine ⟨9895476180734613727629401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6596984120489742485086267 9895476180734613727629401)
          ·
            refine ⟨7421607135550960295722051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9895476180734613727629401 7421607135550960295722051)
            ·
              refine ⟨11132410703326440443583077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7421607135550960295722051 11132410703326440443583077)
              ·
                refine ⟨2087327006873707583171827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11132410703326440443583077 2087327006873707583171827)
                ·
                  refine ⟨3130990510310561374757741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2087327006873707583171827 3130990510310561374757741)
                  ·
                    refine ⟨1174121441366460515534153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3130990510310561374757741 1174121441366460515534153)
                    ·
                      rfl

theorem cell22_3429890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_3429890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429890 prefixEnd_3429890 := by exact prefixLift 3429890
  have htrace : WordTrace (prefixWord ++ tailWord_3429890) baseStart_3429890 baseEnd_3429890 := by
    simpa [prefixWord, tailWord_3429890, baseEnd_3429890] using wordTrace_append hprefix tailTrace_3429890
  have hstable : (prefixWord ++ tailWord_3429890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429890).length < 2 ^ (prefixWord ++ tailWord_3429890).sum := by decide
  have hdescent : baseEnd_3429890 < baseStart_3429890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429897 : List Nat := [1, 2, 1, 1, 3, 1, 4, 3, 6]
def baseStart_3429897 : Nat := 118140960795 + 3429897 * 2 ^ 59
def prefixEnd_3429897 : Nat := 4983230072969 + 3 ^ 40 * 3429897 * 2
def baseEnd_3429897 : Nat := 391374612536504943536377

theorem tailTrace_3429897 : CollatzResearch.WordTrace tailWord_3429897 prefixEnd_3429897 391374612536504943536377 := by
  unfold tailWord_3429897
  simp only [CollatzResearch.WordTrace]
  refine ⟨125098620855076423616399945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83399080570050949077599963 125098620855076423616399945)
  ·
    refine ⟨93823965641307317712299959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125098620855076423616399945 93823965641307317712299959)
    ·
      refine ⟨140735948461960976568449939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93823965641307317712299959 140735948461960976568449939)
      ·
        refine ⟨211103922692941464852674909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140735948461960976568449939 211103922692941464852674909)
        ·
          refine ⟨79163971009853049319753091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211103922692941464852674909 79163971009853049319753091)
          ·
            refine ⟨118745956514779573979629637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79163971009853049319753091 118745956514779573979629637)
            ·
              refine ⟨22264866846521170121180557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118745956514779573979629637 22264866846521170121180557)
              ·
                refine ⟨8349325067445438795442709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22264866846521170121180557 8349325067445438795442709)
                ·
                  refine ⟨391374612536504943536377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8349325067445438795442709 391374612536504943536377)
                  ·
                    rfl

theorem cell22_3429897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 6].length) (baseStart_3429897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3429897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3429897 prefixEnd_3429897 := by exact prefixLift 3429897
  have htrace : WordTrace (prefixWord ++ tailWord_3429897) baseStart_3429897 baseEnd_3429897 := by
    simpa [prefixWord, tailWord_3429897, baseEnd_3429897] using wordTrace_append hprefix tailTrace_3429897
  have hstable : (prefixWord ++ tailWord_3429897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429897).length < 2 ^ (prefixWord ++ tailWord_3429897).sum := by decide
  have hdescent : baseEnd_3429897 < baseStart_3429897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430079 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 1, 6]
def baseStart_3430079 : Nat := 118140960795 + 3430079 * 2 ^ 59
def prefixEnd_3430079 : Nat := 4983230072969 + 3 ^ 40 * 3430079 * 2
def baseEnd_3430079 : Nat := 1174186139928927022558573

theorem tailTrace_3430079 : CollatzResearch.WordTrace tailWord_3430079 prefixEnd_3430079 1174186139928927022558573 := by
  unfold tailWord_3430079
  simp only [CollatzResearch.WordTrace]
  refine ⟨125105258940417068699525291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83403505960278045799683527 125105258940417068699525291)
  ·
    refine ⟨187657888410625603049287937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125105258940417068699525291 187657888410625603049287937)
    ·
      refine ⟨140743416307969202286965953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187657888410625603049287937 140743416307969202286965953)
      ·
        refine ⟨105557562230976901715224465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140743416307969202286965953 105557562230976901715224465)
        ·
          refine ⟨79168171673232676286418349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105557562230976901715224465 79168171673232676286418349)
          ·
            refine ⟨29688064377462253607406881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79168171673232676286418349 29688064377462253607406881)
            ·
              refine ⟨22266048283096690205555161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29688064377462253607406881 22266048283096690205555161)
              ·
                refine ⟨16699536212322517654166371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22266048283096690205555161 16699536212322517654166371)
                ·
                  refine ⟨25049304318483776481249557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16699536212322517654166371 25049304318483776481249557)
                  ·
                    refine ⟨1174186139928927022558573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25049304318483776481249557 1174186139928927022558573)
                    ·
                      rfl

theorem cell22_3430079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_3430079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430079 prefixEnd_3430079 := by exact prefixLift 3430079
  have htrace : WordTrace (prefixWord ++ tailWord_3430079) baseStart_3430079 baseEnd_3430079 := by
    simpa [prefixWord, tailWord_3430079, baseEnd_3430079] using wordTrace_append hprefix tailTrace_3430079
  have hstable : (prefixWord ++ tailWord_3430079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430079).length < 2 ^ (prefixWord ++ tailWord_3430079).sum := by decide
  have hdescent : baseEnd_3430079 < baseStart_3430079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430100 : List Nat := [2, 4, 1, 3, 1, 2, 2, 3, 4]
def baseStart_3430100 : Nat := 118140960795 + 3430100 * 2 ^ 59
def prefixEnd_3430100 : Nat := 4983230072969 + 3 ^ 40 * 3430100 * 2
def baseEnd_3430100 : Nat := 391397776219363322594503

theorem tailTrace_3430100 : CollatzResearch.WordTrace tailWord_3430100 prefixEnd_3430100 391397776219363322594503 := by
  unfold tailWord_3430100
  simp only [CollatzResearch.WordTrace]
  refine ⟨62553012436670494643019877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83404016582227326190693169 62553012436670494643019877)
  ·
    refine ⟨11728689831875717745566227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62553012436670494643019877 11728689831875717745566227)
    ·
      refine ⟨17593034747813576618349341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11728689831875717745566227 17593034747813576618349341)
      ·
        refine ⟨6597388030430091231881003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17593034747813576618349341 6597388030430091231881003)
        ·
          refine ⟨9896082045645136847821505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6597388030430091231881003 9896082045645136847821505)
          ·
            refine ⟨7422061534233852635866129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9896082045645136847821505 7422061534233852635866129)
            ·
              refine ⟨5566546150675389476899597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7422061534233852635866129 5566546150675389476899597)
              ·
                refine ⟨2087454806503271053837349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5566546150675389476899597 2087454806503271053837349)
                ·
                  refine ⟨391397776219363322594503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2087454806503271053837349 391397776219363322594503)
                  ·
                    rfl

theorem cell22_3430100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_3430100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430100 prefixEnd_3430100 := by exact prefixLift 3430100
  have htrace : WordTrace (prefixWord ++ tailWord_3430100) baseStart_3430100 baseEnd_3430100 := by
    simpa [prefixWord, tailWord_3430100, baseEnd_3430100] using wordTrace_append hprefix tailTrace_3430100
  have hstable : (prefixWord ++ tailWord_3430100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430100).length < 2 ^ (prefixWord ++ tailWord_3430100).sum := by decide
  have hdescent : baseEnd_3430100 < baseStart_3430100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430102 : List Nat := [5, 2, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_3430102 : Nat := 118140960795 + 3430102 * 2 ^ 59
def prefixEnd_3430102 : Nat := 4983230072969 + 3 ^ 40 * 3430102 * 2
def baseEnd_3430102 : Nat := 1174194013298962629233503

theorem tailTrace_3430102 : CollatzResearch.WordTrace tailWord_3430102 prefixEnd_3430102 1174194013298962629233503 := by
  unfold tailWord_3430102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7819131113708358976725785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83404065212889162418408373 7819131113708358976725785)
  ·
    refine ⟨5864348335281269232544339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7819131113708358976725785 5864348335281269232544339)
    ·
      refine ⟨8796522502921903848816509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5864348335281269232544339 8796522502921903848816509)
      ·
        refine ⟨3298695938595713943306191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8796522502921903848816509 3298695938595713943306191)
        ·
          refine ⟨4948043907893570914959287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3298695938595713943306191 4948043907893570914959287)
          ·
            refine ⟨7422065861840356372438931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4948043907893570914959287 7422065861840356372438931)
            ·
              refine ⟨11133098792760534558658397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7422065861840356372438931 11133098792760534558658397)
              ·
                refine ⟨4174912047285200459496899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11133098792760534558658397 4174912047285200459496899)
                ·
                  refine ⟨6262368070927800689245349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4174912047285200459496899 6262368070927800689245349)
                  ·
                    refine ⟨1174194013298962629233503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6262368070927800689245349 1174194013298962629233503)
                    ·
                      rfl

theorem cell22_3430102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_3430102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430102 prefixEnd_3430102 := by exact prefixLift 3430102
  have htrace : WordTrace (prefixWord ++ tailWord_3430102) baseStart_3430102 baseEnd_3430102 := by
    simpa [prefixWord, tailWord_3430102, baseEnd_3430102] using wordTrace_append hprefix tailTrace_3430102
  have hstable : (prefixWord ++ tailWord_3430102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430102).length < 2 ^ (prefixWord ++ tailWord_3430102).sum := by decide
  have hdescent : baseEnd_3430102 < baseStart_3430102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430124 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 1, 8]
def baseStart_3430124 : Nat := 118140960795 + 3430124 * 2 ^ 59
def prefixEnd_3430124 : Nat := 4983230072969 + 3 ^ 40 * 3430124 * 2
def baseEnd_3430124 : Nat := 1174201544348561905183435

theorem tailTrace_3430124 : CollatzResearch.WordTrace tailWord_3430124 prefixEnd_3430124 1174201544348561905183435 := by
  unfold tailWord_3430124
  simp only [CollatzResearch.WordTrace]
  refine ⟨62553450112627020692456713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83404600150169360923275617 62553450112627020692456713)
  ·
    refine ⟨46915087584470265519342535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62553450112627020692456713 46915087584470265519342535)
    ·
      refine ⟨70372631376705398279013803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46915087584470265519342535 70372631376705398279013803)
      ·
        refine ⟨105558947065058097418520705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70372631376705398279013803 105558947065058097418520705)
        ·
          refine ⟨79169210298793573063890529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105558947065058097418520705 79169210298793573063890529)
          ·
            refine ⟨59376907724095179797917897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79169210298793573063890529 59376907724095179797917897)
            ·
              refine ⟨44532680793071384848438423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59376907724095179797917897 44532680793071384848438423)
              ·
                refine ⟨66799021189607077272657635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44532680793071384848438423 66799021189607077272657635)
                ·
                  refine ⟨100198531784410615908986453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66799021189607077272657635 100198531784410615908986453)
                  ·
                    refine ⟨1174201544348561905183435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100198531784410615908986453 1174201544348561905183435)
                    ·
                      rfl

theorem cell22_3430124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_3430124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430124 prefixEnd_3430124 := by exact prefixLift 3430124
  have htrace : WordTrace (prefixWord ++ tailWord_3430124) baseStart_3430124 baseEnd_3430124 := by
    simpa [prefixWord, tailWord_3430124, baseEnd_3430124] using wordTrace_append hprefix tailTrace_3430124
  have hstable : (prefixWord ++ tailWord_3430124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430124).length < 2 ^ (prefixWord ++ tailWord_3430124).sum := by decide
  have hdescent : baseEnd_3430124 < baseStart_3430124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430132 : List Nat := [2, 6, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_3430132 : Nat := 118140960795 + 3430132 * 2 ^ 59
def prefixEnd_3430132 : Nat := 4983230072969 + 3 ^ 40 * 3430132 * 2
def baseEnd_3430132 : Nat := 1174204282912052550983411

theorem tailTrace_3430132 : CollatzResearch.WordTrace tailWord_3430132 prefixEnd_3430132 1174204282912052550983411 := by
  unfold tailWord_3430132
  simp only [CollatzResearch.WordTrace]
  refine ⟨62553596004612529375602325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83404794672816705834136433 62553596004612529375602325)
  ·
    refine ⟨2932199812716212314481359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62553596004612529375602325 2932199812716212314481359)
    ·
      refine ⟨4398299719074318471722039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2932199812716212314481359 4398299719074318471722039)
      ·
        refine ⟨6597449578611477707583059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4398299719074318471722039 6597449578611477707583059)
        ·
          refine ⟨9896174367917216561374589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6597449578611477707583059 9896174367917216561374589)
          ·
            refine ⟨3711065387968956210515471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9896174367917216561374589 3711065387968956210515471)
            ·
              refine ⟨5566598081953434315773207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3711065387968956210515471 5566598081953434315773207)
              ·
                refine ⟨8349897122930151473659811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5566598081953434315773207 8349897122930151473659811)
                ·
                  refine ⟨12524845684395227210489717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8349897122930151473659811 12524845684395227210489717)
                  ·
                    refine ⟨1174204282912052550983411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12524845684395227210489717 1174204282912052550983411)
                    ·
                      rfl

theorem cell22_3430132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_3430132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430132 prefixEnd_3430132 := by exact prefixLift 3430132
  have htrace : WordTrace (prefixWord ++ tailWord_3430132) baseStart_3430132 baseEnd_3430132 := by
    simpa [prefixWord, tailWord_3430132, baseEnd_3430132] using wordTrace_append hprefix tailTrace_3430132
  have hstable : (prefixWord ++ tailWord_3430132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430132).length < 2 ^ (prefixWord ++ tailWord_3430132).sum := by decide
  have hdescent : baseEnd_3430132 < baseStart_3430132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430169 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 1, 10]
def baseStart_3430169 : Nat := 118140960795 + 3430169 * 2 ^ 59
def prefixEnd_3430169 : Nat := 4983230072969 + 3 ^ 40 * 3430169 * 2
def baseEnd_3430169 : Nat := 1174216948768196787808297

theorem tailTrace_3430169 : CollatzResearch.WordTrace tailWord_3430169 prefixEnd_3430169 1174216948768196787808297 := by
  unfold tailWord_3430169
  simp only [CollatzResearch.WordTrace]
  refine ⟨125108541510091014070301561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83405694340060676046867707 125108541510091014070301561)
  ·
    refine ⟨93831406132568260552726171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125108541510091014070301561 93831406132568260552726171)
    ·
      refine ⟨140747109198852390829089257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93831406132568260552726171 140747109198852390829089257)
      ·
        refine ⟨105560331899139293121816943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140747109198852390829089257 105560331899139293121816943)
        ·
          refine ⟨158340497848708939682725415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105560331899139293121816943 158340497848708939682725415)
          ·
            refine ⟨237510746773063409524088123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158340497848708939682725415 237510746773063409524088123)
            ·
              refine ⟨356266120159595114286132185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237510746773063409524088123 356266120159595114286132185)
              ·
                refine ⟨267199590119696335714599139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356266120159595114286132185 267199590119696335714599139)
                ·
                  refine ⟨400799385179544503571898709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267199590119696335714599139 400799385179544503571898709)
                  ·
                    refine ⟨1174216948768196787808297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 400799385179544503571898709 1174216948768196787808297)
                    ·
                      rfl

theorem cell22_3430169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_3430169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430169 prefixEnd_3430169 := by exact prefixLift 3430169
  have htrace : WordTrace (prefixWord ++ tailWord_3430169) baseStart_3430169 baseEnd_3430169 := by
    simpa [prefixWord, tailWord_3430169, baseEnd_3430169] using wordTrace_append hprefix tailTrace_3430169
  have hstable : (prefixWord ++ tailWord_3430169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430169).length < 2 ^ (prefixWord ++ tailWord_3430169).sum := by decide
  have hdescent : baseEnd_3430169 < baseStart_3430169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430177 : List Nat := [1, 2, 3, 2, 1, 4, 3, 2, 1, 3]
def baseStart_3430177 : Nat := 118140960795 + 3430177 * 2 ^ 59
def prefixEnd_3430177 : Nat := 4983230072969 + 3 ^ 40 * 3430177 * 2
def baseEnd_3430177 : Nat := 1174219687331687433608273

theorem tailTrace_3430177 : CollatzResearch.WordTrace tailWord_3430177 prefixEnd_3430177 1174219687331687433608273 := by
  unfold tailWord_3430177
  simp only [CollatzResearch.WordTrace]
  refine ⟨125108833294062031436592785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83405888862708020957728523 125108833294062031436592785)
  ·
    refine ⟨93831624970546523577444589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125108833294062031436592785 93831624970546523577444589)
    ·
      refine ⟨35186859363954946341541721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93831624970546523577444589 35186859363954946341541721)
      ·
        refine ⟨26390144522966209756156291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35186859363954946341541721 26390144522966209756156291)
        ·
          refine ⟨39585216784449314634234437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26390144522966209756156291 39585216784449314634234437)
          ·
            refine ⟨7422228147084246493918957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39585216784449314634234437 7422228147084246493918957)
            ·
              refine ⟨2783335555156592435219609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7422228147084246493918957 2783335555156592435219609)
              ·
                refine ⟨2087501666367444326414707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2783335555156592435219609 2087501666367444326414707)
                ·
                  refine ⟨3131252499551166489622061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2087501666367444326414707 3131252499551166489622061)
                  ·
                    refine ⟨1174219687331687433608273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3131252499551166489622061 1174219687331687433608273)
                    ·
                      rfl

theorem cell22_3430177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_3430177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430177 prefixEnd_3430177 := by exact prefixLift 3430177
  have htrace : WordTrace (prefixWord ++ tailWord_3430177) baseStart_3430177 baseEnd_3430177 := by
    simpa [prefixWord, tailWord_3430177, baseEnd_3430177] using wordTrace_append hprefix tailTrace_3430177
  have hstable : (prefixWord ++ tailWord_3430177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430177).length < 2 ^ (prefixWord ++ tailWord_3430177).sum := by decide
  have hdescent : baseEnd_3430177 < baseStart_3430177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430190 : List Nat := [4, 1, 3, 2, 2, 1, 1, 3, 5]
def baseStart_3430190 : Nat := 118140960795 + 3430190 * 2 ^ 59
def prefixEnd_3430190 : Nat := 4983230072969 + 3 ^ 40 * 3430190 * 2
def baseEnd_3430190 : Nat := 391408045832453244344411

theorem tailTrace_3430190 : CollatzResearch.WordTrace tailWord_3430190 prefixEnd_3430190 391408045832453244344411 := by
  unfold tailWord_3430190
  simp only [CollatzResearch.WordTrace]
  refine ⟨15638663430376866832102003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83406204962009956437877349 15638663430376866832102003)
  ·
    refine ⟨23457995145565300248153005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15638663430376866832102003 23457995145565300248153005)
    ·
      refine ⟨8796748179586987593057377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23457995145565300248153005 8796748179586987593057377)
      ·
        refine ⟨6597561134690240694793033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8796748179586987593057377 6597561134690240694793033)
        ·
          refine ⟨4948170851017680521094775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6597561134690240694793033 4948170851017680521094775)
          ·
            refine ⟨7422256276526520781642163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4948170851017680521094775 7422256276526520781642163)
            ·
              refine ⟨11133384414789781172463245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7422256276526520781642163 11133384414789781172463245)
              ·
                refine ⟨4175019155546167939673717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11133384414789781172463245 4175019155546167939673717)
                ·
                  refine ⟨391408045832453244344411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4175019155546167939673717 391408045832453244344411)
                  ·
                    rfl

theorem cell22_3430190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_3430190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430190 prefixEnd_3430190 := by exact prefixLift 3430190
  have htrace : WordTrace (prefixWord ++ tailWord_3430190) baseStart_3430190 baseEnd_3430190 := by
    simpa [prefixWord, tailWord_3430190, baseEnd_3430190] using wordTrace_append hprefix tailTrace_3430190
  have hstable : (prefixWord ++ tailWord_3430190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430190).length < 2 ^ (prefixWord ++ tailWord_3430190).sum := by decide
  have hdescent : baseEnd_3430190 < baseStart_3430190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430216 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 3, 5]
def baseStart_3430216 : Nat := 118140960795 + 3430216 * 2 ^ 59
def prefixEnd_3430216 : Nat := 4983230072969 + 3 ^ 40 * 3430216 * 2
def baseEnd_3430216 : Nat := 1174233037828704331883153

theorem tailTrace_3430216 : CollatzResearch.WordTrace tailWord_3430216 prefixEnd_3430216 1174233037828704331883153 := by
  unfold tailWord_3430216
  simp only [CollatzResearch.WordTrace]
  refine ⟨62555127870460370548631251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83406837160613827398175001 62555127870460370548631251)
  ·
    refine ⟨93832691805690555822946877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62555127870460370548631251 93832691805690555822946877)
    ·
      refine ⟨35187259427133958433605079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93832691805690555822946877 35187259427133958433605079)
      ·
        refine ⟨52780889140700937650407619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35187259427133958433605079 52780889140700937650407619)
        ·
          refine ⟨79171333711051406475611429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52780889140700937650407619 79171333711051406475611429)
          ·
            refine ⟨14844625070822138714177143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79171333711051406475611429 14844625070822138714177143)
            ·
              refine ⟨22266937606233208071265715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14844625070822138714177143 22266937606233208071265715)
              ·
                refine ⟨33400406409349812106898573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22266937606233208071265715 33400406409349812106898573)
                ·
                  refine ⟨12525152403506179540086965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33400406409349812106898573 12525152403506179540086965)
                  ·
                    refine ⟨1174233037828704331883153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12525152403506179540086965 1174233037828704331883153)
                    ·
                      rfl

theorem cell22_3430216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_3430216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430216 prefixEnd_3430216 := by exact prefixLift 3430216
  have htrace : WordTrace (prefixWord ++ tailWord_3430216) baseStart_3430216 baseEnd_3430216 := by
    simpa [prefixWord, tailWord_3430216, baseEnd_3430216] using wordTrace_append hprefix tailTrace_3430216
  have hstable : (prefixWord ++ tailWord_3430216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430216).length < 2 ^ (prefixWord ++ tailWord_3430216).sum := by decide
  have hdescent : baseEnd_3430216 < baseStart_3430216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430218 : List Nat := [3, 1, 2, 1, 1, 1, 4, 5, 4]
def baseStart_3430218 : Nat := 118140960795 + 3430218 * 2 ^ 59
def prefixEnd_3430218 : Nat := 4983230072969 + 3 ^ 40 * 3430218 * 2
def baseEnd_3430218 : Nat := 391411240823192331111049

theorem tailTrace_3430218 : CollatzResearch.WordTrace tailWord_3430218 prefixEnd_3430218 391411240823192331111049 := by
  unfold tailWord_3430218
  simp only [CollatzResearch.WordTrace]
  refine ⟨31277582171728373859708827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83406885791275663625890205 31277582171728373859708827)
  ·
    refine ⟨46916373257592560789563241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31277582171728373859708827 46916373257592560789563241)
    ·
      refine ⟨35187279943194420592172431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46916373257592560789563241 35187279943194420592172431)
      ·
        refine ⟨52780919914791630888258647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35187279943194420592172431 52780919914791630888258647)
        ·
          refine ⟨79171379872187446332387971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52780919914791630888258647 79171379872187446332387971)
          ·
            refine ⟨118757069808281169498581957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79171379872187446332387971 118757069808281169498581957)
            ·
              refine ⟨22266950589052719280984117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118757069808281169498581957 22266950589052719280984117)
              ·
                refine ⟨2087526617723692432592261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22266950589052719280984117 2087526617723692432592261)
                ·
                  refine ⟨391411240823192331111049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2087526617723692432592261 391411240823192331111049)
                  ·
                    rfl

theorem cell22_3430218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 4].length) (baseStart_3430218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430218 prefixEnd_3430218 := by exact prefixLift 3430218
  have htrace : WordTrace (prefixWord ++ tailWord_3430218) baseStart_3430218 baseEnd_3430218 := by
    simpa [prefixWord, tailWord_3430218, baseEnd_3430218] using wordTrace_append hprefix tailTrace_3430218
  have hstable : (prefixWord ++ tailWord_3430218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430218).length < 2 ^ (prefixWord ++ tailWord_3430218).sum := by decide
  have hdescent : baseEnd_3430218 < baseStart_3430218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430295 : List Nat := [1, 1, 3, 3, 1, 4, 2, 1, 3, 3]
def baseStart_3430295 : Nat := 118140960795 + 3430295 * 2 ^ 59
def prefixEnd_3430295 : Nat := 4983230072969 + 3 ^ 40 * 3430295 * 2
def baseEnd_3430295 : Nat := 1174260081143174459157911

theorem tailTrace_3430295 : CollatzResearch.WordTrace tailWord_3430295 prefixEnd_3430295 1174260081143174459157911 := by
  unfold tailWord_3430295
  simp only [CollatzResearch.WordTrace]
  refine ⟨125113137107634537589388339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83408758071756358392925559 125113137107634537589388339)
  ·
    refine ⟨187669705661451806384082509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125113137107634537589388339 187669705661451806384082509)
    ·
      refine ⟨70376139623044427394030941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187669705661451806384082509 70376139623044427394030941)
      ·
        refine ⟨26391052358641660272761603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70376139623044427394030941 26391052358641660272761603)
        ·
          refine ⟨39586578537962490409142405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26391052358641660272761603 39586578537962490409142405)
          ·
            refine ⟨7422483475867966951714201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39586578537962490409142405 7422483475867966951714201)
            ·
              refine ⟨5566862606900975213785651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7422483475867966951714201 5566862606900975213785651)
              ·
                refine ⟨8350293910351462820678477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5566862606900975213785651 8350293910351462820678477)
                ·
                  refine ⟨3131360216381798557754429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8350293910351462820678477 3131360216381798557754429)
                  ·
                    refine ⟨1174260081143174459157911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3131360216381798557754429 1174260081143174459157911)
                    ·
                      rfl

theorem cell22_3430295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_3430295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430295 prefixEnd_3430295 := by exact prefixLift 3430295
  have htrace : WordTrace (prefixWord ++ tailWord_3430295) baseStart_3430295 baseEnd_3430295 := by
    simpa [prefixWord, tailWord_3430295, baseEnd_3430295] using wordTrace_append hprefix tailTrace_3430295
  have hstable : (prefixWord ++ tailWord_3430295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430295).length < 2 ^ (prefixWord ++ tailWord_3430295).sum := by decide
  have hdescent : baseEnd_3430295 < baseStart_3430295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430385 : List Nat := [1, 2, 2, 2, 5, 1, 1, 2, 1, 5]
def baseStart_3430385 : Nat := 118140960795 + 3430385 * 2 ^ 59
def prefixEnd_3430385 : Nat := 4983230072969 + 3 ^ 40 * 3430385 * 2
def baseEnd_3430385 : Nat := 1174290889982444224407635

theorem tailTrace_3430385 : CollatzResearch.WordTrace tailWord_3430385 prefixEnd_3430385 1174290889982444224407635 := by
  unfold tailWord_3430385
  simp only [CollatzResearch.WordTrace]
  refine ⟨125116419677308482960164609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83410946451538988640109739 125116419677308482960164609)
  ·
    refine ⟨93837314757981362220123457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125116419677308482960164609 93837314757981362220123457)
    ·
      refine ⟨70377986068486021665092593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93837314757981362220123457 70377986068486021665092593)
      ·
        refine ⟨52783489551364516248819445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70377986068486021665092593 52783489551364516248819445)
        ·
          refine ⟨4948452145440423398326823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52783489551364516248819445 4948452145440423398326823)
          ·
            refine ⟨7422678218160635097490235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4948452145440423398326823 7422678218160635097490235)
            ·
              refine ⟨11134017327240952646235353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7422678218160635097490235 11134017327240952646235353)
              ·
                refine ⟨8350512995430714484676515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11134017327240952646235353 8350512995430714484676515)
                ·
                  refine ⟨12525769493146071727014773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8350512995430714484676515 12525769493146071727014773)
                  ·
                    refine ⟨1174290889982444224407635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12525769493146071727014773 1174290889982444224407635)
                    ·
                      rfl

theorem cell22_3430385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_3430385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430385 prefixEnd_3430385 := by exact prefixLift 3430385
  have htrace : WordTrace (prefixWord ++ tailWord_3430385) baseStart_3430385 baseEnd_3430385 := by
    simpa [prefixWord, tailWord_3430385, baseEnd_3430385] using wordTrace_append hprefix tailTrace_3430385
  have hstable : (prefixWord ++ tailWord_3430385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430385).length < 2 ^ (prefixWord ++ tailWord_3430385).sum := by decide
  have hdescent : baseEnd_3430385 < baseStart_3430385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430404 : List Nat := [2, 3, 2, 4, 1, 1, 1, 4, 4]
def baseStart_3430404 : Nat := 118140960795 + 3430404 * 2 ^ 59
def prefixEnd_3430404 : Nat := 4983230072969 + 3 ^ 40 * 3430404 * 2
def baseEnd_3430404 : Nat := 391432464690244836060859

theorem tailTrace_3430404 : CollatzResearch.WordTrace tailWord_3430404 prefixEnd_3430404 391432464690244836060859 := by
  unfold tailWord_3430404
  simp only [CollatzResearch.WordTrace]
  refine ⟨62558556332119824602553133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83411408442826432803404177 62558556332119824602553133)
  ·
    refine ⟨23459458624544934225957425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62558556332119824602553133 23459458624544934225957425)
    ·
      refine ⟨17594593968408700669468069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23459458624544934225957425 17594593968408700669468069)
      ·
        refine ⟨3298986369076631375525263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17594593968408700669468069 3298986369076631375525263)
        ·
          refine ⟨4948479553614947063287895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3298986369076631375525263 4948479553614947063287895)
          ·
            refine ⟨7422719330422420594931843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4948479553614947063287895 7422719330422420594931843)
            ·
              refine ⟨11134078995633630892397765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7422719330422420594931843 11134078995633630892397765)
              ·
                refine ⟨2087639811681305792324581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11134078995633630892397765 2087639811681305792324581)
                ·
                  refine ⟨391432464690244836060859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2087639811681305792324581 391432464690244836060859)
                  ·
                    rfl

theorem cell22_3430404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_3430404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430404 prefixEnd_3430404 := by exact prefixLift 3430404
  have htrace : WordTrace (prefixWord ++ tailWord_3430404) baseStart_3430404 baseEnd_3430404 := by
    simpa [prefixWord, tailWord_3430404, baseEnd_3430404] using wordTrace_append hprefix tailTrace_3430404
  have hstable : (prefixWord ++ tailWord_3430404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430404).length < 2 ^ (prefixWord ++ tailWord_3430404).sum := by decide
  have hdescent : baseEnd_3430404 < baseStart_3430404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430498 : List Nat := [3, 3, 2, 2, 2, 2, 1, 3, 1, 3]
def baseStart_3430498 : Nat := 118140960795 + 3430498 * 2 ^ 59
def prefixEnd_3430498 : Nat := 4983230072969 + 3 ^ 40 * 3430498 * 2
def baseEnd_3430498 : Nat := 1174329572191749596332289

theorem tailTrace_3430498 : CollatzResearch.WordTrace tailWord_3430498 prefixEnd_3430498 1174329572191749596332289 := by
  unfold tailWord_3430498
  simp only [CollatzResearch.WordTrace]
  refine ⟨31280135281474775814757037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83413694083932735506018765 31280135281474775814757037)
  ·
    refine ⟨11730050730553040930533889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31280135281474775814757037 11730050730553040930533889)
    ·
      refine ⟨8797538047914780697900417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11730050730553040930533889 8797538047914780697900417)
      ·
        refine ⟨6598153535936085523425313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8797538047914780697900417 6598153535936085523425313)
        ·
          refine ⟨4948615151952064142568985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6598153535936085523425313 4948615151952064142568985)
          ·
            refine ⟨3711461363964048106926739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4948615151952064142568985 3711461363964048106926739)
            ·
              refine ⟨5567192045946072160390109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3711461363964048106926739 5567192045946072160390109)
              ·
                refine ⟨2087697017229777060146291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5567192045946072160390109 2087697017229777060146291)
                ·
                  refine ⟨3131545525844665590219437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2087697017229777060146291 3131545525844665590219437)
                  ·
                    refine ⟨1174329572191749596332289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3131545525844665590219437 1174329572191749596332289)
                    ·
                      rfl

theorem cell22_3430498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_3430498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430498 prefixEnd_3430498 := by exact prefixLift 3430498
  have htrace : WordTrace (prefixWord ++ tailWord_3430498) baseStart_3430498 baseEnd_3430498 := by
    simpa [prefixWord, tailWord_3430498, baseEnd_3430498] using wordTrace_append hprefix tailTrace_3430498
  have hstable : (prefixWord ++ tailWord_3430498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430498).length < 2 ^ (prefixWord ++ tailWord_3430498).sum := by decide
  have hdescent : baseEnd_3430498 < baseStart_3430498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430537 : List Nat := [1, 2, 1, 1, 4, 2, 3, 3, 2, 3]
def baseStart_3430537 : Nat := 118140960795 + 3430537 * 2 ^ 59
def prefixEnd_3430537 : Nat := 4983230072969 + 3 ^ 40 * 3430537 * 2
def baseEnd_3430537 : Nat := 1174342922688766494607169

theorem tailTrace_3430537 : CollatzResearch.WordTrace tailWord_3430537 prefixEnd_3430537 1174342922688766494607169 := by
  unfold tailWord_3430537
  simp only [CollatzResearch.WordTrace]
  refine ⟨125121963572757812919697865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83414642381838541946465243 125121963572757812919697865)
  ·
    refine ⟨93841472679568359689773399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125121963572757812919697865 93841472679568359689773399)
    ·
      refine ⟨140762209019352539534660099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93841472679568359689773399 140762209019352539534660099)
      ·
        refine ⟨211143313529028809301990149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140762209019352539534660099 211143313529028809301990149)
        ·
          refine ⟨39589371286692901744123153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211143313529028809301990149 39589371286692901744123153)
          ·
            refine ⟨29692028465019676308092365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39589371286692901744123153 29692028465019676308092365)
            ·
              refine ⟨11134510674382378615534637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29692028465019676308092365 11134510674382378615534637)
              ·
                refine ⟨4175441502893391980825489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11134510674382378615534637 4175441502893391980825489)
                ·
                  refine ⟨3131581127170043985619117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4175441502893391980825489 3131581127170043985619117)
                  ·
                    refine ⟨1174342922688766494607169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3131581127170043985619117 1174342922688766494607169)
                    ·
                      rfl

theorem cell22_3430537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 3].length) (baseStart_3430537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430537 prefixEnd_3430537 := by exact prefixLift 3430537
  have htrace : WordTrace (prefixWord ++ tailWord_3430537) baseStart_3430537 baseEnd_3430537 := by
    simpa [prefixWord, tailWord_3430537, baseEnd_3430537] using wordTrace_append hprefix tailTrace_3430537
  have hstable : (prefixWord ++ tailWord_3430537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430537).length < 2 ^ (prefixWord ++ tailWord_3430537).sum := by decide
  have hdescent : baseEnd_3430537 < baseStart_3430537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430567 : List Nat := [1, 1, 6, 2, 3, 9]
def baseStart_3430567 : Nat := 118140960795 + 3430567 * 2 ^ 59
def prefixEnd_3430567 : Nat := 4983230072969 + 3 ^ 40 * 3430567 * 2
def baseEnd_3430567 : Nat := 14498187559282177979717

theorem tailTrace_3430567 : CollatzResearch.WordTrace tailWord_3430567 prefixEnd_3430567 14498187559282177979717 := by
  unfold tailWord_3430567
  simp only [CollatzResearch.WordTrace]
  refine ⟨125123057762649128043289955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83415371841766085362193303 125123057762649128043289955)
  ·
    refine ⟨187684586643973692064934933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125123057762649128043289955 187684586643973692064934933)
    ·
      refine ⟨8797714998936266815543825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 187684586643973692064934933 8797714998936266815543825)
      ·
        refine ⟨6598286249202200111657869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8797714998936266815543825 6598286249202200111657869)
        ·
          refine ⟨2474357343450825041871701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6598286249202200111657869 2474357343450825041871701)
          ·
            refine ⟨14498187559282177979717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2474357343450825041871701 14498187559282177979717)
            ·
              rfl

theorem cell22_3430567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 9].length) (baseStart_3430567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430567 prefixEnd_3430567 := by exact prefixLift 3430567
  have htrace : WordTrace (prefixWord ++ tailWord_3430567) baseStart_3430567 baseEnd_3430567 := by
    simpa [prefixWord, tailWord_3430567, baseEnd_3430567] using wordTrace_append hprefix tailTrace_3430567
  have hstable : (prefixWord ++ tailWord_3430567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430567).length < 2 ^ (prefixWord ++ tailWord_3430567).sum := by decide
  have hdescent : baseEnd_3430567 < baseStart_3430567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430616 : List Nat := [2, 1, 2, 2, 4, 2, 2, 3, 1, 3]
def baseStart_3430616 : Nat := 118140960795 + 3430616 * 2 ^ 59
def prefixEnd_3430616 : Nat := 4983230072969 + 3 ^ 40 * 3430616 * 2
def baseEnd_3430616 : Nat := 1174369966003236621881927

theorem tailTrace_3430616 : CollatzResearch.WordTrace tailWord_3430616 prefixEnd_3430616 1174369966003236621881927 := by
  unfold tailWord_3430616
  simp only [CollatzResearch.WordTrace]
  refine ⟨62562422469735804705911851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83416563292981072941215801 62562422469735804705911851)
  ·
    refine ⟨93843633704603707058867777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62562422469735804705911851 93843633704603707058867777)
    ·
      refine ⟨70382725278452780294150833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93843633704603707058867777 70382725278452780294150833)
      ·
        refine ⟨52787043958839585220613125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70382725278452780294150833 52787043958839585220613125)
        ·
          refine ⟨9897570742282422228864961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52787043958839585220613125 9897570742282422228864961)
          ·
            refine ⟨7423178056711816671648721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9897570742282422228864961 7423178056711816671648721)
            ·
              refine ⟨5567383542533862503736541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7423178056711816671648721 5567383542533862503736541)
              ·
                refine ⟨2087768828450198438901203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5567383542533862503736541 2087768828450198438901203)
                ·
                  refine ⟨3131653242675297658351805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2087768828450198438901203 3131653242675297658351805)
                  ·
                    refine ⟨1174369966003236621881927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3131653242675297658351805 1174369966003236621881927)
                    ·
                      rfl

theorem cell22_3430616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 1, 3].length) (baseStart_3430616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430616 prefixEnd_3430616 := by exact prefixLift 3430616
  have htrace : WordTrace (prefixWord ++ tailWord_3430616) baseStart_3430616 baseEnd_3430616 := by
    simpa [prefixWord, tailWord_3430616, baseEnd_3430616] using wordTrace_append hprefix tailTrace_3430616
  have hstable : (prefixWord ++ tailWord_3430616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430616).length < 2 ^ (prefixWord ++ tailWord_3430616).sum := by decide
  have hdescent : baseEnd_3430616 < baseStart_3430616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430629 : List Nat := [1, 3, 1, 4, 2, 3, 1, 2, 5]
def baseStart_3430629 : Nat := 118140960795 + 3430629 * 2 ^ 59
def prefixEnd_3430629 : Nat := 4983230072969 + 3 ^ 40 * 3430629 * 2
def baseEnd_3430629 : Nat := 391458138722969640435629

theorem tailTrace_3430629 : CollatzResearch.WordTrace tailWord_3430629 prefixEnd_3430629 391458138722969640435629 := by
  unfold tailWord_3430629
  simp only [CollatzResearch.WordTrace]
  refine ⟨125125319088424512632046941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83416879392283008421364627 125125319088424512632046941)
  ·
    refine ⟨46921994658159192237017603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125125319088424512632046941 46921994658159192237017603)
    ·
      refine ⟨70382991987238788355526405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46921994658159192237017603 70382991987238788355526405)
      ·
        refine ⟨13196810997607272816661201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70382991987238788355526405 13196810997607272816661201)
        ·
          refine ⟨9897608248205454612495901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13196810997607272816661201 9897608248205454612495901)
          ·
            refine ⟨3711603093077045479685963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9897608248205454612495901 3711603093077045479685963)
            ·
              refine ⟨5567404639615568219528945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3711603093077045479685963 5567404639615568219528945)
              ·
                refine ⟨4175553479711676164646709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5567404639615568219528945 4175553479711676164646709)
                ·
                  refine ⟨391458138722969640435629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4175553479711676164646709 391458138722969640435629)
                  ·
                    rfl

theorem cell22_3430629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_3430629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430629 prefixEnd_3430629 := by exact prefixLift 3430629
  have htrace : WordTrace (prefixWord ++ tailWord_3430629) baseStart_3430629 baseEnd_3430629 := by
    simpa [prefixWord, tailWord_3430629, baseEnd_3430629] using wordTrace_append hprefix tailTrace_3430629
  have hstable : (prefixWord ++ tailWord_3430629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430629).length < 2 ^ (prefixWord ++ tailWord_3430629).sum := by decide
  have hdescent : baseEnd_3430629 < baseStart_3430629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430687 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 4, 4]
def baseStart_3430687 : Nat := 118140960795 + 3430687 * 2 ^ 59
def prefixEnd_3430687 : Nat := 4983230072969 + 3 ^ 40 * 3430687 * 2
def baseEnd_3430687 : Nat := 1174394270754216103356709

theorem tailTrace_3430687 : CollatzResearch.WordTrace tailWord_3430687 prefixEnd_3430687 1174394270754216103356709 := by
  unfold tailWord_3430687
  simp only [CollatzResearch.WordTrace]
  refine ⟨125127434522214388537658315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83418289681476259025105543 125127434522214388537658315)
  ·
    refine ⟨187691151783321582806487473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125127434522214388537658315 187691151783321582806487473)
    ·
      refine ⟨140768363837491187104865605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187691151783321582806487473 140768363837491187104865605)
      ·
        refine ⟨26394068219529597582162301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140768363837491187104865605 26394068219529597582162301)
        ·
          refine ⟨9897775582323599093310863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26394068219529597582162301 9897775582323599093310863)
          ·
            refine ⟨14846663373485398639966295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9897775582323599093310863 14846663373485398639966295)
            ·
              refine ⟨22269995060228097959949443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14846663373485398639966295 22269995060228097959949443)
              ·
                refine ⟨33404992590342146939924165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22269995060228097959949443 33404992590342146939924165)
                ·
                  refine ⟨6263436110689152551235781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33404992590342146939924165 6263436110689152551235781)
                  ·
                    refine ⟨1174394270754216103356709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6263436110689152551235781 1174394270754216103356709)
                    ·
                      rfl

theorem cell22_3430687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 4].length) (baseStart_3430687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430687 prefixEnd_3430687 := by exact prefixLift 3430687
  have htrace : WordTrace (prefixWord ++ tailWord_3430687) baseStart_3430687 baseEnd_3430687 := by
    simpa [prefixWord, tailWord_3430687, baseEnd_3430687] using wordTrace_append hprefix tailTrace_3430687
  have hstable : (prefixWord ++ tailWord_3430687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430687).length < 2 ^ (prefixWord ++ tailWord_3430687).sum := by decide
  have hdescent : baseEnd_3430687 < baseStart_3430687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430706 : List Nat := [3, 2, 1, 1, 5, 1, 1, 3, 2, 3]
def baseStart_3430706 : Nat := 118140960795 + 3430706 * 2 ^ 59
def prefixEnd_3430706 : Nat := 4983230072969 + 3 ^ 40 * 3430706 * 2
def baseEnd_3430706 : Nat := 1174400774842506387131651

theorem tailTrace_3430706 : CollatzResearch.WordTrace tailWord_3430706 prefixEnd_3430706 1174400774842506387131651 := by
  unfold tailWord_3430706
  simp only [CollatzResearch.WordTrace]
  refine ⟨31282031877286388695649993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83418751672763703188399981 31282031877286388695649993)
  ·
    refine ⟨23461523907964791521737495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31282031877286388695649993 23461523907964791521737495)
    ·
      refine ⟨35192285861947187282606243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23461523907964791521737495 35192285861947187282606243)
      ·
        refine ⟨52788428792920780923909365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35192285861947187282606243 52788428792920780923909365)
        ·
          refine ⟨4948915199336323211616503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52788428792920780923909365 4948915199336323211616503)
          ·
            refine ⟨7423372799004484817424755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4948915199336323211616503 7423372799004484817424755)
            ·
              refine ⟨11135059198506727226137133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7423372799004484817424755 11135059198506727226137133)
              ·
                refine ⟨4175647199440022709801425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11135059198506727226137133 4175647199440022709801425)
                ·
                  refine ⟨3131735399580017032351069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4175647199440022709801425 3131735399580017032351069)
                  ·
                    refine ⟨1174400774842506387131651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3131735399580017032351069 1174400774842506387131651)
                    ·
                      rfl

theorem cell22_3430706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_3430706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430706 prefixEnd_3430706 := by exact prefixLift 3430706
  have htrace : WordTrace (prefixWord ++ tailWord_3430706) baseStart_3430706 baseEnd_3430706 := by
    simpa [prefixWord, tailWord_3430706, baseEnd_3430706] using wordTrace_append hprefix tailTrace_3430706
  have hstable : (prefixWord ++ tailWord_3430706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430706).length < 2 ^ (prefixWord ++ tailWord_3430706).sum := by decide
  have hdescent : baseEnd_3430706 < baseStart_3430706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430721 : List Nat := [1, 2, 5, 2, 2, 1, 2, 1, 2, 4]
def baseStart_3430721 : Nat := 118140960795 + 3430721 * 2 ^ 59
def prefixEnd_3430721 : Nat := 4983230072969 + 3 ^ 40 * 3430721 * 2
def baseEnd_3430721 : Nat := 1174405909649051348006605

theorem tailTrace_3430721 : CollatzResearch.WordTrace tailWord_3430721 prefixEnd_3430721 1174405909649051348006605 := by
  unfold tailWord_3430721
  simp only [CollatzResearch.WordTrace]
  refine ⟨125128674604091212344396017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83419116402727474896264011 125128674604091212344396017)
  ·
    refine ⟨93846505953068409258297013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125128674604091212344396017 93846505953068409258297013)
    ·
      refine ⟨8798109933100163367965345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93846505953068409258297013 8798109933100163367965345)
      ·
        refine ⟨6598582449825122525974009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8798109933100163367965345 6598582449825122525974009)
        ·
          refine ⟨4948936837368841894480507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6598582449825122525974009 4948936837368841894480507)
          ·
            refine ⟨7423405256053262841720761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4948936837368841894480507 7423405256053262841720761)
            ·
              refine ⟨5567553942039947131290571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7423405256053262841720761 5567553942039947131290571)
              ·
                refine ⟨8351330913059920696935857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5567553942039947131290571 8351330913059920696935857)
                ·
                  refine ⟨6263498184794940522701893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8351330913059920696935857 6263498184794940522701893)
                  ·
                    refine ⟨1174405909649051348006605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6263498184794940522701893 1174405909649051348006605)
                    ·
                      rfl

theorem cell22_3430721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_3430721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430721 prefixEnd_3430721 := by exact prefixLift 3430721
  have htrace : WordTrace (prefixWord ++ tailWord_3430721) baseStart_3430721 baseEnd_3430721 := by
    simpa [prefixWord, tailWord_3430721, baseEnd_3430721] using wordTrace_append hprefix tailTrace_3430721
  have hstable : (prefixWord ++ tailWord_3430721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430721).length < 2 ^ (prefixWord ++ tailWord_3430721).sum := by decide
  have hdescent : baseEnd_3430721 < baseStart_3430721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430792 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 8]
def baseStart_3430792 : Nat := 118140960795 + 3430792 * 2 ^ 59
def prefixEnd_3430792 : Nat := 4983230072969 + 3 ^ 40 * 3430792 * 2
def baseEnd_3430792 : Nat := 391476738133343609827129

theorem tailTrace_3430792 : CollatzResearch.WordTrace tailWord_3430792 prefixEnd_3430792 391476738133343609827129 := by
  unfold tailWord_3430792
  simp only [CollatzResearch.WordTrace]
  refine ⟨62565632093416995735115315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83420842791222660980153753 62565632093416995735115315)
  ·
    refine ⟨93848448140125493602672973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62565632093416995735115315 93848448140125493602672973)
    ·
      refine ⟨35193168052547060101002365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93848448140125493602672973 35193168052547060101002365)
      ·
        refine ⟨13197438019705147537875887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35193168052547060101002365 13197438019705147537875887)
        ·
          refine ⟨19796157029557721306813831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13197438019705147537875887 19796157029557721306813831)
          ·
            refine ⟨29694235544336581960220747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19796157029557721306813831 29694235544336581960220747)
            ·
              refine ⟨44541353316504872940331121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29694235544336581960220747 44541353316504872940331121)
              ·
                refine ⟨33406014987378654705248341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44541353316504872940331121 33406014987378654705248341)
                ·
                  refine ⟨391476738133343609827129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33406014987378654705248341 391476738133343609827129)
                  ·
                    rfl

theorem cell22_3430792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 8].length) (baseStart_3430792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430792 prefixEnd_3430792 := by exact prefixLift 3430792
  have htrace : WordTrace (prefixWord ++ tailWord_3430792) baseStart_3430792 baseEnd_3430792 := by
    simpa [prefixWord, tailWord_3430792, baseEnd_3430792] using wordTrace_append hprefix tailTrace_3430792
  have hstable : (prefixWord ++ tailWord_3430792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430792).length < 2 ^ (prefixWord ++ tailWord_3430792).sum := by decide
  have hdescent : baseEnd_3430792 < baseStart_3430792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430807 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 3, 5]
def baseStart_3430807 : Nat := 118140960795 + 3430807 * 2 ^ 59
def prefixEnd_3430807 : Nat := 4983230072969 + 3 ^ 40 * 3430807 * 2
def baseEnd_3430807 : Nat := 1174435349206575790356341

theorem tailTrace_3430807 : CollatzResearch.WordTrace tailWord_3430807 prefixEnd_3430807 1174435349206575790356341 := by
  unfold tailWord_3430807
  simp only [CollatzResearch.WordTrace]
  refine ⟨125131811281779649032026675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83421207521186432688017783 125131811281779649032026675)
  ·
    refine ⟨187697716922669473548040013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125131811281779649032026675 187697716922669473548040013)
    ·
      refine ⟨70386643846001052580515005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187697716922669473548040013 70386643846001052580515005)
      ·
        refine ⟨26394991442250394717693127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70386643846001052580515005 26394991442250394717693127)
        ·
          refine ⟨39592487163375592076539691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26394991442250394717693127 39592487163375592076539691)
          ·
            refine ⟨59388730745063388114809537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39592487163375592076539691 59388730745063388114809537)
            ·
              refine ⟨44541548058797541086107153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59388730745063388114809537 44541548058797541086107153)
              ·
                refine ⟨33406161044098155814580365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44541548058797541086107153 33406161044098155814580365)
                ·
                  refine ⟨12527310391536808430467637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33406161044098155814580365 12527310391536808430467637)
                  ·
                    refine ⟨1174435349206575790356341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12527310391536808430467637 1174435349206575790356341)
                    ·
                      rfl

theorem cell22_3430807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_3430807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430807 prefixEnd_3430807 := by exact prefixLift 3430807
  have htrace : WordTrace (prefixWord ++ tailWord_3430807) baseStart_3430807 baseEnd_3430807 := by
    simpa [prefixWord, tailWord_3430807, baseEnd_3430807] using wordTrace_append hprefix tailTrace_3430807
  have hstable : (prefixWord ++ tailWord_3430807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430807).length < 2 ^ (prefixWord ++ tailWord_3430807).sum := by decide
  have hdescent : baseEnd_3430807 < baseStart_3430807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430809 : List Nat := [1, 2, 1, 2, 1, 4, 1, 6, 4]
def baseStart_3430809 : Nat := 118140960795 + 3430809 * 2 ^ 59
def prefixEnd_3430809 : Nat := 4983230072969 + 3 ^ 40 * 3430809 * 2
def baseEnd_3430809 : Nat := 391478677949149483935445

theorem tailTrace_3430809 : CollatzResearch.WordTrace tailWord_3430809 prefixEnd_3430809 391478677949149483935445 := by
  unfold tailWord_3430809
  simp only [CollatzResearch.WordTrace]
  refine ⟨125131884227772403373599481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83421256151848268915732987 125131884227772403373599481)
  ·
    refine ⟨93848913170829302530199611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125131884227772403373599481 93848913170829302530199611)
    ·
      refine ⟨140773369756243953795299417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93848913170829302530199611 140773369756243953795299417)
      ·
        refine ⟨105580027317182965346474563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140773369756243953795299417 105580027317182965346474563)
        ·
          refine ⟨158370040975774448019711845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105580027317182965346474563 158370040975774448019711845)
          ·
            refine ⟨29694382682957709003695971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158370040975774448019711845 29694382682957709003695971)
            ·
              refine ⟨44541574024436563505543957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29694382682957709003695971 44541574024436563505543957)
              ·
                refine ⟨2087886282395463914322373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44541574024436563505543957 2087886282395463914322373)
                ·
                  refine ⟨391478677949149483935445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2087886282395463914322373 391478677949149483935445)
                  ·
                    rfl

theorem cell22_3430809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 4].length) (baseStart_3430809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430809 prefixEnd_3430809 := by exact prefixLift 3430809
  have htrace : WordTrace (prefixWord ++ tailWord_3430809) baseStart_3430809 baseEnd_3430809 := by
    simpa [prefixWord, tailWord_3430809, baseEnd_3430809] using wordTrace_append hprefix tailTrace_3430809
  have hstable : (prefixWord ++ tailWord_3430809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430809).length < 2 ^ (prefixWord ++ tailWord_3430809).sum := by decide
  have hdescent : baseEnd_3430809 < baseStart_3430809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430916 : List Nat := [2, 3, 2, 3, 1, 1, 1, 4, 5]
def baseStart_3430916 : Nat := 118140960795 + 3430916 * 2 ^ 59
def prefixEnd_3430916 : Nat := 4983230072969 + 3 ^ 40 * 3430916 * 2
def baseEnd_3430916 : Nat := 391490887378045279793669

theorem tailTrace_3430916 : CollatzResearch.WordTrace tailWord_3430916 prefixEnd_3430916 391490887378045279793669 := by
  unfold tailWord_3430916
  simp only [CollatzResearch.WordTrace]
  refine ⟨62567893419192380323872301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83423857892256507098496401 62567893419192380323872301)
  ·
    refine ⟨23462960032197142621452113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62567893419192380323872301 23462960032197142621452113)
    ·
      refine ⟨17597220024147856966089085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23462960032197142621452113 17597220024147856966089085)
      ·
        refine ⟨6598957509055446362283407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17597220024147856966089085 6598957509055446362283407)
        ·
          refine ⟨9898436263583169543425111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6598957509055446362283407 9898436263583169543425111)
          ·
            refine ⟨14847654395374754315137667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9898436263583169543425111 14847654395374754315137667)
            ·
              refine ⟨22271481593062131472706501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14847654395374754315137667 22271481593062131472706501)
              ·
                refine ⟨4175902798699149651132469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22271481593062131472706501 4175902798699149651132469)
                ·
                  refine ⟨391490887378045279793669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4175902798699149651132469 391490887378045279793669)
                  ·
                    rfl

theorem cell22_3430916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_3430916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430916 prefixEnd_3430916 := by exact prefixLift 3430916
  have htrace : WordTrace (prefixWord ++ tailWord_3430916) baseStart_3430916 baseEnd_3430916 := by
    simpa [prefixWord, tailWord_3430916, baseEnd_3430916] using wordTrace_append hprefix tailTrace_3430916
  have hstable : (prefixWord ++ tailWord_3430916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430916).length < 2 ^ (prefixWord ++ tailWord_3430916).sum := by decide
  have hdescent : baseEnd_3430916 < baseStart_3430916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430946 : List Nat := [3, 3, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_3430946 : Nat := 118140960795 + 3430946 * 2 ^ 59
def prefixEnd_3430946 : Nat := 4983230072969 + 3 ^ 40 * 3430946 * 2
def baseEnd_3430946 : Nat := 1174482931747225761130915

theorem tailTrace_3430946 : CollatzResearch.WordTrace tailWord_3430946 prefixEnd_3430946 1174482931747225761130915 := by
  unfold tailWord_3430946
  simp only [CollatzResearch.WordTrace]
  refine ⟨31284220257069018942834173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83424587352184050514224461 31284220257069018942834173)
  ·
    refine ⟨11731582596400882103562815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31284220257069018942834173 11731582596400882103562815)
    ·
      refine ⟨17597373894601323155344223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11731582596400882103562815 17597373894601323155344223)
      ·
        refine ⟨26396060841901984733016335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17597373894601323155344223 26396060841901984733016335)
        ·
          refine ⟨39594091262852977099524503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26396060841901984733016335 39594091262852977099524503)
          ·
            refine ⟨59391136894279465649286755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39594091262852977099524503 59391136894279465649286755)
            ·
              refine ⟨89086705341419198473930133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59391136894279465649286755 89086705341419198473930133)
              ·
                refine ⟨4175939312879024928465475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89086705341419198473930133 4175939312879024928465475)
                ·
                  refine ⟨6263908969318537392698213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4175939312879024928465475 6263908969318537392698213)
                  ·
                    refine ⟨1174482931747225761130915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6263908969318537392698213 1174482931747225761130915)
                    ·
                      rfl

theorem cell22_3430946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_3430946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430946 prefixEnd_3430946 := by exact prefixLift 3430946
  have htrace : WordTrace (prefixWord ++ tailWord_3430946) baseStart_3430946 baseEnd_3430946 := by
    simpa [prefixWord, tailWord_3430946, baseEnd_3430946] using wordTrace_append hprefix tailTrace_3430946
  have hstable : (prefixWord ++ tailWord_3430946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430946).length < 2 ^ (prefixWord ++ tailWord_3430946).sum := by decide
  have hdescent : baseEnd_3430946 < baseStart_3430946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3430961 : List Nat := [1, 2, 2, 3, 1, 1, 3, 5, 4]
def baseStart_3430961 : Nat := 118140960795 + 3430961 * 2 ^ 59
def prefixEnd_3430961 : Nat := 4983230072969 + 3 ^ 40 * 3430961 * 2
def baseEnd_3430961 : Nat := 391496022184590240668623

theorem tailTrace_3430961 : CollatzResearch.WordTrace tailWord_3430961 prefixEnd_3430961 391496022184590240668623 := by
  unfold tailWord_3430961
  simp only [CollatzResearch.WordTrace]
  refine ⟨125137428123221733333132737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83424952082147822222088491 125137428123221733333132737)
  ·
    refine ⟨93853071092416299999849553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125137428123221733333132737 93853071092416299999849553)
    ·
      refine ⟨70389803319312224999887165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93853071092416299999849553 70389803319312224999887165)
      ·
        refine ⟨26396176244742084374957687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70389803319312224999887165 26396176244742084374957687)
        ·
          refine ⟨39594264367113126562436531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26396176244742084374957687 39594264367113126562436531)
          ·
            refine ⟨59391396550669689843654797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39594264367113126562436531 59391396550669689843654797)
            ·
              refine ⟨22271773706501133691370549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59391396550669689843654797 22271773706501133691370549)
              ·
                refine ⟨2087978784984481283565989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22271773706501133691370549 2087978784984481283565989)
                ·
                  refine ⟨391496022184590240668623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2087978784984481283565989 391496022184590240668623)
                  ·
                    rfl

theorem cell22_3430961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 4].length) (baseStart_3430961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3430961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3430961 prefixEnd_3430961 := by exact prefixLift 3430961
  have htrace : WordTrace (prefixWord ++ tailWord_3430961) baseStart_3430961 baseEnd_3430961 := by
    simpa [prefixWord, tailWord_3430961, baseEnd_3430961] using wordTrace_append hprefix tailTrace_3430961
  have hstable : (prefixWord ++ tailWord_3430961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3430961).length < 2 ^ (prefixWord ++ tailWord_3430961).sum := by decide
  have hdescent : baseEnd_3430961 < baseStart_3430961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3430961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431049 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 1, 7]
def baseStart_3431049 : Nat := 118140960795 + 3431049 * 2 ^ 59
def prefixEnd_3431049 : Nat := 4983230072969 + 3 ^ 40 * 3431049 * 2
def baseEnd_3431049 : Nat := 1174518190752167825805599

theorem tailTrace_3431049 : CollatzResearch.WordTrace tailWord_3431049 prefixEnd_3431049 1174518190752167825805599 := by
  unfold tailWord_3431049
  simp only [CollatzResearch.WordTrace]
  refine ⟨125140637746902924362336201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83427091831268616241557467 125140637746902924362336201)
  ·
    refine ⟨93855478310177193271752151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125140637746902924362336201 93855478310177193271752151)
    ·
      refine ⟨140783217465265789907628227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93855478310177193271752151 140783217465265789907628227)
      ·
        refine ⟨211174826197898684861442341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140783217465265789907628227 211174826197898684861442341)
        ·
          refine ⟨39595279912106003411520439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211174826197898684861442341 39595279912106003411520439)
          ·
            refine ⟨59392919868159005117280659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39595279912106003411520439 59392919868159005117280659)
            ·
              refine ⟨89089379802238507675920989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59392919868159005117280659 89089379802238507675920989)
              ·
                refine ⟨33408517425839440378470371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89089379802238507675920989 33408517425839440378470371)
                ·
                  refine ⟨50112776138759160567705557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33408517425839440378470371 50112776138759160567705557)
                  ·
                    refine ⟨1174518190752167825805599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50112776138759160567705557 1174518190752167825805599)
                    ·
                      rfl

theorem cell22_3431049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_3431049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431049 prefixEnd_3431049 := by exact prefixLift 3431049
  have htrace : WordTrace (prefixWord ++ tailWord_3431049) baseStart_3431049 baseEnd_3431049 := by
    simpa [prefixWord, tailWord_3431049, baseEnd_3431049] using wordTrace_append hprefix tailTrace_3431049
  have hstable : (prefixWord ++ tailWord_3431049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431049).length < 2 ^ (prefixWord ++ tailWord_3431049).sum := by decide
  have hdescent : baseEnd_3431049 < baseStart_3431049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431132 : List Nat := [2, 2, 5, 1, 1, 1, 4, 1, 1, 4]
def baseStart_3431132 : Nat := 118140960795 + 3431132 * 2 ^ 59
def prefixEnd_3431132 : Nat := 4983230072969 + 3 ^ 40 * 3431132 * 2
def baseEnd_3431132 : Nat := 1174546603348383275980345

theorem tailTrace_3431132 : CollatzResearch.WordTrace tailWord_3431132 prefixEnd_3431132 1174546603348383275980345 := by
  unfold tailWord_3431132
  simp only [CollatzResearch.WordTrace]
  refine ⟨62571832502801114768803825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83429110003734819691738433 62571832502801114768803825)
  ·
    refine ⟨46928874377100836076602869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62571832502801114768803825 46928874377100836076602869)
    ·
      refine ⟨4399581972853203382181519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46928874377100836076602869 4399581972853203382181519)
      ·
        refine ⟨6599372959279805073272279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4399581972853203382181519 6599372959279805073272279)
        ·
          refine ⟨9899059438919707609908419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6599372959279805073272279 9899059438919707609908419)
          ·
            refine ⟨14848589158379561414862629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9899059438919707609908419 14848589158379561414862629)
            ·
              refine ⟨2784110467196167765286743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14848589158379561414862629 2784110467196167765286743)
              ·
                refine ⟨4176165700794251647930115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2784110467196167765286743 4176165700794251647930115)
                ·
                  refine ⟨6264248551191377471895173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4176165700794251647930115 6264248551191377471895173)
                  ·
                    refine ⟨1174546603348383275980345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6264248551191377471895173 1174546603348383275980345)
                    ·
                      rfl

theorem cell22_3431132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_3431132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431132 prefixEnd_3431132 := by exact prefixLift 3431132
  have htrace : WordTrace (prefixWord ++ tailWord_3431132) baseStart_3431132 baseEnd_3431132 := by
    simpa [prefixWord, tailWord_3431132, baseEnd_3431132] using wordTrace_append hprefix tailTrace_3431132
  have hstable : (prefixWord ++ tailWord_3431132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431132).length < 2 ^ (prefixWord ++ tailWord_3431132).sum := by decide
  have hdescent : baseEnd_3431132 < baseStart_3431132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431141 : List Nat := [1, 3, 1, 4, 1, 3, 9]
def baseStart_3431141 : Nat := 118140960795 + 3431141 * 2 ^ 59
def prefixEnd_3431141 : Nat := 4983230072969 + 3 ^ 40 * 3431141 * 2
def baseEnd_3431141 : Nat := 43501840156752231574271

theorem tailTrace_3431141 : CollatzResearch.WordTrace tailWord_3431141 prefixEnd_3431141 43501840156752231574271 := by
  unfold tailWord_3431141
  simp only [CollatzResearch.WordTrace]
  refine ⟨125143993262569624074685277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83429328841713082716456851 125143993262569624074685277)
  ·
    refine ⟨46928997473463609028006979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125143993262569624074685277 46928997473463609028006979)
    ·
      refine ⟨70393496210195413542010469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46928997473463609028006979 70393496210195413542010469)
      ·
        refine ⟨13198780539411640039126963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70393496210195413542010469 13198780539411640039126963)
        ·
          refine ⟨19798170809117460058690445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13198780539411640039126963 19798170809117460058690445)
          ·
            refine ⟨7424314053419047522008917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19798170809117460058690445 7424314053419047522008917)
            ·
              refine ⟨43501840156752231574271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7424314053419047522008917 43501840156752231574271)
              ·
                rfl

theorem cell22_3431141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 9].length) (baseStart_3431141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431141 prefixEnd_3431141 := by exact prefixLift 3431141
  have htrace : WordTrace (prefixWord ++ tailWord_3431141) baseStart_3431141 baseEnd_3431141 := by
    simpa [prefixWord, tailWord_3431141, baseEnd_3431141] using wordTrace_append hprefix tailTrace_3431141
  have hstable : (prefixWord ++ tailWord_3431141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431141).length < 2 ^ (prefixWord ++ tailWord_3431141).sum := by decide
  have hdescent : baseEnd_3431141 < baseStart_3431141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431175 : List Nat := [1, 1, 4, 4, 1, 3, 2, 6]
def baseStart_3431175 : Nat := 118140960795 + 3431175 * 2 ^ 59
def prefixEnd_3431175 : Nat := 4983230072969 + 3 ^ 40 * 3431175 * 2
def baseEnd_3431175 : Nat := 130506813680793944128357

theorem tailTrace_3431175 : CollatzResearch.WordTrace tailWord_3431175 prefixEnd_3431175 130506813680793944128357 := by
  unfold tailWord_3431175
  simp only [CollatzResearch.WordTrace]
  refine ⟨125145233344446447881422979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83430155562964298587615319 125145233344446447881422979)
  ·
    refine ⟨187717850016669671822134469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125145233344446447881422979 187717850016669671822134469)
    ·
      refine ⟨35197096878125563466650213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187717850016669671822134469 35197096878125563466650213)
      ·
        refine ⟨6599455664648543149996915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35197096878125563466650213 6599455664648543149996915)
        ·
          refine ⟨9899183496972814724995373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6599455664648543149996915 9899183496972814724995373)
          ·
            refine ⟨3712193811364805521873265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9899183496972814724995373 3712193811364805521873265)
            ·
              refine ⟨2784145358523604141404949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3712193811364805521873265 2784145358523604141404949)
              ·
                refine ⟨130506813680793944128357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2784145358523604141404949 130506813680793944128357)
                ·
                  rfl

theorem cell22_3431175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 6].length) (baseStart_3431175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431175 prefixEnd_3431175 := by exact prefixLift 3431175
  have htrace : WordTrace (prefixWord ++ tailWord_3431175) baseStart_3431175 baseEnd_3431175 := by
    simpa [prefixWord, tailWord_3431175, baseEnd_3431175] using wordTrace_append hprefix tailTrace_3431175
  have hstable : (prefixWord ++ tailWord_3431175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431175).length < 2 ^ (prefixWord ++ tailWord_3431175).sum := by decide
  have hdescent : baseEnd_3431175 < baseStart_3431175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431213 : List Nat := [1, 5, 3, 2, 2, 1, 2, 1, 2, 3]
def baseStart_3431213 : Nat := 118140960795 + 3431213 * 2 ^ 59
def prefixEnd_3431213 : Nat := 4983230072969 + 3 ^ 40 * 3431213 * 2
def baseEnd_3431213 : Nat := 1174574331303726064705097

theorem tailTrace_3431213 : CollatzResearch.WordTrace tailWord_3431213 prefixEnd_3431213 1174574331303726064705097 := by
  unfold tailWord_3431213
  simp only [CollatzResearch.WordTrace]
  refine ⟨125146619318308780371306293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83431079545539186914204195 125146619318308780371306293)
  ·
    refine ⟨11732495561091448159809965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125146619318308780371306293 11732495561091448159809965)
    ·
      refine ⟨4399685835409293059928737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11732495561091448159809965 4399685835409293059928737)
      ·
        refine ⟨3299764376556969794946553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4399685835409293059928737 3299764376556969794946553)
        ·
          refine ⟨2474823282417727346209915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3299764376556969794946553 2474823282417727346209915)
          ·
            refine ⟨3712234923626591019314873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2474823282417727346209915 3712234923626591019314873)
            ·
              refine ⟨2784176192719943264486155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3712234923626591019314873 2784176192719943264486155)
              ·
                refine ⟨4176264289079914896729233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2784176192719943264486155 4176264289079914896729233)
                ·
                  refine ⟨3132198216809936172546925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4176264289079914896729233 3132198216809936172546925)
                  ·
                    refine ⟨1174574331303726064705097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3132198216809936172546925 1174574331303726064705097)
                    ·
                      rfl

theorem cell22_3431213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_3431213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431213 prefixEnd_3431213 := by exact prefixLift 3431213
  have htrace : WordTrace (prefixWord ++ tailWord_3431213) baseStart_3431213 baseEnd_3431213 := by
    simpa [prefixWord, tailWord_3431213, baseEnd_3431213] using wordTrace_append hprefix tailTrace_3431213
  have hstable : (prefixWord ++ tailWord_3431213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431213).length < 2 ^ (prefixWord ++ tailWord_3431213).sum := by decide
  have hdescent : baseEnd_3431213 < baseStart_3431213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431280 : List Nat := [2, 1, 1, 1, 4, 1, 4, 3, 2, 3]
def baseStart_3431280 : Nat := 118140960795 + 3431280 * 2 ^ 59
def prefixEnd_3431280 : Nat := 4983230072969 + 3 ^ 40 * 3431280 * 2
def baseEnd_3431280 : Nat := 1174597266772960223279891

theorem tailTrace_3431280 : CollatzResearch.WordTrace tailWord_3431280 prefixEnd_3431280 1174597266772960223279891 := by
  unfold tailWord_3431280
  simp only [CollatzResearch.WordTrace]
  refine ⟨62574531504533025406997647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83432708672710700542663529 62574531504533025406997647)
  ·
    refine ⟨93861797256799538110496471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62574531504533025406997647 93861797256799538110496471)
    ·
      refine ⟨140792695885199307165744707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93861797256799538110496471 140792695885199307165744707)
      ·
        refine ⟨211189043827798960748617061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140792695885199307165744707 211189043827798960748617061)
        ·
          refine ⟨39597945717712305140365699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211189043827798960748617061 39597945717712305140365699)
          ·
            refine ⟨59396918576568457710548549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39597945717712305140365699 59396918576568457710548549)
            ·
              refine ⟨11136922233106585820727853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59396918576568457710548549 11136922233106585820727853)
              ·
                refine ⟨4176345837414969682772945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11136922233106585820727853 4176345837414969682772945)
                ·
                  refine ⟨3132259378061227262079709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4176345837414969682772945 3132259378061227262079709)
                  ·
                    refine ⟨1174597266772960223279891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3132259378061227262079709 1174597266772960223279891)
                    ·
                      rfl

theorem cell22_3431280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 2, 3].length) (baseStart_3431280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431280 prefixEnd_3431280 := by exact prefixLift 3431280
  have htrace : WordTrace (prefixWord ++ tailWord_3431280) baseStart_3431280 baseEnd_3431280 := by
    simpa [prefixWord, tailWord_3431280, baseEnd_3431280] using wordTrace_append hprefix tailTrace_3431280
  have hstable : (prefixWord ++ tailWord_3431280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431280).length < 2 ^ (prefixWord ++ tailWord_3431280).sum := by decide
  have hdescent : baseEnd_3431280 < baseStart_3431280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431350 : List Nat := [5, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_3431350 : Nat := 118140960795 + 3431350 * 2 ^ 59
def prefixEnd_3431350 : Nat := 4983230072969 + 3 ^ 40 * 3431350 * 2
def baseEnd_3431350 : Nat := 391540409734501124676559

theorem tailTrace_3431350 : CollatzResearch.WordTrace tailWord_3431350 prefixEnd_3431350 391540409734501124676559 := by
  unfold tailWord_3431350
  simp only [CollatzResearch.WordTrace]
  refine ⟨7821976007425778298065219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83434410745874968512695669 7821976007425778298065219)
  ·
    refine ⟨11732964011138667447097829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7821976007425778298065219 11732964011138667447097829)
    ·
      refine ⟨2199930752088500146330843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11732964011138667447097829 2199930752088500146330843)
      ·
        refine ⟨3299896128132750219496265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2199930752088500146330843 3299896128132750219496265)
        ·
          refine ⟨2474922096099562664622199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3299896128132750219496265 2474922096099562664622199)
          ·
            refine ⟨3712383144149343996933299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2474922096099562664622199 3712383144149343996933299)
            ·
              refine ⟨5568574716224015995399949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3712383144149343996933299 5568574716224015995399949)
              ·
                refine ⟨2088215518584005998274981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5568574716224015995399949 2088215518584005998274981)
                ·
                  refine ⟨391540409734501124676559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2088215518584005998274981 391540409734501124676559)
                  ·
                    rfl

theorem cell22_3431350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_3431350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431350 prefixEnd_3431350 := by exact prefixLift 3431350
  have htrace : WordTrace (prefixWord ++ tailWord_3431350) baseStart_3431350 baseEnd_3431350 := by
    simpa [prefixWord, tailWord_3431350, baseEnd_3431350] using wordTrace_append hprefix tailTrace_3431350
  have hstable : (prefixWord ++ tailWord_3431350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431350).length < 2 ^ (prefixWord ++ tailWord_3431350).sum := by decide
  have hdescent : baseEnd_3431350 < baseStart_3431350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431383 : List Nat := [1, 1, 3, 2, 1, 1, 2, 5, 6]
def baseStart_3431383 : Nat := 118140960795 + 3431383 * 2 ^ 59
def prefixEnd_3431383 : Nat := 4983230072969 + 3 ^ 40 * 3431383 * 2
def baseEnd_3431383 : Nat := 391544175259300762651525

theorem tailTrace_3431383 : CollatzResearch.WordTrace tailWord_3431383 prefixEnd_3431383 391544175259300762651525 := by
  unfold tailWord_3431383
  simp only [CollatzResearch.WordTrace]
  refine ⟨125152819727692899404994803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83435213151795266269996535 125152819727692899404994803)
  ·
    refine ⟨187729229591539349107492205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125152819727692899404994803 187729229591539349107492205)
    ·
      refine ⟨70398461096827255915309577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187729229591539349107492205 70398461096827255915309577)
      ·
        refine ⟨52798845822620441936482183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70398461096827255915309577 52798845822620441936482183)
        ·
          refine ⟨79198268733930662904723275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52798845822620441936482183 79198268733930662904723275)
          ·
            refine ⟨118797403100895994357084913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79198268733930662904723275 118797403100895994357084913)
            ·
              refine ⟨89098052325671995767813685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118797403100895994357084913 89098052325671995767813685)
              ·
                refine ⟨8352942405531749603232533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89098052325671995767813685 8352942405531749603232533)
                ·
                  refine ⟨391544175259300762651525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8352942405531749603232533 391544175259300762651525)
                  ·
                    rfl

theorem cell22_3431383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 6].length) (baseStart_3431383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431383 prefixEnd_3431383 := by exact prefixLift 3431383
  have htrace : WordTrace (prefixWord ++ tailWord_3431383) baseStart_3431383 baseEnd_3431383 := by
    simpa [prefixWord, tailWord_3431383, baseEnd_3431383] using wordTrace_append hprefix tailTrace_3431383
  have hstable : (prefixWord ++ tailWord_3431383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431383).length < 2 ^ (prefixWord ++ tailWord_3431383).sum := by decide
  have hdescent : baseEnd_3431383 < baseStart_3431383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431389 : List Nat := [1, 4, 3, 1, 2, 3, 2, 1, 5]
def baseStart_3431389 : Nat := 118140960795 + 3431389 * 2 ^ 59
def prefixEnd_3431389 : Nat := 4983230072969 + 3 ^ 40 * 3431389 * 2
def baseEnd_3431389 : Nat := 391544859900173424101519

theorem tailTrace_3431389 : CollatzResearch.WordTrace tailWord_3431389 prefixEnd_3431389 391544859900173424101519 := by
  unfold tailWord_3431389
  simp only [CollatzResearch.WordTrace]
  refine ⟨125153038565671162429713221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83435359043780774953142147 125153038565671162429713221)
  ·
    refine ⟨23466194731063342955571229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125153038565671162429713221 23466194731063342955571229)
    ·
      refine ⟨8799823024148753608339211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23466194731063342955571229 8799823024148753608339211)
      ·
        refine ⟨13199734536223130412508817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8799823024148753608339211 13199734536223130412508817)
        ·
          refine ⟨9899800902167347809381613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13199734536223130412508817 9899800902167347809381613)
          ·
            refine ⟨3712425338312755428518105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9899800902167347809381613 3712425338312755428518105)
            ·
              refine ⟨2784319003734566571388579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3712425338312755428518105 2784319003734566571388579)
              ·
                refine ⟨4176478505601849857082869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2784319003734566571388579 4176478505601849857082869)
                ·
                  refine ⟨391544859900173424101519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4176478505601849857082869 391544859900173424101519)
                  ·
                    rfl

theorem cell22_3431389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_3431389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431389 prefixEnd_3431389 := by exact prefixLift 3431389
  have htrace : WordTrace (prefixWord ++ tailWord_3431389) baseStart_3431389 baseEnd_3431389 := by
    simpa [prefixWord, tailWord_3431389, baseEnd_3431389] using wordTrace_append hprefix tailTrace_3431389
  have hstable : (prefixWord ++ tailWord_3431389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431389).length < 2 ^ (prefixWord ++ tailWord_3431389).sum := by decide
  have hdescent : baseEnd_3431389 < baseStart_3431389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431402 : List Nat := [3, 1, 3, 1, 2, 2, 3, 2, 1, 4]
def baseStart_3431402 : Nat := 118140960795 + 3431402 * 2 ^ 59
def prefixEnd_3431402 : Nat := 4983230072969 + 3 ^ 40 * 3431402 * 2
def baseEnd_3431402 : Nat := 1174639029866192571729517

theorem tailTrace_3431402 : CollatzResearch.WordTrace tailWord_3431402 prefixEnd_3431402 1174639029866192571729517 := by
  unfold tailWord_3431402
  simp only [CollatzResearch.WordTrace]
  refine ⟨31288378178656016412484115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83435675143082710433290973 31288378178656016412484115)
  ·
    refine ⟨46932567267984024618726173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31288378178656016412484115 46932567267984024618726173)
    ·
      refine ⟨17599712725494009232022315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46932567267984024618726173 17599712725494009232022315)
      ·
        refine ⟨26399569088241013848033473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17599712725494009232022315 26399569088241013848033473)
        ·
          refine ⟨19799676816180760386025105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26399569088241013848033473 19799676816180760386025105)
          ·
            refine ⟨14849757612135570289518829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19799676816180760386025105 14849757612135570289518829)
            ·
              refine ⟨5568659104550838858569561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14849757612135570289518829 5568659104550838858569561)
              ·
                refine ⟨4176494328413129143927171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5568659104550838858569561 4176494328413129143927171)
                ·
                  refine ⟨6264741492619693715890757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4176494328413129143927171 6264741492619693715890757)
                  ·
                    refine ⟨1174639029866192571729517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6264741492619693715890757 1174639029866192571729517)
                    ·
                      rfl

theorem cell22_3431402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_3431402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431402 prefixEnd_3431402 := by exact prefixLift 3431402
  have htrace : WordTrace (prefixWord ++ tailWord_3431402) baseStart_3431402 baseEnd_3431402 := by
    simpa [prefixWord, tailWord_3431402, baseEnd_3431402] using wordTrace_append hprefix tailTrace_3431402
  have hstable : (prefixWord ++ tailWord_3431402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431402).length < 2 ^ (prefixWord ++ tailWord_3431402).sum := by decide
  have hdescent : baseEnd_3431402 < baseStart_3431402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431428 : List Nat := [2, 3, 2, 15]
def baseStart_3431428 : Nat := 118140960795 + 3431428 * 2 ^ 59
def prefixEnd_3431428 : Nat := 4983230072969 + 3 ^ 40 * 3431428 * 2
def baseEnd_3431428 : Nat := 1611314033192780755253

theorem tailTrace_3431428 : CollatzResearch.WordTrace tailWord_3431428 prefixEnd_3431428 1611314033192780755253 := by
  unfold tailWord_3431428
  simp only [CollatzResearch.WordTrace]
  refine ⟨62577230506264936045191469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83436307341686581393588625 62577230506264936045191469)
  ·
    refine ⟨23466461439849351016946801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62577230506264936045191469 23466461439849351016946801)
    ·
      refine ⟨17599846079887013262710101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23466461439849351016946801 17599846079887013262710101)
      ·
        refine ⟨1611314033192780755253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 17599846079887013262710101 1611314033192780755253)
        ·
          rfl

theorem cell22_3431428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 15].length) (baseStart_3431428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431428 prefixEnd_3431428 := by exact prefixLift 3431428
  have htrace : WordTrace (prefixWord ++ tailWord_3431428) baseStart_3431428 baseEnd_3431428 := by
    simpa [prefixWord, tailWord_3431428, baseEnd_3431428] using wordTrace_append hprefix tailTrace_3431428
  have hstable : (prefixWord ++ tailWord_3431428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431428).length < 2 ^ (prefixWord ++ tailWord_3431428).sum := by decide
  have hdescent : baseEnd_3431428 < baseStart_3431428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431432 : List Nat := [2, 1, 3, 2, 1, 3, 1, 4, 2, 3]
def baseStart_3431432 : Nat := 118140960795 + 3431432 * 2 ^ 59
def prefixEnd_3431432 : Nat := 4983230072969 + 3 ^ 40 * 3431432 * 2
def baseEnd_3431432 : Nat := 1174649299479282493479425

theorem tailTrace_3431432 : CollatzResearch.WordTrace tailWord_3431432 prefixEnd_3431432 1174649299479282493479425 := by
  unfold tailWord_3431432
  simp only [CollatzResearch.WordTrace]
  refine ⟨62577303452257690386764275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83436404603010253849019033 62577303452257690386764275)
  ·
    refine ⟨93865955178386535580146413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62577303452257690386764275 93865955178386535580146413)
    ·
      refine ⟨35199733191894950842554905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93865955178386535580146413 35199733191894950842554905)
      ·
        refine ⟨26399799893921213131916179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35199733191894950842554905 26399799893921213131916179)
        ·
          refine ⟨39599699840881819697874269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26399799893921213131916179 39599699840881819697874269)
          ·
            refine ⟨14849887440330682386702851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39599699840881819697874269 14849887440330682386702851)
            ·
              refine ⟨22274831160496023580054277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14849887440330682386702851 22274831160496023580054277)
              ·
                refine ⟨4176530842593004421260177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22274831160496023580054277 4176530842593004421260177)
                ·
                  refine ⟨3132398131944753315945133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4176530842593004421260177 3132398131944753315945133)
                  ·
                    refine ⟨1174649299479282493479425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3132398131944753315945133 1174649299479282493479425)
                    ·
                      rfl

theorem cell22_3431432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_3431432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431432 prefixEnd_3431432 := by exact prefixLift 3431432
  have htrace : WordTrace (prefixWord ++ tailWord_3431432) baseStart_3431432 baseEnd_3431432 := by
    simpa [prefixWord, tailWord_3431432, baseEnd_3431432] using wordTrace_append hprefix tailTrace_3431432
  have hstable : (prefixWord ++ tailWord_3431432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431432).length < 2 ^ (prefixWord ++ tailWord_3431432).sum := by decide
  have hdescent : baseEnd_3431432 < baseStart_3431432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431434 : List Nat := [3, 1, 2, 2, 3, 1, 4, 2, 4]
def baseStart_3431434 : Nat := 118140960795 + 3431434 * 2 ^ 59
def prefixEnd_3431434 : Nat := 4983230072969 + 3 ^ 40 * 3431434 * 2
def baseEnd_3431434 : Nat := 391549994706718384976473

theorem tailTrace_3431434 : CollatzResearch.WordTrace tailWord_3431434 prefixEnd_3431434 391549994706718384976473 := by
  unfold tailWord_3431434
  simp only [CollatzResearch.WordTrace]
  refine ⟨31288669962627033778775339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83436453233672090076734237 31288669962627033778775339)
  ·
    refine ⟨46933004943940550668163009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31288669962627033778775339 46933004943940550668163009)
    ·
      refine ⟨35199753707955413001122257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46933004943940550668163009 35199753707955413001122257)
      ·
        refine ⟨26399815280966559750841693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35199753707955413001122257 26399815280966559750841693)
        ·
          refine ⟨9899930730362459906565635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26399815280966559750841693 9899930730362459906565635)
          ·
            refine ⟨14849896095543689859848453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9899930730362459906565635 14849896095543689859848453)
            ·
              refine ⟨2784355517914441848721585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14849896095543689859848453 2784355517914441848721585)
              ·
                refine ⟨2088266638435831386541189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2784355517914441848721585 2088266638435831386541189)
                ·
                  refine ⟨391549994706718384976473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2088266638435831386541189 391549994706718384976473)
                  ·
                    rfl

theorem cell22_3431434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 4].length) (baseStart_3431434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431434 prefixEnd_3431434 := by exact prefixLift 3431434
  have htrace : WordTrace (prefixWord ++ tailWord_3431434) baseStart_3431434 baseEnd_3431434 := by
    simpa [prefixWord, tailWord_3431434, baseEnd_3431434] using wordTrace_append hprefix tailTrace_3431434
  have hstable : (prefixWord ++ tailWord_3431434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431434).length < 2 ^ (prefixWord ++ tailWord_3431434).sum := by decide
  have hdescent : baseEnd_3431434 < baseStart_3431434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431443 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 2, 7]
def baseStart_3431443 : Nat := 118140960795 + 3431443 * 2 ^ 59
def prefixEnd_3431443 : Nat := 4983230072969 + 3 ^ 40 * 3431443 * 2
def baseEnd_3431443 : Nat := 1174653065004082131454391

theorem tailTrace_3431443 : CollatzResearch.WordTrace tailWord_3431443 prefixEnd_3431443 1174653065004082131454391 := by
  unfold tailWord_3431443
  simp only [CollatzResearch.WordTrace]
  refine ⟨125155008107475529652178983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83436672071650353101452655 125155008107475529652178983)
  ·
    refine ⟨187732512161213294478268475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125155008107475529652178983 187732512161213294478268475)
    ·
      refine ⟨281598768241819941717402713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187732512161213294478268475 281598768241819941717402713)
      ·
        refine ⟨211199076181364956288052035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281598768241819941717402713 211199076181364956288052035)
        ·
          refine ⟨316798614272047434432078053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211199076181364956288052035 316798614272047434432078053)
          ·
            refine ⟨59399740176008893956014635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 316798614272047434432078053 59399740176008893956014635)
            ·
              refine ⟨89099610264013340934021953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59399740176008893956014635 89099610264013340934021953)
              ·
                refine ⟨66824707698010005700516465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89099610264013340934021953 66824707698010005700516465)
                ·
                  refine ⟨50118530773507504275387349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66824707698010005700516465 50118530773507504275387349)
                  ·
                    refine ⟨1174653065004082131454391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50118530773507504275387349 1174653065004082131454391)
                    ·
                      rfl

theorem cell22_3431443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 7].length) (baseStart_3431443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431443 prefixEnd_3431443 := by exact prefixLift 3431443
  have htrace : WordTrace (prefixWord ++ tailWord_3431443) baseStart_3431443 baseEnd_3431443 := by
    simpa [prefixWord, tailWord_3431443, baseEnd_3431443] using wordTrace_append hprefix tailTrace_3431443
  have hstable : (prefixWord ++ tailWord_3431443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431443).length < 2 ^ (prefixWord ++ tailWord_3431443).sum := by decide
  have hdescent : baseEnd_3431443 < baseStart_3431443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431445 : List Nat := [1, 3, 2, 1, 4, 1, 3, 7]
def baseStart_3431445 : Nat := 118140960795 + 3431445 * 2 ^ 59
def prefixEnd_3431445 : Nat := 4983230072969 + 3 ^ 40 * 3431445 * 2
def baseEnd_3431445 : Nat := 130517083293883865878265

theorem tailTrace_3431445 : CollatzResearch.WordTrace tailWord_3431445 prefixEnd_3431445 130517083293883865878265 := by
  unfold tailWord_3431445
  simp only [CollatzResearch.WordTrace]
  refine ⟨125155081053468283993751789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83436720702312189329167859 125155081053468283993751789)
  ·
    refine ⟨46933155395050606497656921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125155081053468283993751789 46933155395050606497656921)
    ·
      refine ⟨35199866546287954873242691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46933155395050606497656921 35199866546287954873242691)
      ·
        refine ⟨52799799819431932309864037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35199866546287954873242691 52799799819431932309864037)
        ·
          refine ⟨9899962466143487308099507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52799799819431932309864037 9899962466143487308099507)
          ·
            refine ⟨14849943699215230962149261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9899962466143487308099507 14849943699215230962149261)
            ·
              refine ⟨5568728887205711610805973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14849943699215230962149261 5568728887205711610805973)
              ·
                refine ⟨130517083293883865878265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5568728887205711610805973 130517083293883865878265)
                ·
                  rfl

theorem cell22_3431445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 7].length) (baseStart_3431445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431445 prefixEnd_3431445 := by exact prefixLift 3431445
  have htrace : WordTrace (prefixWord ++ tailWord_3431445) baseStart_3431445 baseEnd_3431445 := by
    simpa [prefixWord, tailWord_3431445, baseEnd_3431445] using wordTrace_append hprefix tailTrace_3431445
  have hstable : (prefixWord ++ tailWord_3431445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431445).length < 2 ^ (prefixWord ++ tailWord_3431445).sum := by decide
  have hdescent : baseEnd_3431445 < baseStart_3431445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431505 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 2, 5]
def baseStart_3431505 : Nat := 118140960795 + 3431505 * 2 ^ 59
def prefixEnd_3431505 : Nat := 4983230072969 + 3 ^ 40 * 3431505 * 2
def baseEnd_3431505 : Nat := 1174674288871134636404201

theorem tailTrace_3431505 : CollatzResearch.WordTrace tailWord_3431505 prefixEnd_3431505 1174674288871134636404201 := by
  unfold tailWord_3431505
  simp only [CollatzResearch.WordTrace]
  refine ⟨125157269433250914240935969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83438179622167276160623979 125157269433250914240935969)
  ·
    refine ⟨93867952074938185680701977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125157269433250914240935969 93867952074938185680701977)
    ·
      refine ⟨70400964056203639260526483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93867952074938185680701977 70400964056203639260526483)
      ·
        refine ⟨105601446084305458890789725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70400964056203639260526483 105601446084305458890789725)
        ·
          refine ⟨39600542281614547084046147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105601446084305458890789725 39600542281614547084046147)
          ·
            refine ⟨59400813422421820626069221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39600542281614547084046147 59400813422421820626069221)
            ·
              refine ⟨11137652516704091367387979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59400813422421820626069221 11137652516704091367387979)
              ·
                refine ⟨16706478775056137051081969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11137652516704091367387979 16706478775056137051081969)
                ·
                  refine ⟨12529859081292102788311477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16706478775056137051081969 12529859081292102788311477)
                  ·
                    refine ⟨1174674288871134636404201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12529859081292102788311477 1174674288871134636404201)
                    ·
                      rfl

theorem cell22_3431505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_3431505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431505 prefixEnd_3431505 := by exact prefixLift 3431505
  have htrace : WordTrace (prefixWord ++ tailWord_3431505) baseStart_3431505 baseEnd_3431505 := by
    simpa [prefixWord, tailWord_3431505, baseEnd_3431505] using wordTrace_append hprefix tailTrace_3431505
  have hstable : (prefixWord ++ tailWord_3431505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431505).length < 2 ^ (prefixWord ++ tailWord_3431505).sum := by decide
  have hdescent : baseEnd_3431505 < baseStart_3431505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431552 : List Nat := [2, 1, 1, 2, 1, 3, 2, 6, 4]
def baseStart_3431552 : Nat := 118140960795 + 3431552 * 2 ^ 59
def prefixEnd_3431552 : Nat := 4983230072969 + 3 ^ 40 * 3431552 * 2
def baseEnd_3431552 : Nat := 391563459310547393493019

theorem tailTrace_3431552 : CollatzResearch.WordTrace tailWord_3431552 prefixEnd_3431552 391563459310547393493019 := by
  unfold tailWord_3431552
  simp only [CollatzResearch.WordTrace]
  refine ⟨62579491832040320633948455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83439322442720427511931273 62579491832040320633948455)
  ·
    refine ⟨93869237748060480950922683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62579491832040320633948455 93869237748060480950922683)
    ·
      refine ⟨140803856622090721426384025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93869237748060480950922683 140803856622090721426384025)
      ·
        refine ⟨105602892466568041069788019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140803856622090721426384025 105602892466568041069788019)
        ·
          refine ⟨158404338699852061604682029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105602892466568041069788019 158404338699852061604682029)
          ·
            refine ⟨59401627012444523101755761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158404338699852061604682029 59401627012444523101755761)
            ·
              refine ⟨44551220259333392326316821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59401627012444523101755761 44551220259333392326316821)
              ·
                refine ⟨2088338449656252765296101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44551220259333392326316821 2088338449656252765296101)
                ·
                  refine ⟨391563459310547393493019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2088338449656252765296101 391563459310547393493019)
                  ·
                    rfl

theorem cell22_3431552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 4].length) (baseStart_3431552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431552 prefixEnd_3431552 := by exact prefixLift 3431552
  have htrace : WordTrace (prefixWord ++ tailWord_3431552) baseStart_3431552 baseEnd_3431552 := by
    simpa [prefixWord, tailWord_3431552, baseEnd_3431552] using wordTrace_append hprefix tailTrace_3431552
  have hstable : (prefixWord ++ tailWord_3431552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431552).length < 2 ^ (prefixWord ++ tailWord_3431552).sum := by decide
  have hdescent : baseEnd_3431552 < baseStart_3431552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431597 : List Nat := [1, 5, 2, 1, 3, 10]
def baseStart_3431597 : Nat := 118140960795 + 3431597 * 2 ^ 59
def prefixEnd_3431597 : Nat := 4983230072969 + 3 ^ 40 * 3431597 * 2
def baseEnd_3431597 : Nat := 14502540522855272383999

theorem tailTrace_3431597 : CollatzResearch.WordTrace tailWord_3431597 prefixEnd_3431597 14502540522855272383999 := by
  unfold tailWord_3431597
  simp only [CollatzResearch.WordTrace]
  refine ⟨125160624948917613953285045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83440416632611742635523363 125160624948917613953285045)
  ·
    refine ⟨11733808588961026308120473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125160624948917613953285045 11733808588961026308120473)
    ·
      refine ⟨8800356441720769731090355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11733808588961026308120473 8800356441720769731090355)
      ·
        refine ⟨13200534662581154596635533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8800356441720769731090355 13200534662581154596635533)
        ·
          refine ⟨4950200498467932973738325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13200534662581154596635533 4950200498467932973738325)
          ·
            refine ⟨14502540522855272383999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4950200498467932973738325 14502540522855272383999)
            ·
              rfl

theorem cell22_3431597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 10].length) (baseStart_3431597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431597 prefixEnd_3431597 := by exact prefixLift 3431597
  have htrace : WordTrace (prefixWord ++ tailWord_3431597) baseStart_3431597 baseEnd_3431597 := by
    simpa [prefixWord, tailWord_3431597, baseEnd_3431597] using wordTrace_append hprefix tailTrace_3431597
  have hstable : (prefixWord ++ tailWord_3431597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431597).length < 2 ^ (prefixWord ++ tailWord_3431597).sum := by decide
  have hdescent : baseEnd_3431597 < baseStart_3431597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431601 : List Nat := [1, 2, 2, 5, 1, 2, 2, 2, 2, 3]
def baseStart_3431601 : Nat := 118140960795 + 3431601 * 2 ^ 59
def prefixEnd_3431601 : Nat := 4983230072969 + 3 ^ 40 * 3431601 * 2
def baseEnd_3431601 : Nat := 1174707151633022386003907

theorem tailTrace_3431601 : CollatzResearch.WordTrace tailWord_3431601 prefixEnd_3431601 1174707151633022386003907 := by
  unfold tailWord_3431601
  simp only [CollatzResearch.WordTrace]
  refine ⟨125160770840903122636430657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83440513893935415090953771 125160770840903122636430657)
  ·
    refine ⟨93870578130677341977322993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125160770840903122636430657 93870578130677341977322993)
    ·
      refine ⟨70402933598008006482992245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93870578130677341977322993 70402933598008006482992245)
      ·
        refine ⟨6600275024813250607780523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70402933598008006482992245 6600275024813250607780523)
        ·
          refine ⟨9900412537219875911670785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6600275024813250607780523 9900412537219875911670785)
          ·
            refine ⟨7425309402914906933753089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9900412537219875911670785 7425309402914906933753089)
            ·
              refine ⟨5568982052186180200314817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7425309402914906933753089 5568982052186180200314817)
              ·
                refine ⟨4176736539139635150236113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5568982052186180200314817 4176736539139635150236113)
                ·
                  refine ⟨3132552404354726362677085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4176736539139635150236113 3132552404354726362677085)
                  ·
                    refine ⟨1174707151633022386003907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3132552404354726362677085 1174707151633022386003907)
                    ·
                      rfl

theorem cell22_3431601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_3431601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431601 prefixEnd_3431601 := by exact prefixLift 3431601
  have htrace : WordTrace (prefixWord ++ tailWord_3431601) baseStart_3431601 baseEnd_3431601 := by
    simpa [prefixWord, tailWord_3431601, baseEnd_3431601] using wordTrace_append hprefix tailTrace_3431601
  have hstable : (prefixWord ++ tailWord_3431601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431601).length < 2 ^ (prefixWord ++ tailWord_3431601).sum := by decide
  have hdescent : baseEnd_3431601 < baseStart_3431601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431614 : List Nat := [4, 2, 1, 1, 3, 3, 1, 7]
def baseStart_3431614 : Nat := 118140960795 + 3431614 * 2 ^ 59
def prefixEnd_3431614 : Nat := 4983230072969 + 3 ^ 40 * 3431614 * 2
def baseEnd_3431614 : Nat := 130523511310966076158763

theorem tailTrace_3431614 : CollatzResearch.WordTrace tailWord_3431614 prefixEnd_3431614 130523511310966076158763 := by
  unfold tailWord_3431614
  simp only [CollatzResearch.WordTrace]
  refine ⟨15645155623732003232081737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83440829993237350571102597 15645155623732003232081737)
  ·
    refine ⟨11733866717799002424061303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15645155623732003232081737 11733866717799002424061303)
    ·
      refine ⟨17600800076698503636091955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11733866717799002424061303 17600800076698503636091955)
      ·
        refine ⟨26401200115047755454137933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17600800076698503636091955 26401200115047755454137933)
        ·
          refine ⟨9900450043142908295301725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26401200115047755454137933 9900450043142908295301725)
          ·
            refine ⟨3712668766178590610738147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9900450043142908295301725 3712668766178590610738147)
            ·
              refine ⟨5569003149267885916107221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3712668766178590610738147 5569003149267885916107221)
              ·
                refine ⟨130523511310966076158763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5569003149267885916107221 130523511310966076158763)
                ·
                  rfl

theorem cell22_3431614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_3431614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431614 prefixEnd_3431614 := by exact prefixLift 3431614
  have htrace : WordTrace (prefixWord ++ tailWord_3431614) baseStart_3431614 baseEnd_3431614 := by
    simpa [prefixWord, tailWord_3431614, baseEnd_3431614] using wordTrace_append hprefix tailTrace_3431614
  have hstable : (prefixWord ++ tailWord_3431614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431614).length < 2 ^ (prefixWord ++ tailWord_3431614).sum := by decide
  have hdescent : baseEnd_3431614 < baseStart_3431614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431618 : List Nat := [3, 5, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_3431618 : Nat := 118140960795 + 3431618 * 2 ^ 59
def prefixEnd_3431618 : Nat := 4983230072969 + 3 ^ 40 * 3431618 * 2
def baseEnd_3431618 : Nat := 1174712971080440008328855

theorem tailTrace_3431618 : CollatzResearch.WordTrace tailWord_3431618 prefixEnd_3431618 1174712971080440008328855 := by
  unfold tailWord_3431618
  simp only [CollatzResearch.WordTrace]
  refine ⟨31290347720460383634949877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83440927254561023026533005 31290347720460383634949877)
  ·
    refine ⟨2933470098793160965776551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31290347720460383634949877 2933470098793160965776551)
    ·
      refine ⟨4400205148189741448664827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2933470098793160965776551 4400205148189741448664827)
      ·
        refine ⟨6600307722284612172997241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4400205148189741448664827 6600307722284612172997241)
        ·
          refine ⟨4950230791713459129747931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6600307722284612172997241 4950230791713459129747931)
          ·
            refine ⟨7425346187570188694621897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4950230791713459129747931 7425346187570188694621897)
            ·
              refine ⟨5569009640677641520966423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7425346187570188694621897 5569009640677641520966423)
              ·
                refine ⟨8353514461016462281449635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5569009640677641520966423 8353514461016462281449635)
                ·
                  refine ⟨12530271691524693422174453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8353514461016462281449635 12530271691524693422174453)
                  ·
                    refine ⟨1174712971080440008328855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12530271691524693422174453 1174712971080440008328855)
                    ·
                      rfl

theorem cell22_3431618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_3431618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431618 prefixEnd_3431618 := by exact prefixLift 3431618
  have htrace : WordTrace (prefixWord ++ tailWord_3431618) baseStart_3431618 baseEnd_3431618 := by
    simpa [prefixWord, tailWord_3431618, baseEnd_3431618] using wordTrace_append hprefix tailTrace_3431618
  have hstable : (prefixWord ++ tailWord_3431618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431618).length < 2 ^ (prefixWord ++ tailWord_3431618).sum := by decide
  have hdescent : baseEnd_3431618 < baseStart_3431618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431659 : List Nat := [1, 1, 1, 1, 2, 8, 1, 2, 5]
def baseStart_3431659 : Nat := 118140960795 + 3431659 * 2 ^ 59
def prefixEnd_3431659 : Nat := 4983230072969 + 3 ^ 40 * 3431659 * 2
def baseEnd_3431659 : Nat := 391575668739443189351243

theorem tailTrace_3431659 : CollatzResearch.WordTrace tailWord_3431659 prefixEnd_3431659 391575668739443189351243 := by
  unfold tailWord_3431659
  simp only [CollatzResearch.WordTrace]
  refine ⟨125162886274692998542042031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83441924183128665694694687 125162886274692998542042031)
  ·
    refine ⟨187744329412039497813063047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125162886274692998542042031 187744329412039497813063047)
    ·
      refine ⟨281616494118059246719594571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187744329412039497813063047 281616494118059246719594571)
      ·
        refine ⟨422424741177088870079391857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281616494118059246719594571 422424741177088870079391857)
        ·
          refine ⟨316818555882816652559543893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422424741177088870079391857 316818555882816652559543893)
          ·
            refine ⟨3712717451751757647182155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 316818555882816652559543893 3712717451751757647182155)
            ·
              refine ⟨5569076177627636470773233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3712717451751757647182155 5569076177627636470773233)
              ·
                refine ⟨4176807133220727353079925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5569076177627636470773233 4176807133220727353079925)
                ·
                  refine ⟨391575668739443189351243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4176807133220727353079925 391575668739443189351243)
                  ·
                    rfl

theorem cell22_3431659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 5].length) (baseStart_3431659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431659 prefixEnd_3431659 := by exact prefixLift 3431659
  have htrace : WordTrace (prefixWord ++ tailWord_3431659) baseStart_3431659 baseEnd_3431659 := by
    simpa [prefixWord, tailWord_3431659, baseEnd_3431659] using wordTrace_append hprefix tailTrace_3431659
  have hstable : (prefixWord ++ tailWord_3431659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431659).length < 2 ^ (prefixWord ++ tailWord_3431659).sum := by decide
  have hdescent : baseEnd_3431659 < baseStart_3431659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431676 : List Nat := [2, 2, 2, 1, 5, 1, 3, 1, 5]
def baseStart_3431676 : Nat := 118140960795 + 3431676 * 2 ^ 59
def prefixEnd_3431676 : Nat := 4983230072969 + 3 ^ 40 * 3431676 * 2
def baseEnd_3431676 : Nat := 391577608555249063459559

theorem tailTrace_3431676 : CollatzResearch.WordTrace tailWord_3431676 prefixEnd_3431676 391577608555249063459559 := by
  unfold tailWord_3431676
  simp only [CollatzResearch.WordTrace]
  refine ⟨62581753157815705222705441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83442337543754273630273921 62581753157815705222705441)
  ·
    refine ⟨46936314868361778917029081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62581753157815705222705441 46936314868361778917029081)
    ·
      refine ⟨35202236151271334187771811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46936314868361778917029081 35202236151271334187771811)
      ·
        refine ⟨52803354226907001281657717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35202236151271334187771811 52803354226907001281657717)
        ·
          refine ⟨4950314458772531370155411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52803354226907001281657717 4950314458772531370155411)
          ·
            refine ⟨7425471688158797055233117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4950314458772531370155411 7425471688158797055233117)
            ·
              refine ⟨2784551883059548895712419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7425471688158797055233117 2784551883059548895712419)
              ·
                refine ⟨4176827824589323343568629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2784551883059548895712419 4176827824589323343568629)
                ·
                  refine ⟨391577608555249063459559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4176827824589323343568629 391577608555249063459559)
                  ·
                    rfl

theorem cell22_3431676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 5].length) (baseStart_3431676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431676 prefixEnd_3431676 := by exact prefixLift 3431676
  have htrace : WordTrace (prefixWord ++ tailWord_3431676) baseStart_3431676 baseEnd_3431676 := by
    simpa [prefixWord, tailWord_3431676, baseEnd_3431676] using wordTrace_append hprefix tailTrace_3431676
  have hstable : (prefixWord ++ tailWord_3431676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431676).length < 2 ^ (prefixWord ++ tailWord_3431676).sum := by decide
  have hdescent : baseEnd_3431676 < baseStart_3431676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431689 : List Nat := [1, 2, 1, 1, 3, 3, 4, 2, 1, 4]
def baseStart_3431689 : Nat := 118140960795 + 3431689 * 2 ^ 59
def prefixEnd_3431689 : Nat := 4983230072969 + 3 ^ 40 * 3431689 * 2
def baseEnd_3431689 : Nat := 1174737275831419489803637

theorem tailTrace_3431689 : CollatzResearch.WordTrace tailWord_3431689 prefixEnd_3431689 1174737275831419489803637 := by
  unfold tailWord_3431689
  simp only [CollatzResearch.WordTrace]
  refine ⟨125163980464584313665634121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83442653643056209110422747 125163980464584313665634121)
  ·
    refine ⟨93872985348438235249225591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125163980464584313665634121 93872985348438235249225591)
    ·
      refine ⟨140809478022657352873838387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93872985348438235249225591 140809478022657352873838387)
      ·
        refine ⟨211214217033986029310757581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140809478022657352873838387 211214217033986029310757581)
        ·
          refine ⟨79205331387744760991534093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211214217033986029310757581 79205331387744760991534093)
          ·
            refine ⟨29701999270404285371825285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79205331387744760991534093 29701999270404285371825285)
            ·
              refine ⟨5569124863200803507217241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29701999270404285371825285 5569124863200803507217241)
              ·
                refine ⟨4176843647400602630412931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5569124863200803507217241 4176843647400602630412931)
                ·
                  refine ⟨6265265471100903945619397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4176843647400602630412931 6265265471100903945619397)
                  ·
                    refine ⟨1174737275831419489803637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6265265471100903945619397 1174737275831419489803637)
                    ·
                      rfl

theorem cell22_3431689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 4].length) (baseStart_3431689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431689 prefixEnd_3431689 := by exact prefixLift 3431689
  have htrace : WordTrace (prefixWord ++ tailWord_3431689) baseStart_3431689 baseEnd_3431689 := by
    simpa [prefixWord, tailWord_3431689, baseEnd_3431689] using wordTrace_append hprefix tailTrace_3431689
  have hstable : (prefixWord ++ tailWord_3431689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431689).length < 2 ^ (prefixWord ++ tailWord_3431689).sum := by decide
  have hdescent : baseEnd_3431689 < baseStart_3431689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431777 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 7]
def baseStart_3431777 : Nat := 118140960795 + 3431777 * 2 ^ 59
def prefixEnd_3431777 : Nat := 4983230072969 + 3 ^ 40 * 3431777 * 2
def baseEnd_3431777 : Nat := 391589133343272197867789

theorem tailTrace_3431777 : CollatzResearch.WordTrace tailWord_3431777 prefixEnd_3431777 391589133343272197867789 := by
  unfold tailWord_3431777
  simp only [CollatzResearch.WordTrace]
  refine ⟨125167190088265504694837585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83444793392177003129891723 125167190088265504694837585)
  ·
    refine ⟨93875392566199128521128189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125167190088265504694837585 93875392566199128521128189)
    ·
      refine ⟨35203272212324673195423071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93875392566199128521128189 35203272212324673195423071)
      ·
        refine ⟨52804908318487009793134607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35203272212324673195423071 52804908318487009793134607)
        ·
          refine ⟨79207362477730514689701911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52804908318487009793134607 79207362477730514689701911)
          ·
            refine ⟨118811043716595772034552867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79207362477730514689701911 118811043716595772034552867)
            ·
              refine ⟨178216565574893658051829301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118811043716595772034552867 178216565574893658051829301)
              ·
                refine ⟨16707803022646280442358997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178216565574893658051829301 16707803022646280442358997)
                ·
                  refine ⟨391589133343272197867789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16707803022646280442358997 391589133343272197867789)
                  ·
                    rfl

theorem cell22_3431777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 7].length) (baseStart_3431777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431777 prefixEnd_3431777 := by exact prefixLift 3431777
  have htrace : WordTrace (prefixWord ++ tailWord_3431777) baseStart_3431777 baseEnd_3431777 := by
    simpa [prefixWord, tailWord_3431777, baseEnd_3431777] using wordTrace_append hprefix tailTrace_3431777
  have hstable : (prefixWord ++ tailWord_3431777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431777).length < 2 ^ (prefixWord ++ tailWord_3431777).sum := by decide
  have hdescent : baseEnd_3431777 < baseStart_3431777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431794 : List Nat := [3, 2, 1, 2, 1, 2, 1, 5, 5]
def baseStart_3431794 : Nat := 118140960795 + 3431794 * 2 ^ 59
def prefixEnd_3431794 : Nat := 4983230072969 + 3 ^ 40 * 3431794 * 2
def baseEnd_3431794 : Nat := 391591073159078071976105

theorem tailTrace_3431794 : CollatzResearch.WordTrace tailWord_3431794 prefixEnd_3431794 391591073159078071976105 := by
  unfold tailWord_3431794
  simp only [CollatzResearch.WordTrace]
  refine ⟨31291952532300979149551609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83445206752802611065470957 31291952532300979149551609)
  ·
    refine ⟨23468964399225734362163707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31291952532300979149551609 23468964399225734362163707)
    ·
      refine ⟨35203446598838601543245561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23468964399225734362163707 35203446598838601543245561)
      ·
        refine ⟨26402584949128951157434171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35203446598838601543245561 26402584949128951157434171)
        ·
          refine ⟨39603877423693426736151257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26402584949128951157434171 39603877423693426736151257)
          ·
            refine ⟨29702908067770070052113443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39603877423693426736151257 29702908067770070052113443)
            ·
              refine ⟨44554362101655105078170165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29702908067770070052113443 44554362101655105078170165)
              ·
                refine ⟨4176971447030166101078453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44554362101655105078170165 4176971447030166101078453)
                ·
                  refine ⟨391591073159078071976105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4176971447030166101078453 391591073159078071976105)
                  ·
                    rfl

theorem cell22_3431794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_3431794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431794 prefixEnd_3431794 := by exact prefixLift 3431794
  have htrace : WordTrace (prefixWord ++ tailWord_3431794) baseStart_3431794 baseEnd_3431794 := by
    simpa [prefixWord, tailWord_3431794, baseEnd_3431794] using wordTrace_append hprefix tailTrace_3431794
  have hstable : (prefixWord ++ tailWord_3431794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431794).length < 2 ^ (prefixWord ++ tailWord_3431794).sum := by decide
  have hdescent : baseEnd_3431794 < baseStart_3431794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431828 : List Nat := [2, 4, 2, 1, 2, 3, 1, 2, 5]
def baseStart_3431828 : Nat := 118140960795 + 3431828 * 2 ^ 59
def prefixEnd_3431828 : Nat := 4983230072969 + 3 ^ 40 * 3431828 * 2
def baseEnd_3431828 : Nat := 391594952790689820192737

theorem tailTrace_3431828 : CollatzResearch.WordTrace tailWord_3431828 prefixEnd_3431828 391594952790689820192737 := by
  unfold tailWord_3431828
  simp only [CollatzResearch.WordTrace]
  refine ⟨62584525105540370202472069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83446033474053826936629425 62584525105540370202472069)
  ·
    refine ⟨11734598457288819412963513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62584525105540370202472069 11734598457288819412963513)
    ·
      refine ⟨8800948842966614559722635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11734598457288819412963513 8800948842966614559722635)
      ·
        refine ⟨13201423264449921839583953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8800948842966614559722635 13201423264449921839583953)
        ·
          refine ⟨9901067448337441379687965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13201423264449921839583953 9901067448337441379687965)
          ·
            refine ⟨3712900293126540517382987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9901067448337441379687965 3712900293126540517382987)
            ·
              refine ⟨5569350439689810776074481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3712900293126540517382987 5569350439689810776074481)
              ·
                refine ⟨4177012829767358082055861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5569350439689810776074481 4177012829767358082055861)
                ·
                  refine ⟨391594952790689820192737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4177012829767358082055861 391594952790689820192737)
                  ·
                    rfl

theorem cell22_3431828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_3431828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431828 prefixEnd_3431828 := by exact prefixLift 3431828
  have htrace : WordTrace (prefixWord ++ tailWord_3431828) baseStart_3431828 baseEnd_3431828 := by
    simpa [prefixWord, tailWord_3431828, baseEnd_3431828] using wordTrace_append hprefix tailTrace_3431828
  have hstable : (prefixWord ++ tailWord_3431828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431828).length < 2 ^ (prefixWord ++ tailWord_3431828).sum := by decide
  have hdescent : baseEnd_3431828 < baseStart_3431828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431839 : List Nat := [1, 1, 2, 5, 1, 2, 1, 3, 6]
def baseStart_3431839 : Nat := 118140960795 + 3431839 * 2 ^ 59
def prefixEnd_3431839 : Nat := 4983230072969 + 3 ^ 40 * 3431839 * 2
def baseEnd_3431839 : Nat := 391596207965623032851059

theorem tailTrace_3431839 : CollatzResearch.WordTrace tailWord_3431839 prefixEnd_3431839 391596207965623032851059 := by
  unfold tailWord_3431839
  simp only [CollatzResearch.WordTrace]
  refine ⟨125169451414040889283594571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83446300942693926189063047 125169451414040889283594571)
  ·
    refine ⟨187754177121061333925391857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125169451414040889283594571 187754177121061333925391857)
    ·
      refine ⟨140815632840796000444043893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187754177121061333925391857 140815632840796000444043893)
      ·
        refine ⟨13201465578824625041629115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140815632840796000444043893 13201465578824625041629115)
        ·
          refine ⟨19802198368236937562443673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13201465578824625041629115 19802198368236937562443673)
          ·
            refine ⟨14851648776177703171832755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19802198368236937562443673 14851648776177703171832755)
            ·
              refine ⟨22277473164266554757749133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14851648776177703171832755 22277473164266554757749133)
              ·
                refine ⟨8354052436599958034155925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22277473164266554757749133 8354052436599958034155925)
                ·
                  refine ⟨391596207965623032851059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8354052436599958034155925 391596207965623032851059)
                  ·
                    rfl

theorem cell22_3431839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 6].length) (baseStart_3431839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431839 prefixEnd_3431839 := by exact prefixLift 3431839
  have htrace : WordTrace (prefixWord ++ tailWord_3431839) baseStart_3431839 baseEnd_3431839 := by
    simpa [prefixWord, tailWord_3431839, baseEnd_3431839] using wordTrace_append hprefix tailTrace_3431839
  have hstable : (prefixWord ++ tailWord_3431839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431839).length < 2 ^ (prefixWord ++ tailWord_3431839).sum := by decide
  have hdescent : baseEnd_3431839 < baseStart_3431839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431869 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_3431869 : Nat := 118140960795 + 3431869 * 2 ^ 59
def prefixEnd_3431869 : Nat := 4983230072969 + 3 ^ 40 * 3431869 * 2
def baseEnd_3431869 : Nat := 1174798893509959020303085

theorem tailTrace_3431869 : CollatzResearch.WordTrace tailWord_3431869 prefixEnd_3431869 1174798893509959020303085 := by
  unfold tailWord_3431869
  simp only [CollatzResearch.WordTrace]
  refine ⟨125170545603932204407186661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83447030402621469604791107 125170545603932204407186661)
  ·
    refine ⟨23469477300737288326347499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125170545603932204407186661 23469477300737288326347499)
    ·
      refine ⟨35204215951105932489521249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23469477300737288326347499 35204215951105932489521249)
      ·
        refine ⟨26403161963329449367140937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35204215951105932489521249 26403161963329449367140937)
        ·
          refine ⟨19802371472497087025355703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26403161963329449367140937 19802371472497087025355703)
          ·
            refine ⟨29703557208745630538033555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19802371472497087025355703 29703557208745630538033555)
            ·
              refine ⟨44555335813118445807050333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29703557208745630538033555 44555335813118445807050333)
              ·
                refine ⟨16708250929919417177643875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44555335813118445807050333 16708250929919417177643875)
                ·
                  refine ⟨25062376394879125766465813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16708250929919417177643875 25062376394879125766465813)
                  ·
                    refine ⟨1174798893509959020303085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25062376394879125766465813 1174798893509959020303085)
                    ·
                      rfl

theorem cell22_3431869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_3431869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431869 prefixEnd_3431869 := by exact prefixLift 3431869
  have htrace : WordTrace (prefixWord ++ tailWord_3431869) baseStart_3431869 baseEnd_3431869 := by
    simpa [prefixWord, tailWord_3431869, baseEnd_3431869] using wordTrace_append hprefix tailTrace_3431869
  have hstable : (prefixWord ++ tailWord_3431869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431869).length < 2 ^ (prefixWord ++ tailWord_3431869).sum := by decide
  have hdescent : baseEnd_3431869 < baseStart_3431869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431884 : List Nat := [2, 2, 1, 4, 2, 1, 10]
def baseStart_3431884 : Nat := 118140960795 + 3431884 * 2 ^ 59
def prefixEnd_3431884 : Nat := 4983230072969 + 3 ^ 40 * 3431884 * 2
def baseEnd_3431884 : Nat := 43511260308018665969557

theorem tailTrace_3431884 : CollatzResearch.WordTrace tailWord_3431884 prefixEnd_3431884 43511260308018665969557 := by
  unfold tailWord_3431884
  simp only [CollatzResearch.WordTrace]
  refine ⟨62585546349438930984491353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83447395132585241312655137 62585546349438930984491353)
  ·
    refine ⟨46939159762079198238368515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62585546349438930984491353 46939159762079198238368515)
    ·
      refine ⟨70408739643118797357552773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46939159762079198238368515 70408739643118797357552773)
      ·
        refine ⟨13201638683084774504541145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70408739643118797357552773 13201638683084774504541145)
        ·
          refine ⟨9901229012313580878405859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13201638683084774504541145 9901229012313580878405859)
          ·
            refine ⟨14851843518470371317608789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9901229012313580878405859 14851843518470371317608789)
            ·
              refine ⟨43511260308018665969557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14851843518470371317608789 43511260308018665969557)
              ·
                rfl

theorem cell22_3431884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 10].length) (baseStart_3431884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431884 prefixEnd_3431884 := by exact prefixLift 3431884
  have htrace : WordTrace (prefixWord ++ tailWord_3431884) baseStart_3431884 baseEnd_3431884 := by
    simpa [prefixWord, tailWord_3431884, baseEnd_3431884] using wordTrace_append hprefix tailTrace_3431884
  have hstable : (prefixWord ++ tailWord_3431884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431884).length < 2 ^ (prefixWord ++ tailWord_3431884).sum := by decide
  have hdescent : baseEnd_3431884 < baseStart_3431884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431901 : List Nat := [1, 4, 3, 1, 1, 3, 2, 7]
def baseStart_3431901 : Nat := 118140960795 + 3431901 * 2 ^ 59
def prefixEnd_3431901 : Nat := 4983230072969 + 3 ^ 40 * 3431901 * 2
def baseEnd_3431901 : Nat := 130534427529324622611443

theorem tailTrace_3431901 : CollatzResearch.WordTrace tailWord_3431901 prefixEnd_3431901 130534427529324622611443 := by
  unfold tailWord_3431901
  simp only [CollatzResearch.WordTrace]
  refine ⟨125171712739816273872351557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83447808493210849248234371 125171712739816273872351557)
  ·
    refine ⟨23469696138715551351065917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125171712739816273872351557 23469696138715551351065917)
    ·
      refine ⟨8801136052018331756649719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23469696138715551351065917 8801136052018331756649719)
      ·
        refine ⟨13201704078027497634974579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8801136052018331756649719 13201704078027497634974579)
        ·
          refine ⟨19802556117041246452461869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13201704078027497634974579 19802556117041246452461869)
          ·
            refine ⟨7425958543890467419673201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19802556117041246452461869 7425958543890467419673201)
            ·
              refine ⟨5569468907917850564754901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7425958543890467419673201 5569468907917850564754901)
              ·
                refine ⟨130534427529324622611443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5569468907917850564754901 130534427529324622611443)
                ·
                  rfl

theorem cell22_3431901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 7].length) (baseStart_3431901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431901 prefixEnd_3431901 := by exact prefixLift 3431901
  have htrace : WordTrace (prefixWord ++ tailWord_3431901) baseStart_3431901 baseEnd_3431901 := by
    simpa [prefixWord, tailWord_3431901, baseEnd_3431901] using wordTrace_append hprefix tailTrace_3431901
  have hstable : (prefixWord ++ tailWord_3431901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431901).length < 2 ^ (prefixWord ++ tailWord_3431901).sum := by decide
  have hdescent : baseEnd_3431901 < baseStart_3431901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431905 : List Nat := [1, 2, 3, 1, 2, 5, 2, 1, 2, 3]
def baseStart_3431905 : Nat := 118140960795 + 3431905 * 2 ^ 59
def prefixEnd_3431905 : Nat := 4983230072969 + 3 ^ 40 * 3431905 * 2
def baseEnd_3431905 : Nat := 1174811217045666926402975

theorem tailTrace_3431905 : CollatzResearch.WordTrace tailWord_3431905 prefixEnd_3431905 1174811217045666926402975 := by
  unfold tailWord_3431905
  simp only [CollatzResearch.WordTrace]
  refine ⟨125171858631801782555497169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83447905754534521703664779 125171858631801782555497169)
  ·
    refine ⟨93878893973851336916622877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125171858631801782555497169 93878893973851336916622877)
    ·
      refine ⟨35204585240194251343733579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93878893973851336916622877 35204585240194251343733579)
      ·
        refine ⟨52806877860291377015600369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35204585240194251343733579 52806877860291377015600369)
        ·
          refine ⟨39605158395218532761700277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52806877860291377015600369 39605158395218532761700277)
          ·
            refine ⟨3712983599551737446409401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39605158395218532761700277 3712983599551737446409401)
            ·
              refine ⟨2784737699663803084807051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3712983599551737446409401 2784737699663803084807051)
              ·
                refine ⟨4177106549495704627210577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2784737699663803084807051 4177106549495704627210577)
                ·
                  refine ⟨3132829912121778470407933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4177106549495704627210577 3132829912121778470407933)
                  ·
                    refine ⟨1174811217045666926402975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3132829912121778470407933 1174811217045666926402975)
                    ·
                      rfl

theorem cell22_3431905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_3431905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431905 prefixEnd_3431905 := by exact prefixLift 3431905
  have htrace : WordTrace (prefixWord ++ tailWord_3431905) baseStart_3431905 baseEnd_3431905 := by
    simpa [prefixWord, tailWord_3431905, baseEnd_3431905] using wordTrace_append hprefix tailTrace_3431905
  have hstable : (prefixWord ++ tailWord_3431905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431905).length < 2 ^ (prefixWord ++ tailWord_3431905).sum := by decide
  have hdescent : baseEnd_3431905 < baseStart_3431905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431946 : List Nat := [3, 1, 2, 2, 2, 2, 1, 4, 5]
def baseStart_3431946 : Nat := 118140960795 + 3431946 * 2 ^ 59
def prefixEnd_3431946 : Nat := 4983230072969 + 3 ^ 40 * 3431946 * 2
def baseEnd_3431946 : Nat := 391608417394518828709283

theorem tailTrace_3431946 : CollatzResearch.WordTrace tailWord_3431946 prefixEnd_3431946 391608417394518828709283 := by
  unfold tailWord_3431946
  simp only [CollatzResearch.WordTrace]
  refine ⟨31293338506163311639434923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83448902683102164371826461 31293338506163311639434923)
  ·
    refine ⟨46940007759244967459152385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31293338506163311639434923 46940007759244967459152385)
    ·
      refine ⟨35205005819433725594364289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46940007759244967459152385 35205005819433725594364289)
      ·
        refine ⟨26403754364575294195773217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35205005819433725594364289 26403754364575294195773217)
        ·
          refine ⟨19802815773431470646829913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26403754364575294195773217 19802815773431470646829913)
          ·
            refine ⟨14852111830073602985122435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19802815773431470646829913 14852111830073602985122435)
            ·
              refine ⟨22278167745110404477683653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14852111830073602985122435 22278167745110404477683653)
              ·
                refine ⟨4177156452208200839565685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22278167745110404477683653 4177156452208200839565685)
                ·
                  refine ⟨391608417394518828709283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4177156452208200839565685 391608417394518828709283)
                  ·
                    rfl

theorem cell22_3431946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_3431946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431946 prefixEnd_3431946 := by exact prefixLift 3431946
  have htrace : WordTrace (prefixWord ++ tailWord_3431946) baseStart_3431946 baseEnd_3431946 := by
    simpa [prefixWord, tailWord_3431946, baseEnd_3431946] using wordTrace_append hprefix tailTrace_3431946
  have hstable : (prefixWord ++ tailWord_3431946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431946).length < 2 ^ (prefixWord ++ tailWord_3431946).sum := by decide
  have hdescent : baseEnd_3431946 < baseStart_3431946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3431993 : List Nat := [1, 2, 1, 5, 1, 3, 1, 3, 1, 4]
def baseStart_3431993 : Nat := 118140960795 + 3431993 * 2 ^ 59
def prefixEnd_3431993 : Nat := 4983230072969 + 3 ^ 40 * 3431993 * 2
def baseEnd_3431993 : Nat := 1174841341244064030202705

theorem tailTrace_3431993 : CollatzResearch.WordTrace tailWord_3431993 prefixEnd_3431993 1174841341244064030202705 := by
  unfold tailWord_3431993
  simp only [CollatzResearch.WordTrace]
  refine ⟨125175068255482973584700633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83450045503655315723133755 125175068255482973584700633)
  ·
    refine ⟨93881301191612230188525475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125175068255482973584700633 93881301191612230188525475)
    ·
      refine ⟨140821951787418345282788213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93881301191612230188525475 140821951787418345282788213)
      ·
        refine ⟨13202057980070469870261395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140821951787418345282788213 13202057980070469870261395)
        ·
          refine ⟨19803086970105704805392093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13202057980070469870261395 19803086970105704805392093)
          ·
            refine ⟨7426157613789639302022035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19803086970105704805392093 7426157613789639302022035)
            ·
              refine ⟨11139236420684458953033053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7426157613789639302022035 11139236420684458953033053)
              ·
                refine ⟨4177213657756672107387395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11139236420684458953033053 4177213657756672107387395)
                ·
                  refine ⟨6265820486635008161081093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4177213657756672107387395 6265820486635008161081093)
                  ·
                    refine ⟨1174841341244064030202705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6265820486635008161081093 1174841341244064030202705)
                    ·
                      rfl

theorem cell22_3431993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 4].length) (baseStart_3431993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3431993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3431993 prefixEnd_3431993 := by exact prefixLift 3431993
  have htrace : WordTrace (prefixWord ++ tailWord_3431993) baseStart_3431993 baseEnd_3431993 := by
    simpa [prefixWord, tailWord_3431993, baseEnd_3431993] using wordTrace_append hprefix tailTrace_3431993
  have hstable : (prefixWord ++ tailWord_3431993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3431993).length < 2 ^ (prefixWord ++ tailWord_3431993).sum := by decide
  have hdescent : baseEnd_3431993 < baseStart_3431993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3431993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432023 : List Nat := [1, 1, 3, 2, 2, 5, 1, 1, 1, 5]
def baseStart_3432023 : Nat := 118140960795 + 3432023 * 2 ^ 59
def prefixEnd_3432023 : Nat := 4983230072969 + 3 ^ 40 * 3432023 * 2
def baseEnd_3432023 : Nat := 1174851610857153951952613

theorem tailTrace_3432023 : CollatzResearch.WordTrace tailWord_3432023 prefixEnd_3432023 1174851610857153951952613 := by
  unfold tailWord_3432023
  simp only [CollatzResearch.WordTrace]
  refine ⟨125176162445374288708292723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83450774963582859138861815 125176162445374288708292723)
  ·
    refine ⟨187764243668061433062439085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125176162445374288708292723 187764243668061433062439085)
    ·
      refine ⟨70411591375523037398414657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187764243668061433062439085 70411591375523037398414657)
      ·
        refine ⟨52808693531642278048810993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70411591375523037398414657 52808693531642278048810993)
        ·
          refine ⟨39606520148731708536608245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52808693531642278048810993 39606520148731708536608245)
          ·
            refine ⟨3713111263943597675307023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39606520148731708536608245 3713111263943597675307023)
            ·
              refine ⟨5569666895915396512960535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3713111263943597675307023 5569666895915396512960535)
              ·
                refine ⟨8354500343873094769440803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5569666895915396512960535 8354500343873094769440803)
                ·
                  refine ⟨12531750515809642154161205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8354500343873094769440803 12531750515809642154161205)
                  ·
                    refine ⟨1174851610857153951952613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12531750515809642154161205 1174851610857153951952613)
                    ·
                      rfl

theorem cell22_3432023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_3432023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432023 prefixEnd_3432023 := by exact prefixLift 3432023
  have htrace : WordTrace (prefixWord ++ tailWord_3432023) baseStart_3432023 baseEnd_3432023 := by
    simpa [prefixWord, tailWord_3432023, baseEnd_3432023] using wordTrace_append hprefix tailTrace_3432023
  have hstable : (prefixWord ++ tailWord_3432023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432023).length < 2 ^ (prefixWord ++ tailWord_3432023).sum := by decide
  have hdescent : baseEnd_3432023 < baseStart_3432023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432036 : List Nat := [2, 3, 1, 1, 2, 4, 1, 8]
def baseStart_3432036 : Nat := 118140960795 + 3432036 * 2 ^ 59
def prefixEnd_3432036 : Nat := 4983230072969 + 3 ^ 40 * 3432036 * 2
def baseEnd_3432036 : Nat := 130539562335869583486397

theorem tailTrace_3432036 : CollatzResearch.WordTrace tailWord_3432036 prefixEnd_3432036 130539562335869583486397 := by
  unfold tailWord_3432036
  simp only [CollatzResearch.WordTrace]
  refine ⟨62588318297163595964257981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83451091062884794619010641 62588318297163595964257981)
  ·
    refine ⟨23470619361436348486596743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62588318297163595964257981 23470619361436348486596743)
    ·
      refine ⟨35205929042154522729895115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23470619361436348486596743 35205929042154522729895115)
      ·
        refine ⟨52808893563231784094842673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35205929042154522729895115 52808893563231784094842673)
        ·
          refine ⟨39606670172423838071132005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52808893563231784094842673 39606670172423838071132005)
          ·
            refine ⟨7426250657329469638337251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39606670172423838071132005 7426250657329469638337251)
            ·
              refine ⟨11139375985994204457505877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7426250657329469638337251 11139375985994204457505877)
              ·
                refine ⟨130539562335869583486397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11139375985994204457505877 130539562335869583486397)
                ·
                  rfl

theorem cell22_3432036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 8].length) (baseStart_3432036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432036 prefixEnd_3432036 := by exact prefixLift 3432036
  have htrace : WordTrace (prefixWord ++ tailWord_3432036) baseStart_3432036 baseEnd_3432036 := by
    simpa [prefixWord, tailWord_3432036, baseEnd_3432036] using wordTrace_append hprefix tailTrace_3432036
  have hstable : (prefixWord ++ tailWord_3432036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432036).length < 2 ^ (prefixWord ++ tailWord_3432036).sum := by decide
  have hdescent : baseEnd_3432036 < baseStart_3432036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432053 : List Nat := [1, 3, 4, 2, 1, 3, 8]
def baseStart_3432053 : Nat := 118140960795 + 3432053 * 2 ^ 59
def prefixEnd_3432053 : Nat := 4983230072969 + 3 ^ 40 * 3432053 * 2
def baseEnd_3432053 : Nat := 43513402980379402729723

theorem tailTrace_3432053 : CollatzResearch.WordTrace tailWord_3432053 prefixEnd_3432053 43513402980379402729723 := by
  unfold tailWord_3432053
  simp only [CollatzResearch.WordTrace]
  refine ⟨125177256635265603831884813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83451504423510402554589875 125177256635265603831884813)
  ·
    refine ⟨46941471238224601436956805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125177256635265603831884813 46941471238224601436956805)
    ·
      refine ⟨8801525857167112769429401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46941471238224601436956805 8801525857167112769429401)
      ·
        refine ⟨6601144392875334577072051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8801525857167112769429401 6601144392875334577072051)
        ·
          refine ⟨9901716589313001865608077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6601144392875334577072051 9901716589313001865608077)
          ·
            refine ⟨3713143720992375699603029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9901716589313001865608077 3713143720992375699603029)
            ·
              refine ⟨43513402980379402729723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3713143720992375699603029 43513402980379402729723)
              ·
                rfl

theorem cell22_3432053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 8].length) (baseStart_3432053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432053 prefixEnd_3432053 := by exact prefixLift 3432053
  have htrace : WordTrace (prefixWord ++ tailWord_3432053) baseStart_3432053 baseEnd_3432053 := by
    simpa [prefixWord, tailWord_3432053, baseEnd_3432053] using wordTrace_append hprefix tailTrace_3432053
  have hstable : (prefixWord ++ tailWord_3432053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432053).length < 2 ^ (prefixWord ++ tailWord_3432053).sum := by decide
  have hdescent : baseEnd_3432053 < baseStart_3432053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432119 : List Nat := [1, 1, 3, 1, 5, 3, 2, 2, 1, 3]
def baseStart_3432119 : Nat := 118140960795 + 3432119 * 2 ^ 59
def prefixEnd_3432119 : Nat := 4983230072969 + 3 ^ 40 * 3432119 * 2
def baseEnd_3432119 : Nat := 1174884473619041701552319

theorem tailTrace_3432119 : CollatzResearch.WordTrace tailWord_3432119 prefixEnd_3432119 1174884473619041701552319 := by
  unfold tailWord_3432119
  simp only [CollatzResearch.WordTrace]
  refine ⟨125179663853026497103787411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83453109235350998069191607 125179663853026497103787411)
  ·
    refine ⟨187769495779539745655681117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125179663853026497103787411 187769495779539745655681117)
    ·
      refine ⟨70413560917327404620880419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187769495779539745655681117 70413560917327404620880419)
      ·
        refine ⟨105620341375991106931320629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70413560917327404620880419 105620341375991106931320629)
        ·
          refine ⟨9901907003999166274811309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105620341375991106931320629 9901907003999166274811309)
          ·
            refine ⟨3713215126499687353054241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9901907003999166274811309 3713215126499687353054241)
            ·
              refine ⟨2784911344874765514790681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3713215126499687353054241 2784911344874765514790681)
              ·
                refine ⟨2088683508656074136093011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2784911344874765514790681 2088683508656074136093011)
                ·
                  refine ⟨3133025262984111204139517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2088683508656074136093011 3133025262984111204139517)
                  ·
                    refine ⟨1174884473619041701552319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3133025262984111204139517 1174884473619041701552319)
                    ·
                      rfl

theorem cell22_3432119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 1, 3].length) (baseStart_3432119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432119 prefixEnd_3432119 := by exact prefixLift 3432119
  have htrace : WordTrace (prefixWord ++ tailWord_3432119) baseStart_3432119 baseEnd_3432119 := by
    simpa [prefixWord, tailWord_3432119, baseEnd_3432119] using wordTrace_append hprefix tailTrace_3432119
  have hstable : (prefixWord ++ tailWord_3432119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432119).length < 2 ^ (prefixWord ++ tailWord_3432119).sum := by decide
  have hdescent : baseEnd_3432119 < baseStart_3432119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432250 : List Nat := [3, 1, 1, 1, 5, 2, 1, 3, 5]
def baseStart_3432250 : Nat := 118140960795 + 3432250 * 2 ^ 59
def prefixEnd_3432250 : Nat := 4983230072969 + 3 ^ 40 * 3432250 * 2
def baseEnd_3432250 : Nat := 391643105865400342175639

theorem tailTrace_3432250 : CollatzResearch.WordTrace tailWord_3432250 prefixEnd_3432250 391643105865400342175639 := by
  unfold tailWord_3432250
  simp only [CollatzResearch.WordTrace]
  refine ⟨31296110453887976619201551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83456294543701270984537469 31296110453887976619201551)
  ·
    refine ⟨46944165680831964928802327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31296110453887976619201551 46944165680831964928802327)
    ·
      refine ⟨70416248521247947393203491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46944165680831964928802327 70416248521247947393203491)
      ·
        refine ⟨105624372781871921089805237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70416248521247947393203491 105624372781871921089805237)
        ·
          refine ⟨9902284948300492602169241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105624372781871921089805237 9902284948300492602169241)
          ·
            refine ⟨7426713711225369451626931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9902284948300492602169241 7426713711225369451626931)
            ·
              refine ⟨11140070566838054177440397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7426713711225369451626931 11140070566838054177440397)
              ·
                refine ⟨4177526462564270316540149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11140070566838054177440397 4177526462564270316540149)
                ·
                  refine ⟨391643105865400342175639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4177526462564270316540149 391643105865400342175639)
                  ·
                    rfl

theorem cell22_3432250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_3432250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432250 prefixEnd_3432250 := by exact prefixLift 3432250
  have htrace : WordTrace (prefixWord ++ tailWord_3432250) baseStart_3432250 baseEnd_3432250 := by
    simpa [prefixWord, tailWord_3432250, baseEnd_3432250] using wordTrace_append hprefix tailTrace_3432250
  have hstable : (prefixWord ++ tailWord_3432250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432250).length < 2 ^ (prefixWord ++ tailWord_3432250).sum := by decide
  have hdescent : baseEnd_3432250 < baseStart_3432250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432293 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 5, 5]
def baseStart_3432293 : Nat := 118140960795 + 3432293 * 2 ^ 59
def prefixEnd_3432293 : Nat := 4983230072969 + 3 ^ 40 * 3432293 * 2
def baseEnd_3432293 : Nat := 1174944037374963247701785

theorem tailTrace_3432293 : CollatzResearch.WordTrace tailWord_3432293 prefixEnd_3432293 1174944037374963247701785 := by
  unfold tailWord_3432293
  simp only [CollatzResearch.WordTrace]
  refine ⟨125186010154396124820621533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83457340102930749880414355 125186010154396124820621533)
  ·
    refine ⟨46944753807898546807733075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125186010154396124820621533 46944753807898546807733075)
    ·
      refine ⟨70417130711847820211599613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46944753807898546807733075 70417130711847820211599613)
      ·
        refine ⟨26406424016942932579349855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70417130711847820211599613 26406424016942932579349855)
        ·
          refine ⟨39609636025414398869024783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26406424016942932579349855 39609636025414398869024783)
          ·
            refine ⟨59414454038121598303537175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39609636025414398869024783 59414454038121598303537175)
            ·
              refine ⟨89121681057182397455305763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59414454038121598303537175 89121681057182397455305763)
              ·
                refine ⟨133682521585773596182958645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89121681057182397455305763 133682521585773596182958645)
                ·
                  refine ⟨12532736398666274642152373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133682521585773596182958645 12532736398666274642152373)
                  ·
                    refine ⟨1174944037374963247701785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12532736398666274642152373 1174944037374963247701785)
                    ·
                      rfl

theorem cell22_3432293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_3432293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432293 prefixEnd_3432293 := by exact prefixLift 3432293
  have htrace : WordTrace (prefixWord ++ tailWord_3432293) baseStart_3432293 baseEnd_3432293 := by
    simpa [prefixWord, tailWord_3432293, baseEnd_3432293] using wordTrace_append hprefix tailTrace_3432293
  have hstable : (prefixWord ++ tailWord_3432293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432293).length < 2 ^ (prefixWord ++ tailWord_3432293).sum := by decide
  have hdescent : baseEnd_3432293 < baseStart_3432293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432340 : List Nat := [2, 4, 2, 1, 1, 3, 9]
def baseStart_3432340 : Nat := 118140960795 + 3432340 * 2 ^ 59
def prefixEnd_3432340 : Nat := 4983230072969 + 3 ^ 40 * 3432340 * 2
def baseEnd_3432340 : Nat := 43517041719832251547283

theorem tailTrace_3432340 : CollatzResearch.WordTrace tailWord_3432340 prefixEnd_3432340 43517041719832251547283 := by
  unfold tailWord_3432340
  simp only [CollatzResearch.WordTrace]
  refine ⟨62593862192612925923791237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83458482923483901231721649 62593862192612925923791237)
  ·
    refine ⟨11736349161114923610710857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62593862192612925923791237 11736349161114923610710857)
    ·
      refine ⟨8802261870836192708033143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11736349161114923610710857 8802261870836192708033143)
      ·
        refine ⟨13203392806254289062049715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8802261870836192708033143 13203392806254289062049715)
        ·
          refine ⟨19805089209381433593074573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13203392806254289062049715 19805089209381433593074573)
          ·
            refine ⟨7426908453518037597402965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19805089209381433593074573 7426908453518037597402965)
            ·
              refine ⟨43517041719832251547283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7426908453518037597402965 43517041719832251547283)
              ·
                rfl

theorem cell22_3432340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 9].length) (baseStart_3432340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432340 prefixEnd_3432340 := by exact prefixLift 3432340
  have htrace : WordTrace (prefixWord ++ tailWord_3432340) baseStart_3432340 baseEnd_3432340 := by
    simpa [prefixWord, tailWord_3432340, baseEnd_3432340] using wordTrace_append hprefix tailTrace_3432340
  have hstable : (prefixWord ++ tailWord_3432340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432340).length < 2 ^ (prefixWord ++ tailWord_3432340).sum := by decide
  have hdescent : baseEnd_3432340 < baseStart_3432340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432344 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 4, 3]
def baseStart_3432344 : Nat := 118140960795 + 3432344 * 2 ^ 59
def prefixEnd_3432344 : Nat := 4983230072969 + 3 ^ 40 * 3432344 * 2
def baseEnd_3432344 : Nat := 1174961495717216114676629

theorem tailTrace_3432344 : CollatzResearch.WordTrace tailWord_3432344 prefixEnd_3432344 1174961495717216114676629 := by
  unfold tailWord_3432344
  simp only [CollatzResearch.WordTrace]
  refine ⟨62593935138605680265364043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83458580184807573687152057 62593935138605680265364043)
  ·
    refine ⟨93890902707908520398046065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62593935138605680265364043 93890902707908520398046065)
    ·
      refine ⟨70418177030931390298534549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93890902707908520398046065 70418177030931390298534549)
      ·
        refine ⟨3300852048324908920243807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70418177030931390298534549 3300852048324908920243807)
        ·
          refine ⟨4951278072487363380365711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3300852048324908920243807 4951278072487363380365711)
          ·
            refine ⟨7426917108731045070548567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4951278072487363380365711 7426917108731045070548567)
            ·
              refine ⟨11140375663096567605822851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7426917108731045070548567 11140375663096567605822851)
              ·
                refine ⟨16710563494644851408734277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11140375663096567605822851 16710563494644851408734277)
                ·
                  refine ⟨3133230655245909639137677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16710563494644851408734277 3133230655245909639137677)
                  ·
                    refine ⟨1174961495717216114676629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3133230655245909639137677 1174961495717216114676629)
                    ·
                      rfl

theorem cell22_3432344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_3432344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432344 prefixEnd_3432344 := by exact prefixLift 3432344
  have htrace : WordTrace (prefixWord ++ tailWord_3432344) baseStart_3432344 baseEnd_3432344 := by
    simpa [prefixWord, tailWord_3432344, baseEnd_3432344] using wordTrace_append hprefix tailTrace_3432344
  have hstable : (prefixWord ++ tailWord_3432344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432344).length < 2 ^ (prefixWord ++ tailWord_3432344).sum := by decide
  have hdescent : baseEnd_3432344 < baseStart_3432344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432412 : List Nat := [2, 2, 6, 1, 2, 1, 2, 1, 2, 3]
def baseStart_3432412 : Nat := 118140960795 + 3432412 * 2 ^ 59
def prefixEnd_3432412 : Nat := 4983230072969 + 3 ^ 40 * 3432412 * 2
def baseEnd_3432412 : Nat := 1174984773506886603976421

theorem tailTrace_3432412 : CollatzResearch.WordTrace tailWord_3432412 prefixEnd_3432412 1174984773506886603976421 := by
  unfold tailWord_3432412
  simp only [CollatzResearch.WordTrace]
  refine ⟨62595175220482504072101745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83460233627310005429468993 62595175220482504072101745)
  ·
    refine ⟨46946381415361878054076309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62595175220482504072101745 46946381415361878054076309)
    ·
      refine ⟨2200611628845088033784827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46946381415361878054076309 2200611628845088033784827)
      ·
        refine ⟨3300917443267632050677241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2200611628845088033784827 3300917443267632050677241)
        ·
          refine ⟨2475688082450724038007931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3300917443267632050677241 2475688082450724038007931)
          ·
            refine ⟨3713532123676086057011897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475688082450724038007931 3713532123676086057011897)
            ·
              refine ⟨2785149092757064542758923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3713532123676086057011897 2785149092757064542758923)
              ·
                refine ⟨4177723639135596814138385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2785149092757064542758923 4177723639135596814138385)
                ·
                  refine ⟨3133292729351697610603789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4177723639135596814138385 3133292729351697610603789)
                  ·
                    refine ⟨1174984773506886603976421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3133292729351697610603789 1174984773506886603976421)
                    ·
                      rfl

theorem cell22_3432412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_3432412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432412 prefixEnd_3432412 := by exact prefixLift 3432412
  have htrace : WordTrace (prefixWord ++ tailWord_3432412) baseStart_3432412 baseEnd_3432412 := by
    simpa [prefixWord, tailWord_3432412, baseEnd_3432412] using wordTrace_append hprefix tailTrace_3432412
  have hstable : (prefixWord ++ tailWord_3432412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432412).length < 2 ^ (prefixWord ++ tailWord_3432412).sum := by decide
  have hdescent : baseEnd_3432412 < baseStart_3432412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432419 : List Nat := [1, 1, 1, 6, 1, 4, 2, 1, 5]
def baseStart_3432419 : Nat := 118140960795 + 3432419 * 2 ^ 59
def prefixEnd_3432419 : Nat := 4983230072969 + 3 ^ 40 * 3432419 * 2
def baseEnd_3432419 : Nat := 391662389916646973017133

theorem tailTrace_3432419 : CollatzResearch.WordTrace tailWord_3432419 prefixEnd_3432419 391662389916646973017133 := by
  unfold tailWord_3432419
  simp only [CollatzResearch.WordTrace]
  refine ⟨125190605751939648339708311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83460403834626432226472207 125190605751939648339708311)
  ·
    refine ⟨187785908627909472509562467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125190605751939648339708311 187785908627909472509562467)
    ·
      refine ⟨281678862941864208764343701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187785908627909472509562467 281678862941864208764343701)
      ·
        refine ⟨13203696700399884785828611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 281678862941864208764343701 13203696700399884785828611)
        ·
          refine ⟨19805545050599827178742917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13203696700399884785828611 19805545050599827178742917)
          ·
            refine ⟨3713539696987467596014297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19805545050599827178742917 3713539696987467596014297)
            ·
              refine ⟨2785154772740600697010723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3713539696987467596014297 2785154772740600697010723)
              ·
                refine ⟨4177732159110901045516085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2785154772740600697010723 4177732159110901045516085)
                ·
                  refine ⟨391662389916646973017133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4177732159110901045516085 391662389916646973017133)
                  ·
                    rfl

theorem cell22_3432419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 5].length) (baseStart_3432419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432419 prefixEnd_3432419 := by exact prefixLift 3432419
  have htrace : WordTrace (prefixWord ++ tailWord_3432419) baseStart_3432419 baseEnd_3432419 := by
    simpa [prefixWord, tailWord_3432419, baseEnd_3432419] using wordTrace_append hprefix tailTrace_3432419
  have hstable : (prefixWord ++ tailWord_3432419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432419).length < 2 ^ (prefixWord ++ tailWord_3432419).sum := by decide
  have hdescent : baseEnd_3432419 < baseStart_3432419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432432 : List Nat := [2, 1, 1, 1, 3, 2, 5, 2, 1, 4]
def baseStart_3432432 : Nat := 118140960795 + 3432432 * 2 ^ 59
def prefixEnd_3432432 : Nat := 4983230072969 + 3 ^ 40 * 3432432 * 2
def baseEnd_3432432 : Nat := 1174991619915613218476359

theorem tailTrace_3432432 : CollatzResearch.WordTrace tailWord_3432432 prefixEnd_3432432 1174991619915613218476359 := by
  unfold tailWord_3432432
  simp only [CollatzResearch.WordTrace]
  refine ⟨62595539950446275779965775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83460719933928367706621033 62595539950446275779965775)
  ·
    refine ⟨93893309925669413669948663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62595539950446275779965775 93893309925669413669948663)
    ·
      refine ⟨140839964888504120504922995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93893309925669413669948663 140839964888504120504922995)
      ·
        refine ⟨211259947332756180757384493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140839964888504120504922995 211259947332756180757384493)
        ·
          refine ⟨79222480249783567784019185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211259947332756180757384493 79222480249783567784019185)
          ·
            refine ⟨59416860187337675838014389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79222480249783567784019185 59416860187337675838014389)
            ·
              refine ⟨5570330642562907109813849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59416860187337675838014389 5570330642562907109813849)
              ·
                refine ⟨4177747981922180332360387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5570330642562907109813849 4177747981922180332360387)
                ·
                  refine ⟨6266621972883270498540581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4177747981922180332360387 6266621972883270498540581)
                  ·
                    refine ⟨1174991619915613218476359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6266621972883270498540581 1174991619915613218476359)
                    ·
                      rfl

theorem cell22_3432432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 1, 4].length) (baseStart_3432432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432432 prefixEnd_3432432 := by exact prefixLift 3432432
  have htrace : WordTrace (prefixWord ++ tailWord_3432432) baseStart_3432432 baseEnd_3432432 := by
    simpa [prefixWord, tailWord_3432432, baseEnd_3432432] using wordTrace_append hprefix tailTrace_3432432
  have hstable : (prefixWord ++ tailWord_3432432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432432).length < 2 ^ (prefixWord ++ tailWord_3432432).sum := by decide
  have hdescent : baseEnd_3432432 < baseStart_3432432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432445 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_3432445 : Nat := 118140960795 + 3432445 * 2 ^ 59
def prefixEnd_3432445 : Nat := 4983230072969 + 3 ^ 40 * 3432445 * 2
def baseEnd_3432445 : Nat := 1174996070081285517901319

theorem tailTrace_3432445 : CollatzResearch.WordTrace tailWord_3432445 prefixEnd_3432445 1174996070081285517901319 := by
  unfold tailWord_3432445
  simp only [CollatzResearch.WordTrace]
  refine ⟨125191554049845454780154789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83461036033230303186769859 125191554049845454780154789)
  ·
    refine ⟨23473416384346022771279023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125191554049845454780154789 23473416384346022771279023)
    ·
      refine ⟨35210124576519034156918535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23473416384346022771279023 35210124576519034156918535)
      ·
        refine ⟨52815186864778551235377803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35210124576519034156918535 52815186864778551235377803)
        ·
          refine ⟨79222780297167826853066705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52815186864778551235377803 79222780297167826853066705)
          ·
            refine ⟨59417085222875870139800029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79222780297167826853066705 59417085222875870139800029)
            ·
              refine ⟨22281406958578451302425011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59417085222875870139800029 22281406958578451302425011)
              ·
                refine ⟨33422110437867676953637517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22281406958578451302425011 33422110437867676953637517)
                ·
                  refine ⟨12533291414200378857614069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33422110437867676953637517 12533291414200378857614069)
                  ·
                    refine ⟨1174996070081285517901319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12533291414200378857614069 1174996070081285517901319)
                    ·
                      rfl

theorem cell22_3432445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_3432445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432445 prefixEnd_3432445 := by exact prefixLift 3432445
  have htrace : WordTrace (prefixWord ++ tailWord_3432445) baseStart_3432445 baseEnd_3432445 := by
    simpa [prefixWord, tailWord_3432445, baseEnd_3432445] using wordTrace_append hprefix tailTrace_3432445
  have hstable : (prefixWord ++ tailWord_3432445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432445).length < 2 ^ (prefixWord ++ tailWord_3432445).sum := by decide
  have hdescent : baseEnd_3432445 < baseStart_3432445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432449 : List Nat := [1, 2, 4, 1, 2, 1, 5, 1, 1, 4]
def baseStart_3432449 : Nat := 118140960795 + 3432449 * 2 ^ 59
def prefixEnd_3432449 : Nat := 4983230072969 + 3 ^ 40 * 3432449 * 2
def baseEnd_3432449 : Nat := 1174997439363030840801307

theorem tailTrace_3432449 : CollatzResearch.WordTrace tailWord_3432449 prefixEnd_3432449 1174997439363030840801307 := by
  unfold tailWord_3432449
  simp only [CollatzResearch.WordTrace]
  refine ⟨125191699941830963463300401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83461133294553975642200267 125191699941830963463300401)
  ·
    refine ⟨93893774956373222597475301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125191699941830963463300401 93893774956373222597475301)
    ·
      refine ⟨17605082804319979237026619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93893774956373222597475301 17605082804319979237026619)
      ·
        refine ⟨26407624206479968855539929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17605082804319979237026619 26407624206479968855539929)
        ·
          refine ⟨19805718154859976641654947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26407624206479968855539929 19805718154859976641654947)
          ·
            refine ⟨29708577232289964962482421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19805718154859976641654947 29708577232289964962482421)
            ·
              refine ⟨2785179115527184215232727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29708577232289964962482421 2785179115527184215232727)
              ·
                refine ⟨4177768673290776322849091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2785179115527184215232727 4177768673290776322849091)
                ·
                  refine ⟨6266653009936164484273637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4177768673290776322849091 6266653009936164484273637)
                  ·
                    refine ⟨1174997439363030840801307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6266653009936164484273637 1174997439363030840801307)
                    ·
                      rfl

theorem cell22_3432449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_3432449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432449 prefixEnd_3432449 := by exact prefixLift 3432449
  have htrace : WordTrace (prefixWord ++ tailWord_3432449) baseStart_3432449 baseEnd_3432449 := by
    simpa [prefixWord, tailWord_3432449, baseEnd_3432449] using wordTrace_append hprefix tailTrace_3432449
  have hstable : (prefixWord ++ tailWord_3432449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432449).length < 2 ^ (prefixWord ++ tailWord_3432449).sum := by decide
  have hdescent : baseEnd_3432449 < baseStart_3432449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432494 : List Nat := [4, 1, 3, 1, 1, 2, 3, 1, 2, 4]
def baseStart_3432494 : Nat := 118140960795 + 3432494 * 2 ^ 59
def prefixEnd_3432494 : Nat := 4983230072969 + 3 ^ 40 * 3432494 * 2
def baseEnd_3432494 : Nat := 1175012843782665723426169

theorem tailTrace_3432494 : CollatzResearch.WordTrace tailWord_3432494 prefixEnd_3432494 1175012843782665723426169 := by
  unfold tailWord_3432494
  simp only [CollatzResearch.WordTrace]
  refine ⟨15649167653333492018586067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83462227484445290765792357 15649167653333492018586067)
  ·
    refine ⟨23473751480000238027879101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15649167653333492018586067 23473751480000238027879101)
    ·
      refine ⟨8802656805000089260454663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23473751480000238027879101 8802656805000089260454663)
      ·
        refine ⟨13203985207500133890681995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8802656805000089260454663 13203985207500133890681995)
        ·
          refine ⟨19805977811250200836022993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13203985207500133890681995 19805977811250200836022993)
          ·
            refine ⟨14854483358437650627017245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19805977811250200836022993 14854483358437650627017245)
            ·
              refine ⟨5570431259414118985131467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14854483358437650627017245 5570431259414118985131467)
              ·
                refine ⟨8355646889121178477697201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5570431259414118985131467 8355646889121178477697201)
                ·
                  refine ⟨6266735166840883858272901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8355646889121178477697201 6266735166840883858272901)
                  ·
                    refine ⟨1175012843782665723426169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6266735166840883858272901 1175012843782665723426169)
                    ·
                      rfl

theorem cell22_3432494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_3432494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432494 prefixEnd_3432494 := by exact prefixLift 3432494
  have htrace : WordTrace (prefixWord ++ tailWord_3432494) baseStart_3432494 baseEnd_3432494 := by
    simpa [prefixWord, tailWord_3432494, baseEnd_3432494] using wordTrace_append hprefix tailTrace_3432494
  have hstable : (prefixWord ++ tailWord_3432494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432494).length < 2 ^ (prefixWord ++ tailWord_3432494).sum := by decide
  have hdescent : baseEnd_3432494 < baseStart_3432494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
