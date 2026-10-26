import V185TrunkScan22Chunk375

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3351912 : List Nat := [2, 1, 4, 2, 3, 2, 1, 1, 2, 4]
def baseStart_3351912 : Nat := 118140960795 + 3351912 * 2 ^ 59
def prefixEnd_3351912 : Nat := 4983230072969 + 3 ^ 40 * 3351912 * 2
def baseEnd_3351912 : Nat := 1147427978382263241723229

theorem tailTrace_3351912 : CollatzResearch.WordTrace tailWord_3351912 prefixEnd_3351912 1147427978382263241723229 := by
  unfold tailWord_3351912
  simp only [CollatzResearch.WordTrace]
  refine ⟨61127137116301379919380995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81502849488401839892507993 61127137116301379919380995)
  ·
    refine ⟨91690705674452069879071493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61127137116301379919380995 91690705674452069879071493)
    ·
      refine ⟨17192007313959763102325905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91690705674452069879071493 17192007313959763102325905)
      ·
        refine ⟨12894005485469822326744429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17192007313959763102325905 12894005485469822326744429)
        ·
          refine ⟨4835252057051183372529161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12894005485469822326744429 4835252057051183372529161)
          ·
            refine ⟨3626439042788387529396871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4835252057051183372529161 3626439042788387529396871)
            ·
              refine ⟨5439658564182581294095307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3626439042788387529396871 5439658564182581294095307)
              ·
                refine ⟨8159487846273871941142961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5439658564182581294095307 8159487846273871941142961)
                ·
                  refine ⟨6119615884705403955857221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8159487846273871941142961 6119615884705403955857221)
                  ·
                    refine ⟨1147427978382263241723229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6119615884705403955857221 1147427978382263241723229)
                    ·
                      rfl

theorem cell22_3351912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_3351912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351912 prefixEnd_3351912 := by exact prefixLift 3351912
  have htrace : WordTrace (prefixWord ++ tailWord_3351912) baseStart_3351912 baseEnd_3351912 := by
    simpa [prefixWord, tailWord_3351912, baseEnd_3351912] using wordTrace_append hprefix tailTrace_3351912
  have hstable : (prefixWord ++ tailWord_3351912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351912).length < 2 ^ (prefixWord ++ tailWord_3351912).sum := by decide
  have hdescent : baseEnd_3351912 < baseStart_3351912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351985 : List Nat := [1, 2, 2, 4, 1, 1, 1, 5, 1, 4]
def baseStart_3351985 : Nat := 118140960795 + 3351985 * 2 ^ 59
def prefixEnd_3351985 : Nat := 4983230072969 + 3 ^ 40 * 3351985 * 2
def baseEnd_3351985 : Nat := 1147452967774115384648005

theorem tailTrace_3351985 : CollatzResearch.WordTrace tailWord_3351985 prefixEnd_3351985 1147452967774115384648005 := by
  unfold tailWord_3351985
  simp only [CollatzResearch.WordTrace]
  refine ⟨122256936761338293306169409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81504624507558862204112939 122256936761338293306169409)
  ·
    refine ⟨91692702571003719979627057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122256936761338293306169409 91692702571003719979627057)
    ·
      refine ⟨68769526928252789984720293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91692702571003719979627057 68769526928252789984720293)
      ·
        refine ⟨12894286299047398122135055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68769526928252789984720293 12894286299047398122135055)
        ·
          refine ⟨19341429448571097183202583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12894286299047398122135055 19341429448571097183202583)
          ·
            refine ⟨29012144172856645774803875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19341429448571097183202583 29012144172856645774803875)
            ·
              refine ⟨43518216259284968662205813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29012144172856645774803875 43518216259284968662205813)
              ·
                refine ⟨4079832774307965812081795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43518216259284968662205813 4079832774307965812081795)
                ·
                  refine ⟨6119749161461948718122693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4079832774307965812081795 6119749161461948718122693)
                  ·
                    refine ⟨1147452967774115384648005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6119749161461948718122693 1147452967774115384648005)
                    ·
                      rfl

theorem cell22_3351985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_3351985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351985 prefixEnd_3351985 := by exact prefixLift 3351985
  have htrace : WordTrace (prefixWord ++ tailWord_3351985) baseStart_3351985 baseEnd_3351985 := by
    simpa [prefixWord, tailWord_3351985, baseEnd_3351985] using wordTrace_append hprefix tailTrace_3351985
  have hstable : (prefixWord ++ tailWord_3351985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351985).length < 2 ^ (prefixWord ++ tailWord_3351985).sum := by decide
  have hdescent : baseEnd_3351985 < baseStart_3351985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352000 : List Nat := [2, 1, 1, 2, 3, 1, 2, 6, 4]
def baseStart_3352000 : Nat := 118140960795 + 3352000 * 2 ^ 59
def prefixEnd_3352000 : Nat := 4983230072969 + 3 ^ 40 * 3352000 * 2
def baseEnd_3352000 : Nat := 382486034193553448507653

theorem tailTrace_3352000 : CollatzResearch.WordTrace tailWord_3352000 prefixEnd_3352000 382486034193553448507653 := by
  unfold tailWord_3352000
  simp only [CollatzResearch.WordTrace]
  refine ⟨61128741928141975433982727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81504989237522633911976969 61128741928141975433982727)
  ·
    refine ⟨91693112892212963150974091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61128741928141975433982727 91693112892212963150974091)
    ·
      refine ⟨137539669338319444726461137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91693112892212963150974091 137539669338319444726461137)
      ·
        refine ⟨103154752003739583544845853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137539669338319444726461137 103154752003739583544845853)
        ·
          refine ⟨38683032001402343829317195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103154752003739583544845853 38683032001402343829317195)
          ·
            refine ⟨58024548002103515743975793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38683032001402343829317195 58024548002103515743975793)
            ·
              refine ⟨43518411001577636807981845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58024548002103515743975793 43518411001577636807981845)
              ·
                refine ⟨2039925515698951725374149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43518411001577636807981845 2039925515698951725374149)
                ·
                  refine ⟨382486034193553448507653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2039925515698951725374149 382486034193553448507653)
                  ·
                    rfl

theorem cell22_3352000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 4].length) (baseStart_3352000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352000 prefixEnd_3352000 := by exact prefixLift 3352000
  have htrace : WordTrace (prefixWord ++ tailWord_3352000) baseStart_3352000 baseEnd_3352000 := by
    simpa [prefixWord, tailWord_3352000, baseEnd_3352000] using wordTrace_append hprefix tailTrace_3352000
  have hstable : (prefixWord ++ tailWord_3352000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352000).length < 2 ^ (prefixWord ++ tailWord_3352000).sum := by decide
  have hdescent : baseEnd_3352000 < baseStart_3352000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352045 : List Nat := [1, 5, 1, 3, 2, 10]
def baseStart_3352045 : Nat := 118140960795 + 3352045 * 2 ^ 59
def prefixEnd_3352045 : Nat := 4983230072969 + 3 ^ 40 * 3352045 * 2
def baseEnd_3352045 : Nat := 14166339592596237384541

theorem tailTrace_3352045 : CollatzResearch.WordTrace tailWord_3352045 prefixEnd_3352045 14166339592596237384541 := by
  unfold tailWord_3352045
  simp only [CollatzResearch.WordTrace]
  refine ⟨122259125141120923553353589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81506083427413949035569059 122259125141120923553353589)
  ·
    refine ⟨11461792981980086583126899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122259125141120923553353589 11461792981980086583126899)
    ·
      refine ⟨17192689472970129874690349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11461792981980086583126899 17192689472970129874690349)
      ·
        refine ⟨6447258552363798703008881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17192689472970129874690349 6447258552363798703008881)
        ·
          refine ⟨4835443914272849027256661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6447258552363798703008881 4835443914272849027256661)
          ·
            refine ⟨14166339592596237384541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4835443914272849027256661 14166339592596237384541)
            ·
              rfl

theorem cell22_3352045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 10].length) (baseStart_3352045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352045 prefixEnd_3352045 := by exact prefixLift 3352045
  have htrace : WordTrace (prefixWord ++ tailWord_3352045) baseStart_3352045 baseEnd_3352045 := by
    simpa [prefixWord, tailWord_3352045, baseEnd_3352045] using wordTrace_append hprefix tailTrace_3352045
  have hstable : (prefixWord ++ tailWord_3352045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352045).length < 2 ^ (prefixWord ++ tailWord_3352045).sum := by decide
  have hdescent : baseEnd_3352045 < baseStart_3352045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352058 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 1, 8]
def baseStart_3352058 : Nat := 118140960795 + 3352058 * 2 ^ 59
def prefixEnd_3352058 : Nat := 4983230072969 + 3 ^ 40 * 3352058 * 2
def baseEnd_3352058 : Nat := 1147477957165967527572781

theorem tailTrace_3352058 : CollatzResearch.WordTrace tailWord_3352058 prefixEnd_3352058 1147477957165967527572781 := by
  unfold tailWord_3352058
  simp only [CollatzResearch.WordTrace]
  refine ⟨30564899822518456693394207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81506399526715884515717885 30564899822518456693394207)
  ·
    refine ⟨45847349733777685040091311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30564899822518456693394207 45847349733777685040091311)
    ·
      refine ⟨68771024600666527560136967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45847349733777685040091311 68771024600666527560136967)
      ·
        refine ⟨103156536900999791340205451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68771024600666527560136967 103156536900999791340205451)
        ·
          refine ⟨154734805351499687010308177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103156536900999791340205451 154734805351499687010308177)
          ·
            refine ⟨116051104013624765257731133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154734805351499687010308177 116051104013624765257731133)
            ·
              refine ⟨43519164005109286971649175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116051104013624765257731133 43519164005109286971649175)
              ·
                refine ⟨65278746007663930457473763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43519164005109286971649175 65278746007663930457473763)
                ·
                  refine ⟨97918119011495895686210645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65278746007663930457473763 97918119011495895686210645)
                  ·
                    refine ⟨1147477957165967527572781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97918119011495895686210645 1147477957165967527572781)
                    ·
                      rfl

theorem cell22_3352058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_3352058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352058 prefixEnd_3352058 := by exact prefixLift 3352058
  have htrace : WordTrace (prefixWord ++ tailWord_3352058) baseStart_3352058 baseEnd_3352058 := by
    simpa [prefixWord, tailWord_3352058, baseEnd_3352058] using wordTrace_append hprefix tailTrace_3352058
  have hstable : (prefixWord ++ tailWord_3352058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352058).length < 2 ^ (prefixWord ++ tailWord_3352058).sum := by decide
  have hdescent : baseEnd_3352058 < baseStart_3352058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352124 : List Nat := [2, 2, 2, 2, 4, 1, 3, 1, 5]
def baseStart_3352124 : Nat := 118140960795 + 3352124 * 2 ^ 59
def prefixEnd_3352124 : Nat := 4983230072969 + 3 ^ 40 * 3352124 * 2
def baseEnd_3352124 : Nat := 382500183438255118474193

theorem tailTrace_3352124 : CollatzResearch.WordTrace tailWord_3352124 prefixEnd_3352124 382500183438255118474193 := by
  unfold tailWord_3352124
  simp only [CollatzResearch.WordTrace]
  refine ⟨61131003253917360022739713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81508004338556480030319617 61131003253917360022739713)
  ·
    refine ⟨45848252440438020017054785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61131003253917360022739713 45848252440438020017054785)
    ·
      refine ⟨34386189330328515012791089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45848252440438020017054785 34386189330328515012791089)
      ·
        refine ⟨25789641997746386259593317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34386189330328515012791089 25789641997746386259593317)
        ·
          refine ⟨4835557874577447423673747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25789641997746386259593317 4835557874577447423673747)
          ·
            refine ⟨7253336811866171135510621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4835557874577447423673747 7253336811866171135510621)
            ·
              refine ⟨2720001304449814175816483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7253336811866171135510621 2720001304449814175816483)
              ·
                refine ⟨4080001956674721263724725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2720001304449814175816483 4080001956674721263724725)
                ·
                  refine ⟨382500183438255118474193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4080001956674721263724725 382500183438255118474193)
                  ·
                    rfl

theorem cell22_3352124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 5].length) (baseStart_3352124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352124 prefixEnd_3352124 := by exact prefixLift 3352124
  have htrace : WordTrace (prefixWord ++ tailWord_3352124) baseStart_3352124 baseEnd_3352124 := by
    simpa [prefixWord, tailWord_3352124, baseEnd_3352124] using wordTrace_append hprefix tailTrace_3352124
  have hstable : (prefixWord ++ tailWord_3352124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352124).length < 2 ^ (prefixWord ++ tailWord_3352124).sum := by decide
  have hdescent : baseEnd_3352124 < baseStart_3352124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352167 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 4, 3]
def baseStart_3352167 : Nat := 118140960795 + 3352167 * 2 ^ 59
def prefixEnd_3352167 : Nat := 4983230072969 + 3 ^ 40 * 3352167 * 2
def baseEnd_3352167 : Nat := 1147515270093527576597447

theorem tailTrace_3352167 : CollatzResearch.WordTrace tailWord_3352167 prefixEnd_3352167 1147515270093527576597447 := by
  unfold tailWord_3352167
  simp only [CollatzResearch.WordTrace]
  refine ⟨122263574846678938389294755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81509049897785958926196503 122263574846678938389294755)
  ·
    refine ⟨183395362270018407583942133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122263574846678938389294755 183395362270018407583942133)
    ·
      refine ⟨17193315212814225710994575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183395362270018407583942133 17193315212814225710994575)
      ·
        refine ⟨25789972819221338566491863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17193315212814225710994575 25789972819221338566491863)
        ·
          refine ⟨38684959228832007849737795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25789972819221338566491863 38684959228832007849737795)
          ·
            refine ⟨58027438843248011774606693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38684959228832007849737795 58027438843248011774606693)
            ·
              refine ⟨10880144783109002207738755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58027438843248011774606693 10880144783109002207738755)
              ·
                refine ⟨16320217174663503311608133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10880144783109002207738755 16320217174663503311608133)
                ·
                  refine ⟨3060040720249406870926525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16320217174663503311608133 3060040720249406870926525)
                  ·
                    refine ⟨1147515270093527576597447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3060040720249406870926525 1147515270093527576597447)
                    ·
                      rfl

theorem cell22_3352167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_3352167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352167 prefixEnd_3352167 := by exact prefixLift 3352167
  have htrace : WordTrace (prefixWord ++ tailWord_3352167) baseStart_3352167 baseEnd_3352167 := by
    simpa [prefixWord, tailWord_3352167, baseEnd_3352167] using wordTrace_append hprefix tailTrace_3352167
  have hstable : (prefixWord ++ tailWord_3352167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352167).length < 2 ^ (prefixWord ++ tailWord_3352167).sum := by decide
  have hdescent : baseEnd_3352167 < baseStart_3352167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352240 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 1, 7]
def baseStart_3352240 : Nat := 118140960795 + 3352240 * 2 ^ 59
def prefixEnd_3352240 : Nat := 4983230072969 + 3 ^ 40 * 3352240 * 2
def baseEnd_3352240 : Nat := 1147540259485379719522223

theorem tailTrace_3352240 : CollatzResearch.WordTrace tailWord_3352240 prefixEnd_3352240 1147540259485379719522223 := by
  unfold tailWord_3352240
  simp only [CollatzResearch.WordTrace]
  refine ⟨61133118687707235928351087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81510824916942981237801449 61133118687707235928351087)
  ·
    refine ⟨91699678031560853892526631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61133118687707235928351087 91699678031560853892526631)
    ·
      refine ⟨137549517047341280838789947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91699678031560853892526631 137549517047341280838789947)
      ·
        refine ⟨206324275571011921258184921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137549517047341280838789947 206324275571011921258184921)
        ·
          refine ⟨154743206678258940943638691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206324275571011921258184921 154743206678258940943638691)
          ·
            refine ⟨232114810017388411415458037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154743206678258940943638691 232114810017388411415458037)
            ·
              refine ⟨21760763439130163570199191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232114810017388411415458037 21760763439130163570199191)
              ·
                refine ⟨32641145158695245355298787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21760763439130163570199191 32641145158695245355298787)
                ·
                  refine ⟨48961717738042868032948181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32641145158695245355298787 48961717738042868032948181)
                  ·
                    refine ⟨1147540259485379719522223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48961717738042868032948181 1147540259485379719522223)
                    ·
                      rfl

theorem cell22_3352240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_3352240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352240 prefixEnd_3352240 := by exact prefixLift 3352240
  have htrace : WordTrace (prefixWord ++ tailWord_3352240) baseStart_3352240 baseEnd_3352240 := by
    simpa [prefixWord, tailWord_3352240, baseEnd_3352240] using wordTrace_append hprefix tailTrace_3352240
  have hstable : (prefixWord ++ tailWord_3352240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352240).length < 2 ^ (prefixWord ++ tailWord_3352240).sum := by decide
  have hdescent : baseEnd_3352240 < baseStart_3352240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352242 : List Nat := [3, 2, 1, 1, 1, 2, 4, 3, 5]
def baseStart_3352242 : Nat := 118140960795 + 3352242 * 2 ^ 59
def prefixEnd_3352242 : Nat := 4983230072969 + 3 ^ 40 * 3352242 * 2
def baseEnd_3352242 : Nat := 382513648042084126990739

theorem tailTrace_3352242 : CollatzResearch.WordTrace tailWord_3352242 prefixEnd_3352242 382513648042084126990739 := by
  unfold tailWord_3352242
  simp only [CollatzResearch.WordTrace]
  refine ⟨30566577580351806549568745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81510873547604817465516653 30566577580351806549568745)
  ·
    refine ⟨22924933185263854912176559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30566577580351806549568745 22924933185263854912176559)
    ·
      refine ⟨34387399777895782368264839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22924933185263854912176559 34387399777895782368264839)
      ·
        refine ⟨51581099666843673552397259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34387399777895782368264839 51581099666843673552397259)
        ·
          refine ⟨77371649500265510328595889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51581099666843673552397259 77371649500265510328595889)
          ·
            refine ⟨58028737125199132746446917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77371649500265510328595889 58028737125199132746446917)
            ·
              refine ⟨10880388210974837389958797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58028737125199132746446917 10880388210974837389958797)
              ·
                refine ⟨4080145579115564021234549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10880388210974837389958797 4080145579115564021234549)
                ·
                  refine ⟨382513648042084126990739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4080145579115564021234549 382513648042084126990739)
                  ·
                    rfl

theorem cell22_3352242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_3352242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352242 prefixEnd_3352242 := by exact prefixLift 3352242
  have htrace : WordTrace (prefixWord ++ tailWord_3352242) baseStart_3352242 baseEnd_3352242 := by
    simpa [prefixWord, tailWord_3352242, baseEnd_3352242] using wordTrace_append hprefix tailTrace_3352242
  have hstable : (prefixWord ++ tailWord_3352242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352242).length < 2 ^ (prefixWord ++ tailWord_3352242).sum := by decide
  have hdescent : baseEnd_3352242 < baseStart_3352242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352246 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_3352246 : Nat := 118140960795 + 3352246 * 2 ^ 59
def prefixEnd_3352246 : Nat := 4983230072969 + 3 ^ 40 * 3352246 * 2
def baseEnd_3352246 : Nat := 1147542313407997703872205

theorem tailTrace_3352246 : CollatzResearch.WordTrace tailWord_3352246 prefixEnd_3352246 1147542313407997703872205 := by
  unfold tailWord_3352246
  simp only [CollatzResearch.WordTrace]
  refine ⟨7641653513337045930088787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81510970808928489920947061 7641653513337045930088787)
  ·
    refine ⟨11462480270005568895133181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7641653513337045930088787 11462480270005568895133181)
    ·
      refine ⟨4298430101252088335674943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11462480270005568895133181 4298430101252088335674943)
      ·
        refine ⟨6447645151878132503512415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4298430101252088335674943 6447645151878132503512415)
        ·
          refine ⟨9671467727817198755268623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6447645151878132503512415 9671467727817198755268623)
          ·
            refine ⟨14507201591725798132902935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9671467727817198755268623 14507201591725798132902935)
            ·
              refine ⟨21760802387588697199354403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14507201591725798132902935 21760802387588697199354403)
              ·
                refine ⟨32641203581383045799031605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21760802387588697199354403 32641203581383045799031605)
                ·
                  refine ⟨3060112835754660543659213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32641203581383045799031605 3060112835754660543659213)
                  ·
                    refine ⟨1147542313407997703872205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3060112835754660543659213 1147542313407997703872205)
                    ·
                      rfl

theorem cell22_3352246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_3352246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352246 prefixEnd_3352246 := by exact prefixLift 3352246
  have htrace : WordTrace (prefixWord ++ tailWord_3352246) baseStart_3352246 baseEnd_3352246 := by
    simpa [prefixWord, tailWord_3352246, baseEnd_3352246] using wordTrace_append hprefix tailTrace_3352246
  have hstable : (prefixWord ++ tailWord_3352246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352246).length < 2 ^ (prefixWord ++ tailWord_3352246).sum := by decide
  have hdescent : baseEnd_3352246 < baseStart_3352246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352276 : List Nat := [2, 4, 1, 3, 1, 3, 1, 2, 5]
def baseStart_3352276 : Nat := 118140960795 + 3352276 * 2 ^ 59
def prefixEnd_3352276 : Nat := 4983230072969 + 3 ^ 40 * 3352276 * 2
def baseEnd_3352276 : Nat := 382517527673695875207371

theorem tailTrace_3352276 : CollatzResearch.WordTrace tailWord_3352276 prefixEnd_3352276 382517527673695875207371 := by
  unfold tailWord_3352276
  simp only [CollatzResearch.WordTrace]
  refine ⟨61133775201642025002506341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81511700268856033336675121 61133775201642025002506341)
  ·
    refine ⟨11462582850307879687969939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61133775201642025002506341 11462582850307879687969939)
    ·
      refine ⟨17193874275461819531954909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11462582850307879687969939 17193874275461819531954909)
      ·
        refine ⟨6447702853298182324483091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17193874275461819531954909 6447702853298182324483091)
        ·
          refine ⟨9671554279947273486724637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6447702853298182324483091 9671554279947273486724637)
          ·
            refine ⟨3626832854980227557521739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9671554279947273486724637 3626832854980227557521739)
            ·
              refine ⟨5440249282470341336282609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3626832854980227557521739 5440249282470341336282609)
              ·
                refine ⟨4080186961852756002211957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5440249282470341336282609 4080186961852756002211957)
                ·
                  refine ⟨382517527673695875207371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4080186961852756002211957 382517527673695875207371)
                  ·
                    rfl

theorem cell22_3352276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_3352276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352276 prefixEnd_3352276 := by exact prefixLift 3352276
  have htrace : WordTrace (prefixWord ++ tailWord_3352276) baseStart_3352276 baseEnd_3352276 := by
    simpa [prefixWord, tailWord_3352276, baseEnd_3352276] using wordTrace_append hprefix tailTrace_3352276
  have hstable : (prefixWord ++ tailWord_3352276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352276).length < 2 ^ (prefixWord ++ tailWord_3352276).sum := by decide
  have hdescent : baseEnd_3352276 < baseStart_3352276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352287 : List Nat := [1, 1, 2, 3, 2, 2, 4, 1, 6]
def baseStart_3352287 : Nat := 118140960795 + 3352287 * 2 ^ 59
def prefixEnd_3352287 : Nat := 4983230072969 + 3 ^ 40 * 3352287 * 2
def baseEnd_3352287 : Nat := 382518782848629087865693

theorem tailTrace_3352287 : CollatzResearch.WordTrace tailWord_3352287 prefixEnd_3352287 382518782848629087865693 := by
  unfold tailWord_3352287
  simp only [CollatzResearch.WordTrace]
  refine ⟨122267951606244198883663115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81511967737496132589108743 122267951606244198883663115)
  ·
    refine ⟨183401927409366298325494673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122267951606244198883663115 183401927409366298325494673)
    ·
      refine ⟨137551445557024723744121005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183401927409366298325494673 137551445557024723744121005)
      ·
        refine ⟨51581792083884271404045377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137551445557024723744121005 51581792083884271404045377)
        ·
          refine ⟨38686344062913203553034033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51581792083884271404045377 38686344062913203553034033)
          ·
            refine ⟨29014758047184902664775525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38686344062913203553034033 29014758047184902664775525)
            ·
              refine ⟨5440267133847169249645411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29014758047184902664775525 5440267133847169249645411)
              ·
                refine ⟨8160400700770753874468117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5440267133847169249645411 8160400700770753874468117)
                ·
                  refine ⟨382518782848629087865693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8160400700770753874468117 382518782848629087865693)
                  ·
                    rfl

theorem cell22_3352287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 6].length) (baseStart_3352287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352287 prefixEnd_3352287 := by exact prefixLift 3352287
  have htrace : WordTrace (prefixWord ++ tailWord_3352287) baseStart_3352287 baseEnd_3352287 := by
    simpa [prefixWord, tailWord_3352287, baseEnd_3352287] using wordTrace_append hprefix tailTrace_3352287
  have hstable : (prefixWord ++ tailWord_3352287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352287).length < 2 ^ (prefixWord ++ tailWord_3352287).sum := by decide
  have hdescent : baseEnd_3352287 < baseStart_3352287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352353 : List Nat := [1, 2, 3, 2, 1, 5, 2, 1, 2, 3]
def baseStart_3352353 : Nat := 118140960795 + 3352353 * 2 ^ 59
def prefixEnd_3352353 : Nat := 4983230072969 + 3 ^ 40 * 3352353 * 2
def baseEnd_3352353 : Nat := 1147578941694685091446877

theorem tailTrace_3352353 : CollatzResearch.WordTrace tailWord_3352353 prefixEnd_3352353 1147578941694685091446877 := by
  unfold tailWord_3352353
  simp only [CollatzResearch.WordTrace]
  refine ⟨122270358824005092155565713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81513572549336728103710475 122270358824005092155565713)
  ·
    refine ⟨91702769118003819116674285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122270358824005092155565713 91702769118003819116674285)
    ·
      refine ⟨34388538419251432168752857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91702769118003819116674285 34388538419251432168752857)
      ·
        refine ⟨25791403814438574126564643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34388538419251432168752857 25791403814438574126564643)
        ·
          refine ⟨38687105721657861189846965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25791403814438574126564643 38687105721657861189846965)
          ·
            refine ⟨3626916161405424486548153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38687105721657861189846965 3626916161405424486548153)
            ·
              refine ⟨2720187121054068364911115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3626916161405424486548153 2720187121054068364911115)
              ·
                refine ⟨4080280681581102547366673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2720187121054068364911115 4080280681581102547366673)
                ·
                  refine ⟨3060210511185826910525005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4080280681581102547366673 3060210511185826910525005)
                  ·
                    refine ⟨1147578941694685091446877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3060210511185826910525005 1147578941694685091446877)
                    ·
                      rfl

theorem cell22_3352353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_3352353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352353 prefixEnd_3352353 := by exact prefixLift 3352353
  have htrace : WordTrace (prefixWord ++ tailWord_3352353) baseStart_3352353 baseEnd_3352353 := by
    simpa [prefixWord, tailWord_3352353, baseEnd_3352353] using wordTrace_append hprefix tailTrace_3352353
  have hstable : (prefixWord ++ tailWord_3352353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352353).length < 2 ^ (prefixWord ++ tailWord_3352353).sum := by decide
  have hdescent : baseEnd_3352353 < baseStart_3352353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352394 : List Nat := [3, 1, 2, 1, 1, 1, 6, 2, 5]
def baseStart_3352394 : Nat := 118140960795 + 3352394 * 2 ^ 59
def prefixEnd_3352394 : Nat := 4983230072969 + 3 ^ 40 * 3352394 * 2
def baseEnd_3352394 : Nat := 382530992277524883723917

theorem tailTrace_3352394 : CollatzResearch.WordTrace tailWord_3352394 prefixEnd_3352394 382530992277524883723917 := by
  unfold tailWord_3352394
  simp only [CollatzResearch.WordTrace]
  refine ⟨30567963554214139039452059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81514569477904370771872157 30567963554214139039452059)
  ·
    refine ⟨45851945331321208559178089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30567963554214139039452059 45851945331321208559178089)
    ·
      refine ⟨34388958998490906419383567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45851945331321208559178089 34388958998490906419383567)
      ·
        refine ⟨51583438497736359629075351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34388958998490906419383567 51583438497736359629075351)
        ·
          refine ⟨77375157746604539443613027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51583438497736359629075351 77375157746604539443613027)
          ·
            refine ⟨116062736619906809165419541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77375157746604539443613027 116062736619906809165419541)
            ·
              refine ⟨5440440779058131679629041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116062736619906809165419541 5440440779058131679629041)
              ·
                refine ⟨4080330584293598759721781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5440440779058131679629041 4080330584293598759721781)
                ·
                  refine ⟨382530992277524883723917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4080330584293598759721781 382530992277524883723917)
                  ·
                    rfl

theorem cell22_3352394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_3352394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352394 prefixEnd_3352394 := by exact prefixLift 3352394
  have htrace : WordTrace (prefixWord ++ tailWord_3352394) baseStart_3352394 baseEnd_3352394 := by
    simpa [prefixWord, tailWord_3352394, baseEnd_3352394] using wordTrace_append hprefix tailTrace_3352394
  have hstable : (prefixWord ++ tailWord_3352394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352394).length < 2 ^ (prefixWord ++ tailWord_3352394).sum := by decide
  have hdescent : baseEnd_3352394 < baseStart_3352394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352424 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 3, 4]
def baseStart_3352424 : Nat := 118140960795 + 3352424 * 2 ^ 59
def prefixEnd_3352424 : Nat := 4983230072969 + 3 ^ 40 * 3352424 * 2
def baseEnd_3352424 : Nat := 1147603246445664572921659

theorem tailTrace_3352424 : CollatzResearch.WordTrace tailWord_3352424 prefixEnd_3352424 1147603246445664572921659 := by
  unfold tailWord_3352424
  simp only [CollatzResearch.WordTrace]
  refine ⟨61136474203373935640700163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81515298937831914187600217 61136474203373935640700163)
  ·
    refine ⟨91704711305060903461050245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61136474203373935640700163 91704711305060903461050245)
    ·
      refine ⟨17194633369698919398946921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91704711305060903461050245 17194633369698919398946921)
      ·
        refine ⟨12895975027274189549210191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17194633369698919398946921 12895975027274189549210191)
        ·
          refine ⟨19343962540911284323815287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12895975027274189549210191 19343962540911284323815287)
          ·
            refine ⟨29015943811366926485722931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19343962540911284323815287 29015943811366926485722931)
            ·
              refine ⟨43523915717050389728584397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29015943811366926485722931 43523915717050389728584397)
              ·
                refine ⟨16321468393893896148219149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43523915717050389728584397 16321468393893896148219149)
                ·
                  refine ⟨6120550647710211055582181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16321468393893896148219149 6120550647710211055582181)
                  ·
                    refine ⟨1147603246445664572921659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6120550647710211055582181 1147603246445664572921659)
                    ·
                      rfl

theorem cell22_3352424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_3352424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352424 prefixEnd_3352424 := by exact prefixLift 3352424
  have htrace : WordTrace (prefixWord ++ tailWord_3352424) baseStart_3352424 baseEnd_3352424 := by
    simpa [prefixWord, tailWord_3352424, baseEnd_3352424] using wordTrace_append hprefix tailTrace_3352424
  have hstable : (prefixWord ++ tailWord_3352424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352424).length < 2 ^ (prefixWord ++ tailWord_3352424).sum := by decide
  have hdescent : baseEnd_3352424 < baseStart_3352424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352456 : List Nat := [2, 1, 3, 3, 3, 1, 2, 1, 6]
def baseStart_3352456 : Nat := 118140960795 + 3352456 * 2 ^ 59
def prefixEnd_3352456 : Nat := 4983230072969 + 3 ^ 40 * 3352456 * 2
def baseEnd_3352456 : Nat := 382538066899875718707187

theorem tailTrace_3352456 : CollatzResearch.WordTrace tailWord_3352456 prefixEnd_3352456 382538066899875718707187 := by
  unfold tailWord_3352456
  simp only [CollatzResearch.WordTrace]
  refine ⟨61137057771315970373282611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81516077028421293831043481 61137057771315970373282611)
  ·
    refine ⟨91705586656973955559923917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61137057771315970373282611 91705586656973955559923917)
    ·
      refine ⟨34389594996365233334971469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91705586656973955559923917 34389594996365233334971469)
      ·
        refine ⟨12896098123636962500614301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34389594996365233334971469 12896098123636962500614301)
        ·
          refine ⟨4836036796363860937730363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12896098123636962500614301 4836036796363860937730363)
          ·
            refine ⟨7254055194545791406595545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4836036796363860937730363 7254055194545791406595545)
            ·
              refine ⟨5440541395909343554946659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7254055194545791406595545 5440541395909343554946659)
              ·
                refine ⟨8160812093864015332419989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5440541395909343554946659 8160812093864015332419989)
                ·
                  refine ⟨382538066899875718707187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8160812093864015332419989 382538066899875718707187)
                  ·
                    rfl

theorem cell22_3352456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 6].length) (baseStart_3352456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352456 prefixEnd_3352456 := by exact prefixLift 3352456
  have htrace : WordTrace (prefixWord ++ tailWord_3352456) baseStart_3352456 baseEnd_3352456 := by
    simpa [prefixWord, tailWord_3352456, baseEnd_3352456] using wordTrace_append hprefix tailTrace_3352456
  have hstable : (prefixWord ++ tailWord_3352456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352456).length < 2 ^ (prefixWord ++ tailWord_3352456).sum := by decide
  have hdescent : baseEnd_3352456 < baseStart_3352456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352471 : List Nat := [1, 1, 3, 3, 1, 5, 1, 1, 1, 5]
def baseStart_3352471 : Nat := 118140960795 + 3352471 * 2 ^ 59
def prefixEnd_3352471 : Nat := 4983230072969 + 3 ^ 40 * 3352471 * 2
def baseEnd_3352471 : Nat := 1147619335506172116996515

theorem tailTrace_3352471 : CollatzResearch.WordTrace tailWord_3352471 prefixEnd_3352471 1147619335506172116996515 := by
  unfold tailWord_3352471
  simp only [CollatzResearch.WordTrace]
  refine ⟨122274662637577598308361267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81516441758385065538907511 122274662637577598308361267)
  ·
    refine ⟨183411993956366397462541901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122274662637577598308361267 183411993956366397462541901)
    ·
      refine ⟨68779497733637399048453213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183411993956366397462541901 68779497733637399048453213)
      ·
        refine ⟨25792311650114024643169955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68779497733637399048453213 25792311650114024643169955)
        ·
          refine ⟨38688467475171036964754933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25792311650114024643169955 38688467475171036964754933)
          ·
            refine ⟨3627043825797284715445775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38688467475171036964754933 3627043825797284715445775)
            ·
              refine ⟨5440565738695927073168663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3627043825797284715445775 5440565738695927073168663)
              ·
                refine ⟨8160848608043890609752995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5440565738695927073168663 8160848608043890609752995)
                ·
                  refine ⟨12241272912065835914629493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8160848608043890609752995 12241272912065835914629493)
                  ·
                    refine ⟨1147619335506172116996515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12241272912065835914629493 1147619335506172116996515)
                    ·
                      rfl

theorem cell22_3352471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_3352471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352471 prefixEnd_3352471 := by exact prefixLift 3352471
  have htrace : WordTrace (prefixWord ++ tailWord_3352471) baseStart_3352471 baseEnd_3352471 := by
    simpa [prefixWord, tailWord_3352471, baseEnd_3352471] using wordTrace_append hprefix tailTrace_3352471
  have hstable : (prefixWord ++ tailWord_3352471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352471).length < 2 ^ (prefixWord ++ tailWord_3352471).sum := by decide
  have hdescent : baseEnd_3352471 < baseStart_3352471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352484 : List Nat := [2, 3, 1, 2, 1, 4, 1, 8]
def baseStart_3352484 : Nat := 118140960795 + 3352484 * 2 ^ 59
def prefixEnd_3352484 : Nat := 4983230072969 + 3 ^ 40 * 3352484 * 2
def baseEnd_3352484 : Nat := 127513753963538268491275

theorem tailTrace_3352484 : CollatzResearch.WordTrace tailWord_3352484 prefixEnd_3352484 127513753963538268491275 := by
  unfold tailWord_3352484
  simp only [CollatzResearch.WordTrace]
  refine ⟨61137568393265250764292253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81516757857687001019056337 61137568393265250764292253)
  ·
    refine ⟨22926588147474469036609595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61137568393265250764292253 22926588147474469036609595)
    ·
      refine ⟨34389882221211703554914393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22926588147474469036609595 34389882221211703554914393)
      ·
        refine ⟨25792411665908777666185795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34389882221211703554914393 25792411665908777666185795)
        ·
          refine ⟨38688617498863166499278693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25792411665908777666185795 38688617498863166499278693)
          ·
            refine ⟨7254115781036843718614755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38688617498863166499278693 7254115781036843718614755)
            ·
              refine ⟨10881173671555265577922133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7254115781036843718614755 10881173671555265577922133)
              ·
                refine ⟨127513753963538268491275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10881173671555265577922133 127513753963538268491275)
                ·
                  rfl

theorem cell22_3352484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 8].length) (baseStart_3352484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352484 prefixEnd_3352484 := by exact prefixLift 3352484
  have htrace : WordTrace (prefixWord ++ tailWord_3352484) baseStart_3352484 baseEnd_3352484 := by
    simpa [prefixWord, tailWord_3352484, baseEnd_3352484] using wordTrace_append hprefix tailTrace_3352484
  have hstable : (prefixWord ++ tailWord_3352484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352484).length < 2 ^ (prefixWord ++ tailWord_3352484).sum := by decide
  have hdescent : baseEnd_3352484 < baseStart_3352484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352640 : List Nat := [2, 1, 1, 2, 2, 5, 3, 1, 2, 3]
def baseStart_3352640 : Nat := 118140960795 + 3352640 * 2 ^ 59
def prefixEnd_3352640 : Nat := 4983230072969 + 3 ^ 40 * 3352640 * 2
def baseEnd_3352640 : Nat := 1147677187659912009520997

theorem tailTrace_3352640 : CollatzResearch.WordTrace tailWord_3352640 prefixEnd_3352640 1147677187659912009520997 := by
  unfold tailWord_3352640
  simp only [CollatzResearch.WordTrace]
  refine ⟨61140413286982670085631687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81520551049310226780842249 61140413286982670085631687)
  ·
    refine ⟨91710619930474005128447531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61140413286982670085631687 91710619930474005128447531)
    ·
      refine ⟨137565929895711007692671297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91710619930474005128447531 137565929895711007692671297)
      ·
        refine ⟨103174447421783255769503473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137565929895711007692671297 103174447421783255769503473)
        ·
          refine ⟨77380835566337441827127605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103174447421783255769503473 77380835566337441827127605)
          ·
            refine ⟨7254453334344135171293213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77380835566337441827127605 7254453334344135171293213)
            ·
              refine ⟨2720420000379050689234955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7254453334344135171293213 2720420000379050689234955)
              ·
                refine ⟨4080630000568576033852433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2720420000379050689234955 4080630000568576033852433)
                ·
                  refine ⟨3060472500426432025389325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4080630000568576033852433 3060472500426432025389325)
                  ·
                    refine ⟨1147677187659912009520997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3060472500426432025389325 1147677187659912009520997)
                    ·
                      rfl

theorem cell22_3352640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 2, 3].length) (baseStart_3352640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352640 prefixEnd_3352640 := by exact prefixLift 3352640
  have htrace : WordTrace (prefixWord ++ tailWord_3352640) baseStart_3352640 baseEnd_3352640 := by
    simpa [prefixWord, tailWord_3352640, baseEnd_3352640] using wordTrace_append hprefix tailTrace_3352640
  have hstable : (prefixWord ++ tailWord_3352640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352640).length < 2 ^ (prefixWord ++ tailWord_3352640).sum := by decide
  have hdescent : baseEnd_3352640 < baseStart_3352640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352681 : List Nat := [1, 2, 1, 1, 1, 5, 2, 4, 5]
def baseStart_3352681 : Nat := 118140960795 + 3352681 * 2 ^ 59
def prefixEnd_3352681 : Nat := 4983230072969 + 3 ^ 40 * 3352681 * 2
def baseEnd_3352681 : Nat := 382563740932600523081957

theorem tailTrace_3352681 : CollatzResearch.WordTrace tailWord_3352681 prefixEnd_3352681 382563740932600523081957 := by
  unfold tailWord_3352681
  simp only [CollatzResearch.WordTrace]
  refine ⟨122282321966816804173505897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81521547977877869449003931 122282321966816804173505897)
  ·
    refine ⟨91711741475112603130129423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122282321966816804173505897 91711741475112603130129423)
    ·
      refine ⟨137567612212668904695194135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91711741475112603130129423 137567612212668904695194135)
      ·
        refine ⟨206351418319003357042791203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137567612212668904695194135 206351418319003357042791203)
        ·
          refine ⟨309527127478505035564186805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206351418319003357042791203 309527127478505035564186805)
          ·
            refine ⟨29018168201109847084142513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 309527127478505035564186805 29018168201109847084142513)
            ·
              refine ⟨21763626150832385313106885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29018168201109847084142513 21763626150832385313106885)
              ·
                refine ⟨4080679903281072246207541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21763626150832385313106885 4080679903281072246207541)
                ·
                  refine ⟨382563740932600523081957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4080679903281072246207541 382563740932600523081957)
                  ·
                    rfl

theorem cell22_3352681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 5].length) (baseStart_3352681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352681 prefixEnd_3352681 := by exact prefixLift 3352681
  have htrace : WordTrace (prefixWord ++ tailWord_3352681) baseStart_3352681 baseEnd_3352681 := by
    simpa [prefixWord, tailWord_3352681, baseEnd_3352681] using wordTrace_append hprefix tailTrace_3352681
  have hstable : (prefixWord ++ tailWord_3352681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352681).length < 2 ^ (prefixWord ++ tailWord_3352681).sum := by decide
  have hdescent : baseEnd_3352681 < baseStart_3352681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352741 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 3, 5]
def baseStart_3352741 : Nat := 118140960795 + 3352741 * 2 ^ 59
def prefixEnd_3352741 : Nat := 4983230072969 + 3 ^ 40 * 3352741 * 2
def baseEnd_3352741 : Nat := 1147711762023981412745687

theorem tailTrace_3352741 : CollatzResearch.WordTrace tailWord_3352741 prefixEnd_3352741 1147711762023981412745687 := by
  unfold tailWord_3352741
  simp only [CollatzResearch.WordTrace]
  refine ⟨122284510346599434420690077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81523006897732956280460051 122284510346599434420690077)
  ·
    refine ⟨45856691379974787907758779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122284510346599434420690077 45856691379974787907758779)
    ·
      refine ⟨68785037069962181861638169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45856691379974787907758779 68785037069962181861638169)
      ·
        refine ⟨51588777802471636396228627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68785037069962181861638169 51588777802471636396228627)
        ·
          refine ⟨77383166703707454594342941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51588777802471636396228627 77383166703707454594342941)
          ·
            refine ⟨29018687513890295472878603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77383166703707454594342941 29018687513890295472878603)
            ·
              refine ⟨43528031270835443209317905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29018687513890295472878603 43528031270835443209317905)
              ·
                refine ⟨32646023453126582406988429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43528031270835443209317905 32646023453126582406988429)
                ·
                  refine ⟨12242258794922468402620661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32646023453126582406988429 12242258794922468402620661)
                  ·
                    refine ⟨1147711762023981412745687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12242258794922468402620661 1147711762023981412745687)
                    ·
                      rfl

theorem cell22_3352741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_3352741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352741 prefixEnd_3352741 := by exact prefixLift 3352741
  have htrace : WordTrace (prefixWord ++ tailWord_3352741) baseStart_3352741 baseEnd_3352741 := by
    simpa [prefixWord, tailWord_3352741, baseEnd_3352741] using wordTrace_append hprefix tailTrace_3352741
  have hstable : (prefixWord ++ tailWord_3352741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352741).length < 2 ^ (prefixWord ++ tailWord_3352741).sum := by decide
  have hdescent : baseEnd_3352741 < baseStart_3352741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352773 : List Nat := [1, 3, 1, 1, 1, 1, 7, 1, 2, 4]
def baseStart_3352773 : Nat := 118140960795 + 3352773 * 2 ^ 59
def prefixEnd_3352773 : Nat := 4983230072969 + 3 ^ 40 * 3352773 * 2
def baseEnd_3352773 : Nat := 1147722716277943995945589

theorem tailTrace_3352773 : CollatzResearch.WordTrace tailWord_3352773 prefixEnd_3352773 1147722716277943995945589 := by
  unfold tailWord_3352773
  simp only [CollatzResearch.WordTrace]
  refine ⟨122285677482483503885854973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81523784988322335923903315 122285677482483503885854973)
  ·
    refine ⟨45857129055931313957195615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122285677482483503885854973 45857129055931313957195615)
    ·
      refine ⟨68785693583896970935793423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45857129055931313957195615 68785693583896970935793423)
      ·
        refine ⟨103178540375845456403690135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68785693583896970935793423 103178540375845456403690135)
        ·
          refine ⟨154767810563768184605535203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103178540375845456403690135 154767810563768184605535203)
          ·
            refine ⟨232151715845652276908302805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154767810563768184605535203 232151715845652276908302805)
            ·
              refine ⟨5441055840132475240038347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 232151715845652276908302805 5441055840132475240038347)
              ·
                refine ⟨8161583760198712860057521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5441055840132475240038347 8161583760198712860057521)
                ·
                  refine ⟨6121187820149034645043141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8161583760198712860057521 6121187820149034645043141)
                  ·
                    refine ⟨1147722716277943995945589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6121187820149034645043141 1147722716277943995945589)
                    ·
                      rfl

theorem cell22_3352773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_3352773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352773 prefixEnd_3352773 := by exact prefixLift 3352773
  have htrace : WordTrace (prefixWord ++ tailWord_3352773) baseStart_3352773 baseEnd_3352773 := by
    simpa [prefixWord, tailWord_3352773, baseEnd_3352773] using wordTrace_append hprefix tailTrace_3352773
  have hstable : (prefixWord ++ tailWord_3352773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352773).length < 2 ^ (prefixWord ++ tailWord_3352773).sum := by decide
  have hdescent : baseEnd_3352773 < baseStart_3352773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352792 : List Nat := [2, 1, 2, 2, 4, 3, 1, 2, 2, 3]
def baseStart_3352792 : Nat := 118140960795 + 3352792 * 2 ^ 59
def prefixEnd_3352792 : Nat := 4983230072969 + 3 ^ 40 * 3352792 * 2
def baseEnd_3352792 : Nat := 1147729220366234279720531

theorem tailTrace_3352792 : CollatzResearch.WordTrace tailWord_3352792 prefixEnd_3352792 1147729220366234279720531 := by
  unfold tailWord_3352792
  simp only [CollatzResearch.WordTrace]
  refine ⟨61143185234707335065398315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81524246979609780087197753 61143185234707335065398315)
  ·
    refine ⟨91714777852061002598097473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61143185234707335065398315 91714777852061002598097473)
    ·
      refine ⟨68786083389045751948573105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91714777852061002598097473 68786083389045751948573105)
      ·
        refine ⟨51589562541784313961429829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68786083389045751948573105 51589562541784313961429829)
        ·
          refine ⟨9673042976584558867768093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51589562541784313961429829 9673042976584558867768093)
          ·
            refine ⟨3627391116219209575413035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9673042976584558867768093 3627391116219209575413035)
            ·
              refine ⟨5441086674328814363119553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3627391116219209575413035 5441086674328814363119553)
              ·
                refine ⟨4080815005746610772339665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5441086674328814363119553 4080815005746610772339665)
                ·
                  refine ⟨3060611254309958079254749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4080815005746610772339665 3060611254309958079254749)
                  ·
                    refine ⟨1147729220366234279720531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3060611254309958079254749 1147729220366234279720531)
                    ·
                      rfl

theorem cell22_3352792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_3352792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352792 prefixEnd_3352792 := by exact prefixLift 3352792
  have htrace : WordTrace (prefixWord ++ tailWord_3352792) baseStart_3352792 baseEnd_3352792 := by
    simpa [prefixWord, tailWord_3352792, baseEnd_3352792] using wordTrace_append hprefix tailTrace_3352792
  have hstable : (prefixWord ++ tailWord_3352792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352792).length < 2 ^ (prefixWord ++ tailWord_3352792).sum := by decide
  have hdescent : baseEnd_3352792 < baseStart_3352792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352895 : List Nat := [1, 1, 2, 2, 4, 1, 2, 5, 4]
def baseStart_3352895 : Nat := 118140960795 + 3352895 * 2 ^ 59
def prefixEnd_3352895 : Nat := 4983230072969 + 3 ^ 40 * 3352895 * 2
def baseEnd_3352895 : Nat := 382588159790392114798405

theorem tailTrace_3352895 : CollatzResearch.WordTrace tailWord_3352895 prefixEnd_3352895 382588159790392114798405 := by
  unfold tailWord_3352895
  simp only [CollatzResearch.WordTrace]
  refine ⟨122290127188041518721796139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81526751458694345814530759 122290127188041518721796139)
  ·
    refine ⟨183435190782062278082694209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122290127188041518721796139 183435190782062278082694209)
    ·
      refine ⟨137576393086546708562020657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183435190782062278082694209 137576393086546708562020657)
      ·
        refine ⟨103182294814910031421515493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137576393086546708562020657 103182294814910031421515493)
        ·
          refine ⟨19346680277795630891534155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103182294814910031421515493 19346680277795630891534155)
          ·
            refine ⟨29020020416693446337301233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19346680277795630891534155 29020020416693446337301233)
            ·
              refine ⟨21765015312520084752975925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29020020416693446337301233 21765015312520084752975925)
              ·
                refine ⟨2040470185548757945591493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21765015312520084752975925 2040470185548757945591493)
                ·
                  refine ⟨382588159790392114798405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2040470185548757945591493 382588159790392114798405)
                  ·
                    rfl

theorem cell22_3352895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 4].length) (baseStart_3352895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352895 prefixEnd_3352895 := by exact prefixLift 3352895
  have htrace : WordTrace (prefixWord ++ tailWord_3352895) baseStart_3352895 baseEnd_3352895 := by
    simpa [prefixWord, tailWord_3352895, baseEnd_3352895] using wordTrace_append hprefix tailTrace_3352895
  have hstable : (prefixWord ++ tailWord_3352895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352895).length < 2 ^ (prefixWord ++ tailWord_3352895).sum := by decide
  have hdescent : baseEnd_3352895 < baseStart_3352895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352912 : List Nat := [2, 1, 1, 1, 1, 6, 4, 2, 4]
def baseStart_3352912 : Nat := 118140960795 + 3352912 * 2 ^ 59
def prefixEnd_3352912 : Nat := 4983230072969 + 3 ^ 40 * 3352912 * 2
def baseEnd_3352912 : Nat := 382590099606197988906721

theorem tailTrace_3352912 : CollatzResearch.WordTrace tailWord_3352912 prefixEnd_3352912 382590099606197988906721 := by
  unfold tailWord_3352912
  simp only [CollatzResearch.WordTrace]
  refine ⟨61145373614489965312582495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81527164819319953750109993 61145373614489965312582495)
  ·
    refine ⟨91718060421734947968873743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61145373614489965312582495 91718060421734947968873743)
    ·
      refine ⟨137577090632602421953310615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91718060421734947968873743 137577090632602421953310615)
      ·
        refine ⟨206365635948903632929965923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137577090632602421953310615 206365635948903632929965923)
        ·
          refine ⟨309548453923355449394948885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206365635948903632929965923 309548453923355449394948885)
          ·
            refine ⟨14510083777657286690388229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 309548453923355449394948885 14510083777657286690388229)
            ·
              refine ⟨2720640708310741254447793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14510083777657286690388229 2720640708310741254447793)
              ·
                refine ⟨2040480531233055940835845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2720640708310741254447793 2040480531233055940835845)
                ·
                  refine ⟨382590099606197988906721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2040480531233055940835845 382590099606197988906721)
                  ·
                    rfl

theorem cell22_3352912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 4].length) (baseStart_3352912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352912 prefixEnd_3352912 := by exact prefixLift 3352912
  have htrace : WordTrace (prefixWord ++ tailWord_3352912) baseStart_3352912 baseEnd_3352912 := by
    simpa [prefixWord, tailWord_3352912, baseEnd_3352912] using wordTrace_append hprefix tailTrace_3352912
  have hstable : (prefixWord ++ tailWord_3352912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352912).length < 2 ^ (prefixWord ++ tailWord_3352912).sum := by decide
  have hdescent : baseEnd_3352912 < baseStart_3352912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352972 : List Nat := [2, 2, 1, 2, 1, 5, 2, 1, 3, 3]
def baseStart_3352972 : Nat := 118140960795 + 3352972 * 2 ^ 59
def prefixEnd_3352972 : Nat := 4983230072969 + 3 ^ 40 * 3352972 * 2
def baseEnd_3352972 : Nat := 1147790838044773810219979

theorem tailTrace_3352972 : CollatzResearch.WordTrace tailWord_3352972 prefixEnd_3352972 1147790838044773810219979 := by
  unfold tailWord_3352972
  simp only [CollatzResearch.WordTrace]
  refine ⟨61146467804381280436174585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81528623739175040581566113 61146467804381280436174585)
  ·
    refine ⟨45859850853285960327130939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61146467804381280436174585 45859850853285960327130939)
    ·
      refine ⟨68789776279928940490696409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45859850853285960327130939 68789776279928940490696409)
      ·
        refine ⟨51592332209946705368022307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68789776279928940490696409 51592332209946705368022307)
        ·
          refine ⟨77388498314920058052033461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51592332209946705368022307 77388498314920058052033461)
          ·
            refine ⟨7255171717023755442378137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77388498314920058052033461 7255171717023755442378137)
            ·
              refine ⟨5441378787767816581783603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7255171717023755442378137 5441378787767816581783603)
              ·
                refine ⟨8162068181651724872675405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5441378787767816581783603 8162068181651724872675405)
                ·
                  refine ⟨3060775568119396827253277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8162068181651724872675405 3060775568119396827253277)
                  ·
                    refine ⟨1147790838044773810219979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3060775568119396827253277 1147790838044773810219979)
                    ·
                      rfl

theorem cell22_3352972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_3352972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3352972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3352972 prefixEnd_3352972 := by exact prefixLift 3352972
  have htrace : WordTrace (prefixWord ++ tailWord_3352972) baseStart_3352972 baseEnd_3352972 := by
    simpa [prefixWord, tailWord_3352972, baseEnd_3352972] using wordTrace_append hprefix tailTrace_3352972
  have hstable : (prefixWord ++ tailWord_3352972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352972).length < 2 ^ (prefixWord ++ tailWord_3352972).sum := by decide
  have hdescent : baseEnd_3352972 < baseStart_3352972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353036 : List Nat := [2, 2, 1, 4, 4, 1, 2, 1, 5]
def baseStart_3353036 : Nat := 118140960795 + 3353036 * 2 ^ 59
def prefixEnd_3353036 : Nat := 4983230072969 + 3 ^ 40 * 3353036 * 2
def baseEnd_3353036 : Nat := 382604248850899658873261

theorem tailTrace_3353036 : CollatzResearch.WordTrace tailWord_3353036 prefixEnd_3353036 382604248850899658873261 := by
  unfold tailWord_3353036
  simp only [CollatzResearch.WordTrace]
  refine ⟨61147634940265349901339481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81530179920353799868452641 61147634940265349901339481)
  ·
    refine ⟨45860726205199012426004611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61147634940265349901339481 45860726205199012426004611)
    ·
      refine ⟨68791089307798518639006917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45860726205199012426004611 68791089307798518639006917)
      ·
        refine ⟨12898329245212222244813797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68791089307798518639006917 12898329245212222244813797)
        ·
          refine ⟨2418436733477291670902587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12898329245212222244813797 2418436733477291670902587)
          ·
            refine ⟨3627655100215937506353881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2418436733477291670902587 3627655100215937506353881)
            ·
              refine ⟨2720741325161953129765411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3627655100215937506353881 2720741325161953129765411)
              ·
                refine ⟨4081111987742929694648117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2720741325161953129765411 4081111987742929694648117)
                ·
                  refine ⟨382604248850899658873261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4081111987742929694648117 382604248850899658873261)
                  ·
                    rfl

theorem cell22_3353036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 5].length) (baseStart_3353036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353036 prefixEnd_3353036 := by exact prefixLift 3353036
  have htrace : WordTrace (prefixWord ++ tailWord_3353036) baseStart_3353036 baseEnd_3353036 := by
    simpa [prefixWord, tailWord_3353036, baseEnd_3353036] using wordTrace_append hprefix tailTrace_3353036
  have hstable : (prefixWord ++ tailWord_3353036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353036).length < 2 ^ (prefixWord ++ tailWord_3353036).sum := by decide
  have hdescent : baseEnd_3353036 < baseStart_3353036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353092 : List Nat := [2, 3, 2, 3, 1, 1, 3, 7]
def baseStart_3353092 : Nat := 118140960795 + 3353092 * 2 ^ 59
def prefixEnd_3353092 : Nat := 4983230072969 + 3 ^ 40 * 3353092 * 2
def baseEnd_3353092 : Nat := 127536879610792610802179

theorem tailTrace_3353092 : CollatzResearch.WordTrace tailWord_3353092 prefixEnd_3353092 127536879610792610802179 := by
  unfold tailWord_3353092
  simp only [CollatzResearch.WordTrace]
  refine ⟨61148656184163910683358765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81531541578885214244478353 61148656184163910683358765)
  ·
    refine ⟨22930746069061466506259537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61148656184163910683358765 22930746069061466506259537)
    ·
      refine ⟨17198059551796099879694653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22930746069061466506259537 17198059551796099879694653)
      ·
        refine ⟨6449272331923537454885495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17198059551796099879694653 6449272331923537454885495)
        ·
          refine ⟨9673908497885306182328243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6449272331923537454885495 9673908497885306182328243)
          ·
            refine ⟨14510862746827959273492365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9673908497885306182328243 14510862746827959273492365)
            ·
              refine ⟨5441573530060484727559637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14510862746827959273492365 5441573530060484727559637)
              ·
                refine ⟨127536879610792610802179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5441573530060484727559637 127536879610792610802179)
                ·
                  rfl

theorem cell22_3353092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 7].length) (baseStart_3353092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353092 prefixEnd_3353092 := by exact prefixLift 3353092
  have htrace : WordTrace (prefixWord ++ tailWord_3353092) baseStart_3353092 baseEnd_3353092 := by
    simpa [prefixWord, tailWord_3353092, baseEnd_3353092] using wordTrace_append hprefix tailTrace_3353092
  have hstable : (prefixWord ++ tailWord_3353092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353092).length < 2 ^ (prefixWord ++ tailWord_3353092).sum := by decide
  have hdescent : baseEnd_3353092 < baseStart_3353092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353107 : List Nat := [1, 1, 1, 2, 1, 5, 3, 2, 3, 3]
def baseStart_3353107 : Nat := 118140960795 + 3353107 * 2 ^ 59
def prefixEnd_3353107 : Nat := 4983230072969 + 3 ^ 40 * 3353107 * 2
def baseEnd_3353107 : Nat := 1147837051303678458094565

theorem tailTrace_3353107 : CollatzResearch.WordTrace tailWord_3353107 prefixEnd_3353107 1147837051303678458094565 := by
  unfold tailWord_3353107
  simp only [CollatzResearch.WordTrace]
  refine ⟨122297859463273478928513575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81531906308848985952342383 122297859463273478928513575)
  ·
    refine ⟨183446789194910218392770363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122297859463273478928513575 183446789194910218392770363)
    ·
      refine ⟨275170183792365327589155545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183446789194910218392770363 275170183792365327589155545)
      ·
        refine ⟨206377637844273995691866659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275170183792365327589155545 206377637844273995691866659)
        ·
          refine ⟨309566456766410993537799989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206377637844273995691866659 309566456766410993537799989)
          ·
            refine ⟨29021855321851030644168749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 309566456766410993537799989 29021855321851030644168749)
            ·
              refine ⟨10883195745694136491563281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29021855321851030644168749 10883195745694136491563281)
              ·
                refine ⟨8162396809270602368672461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10883195745694136491563281 8162396809270602368672461)
                ·
                  refine ⟨3060898803476475888252173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8162396809270602368672461 3060898803476475888252173)
                  ·
                    refine ⟨1147837051303678458094565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3060898803476475888252173 1147837051303678458094565)
                    ·
                      rfl

theorem cell22_3353107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 3].length) (baseStart_3353107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353107 prefixEnd_3353107 := by exact prefixLift 3353107
  have htrace : WordTrace (prefixWord ++ tailWord_3353107) baseStart_3353107 baseEnd_3353107 := by
    simpa [prefixWord, tailWord_3353107, baseEnd_3353107] using wordTrace_append hprefix tailTrace_3353107
  have hstable : (prefixWord ++ tailWord_3353107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353107).length < 2 ^ (prefixWord ++ tailWord_3353107).sum := by decide
  have hdescent : baseEnd_3353107 < baseStart_3353107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353111 : List Nat := [1, 1, 3, 6, 1, 2, 1, 1, 2, 4]
def baseStart_3353111 : Nat := 118140960795 + 3353111 * 2 ^ 59
def prefixEnd_3353111 : Nat := 4983230072969 + 3 ^ 40 * 3353111 * 2
def baseEnd_3353111 : Nat := 1147838420585423780994553

theorem tailTrace_3353111 : CollatzResearch.WordTrace tailWord_3353111 prefixEnd_3353111 1147838420585423780994553 := by
  unfold tailWord_3353111
  simp only [CollatzResearch.WordTrace]
  refine ⟨122298005355258987611659187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81532003570172658407772791 122298005355258987611659187)
  ·
    refine ⟨183447008032888481417488781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122298005355258987611659187 183447008032888481417488781)
    ·
      refine ⟨68792628012333180531558293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183447008032888481417488781 68792628012333180531558293)
      ·
        refine ⟨3224654438078117837416795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68792628012333180531558293 3224654438078117837416795)
        ·
          refine ⟨4836981657117176756125193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3224654438078117837416795 4836981657117176756125193)
          ·
            refine ⟨3627736242837882567093895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4836981657117176756125193 3627736242837882567093895)
            ·
              refine ⟨5441604364256823850640843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3627736242837882567093895 5441604364256823850640843)
              ·
                refine ⟨8162406546385235775961265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5441604364256823850640843 8162406546385235775961265)
                ·
                  refine ⟨6121804909788926831970949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8162406546385235775961265 6121804909788926831970949)
                  ·
                    refine ⟨1147838420585423780994553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6121804909788926831970949 1147838420585423780994553)
                    ·
                      rfl

theorem cell22_3353111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_3353111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353111 prefixEnd_3353111 := by exact prefixLift 3353111
  have htrace : WordTrace (prefixWord ++ tailWord_3353111) baseStart_3353111 baseEnd_3353111 := by
    simpa [prefixWord, tailWord_3353111, baseEnd_3353111] using wordTrace_append hprefix tailTrace_3353111
  have hstable : (prefixWord ++ tailWord_3353111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353111).length < 2 ^ (prefixWord ++ tailWord_3353111).sum := by decide
  have hdescent : baseEnd_3353111 < baseStart_3353111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353137 : List Nat := [1, 2, 2, 3, 1, 1, 5, 2, 5]
def baseStart_3353137 : Nat := 118140960795 + 3353137 * 2 ^ 59
def prefixEnd_3353137 : Nat := 4983230072969 + 3 ^ 40 * 3353137 * 2
def baseEnd_3353137 : Nat := 382615773638922793281491

theorem tailTrace_3353137 : CollatzResearch.WordTrace tailWord_3353137 prefixEnd_3353137 382615773638922793281491 := by
  unfold tailWord_3353137
  simp only [CollatzResearch.WordTrace]
  refine ⟨122298953653164794052105665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81532635768776529368070443 122298953653164794052105665)
  ·
    refine ⟨91724215239873595539079249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122298953653164794052105665 91724215239873595539079249)
    ·
      refine ⟨68793161429905196654309437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91724215239873595539079249 68793161429905196654309437)
      ·
        refine ⟨25797435536214448745366039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68793161429905196654309437 25797435536214448745366039)
        ·
          refine ⟨38696153304321673118049059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25797435536214448745366039 38696153304321673118049059)
          ·
            refine ⟨58044229956482509677073589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38696153304321673118049059 58044229956482509677073589)
            ·
              refine ⟨5441646558420235282225649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58044229956482509677073589 5441646558420235282225649)
              ·
                refine ⟨4081234918815176461669237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5441646558420235282225649 4081234918815176461669237)
                ·
                  refine ⟨382615773638922793281491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4081234918815176461669237 382615773638922793281491)
                  ·
                    rfl

theorem cell22_3353137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 5].length) (baseStart_3353137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353137 prefixEnd_3353137 := by exact prefixLift 3353137
  have htrace : WordTrace (prefixWord ++ tailWord_3353137) baseStart_3353137 baseEnd_3353137 := by
    simpa [prefixWord, tailWord_3353137, baseEnd_3353137] using wordTrace_append hprefix tailTrace_3353137
  have hstable : (prefixWord ++ tailWord_3353137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353137).length < 2 ^ (prefixWord ++ tailWord_3353137).sum := by decide
  have hdescent : baseEnd_3353137 < baseStart_3353137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353167 : List Nat := [1, 1, 2, 1, 1, 2, 5, 4, 1, 4]
def baseStart_3353167 : Nat := 118140960795 + 3353167 * 2 ^ 59
def prefixEnd_3353167 : Nat := 4983230072969 + 3 ^ 40 * 3353167 * 2
def baseEnd_3353167 : Nat := 1147857590529858301594381

theorem tailTrace_3353167 : CollatzResearch.WordTrace tailWord_3353167 prefixEnd_3353167 1147857590529858301594381 := by
  unfold tailWord_3353167
  simp only [CollatzResearch.WordTrace]
  refine ⟨122300047843056109175697755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81533365228704072783798503 122300047843056109175697755)
  ·
    refine ⟨183450071764584163763546633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122300047843056109175697755 183450071764584163763546633)
    ·
      refine ⟨137587553823438122822659975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183450071764584163763546633 137587553823438122822659975)
      ·
        refine ⟨206381330735157184233989963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137587553823438122822659975 206381330735157184233989963)
        ·
          refine ⟨309571996102735776350984945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206381330735157184233989963 309571996102735776350984945)
          ·
            refine ⟨232178997077051832263238709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309571996102735776350984945 232178997077051832263238709)
            ·
              refine ⟨21766780975973609274678629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232178997077051832263238709 21766780975973609274678629)
              ·
                refine ⟨4081271432995051739002243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21766780975973609274678629 4081271432995051739002243)
                ·
                  refine ⟨6121907149492577608503365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4081271432995051739002243 6121907149492577608503365)
                  ·
                    refine ⟨1147857590529858301594381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6121907149492577608503365 1147857590529858301594381)
                    ·
                      rfl

theorem cell22_3353167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 4].length) (baseStart_3353167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353167 prefixEnd_3353167 := by exact prefixLift 3353167
  have htrace : WordTrace (prefixWord ++ tailWord_3353167) baseStart_3353167 baseEnd_3353167 := by
    simpa [prefixWord, tailWord_3353167, baseEnd_3353167] using wordTrace_append hprefix tailTrace_3353167
  have hstable : (prefixWord ++ tailWord_3353167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353167).length < 2 ^ (prefixWord ++ tailWord_3353167).sum := by decide
  have hdescent : baseEnd_3353167 < baseStart_3353167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353195 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 3, 6]
def baseStart_3353195 : Nat := 118140960795 + 3353195 * 2 ^ 59
def prefixEnd_3353195 : Nat := 4983230072969 + 3 ^ 40 * 3353195 * 2
def baseEnd_3353195 : Nat := 1147867175502075561894295

theorem tailTrace_3353195 : CollatzResearch.WordTrace tailWord_3353195 prefixEnd_3353195 1147867175502075561894295 := by
  unfold tailWord_3353195
  simp only [CollatzResearch.WordTrace]
  refine ⟨122301069086954669957717039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81534046057969779971811359 122301069086954669957717039)
  ·
    refine ⟨183451603630432004936575559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122301069086954669957717039 183451603630432004936575559)
    ·
      refine ⟨275177405445648007404863339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183451603630432004936575559 275177405445648007404863339)
      ·
        refine ⟨412766108168472011107295009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275177405445648007404863339 412766108168472011107295009)
        ·
          refine ⟨309574581126354008330471257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412766108168472011107295009 309574581126354008330471257)
          ·
            refine ⟨232180935844765506247853443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309574581126354008330471257 232180935844765506247853443)
            ·
              refine ⟨348271403767148259371780165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232180935844765506247853443 348271403767148259371780165)
              ·
                refine ⟨65300888206340298632208781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 348271403767148259371780165 65300888206340298632208781)
                ·
                  refine ⟨24487833077377611987078293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65300888206340298632208781 24487833077377611987078293)
                  ·
                    refine ⟨1147867175502075561894295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24487833077377611987078293 1147867175502075561894295)
                    ·
                      rfl

theorem cell22_3353195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 6].length) (baseStart_3353195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353195 prefixEnd_3353195 := by exact prefixLift 3353195
  have htrace : WordTrace (prefixWord ++ tailWord_3353195) baseStart_3353195 baseEnd_3353195 := by
    simpa [prefixWord, tailWord_3353195, baseEnd_3353195] using wordTrace_append hprefix tailTrace_3353195
  have hstable : (prefixWord ++ tailWord_3353195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353195).length < 2 ^ (prefixWord ++ tailWord_3353195).sum := by decide
  have hdescent : baseEnd_3353195 < baseStart_3353195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353334 : List Nat := [5, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_3353334 : Nat := 118140960795 + 3353334 * 2 ^ 59
def prefixEnd_3353334 : Nat := 4983230072969 + 3 ^ 40 * 3353334 * 2
def baseEnd_3353334 : Nat := 382638252680908510889623

theorem tailTrace_3353334 : CollatzResearch.WordTrace tailWord_3353334 prefixEnd_3353334 382638252680908510889623 := by
  unfold tailWord_3353334
  simp only [CollatzResearch.WordTrace]
  refine ⟨7644133677090693543564191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81537425888967397798018037 7644133677090693543564191)
  ·
    refine ⟨11466200515636040315346287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7644133677090693543564191 11466200515636040315346287)
    ·
      refine ⟨17199300773454060473019431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11466200515636040315346287 17199300773454060473019431)
      ·
        refine ⟨25798951160181090709529147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17199300773454060473019431 25798951160181090709529147)
        ·
          refine ⟨38698426740271636064293721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25798951160181090709529147 38698426740271636064293721)
          ·
            refine ⟨29023820055203727048220291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38698426740271636064293721 29023820055203727048220291)
            ·
              refine ⟨43535730082805590572330437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29023820055203727048220291 43535730082805590572330437)
              ·
                refine ⟨8162949390526048232311957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43535730082805590572330437 8162949390526048232311957)
                ·
                  refine ⟨382638252680908510889623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8162949390526048232311957 382638252680908510889623)
                  ·
                    rfl

theorem cell22_3353334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_3353334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353334 prefixEnd_3353334 := by exact prefixLift 3353334
  have htrace : WordTrace (prefixWord ++ tailWord_3353334) baseStart_3353334 baseEnd_3353334 := by
    simpa [prefixWord, tailWord_3353334, baseEnd_3353334] using wordTrace_append hprefix tailTrace_3353334
  have hstable : (prefixWord ++ tailWord_3353334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353334).length < 2 ^ (prefixWord ++ tailWord_3353334).sum := by decide
  have hdescent : baseEnd_3353334 < baseStart_3353334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353424 : List Nat := [2, 1, 1, 1, 1, 4, 3, 4, 5]
def baseStart_3353424 : Nat := 118140960795 + 3353424 * 2 ^ 59
def prefixEnd_3353424 : Nat := 4983230072969 + 3 ^ 40 * 3353424 * 2
def baseEnd_3353424 : Nat := 382648522293998432639531

theorem tailTrace_3353424 : CollatzResearch.WordTrace tailWord_3353424 prefixEnd_3353424 382648522293998432639531 := by
  unfold tailWord_3353424
  simp only [CollatzResearch.WordTrace]
  refine ⟨61154710701562521033901663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81539614268750028045202217 61154710701562521033901663)
  ·
    refine ⟨91732066052343781550852495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61154710701562521033901663 91732066052343781550852495)
    ·
      refine ⟨137598099078515672326278743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91732066052343781550852495 137598099078515672326278743)
      ·
        refine ⟨206397148617773508489418115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137598099078515672326278743 206397148617773508489418115)
        ·
          refine ⟨309595722926660262734127173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206397148617773508489418115 309595722926660262734127173)
          ·
            refine ⟨58049198048748799262648845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 309595722926660262734127173 58049198048748799262648845)
            ·
              refine ⟨21768449268280799723493317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58049198048748799262648845 21768449268280799723493317)
              ·
                refine ⟨4081584237802649948154997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21768449268280799723493317 4081584237802649948154997)
                ·
                  refine ⟨382648522293998432639531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4081584237802649948154997 382648522293998432639531)
                  ·
                    rfl

theorem cell22_3353424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 5].length) (baseStart_3353424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353424 prefixEnd_3353424 := by exact prefixLift 3353424
  have htrace : WordTrace (prefixWord ++ tailWord_3353424) baseStart_3353424 baseEnd_3353424 := by
    simpa [prefixWord, tailWord_3353424, baseEnd_3353424] using wordTrace_append hprefix tailTrace_3353424
  have hstable : (prefixWord ++ tailWord_3353424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353424).length < 2 ^ (prefixWord ++ tailWord_3353424).sum := by decide
  have hdescent : baseEnd_3353424 < baseStart_3353424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353439 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 2, 5]
def baseStart_3353439 : Nat := 118140960795 + 3353439 * 2 ^ 59
def prefixEnd_3353439 : Nat := 4983230072969 + 3 ^ 40 * 3353439 * 2
def baseEnd_3353439 : Nat := 1147950701688540258793547

theorem tailTrace_3353439 : CollatzResearch.WordTrace tailWord_3353439 prefixEnd_3353439 1147950701688540258793547 := by
  unfold tailWord_3353439
  simp only [CollatzResearch.WordTrace]
  refine ⟨122309968498070699629599371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81539978998713799753066247 122309968498070699629599371)
  ·
    refine ⟨183464952747106049444399057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122309968498070699629599371 183464952747106049444399057)
    ·
      refine ⟨137598714560329537083299293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183464952747106049444399057 137598714560329537083299293)
      ·
        refine ⟨51599517960123576406237235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137598714560329537083299293 51599517960123576406237235)
        ·
          refine ⟨77399276940185364609355853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51599517960123576406237235 77399276940185364609355853)
          ·
            refine ⟨29024728852569511728508445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77399276940185364609355853 29024728852569511728508445)
            ·
              refine ⟨10884273319713566898190667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29024728852569511728508445 10884273319713566898190667)
              ·
                refine ⟨16326409979570350347286001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10884273319713566898190667 16326409979570350347286001)
                ·
                  refine ⟨12244807484677762760464501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16326409979570350347286001 12244807484677762760464501)
                  ·
                    refine ⟨1147950701688540258793547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12244807484677762760464501 1147950701688540258793547)
                    ·
                      rfl

theorem cell22_3353439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_3353439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353439 prefixEnd_3353439 := by exact prefixLift 3353439
  have htrace : WordTrace (prefixWord ++ tailWord_3353439) baseStart_3353439 baseEnd_3353439 := by
    simpa [prefixWord, tailWord_3353439, baseEnd_3353439] using wordTrace_append hprefix tailTrace_3353439
  have hstable : (prefixWord ++ tailWord_3353439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353439).length < 2 ^ (prefixWord ++ tailWord_3353439).sum := by decide
  have hdescent : baseEnd_3353439 < baseStart_3353439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353462 : List Nat := [5, 1, 1, 3, 1, 2, 2, 3, 1, 3]
def baseStart_3353462 : Nat := 118140960795 + 3353462 * 2 ^ 59
def prefixEnd_3353462 : Nat := 4983230072969 + 3 ^ 40 * 3353462 * 2
def baseEnd_3353462 : Nat := 1147958575058575865468477

theorem tailTrace_3353462 : CollatzResearch.WordTrace tailWord_3353462 prefixEnd_3353462 1147958575058575865468477 := by
  unfold tailWord_3353462
  simp only [CollatzResearch.WordTrace]
  refine ⟨7644425461061710909855415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81540538251324916371791093 7644425461061710909855415)
  ·
    refine ⟨11466638191592566364783123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7644425461061710909855415 11466638191592566364783123)
    ·
      refine ⟨17199957287388849547174685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11466638191592566364783123 17199957287388849547174685)
      ·
        refine ⟨6449983982770818580190507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17199957287388849547174685 6449983982770818580190507)
        ·
          refine ⟨9674975974156227870285761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6449983982770818580190507 9674975974156227870285761)
          ·
            refine ⟨7256231980617170902714321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9674975974156227870285761 7256231980617170902714321)
            ·
              refine ⟨5442173985462878177035741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7256231980617170902714321 5442173985462878177035741)
              ·
                refine ⟨2040815244548579316388403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5442173985462878177035741 2040815244548579316388403)
                ·
                  refine ⟨3061222866822868974582605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2040815244548579316388403 3061222866822868974582605)
                  ·
                    refine ⟨1147958575058575865468477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3061222866822868974582605 1147958575058575865468477)
                    ·
                      rfl

theorem cell22_3353462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_3353462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353462 prefixEnd_3353462 := by exact prefixLift 3353462
  have htrace : WordTrace (prefixWord ++ tailWord_3353462) baseStart_3353462 baseEnd_3353462 := by
    simpa [prefixWord, tailWord_3353462, baseEnd_3353462] using wordTrace_append hprefix tailTrace_3353462
  have hstable : (prefixWord ++ tailWord_3353462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353462).length < 2 ^ (prefixWord ++ tailWord_3353462).sum := by decide
  have hdescent : baseEnd_3353462 < baseStart_3353462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353484 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 3, 5]
def baseStart_3353484 : Nat := 118140960795 + 3353484 * 2 ^ 59
def prefixEnd_3353484 : Nat := 4983230072969 + 3 ^ 40 * 3353484 * 2
def baseEnd_3353484 : Nat := 1147966106108175141418409

theorem tailTrace_3353484 : CollatzResearch.WordTrace tailWord_3353484 prefixEnd_3353484 1147966106108175141418409 := by
  unfold tailWord_3353484
  simp only [CollatzResearch.WordTrace]
  refine ⟨61155804891453836157493753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81541073188605114876658337 61155804891453836157493753)
  ·
    refine ⟨45866853668590377118120315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61155804891453836157493753 45866853668590377118120315)
    ·
      refine ⟨68800280502885565677180473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45866853668590377118120315 68800280502885565677180473)
      ·
        refine ⟨51600210377164174257885355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68800280502885565677180473 51600210377164174257885355)
        ·
          refine ⟨77400315565746261386828033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51600210377164174257885355 77400315565746261386828033)
          ·
            refine ⟨58050236674309696040121025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77400315565746261386828033 58050236674309696040121025)
            ·
              refine ⟨43537677505732272030090769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58050236674309696040121025 43537677505732272030090769)
              ·
                refine ⟨32653258129299204022568077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43537677505732272030090769 32653258129299204022568077)
                ·
                  refine ⟨12244971798487201508463029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32653258129299204022568077 12244971798487201508463029)
                  ·
                    refine ⟨1147966106108175141418409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12244971798487201508463029 1147966106108175141418409)
                    ·
                      rfl

theorem cell22_3353484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_3353484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353484 prefixEnd_3353484 := by exact prefixLift 3353484
  have htrace : WordTrace (prefixWord ++ tailWord_3353484) baseStart_3353484 baseEnd_3353484 := by
    simpa [prefixWord, tailWord_3353484, baseEnd_3353484] using wordTrace_append hprefix tailTrace_3353484
  have hstable : (prefixWord ++ tailWord_3353484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353484).length < 2 ^ (prefixWord ++ tailWord_3353484).sum := by decide
  have hdescent : baseEnd_3353484 < baseStart_3353484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353533 : List Nat := [1, 4, 1, 2, 4, 1, 1, 2, 2, 4]
def baseStart_3353533 : Nat := 118140960795 + 3353533 * 2 ^ 59
def prefixEnd_3353533 : Nat := 4983230072969 + 3 ^ 40 * 3353533 * 2
def baseEnd_3353533 : Nat := 1147982879809555346943259

theorem tailTrace_3353533 : CollatzResearch.WordTrace tailWord_3353533 prefixEnd_3353533 1147982879809555346943259 := by
  unfold tailWord_3353533
  simp only [CollatzResearch.WordTrace]
  refine ⟨122313396959730153683521253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81542264639820102455680835 122313396959730153683521253)
  ·
    refine ⟨22933761929949403815660235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122313396959730153683521253 22933761929949403815660235)
    ·
      refine ⟨34400642894924105723490353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22933761929949403815660235 34400642894924105723490353)
      ·
        refine ⟨25800482171193079292617765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34400642894924105723490353 25800482171193079292617765)
        ·
          refine ⟨4837590407098702367365831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25800482171193079292617765 4837590407098702367365831)
          ·
            refine ⟨7256385610648053551048747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4837590407098702367365831 7256385610648053551048747)
            ·
              refine ⟨10884578415972080326573121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7256385610648053551048747 10884578415972080326573121)
              ·
                refine ⟨8163433811979060244929841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10884578415972080326573121 8163433811979060244929841)
                ·
                  refine ⟨6122575358984295183697381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8163433811979060244929841 6122575358984295183697381)
                  ·
                    refine ⟨1147982879809555346943259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6122575358984295183697381 1147982879809555346943259)
                    ·
                      rfl

theorem cell22_3353533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_3353533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353533 prefixEnd_3353533 := by exact prefixLift 3353533
  have htrace : WordTrace (prefixWord ++ tailWord_3353533) baseStart_3353533 baseEnd_3353533 := by
    simpa [prefixWord, tailWord_3353533, baseEnd_3353533] using wordTrace_append hprefix tailTrace_3353533
  have hstable : (prefixWord ++ tailWord_3353533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353533).length < 2 ^ (prefixWord ++ tailWord_3353533).sum := by decide
  have hdescent : baseEnd_3353533 < baseStart_3353533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353559 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 9]
def baseStart_3353559 : Nat := 118140960795 + 3353559 * 2 ^ 59
def prefixEnd_3353559 : Nat := 4983230072969 + 3 ^ 40 * 3353559 * 2
def baseEnd_3353559 : Nat := 382663926713633315264393

theorem tailTrace_3353559 : CollatzResearch.WordTrace tailWord_3353559 prefixEnd_3353559 382663926713633315264393 := by
  unfold tailWord_3353559
  simp only [CollatzResearch.WordTrace]
  refine ⟨122314345257635960123967731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81542896838423973415978487 122314345257635960123967731)
  ·
    refine ⟨183471517886453940185951597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122314345257635960123967731 183471517886453940185951597)
    ·
      refine ⟨68801819207420227569731849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183471517886453940185951597 68801819207420227569731849)
      ·
        refine ⟨51601364405565170677298887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68801819207420227569731849 51601364405565170677298887)
        ·
          refine ⟨77402046608347756015948331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51601364405565170677298887 77402046608347756015948331)
          ·
            refine ⟨116103069912521634023922497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77402046608347756015948331 116103069912521634023922497)
            ·
              refine ⟨87077302434391225517941873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116103069912521634023922497 87077302434391225517941873)
              ·
                refine ⟨65307976825793419138456405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87077302434391225517941873 65307976825793419138456405)
                ·
                  refine ⟨382663926713633315264393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65307976825793419138456405 382663926713633315264393)
                  ·
                    rfl

theorem cell22_3353559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 9].length) (baseStart_3353559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353559 prefixEnd_3353559 := by exact prefixLift 3353559
  have htrace : WordTrace (prefixWord ++ tailWord_3353559) baseStart_3353559 baseEnd_3353559 := by
    simpa [prefixWord, tailWord_3353559, baseEnd_3353559] using wordTrace_append hprefix tailTrace_3353559
  have hstable : (prefixWord ++ tailWord_3353559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353559).length < 2 ^ (prefixWord ++ tailWord_3353559).sum := by decide
  have hdescent : baseEnd_3353559 < baseStart_3353559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353588 : List Nat := [2, 6, 2, 1, 1, 2, 2, 2, 4]
def baseStart_3353588 : Nat := 118140960795 + 3353588 * 2 ^ 59
def prefixEnd_3353588 : Nat := 4983230072969 + 3 ^ 40 * 3353588 * 2
def baseEnd_3353588 : Nat := 382667235811184512272697

theorem tailTrace_3353588 : CollatzResearch.WordTrace tailWord_3353588 prefixEnd_3353588 382667235811184512272697 := by
  unfold tailWord_3353588
  simp only [CollatzResearch.WordTrace]
  refine ⟨61157701487265449038386709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81543601983020598717848945 61157701487265449038386709)
  ·
    refine ⟨2866767257215567923674377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61157701487265449038386709 2866767257215567923674377)
    ·
      refine ⟨2150075442911675942755783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2866767257215567923674377 2150075442911675942755783)
      ·
        refine ⟨3225113164367513914133675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2150075442911675942755783 3225113164367513914133675)
        ·
          refine ⟨4837669746551270871200513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3225113164367513914133675 4837669746551270871200513)
          ·
            refine ⟨3628252309913453153400385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4837669746551270871200513 3628252309913453153400385)
            ·
              refine ⟨2721189232435089865050289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3628252309913453153400385 2721189232435089865050289)
              ·
                refine ⟨2040891924326317398787717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2721189232435089865050289 2040891924326317398787717)
                ·
                  refine ⟨382667235811184512272697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2040891924326317398787717 382667235811184512272697)
                  ·
                    rfl

theorem cell22_3353588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_3353588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353588 prefixEnd_3353588 := by exact prefixLift 3353588
  have htrace : WordTrace (prefixWord ++ tailWord_3353588) baseStart_3353588 baseEnd_3353588 := by
    simpa [prefixWord, tailWord_3353588, baseEnd_3353588] using wordTrace_append hprefix tailTrace_3353588
  have hstable : (prefixWord ++ tailWord_3353588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353588).length < 2 ^ (prefixWord ++ tailWord_3353588).sum := by decide
  have hdescent : baseEnd_3353588 < baseStart_3353588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353621 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 8]
def baseStart_3353621 : Nat := 118140960795 + 3353621 * 2 ^ 59
def prefixEnd_3353621 : Nat := 4983230072969 + 3 ^ 40 * 3353621 * 2
def baseEnd_3353621 : Nat := 382671001335984150247663

theorem tailTrace_3353621 : CollatzResearch.WordTrace tailWord_3353621 prefixEnd_3353621 382671001335984150247663 := by
  unfold tailWord_3353621
  simp only [CollatzResearch.WordTrace]
  refine ⟨122316606583411344712724717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81544404388940896475149811 122316606583411344712724717)
  ·
    refine ⟨45868727468779254267271769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122316606583411344712724717 45868727468779254267271769)
    ·
      refine ⟨34401545601584440700453827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45868727468779254267271769 34401545601584440700453827)
      ·
        refine ⟨51602318402376661050680741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34401545601584440700453827 51602318402376661050680741)
        ·
          refine ⟨9675434700445623947002639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51602318402376661050680741 9675434700445623947002639)
          ·
            refine ⟨14513152050668435920503959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9675434700445623947002639 14513152050668435920503959)
            ·
              refine ⟨21769728076002653880755939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14513152050668435920503959 21769728076002653880755939)
              ·
                refine ⟨32654592114003980821133909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21769728076002653880755939 32654592114003980821133909)
                ·
                  refine ⟨382671001335984150247663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32654592114003980821133909 382671001335984150247663)
                  ·
                    rfl

theorem cell22_3353621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_3353621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353621 prefixEnd_3353621 := by exact prefixLift 3353621
  have htrace : WordTrace (prefixWord ++ tailWord_3353621) baseStart_3353621 baseEnd_3353621 := by
    simpa [prefixWord, tailWord_3353621, baseEnd_3353621] using wordTrace_append hprefix tailTrace_3353621
  have hstable : (prefixWord ++ tailWord_3353621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353621).length < 2 ^ (prefixWord ++ tailWord_3353621).sum := by decide
  have hdescent : baseEnd_3353621 < baseStart_3353621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353623 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 3, 4]
def baseStart_3353623 : Nat := 118140960795 + 3353623 * 2 ^ 59
def prefixEnd_3353623 : Nat := 4983230072969 + 3 ^ 40 * 3353623 * 2
def baseEnd_3353623 : Nat := 1148013688648825112192983

theorem tailTrace_3353623 : CollatzResearch.WordTrace tailWord_3353623 prefixEnd_3353623 1148013688648825112192983 := by
  unfold tailWord_3353623
  simp only [CollatzResearch.WordTrace]
  refine ⟨122316679529404099054297523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81544453019602732702865015 122316679529404099054297523)
  ·
    refine ⟨183475019294106148581446285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122316679529404099054297523 183475019294106148581446285)
    ·
      refine ⟨68803132235289805718042357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183475019294106148581446285 68803132235289805718042357)
      ·
        refine ⟨6450293647058419286066471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68803132235289805718042357 6450293647058419286066471)
        ·
          refine ⟨9675440470587628929099707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6450293647058419286066471 9675440470587628929099707)
          ·
            refine ⟨14513160705881443393649561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9675440470587628929099707 14513160705881443393649561)
            ·
              refine ⟨10884870529411082545237171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14513160705881443393649561 10884870529411082545237171)
              ·
                refine ⟨16327305794116623817855757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10884870529411082545237171 16327305794116623817855757)
                ·
                  refine ⟨6122739672793733931695909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16327305794116623817855757 6122739672793733931695909)
                  ·
                    refine ⟨1148013688648825112192983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6122739672793733931695909 1148013688648825112192983)
                    ·
                      rfl

theorem cell22_3353623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_3353623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353623 prefixEnd_3353623 := by exact prefixLift 3353623
  have htrace : WordTrace (prefixWord ++ tailWord_3353623) baseStart_3353623 baseEnd_3353623 := by
    simpa [prefixWord, tailWord_3353623, baseEnd_3353623] using wordTrace_append hprefix tailTrace_3353623
  have hstable : (prefixWord ++ tailWord_3353623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353623).length < 2 ^ (prefixWord ++ tailWord_3353623).sum := by decide
  have hdescent : baseEnd_3353623 < baseStart_3353623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353651 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 4, 4]
def baseStart_3353651 : Nat := 118140960795 + 3353651 * 2 ^ 59
def prefixEnd_3353651 : Nat := 4983230072969 + 3 ^ 40 * 3353651 * 2
def baseEnd_3353651 : Nat := 1148023273621042372492897

theorem tailTrace_3353651 : CollatzResearch.WordTrace tailWord_3353651 prefixEnd_3353651 1148023273621042372492897 := by
  unfold tailWord_3353651
  simp only [CollatzResearch.WordTrace]
  refine ⟨122317700773302659836316807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81545133848868439890877871 122317700773302659836316807)
  ·
    refine ⟨183476551159953989754475211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122317700773302659836316807 183476551159953989754475211)
    ·
      refine ⟨275214826739930984631712817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183476551159953989754475211 275214826739930984631712817)
      ·
        refine ⟨206411120054948238473784613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275214826739930984631712817 206411120054948238473784613)
        ·
          refine ⟨38702085010302794713834615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206411120054948238473784613 38702085010302794713834615)
          ·
            refine ⟨58053127515454192070751923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38702085010302794713834615 58053127515454192070751923)
            ·
              refine ⟨87079691273181288106127885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58053127515454192070751923 87079691273181288106127885)
              ·
                refine ⟨32654884227442983039797957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87079691273181288106127885 32654884227442983039797957)
                ·
                  refine ⟨6122790792645559319962117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32654884227442983039797957 6122790792645559319962117)
                  ·
                    refine ⟨1148023273621042372492897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6122790792645559319962117 1148023273621042372492897)
                    ·
                      rfl

theorem cell22_3353651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 4].length) (baseStart_3353651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353651 prefixEnd_3353651 := by exact prefixLift 3353651
  have htrace : WordTrace (prefixWord ++ tailWord_3353651) baseStart_3353651 baseEnd_3353651 := by
    simpa [prefixWord, tailWord_3353651, baseEnd_3353651] using wordTrace_append hprefix tailTrace_3353651
  have hstable : (prefixWord ++ tailWord_3353651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353651).length < 2 ^ (prefixWord ++ tailWord_3353651).sum := by decide
  have hdescent : baseEnd_3353651 < baseStart_3353651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353711 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 7]
def baseStart_3353711 : Nat := 118140960795 + 3353711 * 2 ^ 59
def prefixEnd_3353711 : Nat := 4983230072969 + 3 ^ 40 * 3353711 * 2
def baseEnd_3353711 : Nat := 382681270949074071997571

theorem tailTrace_3353711 : CollatzResearch.WordTrace tailWord_3353711 prefixEnd_3353711 382681270949074071997571 := by
  unfold tailWord_3353711
  simp only [CollatzResearch.WordTrace]
  refine ⟨122319889153085290083500987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81546592768723526722333991 122319889153085290083500987)
  ·
    refine ⟨183479833729627935125251481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122319889153085290083500987 183479833729627935125251481)
    ·
      refine ⟨137609875297220951343938611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183479833729627935125251481 137609875297220951343938611)
      ·
        refine ⟨206414812945831427015907917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137609875297220951343938611 206414812945831427015907917)
        ·
          refine ⟨77405554854686785130965469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206414812945831427015907917 77405554854686785130965469)
          ·
            refine ⟨29027083070507544424112051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77405554854686785130965469 29027083070507544424112051)
            ·
              refine ⟨43540624605761316636168077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29027083070507544424112051 43540624605761316636168077)
              ·
                refine ⟨16327734227160493738563029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43540624605761316636168077 16327734227160493738563029)
                ·
                  refine ⟨382681270949074071997571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16327734227160493738563029 382681270949074071997571)
                  ·
                    rfl

theorem cell22_3353711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 7].length) (baseStart_3353711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353711 prefixEnd_3353711 := by exact prefixLift 3353711
  have htrace : WordTrace (prefixWord ++ tailWord_3353711) baseStart_3353711 baseEnd_3353711 := by
    simpa [prefixWord, tailWord_3353711, baseEnd_3353711] using wordTrace_append hprefix tailTrace_3353711
  have hstable : (prefixWord ++ tailWord_3353711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353711).length < 2 ^ (prefixWord ++ tailWord_3353711).sum := by decide
  have hdescent : baseEnd_3353711 < baseStart_3353711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353762 : List Nat := [3, 3, 1, 3, 2, 1, 2, 2, 5]
def baseStart_3353762 : Nat := 118140960795 + 3353762 * 2 ^ 59
def prefixEnd_3353762 : Nat := 4983230072969 + 3 ^ 40 * 3353762 * 2
def baseEnd_3353762 : Nat := 382687090396491694322519

theorem tailTrace_3353762 : CollatzResearch.WordTrace tailWord_3353762 prefixEnd_3353762 382687090396491694322519 := by
  unfold tailWord_3353762
  simp only [CollatzResearch.WordTrace]
  refine ⟨30580437318975131448401885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81547832850600350529071693 30580437318975131448401885)
  ·
    refine ⟨11467663994615674293150707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30580437318975131448401885 11467663994615674293150707)
    ·
      refine ⟨17201495991923511439726061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11467663994615674293150707 17201495991923511439726061)
      ·
        refine ⟨6450560996971316789897273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17201495991923511439726061 6450560996971316789897273)
        ·
          refine ⟨4837920747728487592422955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6450560996971316789897273 4837920747728487592422955)
          ·
            refine ⟨7256881121592731388634433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4837920747728487592422955 7256881121592731388634433)
            ·
              refine ⟨5442660841194548541475825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7256881121592731388634433 5442660841194548541475825)
              ·
                refine ⟨4081995630895911406106869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5442660841194548541475825 4081995630895911406106869)
                ·
                  refine ⟨382687090396491694322519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4081995630895911406106869 382687090396491694322519)
                  ·
                    rfl

theorem cell22_3353762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_3353762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353762 prefixEnd_3353762 := by exact prefixLift 3353762
  have htrace : WordTrace (prefixWord ++ tailWord_3353762) baseStart_3353762 baseEnd_3353762 := by
    simpa [prefixWord, tailWord_3353762, baseEnd_3353762] using wordTrace_append hprefix tailTrace_3353762
  have hstable : (prefixWord ++ tailWord_3353762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353762).length < 2 ^ (prefixWord ++ tailWord_3353762).sum := by decide
  have hdescent : baseEnd_3353762 < baseStart_3353762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353790 : List Nat := [4, 2, 1, 1, 3, 2, 1, 2, 6]
def baseStart_3353790 : Nat := 118140960795 + 3353790 * 2 ^ 59
def prefixEnd_3353790 : Nat := 4983230072969 + 3 ^ 40 * 3353790 * 2
def baseEnd_3353790 : Nat := 382690285387230781089157

theorem tailTrace_3353790 : CollatzResearch.WordTrace tailWord_3353790 prefixEnd_3353790 382690285387230781089157 := by
  unfold tailWord_3353790
  simp only [CollatzResearch.WordTrace]
  refine ⟨15290346314974885821953353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81548513679866057717084549 15290346314974885821953353)
  ·
    refine ⟨11467759736231164366465015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15290346314974885821953353 11467759736231164366465015)
    ·
      refine ⟨17201639604346746549697523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11467759736231164366465015 17201639604346746549697523)
      ·
        refine ⟨25802459406520119824546285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17201639604346746549697523 25802459406520119824546285)
        ·
          refine ⟨9675922277445044934204857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25802459406520119824546285 9675922277445044934204857)
          ·
            refine ⟨7256941708083783700653643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9675922277445044934204857 7256941708083783700653643)
            ·
              refine ⟨10885412562125675550980465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7256941708083783700653643 10885412562125675550980465)
              ·
                refine ⟨8164059421594256663235349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10885412562125675550980465 8164059421594256663235349)
                ·
                  refine ⟨382690285387230781089157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8164059421594256663235349 382690285387230781089157)
                  ·
                    rfl

theorem cell22_3353790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_3353790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353790 prefixEnd_3353790 := by exact prefixLift 3353790
  have htrace : WordTrace (prefixWord ++ tailWord_3353790) baseStart_3353790 baseEnd_3353790 := by
    simpa [prefixWord, tailWord_3353790, baseEnd_3353790] using wordTrace_append hprefix tailTrace_3353790
  have hstable : (prefixWord ++ tailWord_3353790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353790).length < 2 ^ (prefixWord ++ tailWord_3353790).sum := by decide
  have hdescent : baseEnd_3353790 < baseStart_3353790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353803 : List Nat := [1, 1, 1, 1, 3, 2, 2, 5, 2, 4]
def baseStart_3353803 : Nat := 118140960795 + 3353803 * 2 ^ 59
def prefixEnd_3353803 : Nat := 4983230072969 + 3 ^ 40 * 3353803 * 2
def baseEnd_3353803 : Nat := 1148075306327364642692431

theorem tailTrace_3353803 : CollatzResearch.WordTrace tailWord_3353803 prefixEnd_3353803 1148075306327364642692431 := by
  unfold tailWord_3353803
  simp only [CollatzResearch.WordTrace]
  refine ⟨122323244668751989795850063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81548829779167993197233375 122323244668751989795850063)
  ·
    refine ⟨183484867003127984693775095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122323244668751989795850063 183484867003127984693775095)
    ·
      refine ⟨275227300504691977040662643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183484867003127984693775095 275227300504691977040662643)
      ·
        refine ⟨412840950757037965560993965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275227300504691977040662643 412840950757037965560993965)
        ·
          refine ⟨154815356533889237085372737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 412840950757037965560993965 154815356533889237085372737)
          ·
            refine ⟨116111517400416927814029553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154815356533889237085372737 116111517400416927814029553)
            ·
              refine ⟨87083638050312695860522165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116111517400416927814029553 87083638050312695860522165)
              ·
                refine ⟨8164091067216815236923953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87083638050312695860522165 8164091067216815236923953)
                ·
                  refine ⟨6123068300412611427692965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8164091067216815236923953 6123068300412611427692965)
                  ·
                    refine ⟨1148075306327364642692431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6123068300412611427692965 1148075306327364642692431)
                    ·
                      rfl

theorem cell22_3353803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 4].length) (baseStart_3353803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353803 prefixEnd_3353803 := by exact prefixLift 3353803
  have htrace : WordTrace (prefixWord ++ tailWord_3353803) baseStart_3353803 baseEnd_3353803 := by
    simpa [prefixWord, tailWord_3353803, baseEnd_3353803] using wordTrace_append hprefix tailTrace_3353803
  have hstable : (prefixWord ++ tailWord_3353803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353803).length < 2 ^ (prefixWord ++ tailWord_3353803).sum := by decide
  have hdescent : baseEnd_3353803 < baseStart_3353803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353839 : List Nat := [1, 1, 2, 1, 7, 1, 3, 1, 2, 3]
def baseStart_3353839 : Nat := 118140960795 + 3353839 * 2 ^ 59
def prefixEnd_3353839 : Nat := 4983230072969 + 3 ^ 40 * 3353839 * 2
def baseEnd_3353839 : Nat := 1148087629863072548792321

theorem tailTrace_3353839 : CollatzResearch.WordTrace tailWord_3353839 prefixEnd_3353839 1148087629863072548792321 := by
  unfold tailWord_3353839
  simp only [CollatzResearch.WordTrace]
  refine ⟨122324557696621567944160571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81549705131081045296107047 122324557696621567944160571)
  ·
    refine ⟨183486836544932351916240857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122324557696621567944160571 183486836544932351916240857)
    ·
      refine ⟨137615127408699263937180643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183486836544932351916240857 137615127408699263937180643)
      ·
        refine ⟨206422691113048895905770965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137615127408699263937180643 206422691113048895905770965)
        ·
          refine ⟨4838031822962083497791507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 206422691113048895905770965 4838031822962083497791507)
          ·
            refine ⟨7257047734443125246687261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4838031822962083497791507 7257047734443125246687261)
            ·
              refine ⟨2721392900416171967507723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7257047734443125246687261 2721392900416171967507723)
              ·
                refine ⟨4082089350624257951261585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2721392900416171967507723 4082089350624257951261585)
                ·
                  refine ⟨3061567012968193463446189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4082089350624257951261585 3061567012968193463446189)
                  ·
                    refine ⟨1148087629863072548792321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3061567012968193463446189 1148087629863072548792321)
                    ·
                      rfl

theorem cell22_3353839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 2, 3].length) (baseStart_3353839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353839 prefixEnd_3353839 := by exact prefixLift 3353839
  have htrace : WordTrace (prefixWord ++ tailWord_3353839) baseStart_3353839 baseEnd_3353839 := by
    simpa [prefixWord, tailWord_3353839, baseEnd_3353839] using wordTrace_append hprefix tailTrace_3353839
  have hstable : (prefixWord ++ tailWord_3353839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353839).length < 2 ^ (prefixWord ++ tailWord_3353839).sum := by decide
  have hdescent : baseEnd_3353839 < baseStart_3353839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353850 : List Nat := [3, 1, 1, 1, 1, 4, 1, 4, 3, 3]
def baseStart_3353850 : Nat := 118140960795 + 3353850 * 2 ^ 59
def prefixEnd_3353850 : Nat := 4983230072969 + 3 ^ 40 * 3353850 * 2
def baseEnd_3353850 : Nat := 1148091395387872186767287

theorem tailTrace_3353850 : CollatzResearch.WordTrace tailWord_3353850 prefixEnd_3353850 1148091395387872186767287 := by
  unfold tailWord_3353850
  simp only [CollatzResearch.WordTrace]
  refine ⟨30581239724895429205702751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81549972599721144548540669 30581239724895429205702751)
  ·
    refine ⟨45871859587343143808554127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30581239724895429205702751 45871859587343143808554127)
    ·
      refine ⟨68807789381014715712831191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45871859587343143808554127 68807789381014715712831191)
      ·
        refine ⟨103211684071522073569246787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68807789381014715712831191 103211684071522073569246787)
        ·
          refine ⟨154817526107283110353870181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103211684071522073569246787 154817526107283110353870181)
          ·
            refine ⟨29028286145115583191350659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154817526107283110353870181 29028286145115583191350659)
            ·
              refine ⟨43542429217673374787025989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29028286145115583191350659 43542429217673374787025989)
              ·
                refine ⟨8164205478313757772567373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43542429217673374787025989 8164205478313757772567373)
                ·
                  refine ⟨3061577054367659164712765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8164205478313757772567373 3061577054367659164712765)
                  ·
                    refine ⟨1148091395387872186767287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3061577054367659164712765 1148091395387872186767287)
                    ·
                      rfl

theorem cell22_3353850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_3353850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353850 prefixEnd_3353850 := by exact prefixLift 3353850
  have htrace : WordTrace (prefixWord ++ tailWord_3353850) baseStart_3353850 baseEnd_3353850 := by
    simpa [prefixWord, tailWord_3353850, baseEnd_3353850] using wordTrace_append hprefix tailTrace_3353850
  have hstable : (prefixWord ++ tailWord_3353850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353850).length < 2 ^ (prefixWord ++ tailWord_3353850).sum := by decide
  have hdescent : baseEnd_3353850 < baseStart_3353850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353852 : List Nat := [2, 2, 2, 1, 5, 2, 2, 6]
def baseStart_3353852 : Nat := 118140960795 + 3353852 * 2 ^ 59
def prefixEnd_3353852 : Nat := 4983230072969 + 3 ^ 40 * 3353852 * 2
def baseEnd_3353852 : Nat := 127565786669860538690809

theorem tailTrace_3353852 : CollatzResearch.WordTrace tailWord_3353852 prefixEnd_3353852 127565786669860538690809 := by
  unfold tailWord_3353852
  simp only [CollatzResearch.WordTrace]
  refine ⟨61162515922787235582191905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81550021230382980776255873 61162515922787235582191905)
  ·
    refine ⟨45871886942090426686643929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61162515922787235582191905 45871886942090426686643929)
    ·
      refine ⟨34403915206567820014982947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45871886942090426686643929 34403915206567820014982947)
      ·
        refine ⟨51605872809851730022474421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34403915206567820014982947 51605872809851730022474421)
        ·
          refine ⟨4838050575923599689606977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51605872809851730022474421 4838050575923599689606977)
          ·
            refine ⟨3628537931942699767205233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4838050575923599689606977 3628537931942699767205233)
            ·
              refine ⟨2721403448957024825403925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3628537931942699767205233 2721403448957024825403925)
              ·
                refine ⟨127565786669860538690809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2721403448957024825403925 127565786669860538690809)
                ·
                  rfl

theorem cell22_3353852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 6].length) (baseStart_3353852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353852 prefixEnd_3353852 := by exact prefixLift 3353852
  have htrace : WordTrace (prefixWord ++ tailWord_3353852) baseStart_3353852 baseEnd_3353852 := by
    simpa [prefixWord, tailWord_3353852, baseEnd_3353852] using wordTrace_append hprefix tailTrace_3353852
  have hstable : (prefixWord ++ tailWord_3353852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353852).length < 2 ^ (prefixWord ++ tailWord_3353852).sum := by decide
  have hdescent : baseEnd_3353852 < baseStart_3353852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353940 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_3353940 : Nat := 118140960795 + 3353940 * 2 ^ 59
def prefixEnd_3353940 : Nat := 4983230072969 + 3 ^ 40 * 3353940 * 2
def baseEnd_3353940 : Nat := 1148122204227141952017011

theorem tailTrace_3353940 : CollatzResearch.WordTrace tailWord_3353940 prefixEnd_3353940 1148122204227141952017011 := by
  unfold tailWord_3353940
  simp only [CollatzResearch.WordTrace]
  refine ⟨61164120734627831096793637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81552160979503774795724849 61164120734627831096793637)
  ·
    refine ⟨11468272637742718330648807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61164120734627831096793637 11468272637742718330648807)
    ·
      refine ⟨17202408956614077495973211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11468272637742718330648807 17202408956614077495973211)
      ·
        refine ⟨25803613434921116243959817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17202408956614077495973211 25803613434921116243959817)
        ·
          refine ⟨19352710076190837182969863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25803613434921116243959817 19352710076190837182969863)
          ·
            refine ⟨29029065114286255774454795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19352710076190837182969863 29029065114286255774454795)
            ·
              refine ⟨43543597671429383661682193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29029065114286255774454795 43543597671429383661682193)
              ·
                refine ⟨32657698253572037746261645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43543597671429383661682193 32657698253572037746261645)
                ·
                  refine ⟨12246636845089514154848117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32657698253572037746261645 12246636845089514154848117)
                  ·
                    refine ⟨1148122204227141952017011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12246636845089514154848117 1148122204227141952017011)
                    ·
                      rfl

theorem cell22_3353940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_3353940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353940 prefixEnd_3353940 := by exact prefixLift 3353940
  have htrace : WordTrace (prefixWord ++ tailWord_3353940) baseStart_3353940 baseEnd_3353940 := by
    simpa [prefixWord, tailWord_3353940, baseEnd_3353940] using wordTrace_append hprefix tailTrace_3353940
  have hstable : (prefixWord ++ tailWord_3353940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353940).length < 2 ^ (prefixWord ++ tailWord_3353940).sum := by decide
  have hdescent : baseEnd_3353940 < baseStart_3353940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353957 : List Nat := [1, 3, 1, 3, 1, 2, 1, 5, 2, 3]
def baseStart_3353957 : Nat := 118140960795 + 3353957 * 2 ^ 59
def prefixEnd_3353957 : Nat := 4983230072969 + 3 ^ 40 * 3353957 * 2
def baseEnd_3353957 : Nat := 1148128023674559574341959

theorem tailTrace_3353957 : CollatzResearch.WordTrace tailWord_3353957 prefixEnd_3353957 1148128023674559574341959 := by
  unfold tailWord_3353957
  simp only [CollatzResearch.WordTrace]
  refine ⟨122328861510194074096956125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81552574340129382731304083 122328861510194074096956125)
  ·
    refine ⟨45873323066322777786358547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122328861510194074096956125 45873323066322777786358547)
    ·
      refine ⟨68809984599484166679537821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45873323066322777786358547 68809984599484166679537821)
      ·
        refine ⟨25803744224806562504826683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68809984599484166679537821 25803744224806562504826683)
        ·
          refine ⟨38705616337209843757240025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25803744224806562504826683 38705616337209843757240025)
          ·
            refine ⟨29029212252907382817930019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38705616337209843757240025 29029212252907382817930019)
            ·
              refine ⟨43543818379361074226895029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29029212252907382817930019 43543818379361074226895029)
              ·
                refine ⟨4082232973065100708771409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43543818379361074226895029 4082232973065100708771409)
                ·
                  refine ⟨3061674729798825531578557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4082232973065100708771409 3061674729798825531578557)
                  ·
                    refine ⟨1148128023674559574341959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3061674729798825531578557 1148128023674559574341959)
                    ·
                      rfl

theorem cell22_3353957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_3353957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3353957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3353957 prefixEnd_3353957 := by exact prefixLift 3353957
  have htrace : WordTrace (prefixWord ++ tailWord_3353957) baseStart_3353957 baseEnd_3353957 := by
    simpa [prefixWord, tailWord_3353957, baseEnd_3353957] using wordTrace_append hprefix tailTrace_3353957
  have hstable : (prefixWord ++ tailWord_3353957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353957).length < 2 ^ (prefixWord ++ tailWord_3353957).sum := by decide
  have hdescent : baseEnd_3353957 < baseStart_3353957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354092 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 4, 3]
def baseStart_3354092 : Nat := 118140960795 + 3354092 * 2 ^ 59
def prefixEnd_3354092 : Nat := 4983230072969 + 3 ^ 40 * 3354092 * 2
def baseEnd_3354092 : Nat := 1148174236933464222216545

theorem tailTrace_3354092 : CollatzResearch.WordTrace tailWord_3354092 prefixEnd_3354092 1148174236933464222216545 := by
  unfold tailWord_3354092
  simp only [CollatzResearch.WordTrace]
  refine ⟨61166892682352496076560265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81555856909803328102080353 61166892682352496076560265)
  ·
    refine ⟨45875169511764372057420199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61166892682352496076560265 45875169511764372057420199)
    ·
      refine ⟨68812754267646558086130299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45875169511764372057420199 68812754267646558086130299)
      ·
        refine ⟨103219131401469837129195449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68812754267646558086130299 103219131401469837129195449)
        ·
          refine ⟨77414348551102377846896587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103219131401469837129195449 77414348551102377846896587)
          ·
            refine ⟨116121522826653566770344881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77414348551102377846896587 116121522826653566770344881)
            ·
              refine ⟨87091142119990175077758661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116121522826653566770344881 87091142119990175077758661)
              ·
                refine ⟨16329589147498157827079749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87091142119990175077758661 16329589147498157827079749)
                ·
                  refine ⟨3061797965155904592577453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16329589147498157827079749 3061797965155904592577453)
                  ·
                    refine ⟨1148174236933464222216545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3061797965155904592577453 1148174236933464222216545)
                    ·
                      rfl

theorem cell22_3354092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_3354092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354092 prefixEnd_3354092 := by exact prefixLift 3354092
  have htrace : WordTrace (prefixWord ++ tailWord_3354092) baseStart_3354092 baseEnd_3354092 := by
    simpa [prefixWord, tailWord_3354092, baseEnd_3354092] using wordTrace_append hprefix tailTrace_3354092
  have hstable : (prefixWord ++ tailWord_3354092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354092).length < 2 ^ (prefixWord ++ tailWord_3354092).sum := by decide
  have hdescent : baseEnd_3354092 < baseStart_3354092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354094 : List Nat := [4, 1, 2, 1, 2, 1, 2, 5, 4]
def baseStart_3354094 : Nat := 118140960795 + 3354094 * 2 ^ 59
def prefixEnd_3354094 : Nat := 4983230072969 + 3 ^ 40 * 3354094 * 2
def baseEnd_3354094 : Nat := 382724973858112294555513

theorem tailTrace_3354094 : CollatzResearch.WordTrace tailWord_3354094 prefixEnd_3354094 382724973858112294555513 := by
  unfold tailWord_3354094
  simp only [CollatzResearch.WordTrace]
  refine ⟨15291732288837218311836667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81555905540465164329795557 15291732288837218311836667)
  ·
    refine ⟨22937598433255827467755001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15291732288837218311836667 22937598433255827467755001)
    ·
      refine ⟨17203198824941870600816251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22937598433255827467755001 17203198824941870600816251)
      ·
        refine ⟨25804798237412805901224377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17203198824941870600816251 25804798237412805901224377)
        ·
          refine ⟨19353598678059604425918283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25804798237412805901224377 19353598678059604425918283)
          ·
            refine ⟨29030398017089406638877425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19353598678059604425918283 29030398017089406638877425)
            ·
              refine ⟨21772798512817054979158069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29030398017089406638877425 21772798512817054979158069)
              ·
                refine ⟨2041199860576598904296069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21772798512817054979158069 2041199860576598904296069)
                ·
                  refine ⟨382724973858112294555513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2041199860576598904296069 382724973858112294555513)
                  ·
                    rfl

theorem cell22_3354094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_3354094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354094 prefixEnd_3354094 := by exact prefixLift 3354094
  have htrace : WordTrace (prefixWord ++ tailWord_3354094) baseStart_3354094 baseEnd_3354094 := by
    simpa [prefixWord, tailWord_3354094, baseEnd_3354094] using wordTrace_append hprefix tailTrace_3354094
  have hstable : (prefixWord ++ tailWord_3354094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354094).length < 2 ^ (prefixWord ++ tailWord_3354094).sum := by decide
  have hdescent : baseEnd_3354094 < baseStart_3354094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354109 : List Nat := [1, 4, 1, 1, 1, 4, 1, 4, 2, 3]
def baseStart_3354109 : Nat := 118140960795 + 3354109 * 2 ^ 59
def prefixEnd_3354109 : Nat := 4983230072969 + 3 ^ 40 * 3354109 * 2
def baseEnd_3354109 : Nat := 1148180056380881844541493

theorem tailTrace_3354109 : CollatzResearch.WordTrace tailWord_3354109 prefixEnd_3354109 1148180056380881844541493 := by
  unfold tailWord_3354109
  simp only [CollatzResearch.WordTrace]
  refine ⟨122334405405643404056489381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81556270270428936037659587 122334405405643404056489381)
  ·
    refine ⟨22937701013558138260591759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122334405405643404056489381 22937701013558138260591759)
    ·
      refine ⟨34406551520337207390887639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22937701013558138260591759 34406551520337207390887639)
      ·
        refine ⟨51609827280505811086331459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34406551520337207390887639 51609827280505811086331459)
        ·
          refine ⟨77414740920758716629497189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51609827280505811086331459 77414740920758716629497189)
          ·
            refine ⟨14515263922642259368030723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77414740920758716629497189 14515263922642259368030723)
            ·
              refine ⟨21772895883963389052046085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14515263922642259368030723 21772895883963389052046085)
              ·
                refine ⟨4082417978243135447258641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21772895883963389052046085 4082417978243135447258641)
                ·
                  refine ⟨3061813483682351585443981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4082417978243135447258641 3061813483682351585443981)
                  ·
                    refine ⟨1148180056380881844541493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3061813483682351585443981 1148180056380881844541493)
                    ·
                      rfl

theorem cell22_3354109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_3354109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354109 prefixEnd_3354109 := by exact prefixLift 3354109
  have htrace : WordTrace (prefixWord ++ tailWord_3354109) baseStart_3354109 baseEnd_3354109 := by
    simpa [prefixWord, tailWord_3354109, baseEnd_3354109] using wordTrace_append hprefix tailTrace_3354109
  have hstable : (prefixWord ++ tailWord_3354109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354109).length < 2 ^ (prefixWord ++ tailWord_3354109).sum := by decide
  have hdescent : baseEnd_3354109 < baseStart_3354109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354122 : List Nat := [3, 1, 2, 2, 2, 2, 3, 7]
def baseStart_3354122 : Nat := 118140960795 + 3354122 * 2 ^ 59
def prefixEnd_3354122 : Nat := 4983230072969 + 3 ^ 40 * 3354122 * 2
def baseEnd_3354122 : Nat := 127576056282950460440717

theorem tailTrace_3354122 : CollatzResearch.WordTrace tailWord_3354122 prefixEnd_3354122 127576056282950460440717 := by
  unfold tailWord_3354122
  simp only [CollatzResearch.WordTrace]
  refine ⟨30583719888649076819178155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81556586369730871517808413 30583719888649076819178155)
  ·
    refine ⟨45875579832973615228767233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30583719888649076819178155 45875579832973615228767233)
    ·
      refine ⟨34406684874730211421575425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45875579832973615228767233 34406684874730211421575425)
      ·
        refine ⟨25805013656047658566181569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34406684874730211421575425 25805013656047658566181569)
        ·
          refine ⟨19353760242035743924636177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25805013656047658566181569 19353760242035743924636177)
          ·
            refine ⟨14515320181526807943477133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19353760242035743924636177 14515320181526807943477133)
            ·
              refine ⟨5443245068072552978803925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14515320181526807943477133 5443245068072552978803925)
              ·
                refine ⟨127576056282950460440717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5443245068072552978803925 127576056282950460440717)
                ·
                  rfl

theorem cell22_3354122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 7].length) (baseStart_3354122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354122 prefixEnd_3354122 := by exact prefixLift 3354122
  have htrace : WordTrace (prefixWord ++ tailWord_3354122) baseStart_3354122 baseEnd_3354122 := by
    simpa [prefixWord, tailWord_3354122, baseEnd_3354122] using wordTrace_append hprefix tailTrace_3354122
  have hstable : (prefixWord ++ tailWord_3354122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354122).length < 2 ^ (prefixWord ++ tailWord_3354122).sum := by decide
  have hdescent : baseEnd_3354122 < baseStart_3354122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354154 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 5, 3]
def baseStart_3354154 : Nat := 118140960795 + 3354154 * 2 ^ 59
def prefixEnd_3354154 : Nat := 4983230072969 + 3 ^ 40 * 3354154 * 2
def baseEnd_3354154 : Nat := 1148195460800516727166355

theorem tailTrace_3354154 : CollatzResearch.WordTrace tailWord_3354154 prefixEnd_3354154 1148195460800516727166355 := by
  unfold tailWord_3354154
  simp only [CollatzResearch.WordTrace]
  refine ⟨30584011672620094185469379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81557364460320251161251677 30584011672620094185469379)
  ·
    refine ⟨45876017508930141278204069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30584011672620094185469379 45876017508930141278204069)
    ·
      refine ⟨8601753282924401489663263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45876017508930141278204069 8601753282924401489663263)
      ·
        refine ⟨12902629924386602234494895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8601753282924401489663263 12902629924386602234494895)
        ·
          refine ⟨19353944886579903351742343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12902629924386602234494895 19353944886579903351742343)
          ·
            refine ⟨29030917329869855027613515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19353944886579903351742343 29030917329869855027613515)
            ·
              refine ⟨43546375994804782541420273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29030917329869855027613515 43546375994804782541420273)
              ·
                refine ⟨32659781996103586906065205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43546375994804782541420273 32659781996103586906065205)
                ·
                  refine ⟨3061854562134711272443613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32659781996103586906065205 3061854562134711272443613)
                  ·
                    refine ⟨1148195460800516727166355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3061854562134711272443613 1148195460800516727166355)
                    ·
                      rfl

theorem cell22_3354154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_3354154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354154 prefixEnd_3354154 := by exact prefixLift 3354154
  have htrace : WordTrace (prefixWord ++ tailWord_3354154) baseStart_3354154 baseEnd_3354154 := by
    simpa [prefixWord, tailWord_3354154, baseEnd_3354154] using wordTrace_append hprefix tailTrace_3354154
  have hstable : (prefixWord ++ tailWord_3354154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354154).length < 2 ^ (prefixWord ++ tailWord_3354154).sum := by decide
  have hdescent : baseEnd_3354154 < baseStart_3354154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354167 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 7]
def baseStart_3354167 : Nat := 118140960795 + 3354167 * 2 ^ 59
def prefixEnd_3354167 : Nat := 4983230072969 + 3 ^ 40 * 3354167 * 2
def baseEnd_3354167 : Nat := 382733303655396342197105

theorem tailTrace_3354167 : CollatzResearch.WordTrace tailWord_3354167 prefixEnd_3354167 382733303655396342197105 := by
  unfold tailWord_3354167
  simp only [CollatzResearch.WordTrace]
  refine ⟨122336520839433279962100755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81557680559622186641400503 122336520839433279962100755)
  ·
    refine ⟨183504781259149919943151133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122336520839433279962100755 183504781259149919943151133)
    ·
      refine ⟨68814292972181219978681675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183504781259149919943151133 68814292972181219978681675)
      ·
        refine ⟨103221439458271829968022513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68814292972181219978681675 103221439458271829968022513)
        ·
          refine ⟨77416079593703872476016885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103221439458271829968022513 77416079593703872476016885)
          ·
            refine ⟨7257757461909738044626583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77416079593703872476016885 7257757461909738044626583)
            ·
              refine ⟨10886636192864607066939875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7257757461909738044626583 10886636192864607066939875)
              ·
                refine ⟨16329954289296910600409813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10886636192864607066939875 16329954289296910600409813)
                ·
                  refine ⟨382733303655396342197105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16329954289296910600409813 382733303655396342197105)
                  ·
                    rfl

theorem cell22_3354167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 7].length) (baseStart_3354167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354167 prefixEnd_3354167 := by exact prefixLift 3354167
  have htrace : WordTrace (prefixWord ++ tailWord_3354167) baseStart_3354167 baseEnd_3354167 := by
    simpa [prefixWord, tailWord_3354167, baseEnd_3354167] using wordTrace_append hprefix tailTrace_3354167
  have hstable : (prefixWord ++ tailWord_3354167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354167).length < 2 ^ (prefixWord ++ tailWord_3354167).sum := by decide
  have hdescent : baseEnd_3354167 < baseStart_3354167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354274 : List Nat := [3, 3, 1, 4, 11]
def baseStart_3354274 : Nat := 118140960795 + 3354274 * 2 ^ 59
def prefixEnd_3354274 : Nat := 4983230072969 + 3 ^ 40 * 3354274 * 2
def baseEnd_3354274 : Nat := 4725253247954223926609

theorem tailTrace_3354274 : CollatzResearch.WordTrace tailWord_3354274 prefixEnd_3354274 4725253247954223926609 := by
  unfold tailWord_3354274
  simp only [CollatzResearch.WordTrace]
  refine ⟨30585105862511409309061469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81560282300030424824163917 30585105862511409309061469)
  ·
    refine ⟨11469414698441778490898051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30585105862511409309061469 11469414698441778490898051)
    ·
      refine ⟨17204122047662667736347077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11469414698441778490898051 17204122047662667736347077)
      ·
        refine ⟨3225772883936750200565077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17204122047662667736347077 3225772883936750200565077)
        ·
          refine ⟨4725253247954223926609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3225772883936750200565077 4725253247954223926609)
          ·
            rfl

theorem cell22_3354274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 11].length) (baseStart_3354274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354274 prefixEnd_3354274 := by exact prefixLift 3354274
  have htrace : WordTrace (prefixWord ++ tailWord_3354274) baseStart_3354274 baseEnd_3354274 := by
    simpa [prefixWord, tailWord_3354274, baseEnd_3354274] using wordTrace_append hprefix tailTrace_3354274
  have hstable : (prefixWord ++ tailWord_3354274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354274).length < 2 ^ (prefixWord ++ tailWord_3354274).sum := by decide
  have hdescent : baseEnd_3354274 < baseStart_3354274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354287 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 1, 8]
def baseStart_3354287 : Nat := 118140960795 + 3354287 * 2 ^ 59
def prefixEnd_3354287 : Nat := 4983230072969 + 3 ^ 40 * 3354287 * 2
def baseEnd_3354287 : Nat := 1148240989418548713590947

theorem tailTrace_3354287 : CollatzResearch.WordTrace tailWord_3354287 prefixEnd_3354287 1148240989418548713590947 := by
  unfold tailWord_3354287
  simp only [CollatzResearch.WordTrace]
  refine ⟨122340897598998540456469115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81560598399332360304312743 122340897598998540456469115)
  ·
    refine ⟨183511346398497810684703673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122340897598998540456469115 183511346398497810684703673)
    ·
      refine ⟨137633509798873358013527755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183511346398497810684703673 137633509798873358013527755)
      ·
        refine ⟨206450264698310037020291633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137633509798873358013527755 206450264698310037020291633)
        ·
          refine ⟨154837698523732527765218725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206450264698310037020291633 154837698523732527765218725)
          ·
            refine ⟨29032068473199848955978511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154837698523732527765218725 29032068473199848955978511)
            ·
              refine ⟨43548102709799773433967767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29032068473199848955978511 43548102709799773433967767)
              ·
                refine ⟨65322154064699660150951651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43548102709799773433967767 65322154064699660150951651)
                ·
                  refine ⟨97983231097049490226427477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65322154064699660150951651 97983231097049490226427477)
                  ·
                    refine ⟨1148240989418548713590947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97983231097049490226427477 1148240989418548713590947)
                    ·
                      rfl

theorem cell22_3354287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_3354287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354287 prefixEnd_3354287 := by exact prefixLift 3354287
  have htrace : WordTrace (prefixWord ++ tailWord_3354287) baseStart_3354287 baseEnd_3354287 := by
    simpa [prefixWord, tailWord_3354287, baseEnd_3354287] using wordTrace_append hprefix tailTrace_3354287
  have hstable : (prefixWord ++ tailWord_3354287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354287).length < 2 ^ (prefixWord ++ tailWord_3354287).sum := by decide
  have hdescent : baseEnd_3354287 < baseStart_3354287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354310 : List Nat := [6, 1, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3354310 : Nat := 118140960795 + 3354310 * 2 ^ 59
def prefixEnd_3354310 : Nat := 4983230072969 + 3 ^ 40 * 3354310 * 2
def baseEnd_3354310 : Nat := 1148248862788584320265877

theorem tailTrace_3354310 : CollatzResearch.WordTrace tailWord_3354310 prefixEnd_3354310 1148248862788584320265877 := by
  unfold tailWord_3354310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3823179264934850480767387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81561157651943476923037589 3823179264934850480767387)
  ·
    refine ⟨5734768897402275721151081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3823179264934850480767387 5734768897402275721151081)
    ·
      refine ⟨4301076673051706790863311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5734768897402275721151081 4301076673051706790863311)
      ·
        refine ⟨6451615009577560186294967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4301076673051706790863311 6451615009577560186294967)
        ·
          refine ⟨9677422514366340279442451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6451615009577560186294967 9677422514366340279442451)
          ·
            refine ⟨14516133771549510419163677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9677422514366340279442451 14516133771549510419163677)
            ·
              refine ⟨5443550164331066407186379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14516133771549510419163677 5443550164331066407186379)
              ·
                refine ⟨8165325246496599610779569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5443550164331066407186379 8165325246496599610779569)
                ·
                  refine ⟨6123993934872449708084677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8165325246496599610779569 6123993934872449708084677)
                  ·
                    refine ⟨1148248862788584320265877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6123993934872449708084677 1148248862788584320265877)
                    ·
                      rfl

theorem cell22_3354310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3354310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354310 prefixEnd_3354310 := by exact prefixLift 3354310
  have htrace : WordTrace (prefixWord ++ tailWord_3354310) baseStart_3354310 baseEnd_3354310 := by
    simpa [prefixWord, tailWord_3354310, baseEnd_3354310] using wordTrace_append hprefix tailTrace_3354310
  have hstable : (prefixWord ++ tailWord_3354310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354310).length < 2 ^ (prefixWord ++ tailWord_3354310).sum := by decide
  have hdescent : baseEnd_3354310 < baseStart_3354310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354364 : List Nat := [2, 2, 2, 1, 3, 1, 1, 4, 6]
def baseStart_3354364 : Nat := 118140960795 + 3354364 * 2 ^ 59
def prefixEnd_3354364 : Nat := 4983230072969 + 3 ^ 40 * 3354364 * 2
def baseEnd_3354364 : Nat := 382755782697382059805237

theorem tailTrace_3354364 : CollatzResearch.WordTrace tailWord_3354364 prefixEnd_3354364 382755782697382059805237 := by
  unfold tailWord_3354364
  simp only [CollatzResearch.WordTrace]
  refine ⟨61171853009859791303511073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81562470679813055071348097 61171853009859791303511073)
  ·
    refine ⟨45878889757394843477633305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61171853009859791303511073 45878889757394843477633305)
    ·
      refine ⟨34409167318046132608224979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45878889757394843477633305 34409167318046132608224979)
      ·
        refine ⟨51613750977069198912337469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34409167318046132608224979 51613750977069198912337469)
        ·
          refine ⟨19355156616400949592126551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51613750977069198912337469 19355156616400949592126551)
          ·
            refine ⟨29032734924601424388189827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19355156616400949592126551 29032734924601424388189827)
            ·
              refine ⟨43549102386902136582284741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29032734924601424388189827 43549102386902136582284741)
              ·
                refine ⟨8165456697544150609178389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43549102386902136582284741 8165456697544150609178389)
                ·
                  refine ⟨382755782697382059805237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8165456697544150609178389 382755782697382059805237)
                  ·
                    rfl

theorem cell22_3354364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_3354364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354364 prefixEnd_3354364 := by exact prefixLift 3354364
  have htrace : WordTrace (prefixWord ++ tailWord_3354364) baseStart_3354364 baseEnd_3354364 := by
    simpa [prefixWord, tailWord_3354364, baseEnd_3354364] using wordTrace_append hprefix tailTrace_3354364
  have hstable : (prefixWord ++ tailWord_3354364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354364).length < 2 ^ (prefixWord ++ tailWord_3354364).sum := by decide
  have hdescent : baseEnd_3354364 < baseStart_3354364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354379 : List Nat := [1, 1, 1, 1, 5, 1, 2, 4, 1, 5]
def baseStart_3354379 : Nat := 118140960795 + 3354379 * 2 ^ 59
def prefixEnd_3354379 : Nat := 4983230072969 + 3 ^ 40 * 3354379 * 2
def baseEnd_3354379 : Nat := 1148272482898691140290665

theorem tailTrace_3354379 : CollatzResearch.WordTrace tailWord_3354379 prefixEnd_3354379 1148272482898691140290665 := by
  unfold tailWord_3354379
  simp only [CollatzResearch.WordTrace]
  refine ⟨122344253114665240168818191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81562835409776826779212127 122344253114665240168818191)
  ·
    refine ⟨183516379671997860253227287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122344253114665240168818191 183516379671997860253227287)
    ·
      refine ⟨275274569507996790379840931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183516379671997860253227287 275274569507996790379840931)
      ·
        refine ⟨412911854261995185569761397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275274569507996790379840931 412911854261995185569761397)
        ·
          refine ⟨38710486337062048647165131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 412911854261995185569761397 38710486337062048647165131)
          ·
            refine ⟨58065729505593072970747697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38710486337062048647165131 58065729505593072970747697)
            ·
              refine ⟨43549297129194804728060773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58065729505593072970747697 43549297129194804728060773)
              ·
                refine ⟨8165493211724025886511395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43549297129194804728060773 8165493211724025886511395)
                ·
                  refine ⟨12248239817586038829767093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8165493211724025886511395 12248239817586038829767093)
                  ·
                    refine ⟨1148272482898691140290665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12248239817586038829767093 1148272482898691140290665)
                    ·
                      rfl

theorem cell22_3354379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 5].length) (baseStart_3354379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354379 prefixEnd_3354379 := by exact prefixLift 3354379
  have htrace : WordTrace (prefixWord ++ tailWord_3354379) baseStart_3354379 baseEnd_3354379 := by
    simpa [prefixWord, tailWord_3354379, baseEnd_3354379] using wordTrace_append hprefix tailTrace_3354379
  have hstable : (prefixWord ++ tailWord_3354379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354379).length < 2 ^ (prefixWord ++ tailWord_3354379).sum := by decide
  have hdescent : baseEnd_3354379 < baseStart_3354379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354396 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 4, 3]
def baseStart_3354396 : Nat := 118140960795 + 3354396 * 2 ^ 59
def prefixEnd_3354396 : Nat := 4983230072969 + 3 ^ 40 * 3354396 * 2
def baseEnd_3354396 : Nat := 1148278302346108762615613

theorem tailTrace_3354396 : CollatzResearch.WordTrace tailWord_3354396 prefixEnd_3354396 1148278302346108762615613 := by
  unfold tailWord_3354396
  simp only [CollatzResearch.WordTrace]
  refine ⟨61172436577801826036093521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81563248770402434714791361 61172436577801826036093521)
  ·
    refine ⟨45879327433351369527070141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61172436577801826036093521 45879327433351369527070141)
    ·
      refine ⟨17204747787506763572651303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45879327433351369527070141 17204747787506763572651303)
      ·
        refine ⟨25807121681260145358976955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17204747787506763572651303 25807121681260145358976955)
        ·
          refine ⟨38710682521890218038465433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25807121681260145358976955 38710682521890218038465433)
          ·
            refine ⟨29033011891417663528849075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38710682521890218038465433 29033011891417663528849075)
            ·
              refine ⟨43549517837126495293273613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29033011891417663528849075 43549517837126495293273613)
              ·
                refine ⟨16331069188922435734977605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43549517837126495293273613 16331069188922435734977605)
                ·
                  refine ⟨3062075472922956700308301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16331069188922435734977605 3062075472922956700308301)
                  ·
                    refine ⟨1148278302346108762615613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3062075472922956700308301 1148278302346108762615613)
                    ·
                      rfl

theorem cell22_3354396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_3354396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354396 prefixEnd_3354396 := by exact prefixLift 3354396
  have htrace : WordTrace (prefixWord ++ tailWord_3354396) baseStart_3354396 baseEnd_3354396 := by
    simpa [prefixWord, tailWord_3354396, baseEnd_3354396] using wordTrace_append hprefix tailTrace_3354396
  have hstable : (prefixWord ++ tailWord_3354396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354396).length < 2 ^ (prefixWord ++ tailWord_3354396).sum := by decide
  have hdescent : baseEnd_3354396 < baseStart_3354396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354460 : List Nat := [2, 2, 4, 2, 3, 1, 1, 7]
def baseStart_3354460 : Nat := 118140960795 + 3354460 * 2 ^ 59
def prefixEnd_3354460 : Nat := 4983230072969 + 3 ^ 40 * 3354460 * 2
def baseEnd_3354460 : Nat := 127588912317114881001713

theorem tailTrace_3354460 : CollatzResearch.WordTrace tailWord_3354460 prefixEnd_3354460 127588912317114881001713 := by
  unfold tailWord_3354460
  simp only [CollatzResearch.WordTrace]
  refine ⟨61173603713685895501258417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81564804951581194001677889 61173603713685895501258417)
  ·
    refine ⟨45880202785264421625943813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61173603713685895501258417 45880202785264421625943813)
    ·
      refine ⟨8602538022237079054864465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45880202785264421625943813 8602538022237079054864465)
      ·
        refine ⟨6451903516677809291148349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8602538022237079054864465 6451903516677809291148349)
        ·
          refine ⟨2419463818754178484180631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6451903516677809291148349 2419463818754178484180631)
          ·
            refine ⟨3629195728131267726270947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2419463818754178484180631 3629195728131267726270947)
            ·
              refine ⟨5443793592196901589406421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3629195728131267726270947 5443793592196901589406421)
              ·
                refine ⟨127588912317114881001713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5443793592196901589406421 127588912317114881001713)
                ·
                  rfl

theorem cell22_3354460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 7].length) (baseStart_3354460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354460 prefixEnd_3354460 := by exact prefixLift 3354460
  have htrace : WordTrace (prefixWord ++ tailWord_3354460) baseStart_3354460 baseEnd_3354460 := by
    simpa [prefixWord, tailWord_3354460, baseEnd_3354460] using wordTrace_append hprefix tailTrace_3354460
  have hstable : (prefixWord ++ tailWord_3354460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354460).length < 2 ^ (prefixWord ++ tailWord_3354460).sum := by decide
  have hdescent : baseEnd_3354460 < baseStart_3354460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354471 : List Nat := [1, 1, 5, 1, 2, 1, 1, 5, 5]
def baseStart_3354471 : Nat := 118140960795 + 3354471 * 2 ^ 59
def prefixEnd_3354471 : Nat := 4983230072969 + 3 ^ 40 * 3354471 * 2
def baseEnd_3354471 : Nat := 382767992126277855663461

theorem tailTrace_3354471 : CollatzResearch.WordTrace tailWord_3354471 prefixEnd_3354471 382767992126277855663461 := by
  unfold tailWord_3354471
  simp only [CollatzResearch.WordTrace]
  refine ⟨122347608630331939881167267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81565072420221293254111511 122347608630331939881167267)
  ·
    refine ⟨183521412945497909821750901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122347608630331939881167267 183521412945497909821750901)
    ·
      refine ⟨17205132463640429045789147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183521412945497909821750901 17205132463640429045789147)
      ·
        refine ⟨25807698695460643568683721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17205132463640429045789147 25807698695460643568683721)
        ·
          refine ⟨19355774021595482676512791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25807698695460643568683721 19355774021595482676512791)
          ·
            refine ⟨29033661032393224014769187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19355774021595482676512791 29033661032393224014769187)
            ·
              refine ⟨43550491548589836022153781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29033661032393224014769187 43550491548589836022153781)
              ·
                refine ⟨4082858582680297127076917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43550491548589836022153781 4082858582680297127076917)
                ·
                  refine ⟨382767992126277855663461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4082858582680297127076917 382767992126277855663461)
                  ·
                    rfl

theorem cell22_3354471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 5].length) (baseStart_3354471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354471 prefixEnd_3354471 := by exact prefixLift 3354471
  have htrace : WordTrace (prefixWord ++ tailWord_3354471) baseStart_3354471 baseEnd_3354471 := by
    simpa [prefixWord, tailWord_3354471, baseEnd_3354471] using wordTrace_append hprefix tailTrace_3354471
  have hstable : (prefixWord ++ tailWord_3354471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354471).length < 2 ^ (prefixWord ++ tailWord_3354471).sum := by decide
  have hdescent : baseEnd_3354471 < baseStart_3354471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354535 : List Nat := [1, 1, 6, 1, 2, 2, 2, 2, 1, 4]
def baseStart_3354535 : Nat := 118140960795 + 3354535 * 2 ^ 59
def prefixEnd_3354535 : Nat := 4983230072969 + 3 ^ 40 * 3354535 * 2
def baseEnd_3354535 : Nat := 1148325884886758733390187

theorem tailTrace_3354535 : CollatzResearch.WordTrace tailWord_3354535 prefixEnd_3354535 1148325884886758733390187 := by
  unfold tailWord_3354535
  simp only [CollatzResearch.WordTrace]
  refine ⟨122349942902100078811497059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81566628601400052540998039 122349942902100078811497059)
  ·
    refine ⟨183524914353150118217245589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122349942902100078811497059 183524914353150118217245589)
    ·
      refine ⟨8602730360303911791433387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 183524914353150118217245589 8602730360303911791433387)
      ·
        refine ⟨12904095540455867687150081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8602730360303911791433387 12904095540455867687150081)
        ·
          refine ⟨9678071655341900765362561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12904095540455867687150081 9678071655341900765362561)
          ·
            refine ⟨7258553741506425574021921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9678071655341900765362561 7258553741506425574021921)
            ·
              refine ⟨5443915306129819180516441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7258553741506425574021921 5443915306129819180516441)
              ·
                refine ⟨4082936479597364385387331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5443915306129819180516441 4082936479597364385387331)
                ·
                  refine ⟨6124404719396046578080997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4082936479597364385387331 6124404719396046578080997)
                  ·
                    refine ⟨1148325884886758733390187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6124404719396046578080997 1148325884886758733390187)
                    ·
                      rfl

theorem cell22_3354535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_3354535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354535 prefixEnd_3354535 := by exact prefixLift 3354535
  have htrace : WordTrace (prefixWord ++ tailWord_3354535) baseStart_3354535 baseEnd_3354535 := by
    simpa [prefixWord, tailWord_3354535, baseEnd_3354535] using wordTrace_append hprefix tailTrace_3354535
  have hstable : (prefixWord ++ tailWord_3354535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354535).length < 2 ^ (prefixWord ++ tailWord_3354535).sum := by decide
  have hdescent : baseEnd_3354535 < baseStart_3354535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354546 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_3354546 : Nat := 118140960795 + 3354546 * 2 ^ 59
def prefixEnd_3354546 : Nat := 4983230072969 + 3 ^ 40 * 3354546 * 2
def baseEnd_3354546 : Nat := 1148329650411558371365153

theorem tailTrace_3354546 : CollatzResearch.WordTrace tailWord_3354546 prefixEnd_3354546 1148329650411558371365153 := by
  unfold tailWord_3354546
  simp only [CollatzResearch.WordTrace]
  refine ⟨30587586026265056922536873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81566896070040151793431661 30587586026265056922536873)
  ·
    refine ⟨22940689519698792691902655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30587586026265056922536873 22940689519698792691902655)
    ·
      refine ⟨34411034279548189037853983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22940689519698792691902655 34411034279548189037853983)
      ·
        refine ⟨51616551419322283556780975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34411034279548189037853983 51616551419322283556780975)
        ·
          refine ⟨77424827128983425335171463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51616551419322283556780975 77424827128983425335171463)
          ·
            refine ⟨116137240693475138002757195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77424827128983425335171463 116137240693475138002757195)
            ·
              refine ⟨174205861040212707004135793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116137240693475138002757195 174205861040212707004135793)
              ·
                refine ⟨130654395780159530253101845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174205861040212707004135793 130654395780159530253101845)
                ·
                  refine ⟨6124424802194977980614149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130654395780159530253101845 6124424802194977980614149)
                  ·
                    refine ⟨1148329650411558371365153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6124424802194977980614149 1148329650411558371365153)
                    ·
                      rfl

theorem cell22_3354546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_3354546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354546 prefixEnd_3354546 := by exact prefixLift 3354546
  have htrace : WordTrace (prefixWord ++ tailWord_3354546) baseStart_3354546 baseEnd_3354546 := by
    simpa [prefixWord, tailWord_3354546, baseEnd_3354546] using wordTrace_append hprefix tailTrace_3354546
  have hstable : (prefixWord ++ tailWord_3354546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354546).length < 2 ^ (prefixWord ++ tailWord_3354546).sum := by decide
  have hdescent : baseEnd_3354546 < baseStart_3354546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354593 : List Nat := [1, 2, 3, 1, 2, 1, 2, 4, 3, 3]
def baseStart_3354593 : Nat := 118140960795 + 3354593 * 2 ^ 59
def prefixEnd_3354593 : Nat := 4983230072969 + 3 ^ 40 * 3354593 * 2
def baseEnd_3354593 : Nat := 1148345739472065915440009

theorem tailTrace_3354593 : CollatzResearch.WordTrace tailWord_3354593 prefixEnd_3354593 1148345739472065915440009 := by
  unfold tailWord_3354593
  simp only [CollatzResearch.WordTrace]
  refine ⟨122352058335889954717108433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81568038890593303144738955 122352058335889954717108433)
  ·
    refine ⟨91764043751917466037831325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122352058335889954717108433 91764043751917466037831325)
    ·
      refine ⟨34411516406969049764186747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91764043751917466037831325 34411516406969049764186747)
      ·
        refine ⟨51617274610453574646280121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34411516406969049764186747 51617274610453574646280121)
        ·
          refine ⟨38712955957840180984710091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51617274610453574646280121 38712955957840180984710091)
          ·
            refine ⟨58069433936760271477065137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38712955957840180984710091 58069433936760271477065137)
            ·
              refine ⟨43552075452570203607798853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58069433936760271477065137 43552075452570203607798853)
              ·
                refine ⟨8166014147356913176462285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43552075452570203607798853 8166014147356913176462285)
                ·
                  refine ⟨3062255305258842441173357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8166014147356913176462285 3062255305258842441173357)
                  ·
                    refine ⟨1148345739472065915440009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3062255305258842441173357 1148345739472065915440009)
                    ·
                      rfl

theorem cell22_3354593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_3354593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354593 prefixEnd_3354593 := by exact prefixLift 3354593
  have htrace : WordTrace (prefixWord ++ tailWord_3354593) baseStart_3354593 baseEnd_3354593 := by
    simpa [prefixWord, tailWord_3354593, baseEnd_3354593] using wordTrace_append hprefix tailTrace_3354593
  have hstable : (prefixWord ++ tailWord_3354593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354593).length < 2 ^ (prefixWord ++ tailWord_3354593).sum := by decide
  have hdescent : baseEnd_3354593 < baseStart_3354593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354638 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_3354638 : Nat := 118140960795 + 3354638 * 2 ^ 59
def prefixEnd_3354638 : Nat := 4983230072969 + 3 ^ 40 * 3354638 * 2
def baseEnd_3354638 : Nat := 1148361143891700798064871

theorem tailTrace_3354638 : CollatzResearch.WordTrace tailWord_3354638 prefixEnd_3354638 1148361143891700798064871 := by
  unfold tailWord_3354638
  simp only [CollatzResearch.WordTrace]
  refine ⟨15294212452590865925312071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81569133080484618268331045 15294212452590865925312071)
  ·
    refine ⟨22941318678886298887968107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15294212452590865925312071 22941318678886298887968107)
    ·
      refine ⟨34411978018329448331952161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22941318678886298887968107 34411978018329448331952161)
      ·
        refine ⟨25808983513747086248964121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34411978018329448331952161 25808983513747086248964121)
        ·
          refine ⟨19356737635310314686723091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25808983513747086248964121 19356737635310314686723091)
          ·
            refine ⟨29035106452965472030084637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19356737635310314686723091 29035106452965472030084637)
            ·
              refine ⟨10888164919862052011281739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29035106452965472030084637 10888164919862052011281739)
              ·
                refine ⟨16332247379793078016922609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10888164919862052011281739 16332247379793078016922609)
                ·
                  refine ⟨12249185534844808512691957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16332247379793078016922609 12249185534844808512691957)
                  ·
                    refine ⟨1148361143891700798064871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12249185534844808512691957 1148361143891700798064871)
                    ·
                      rfl

theorem cell22_3354638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_3354638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354638 prefixEnd_3354638 := by exact prefixLift 3354638
  have htrace : WordTrace (prefixWord ++ tailWord_3354638) baseStart_3354638 baseEnd_3354638 := by
    simpa [prefixWord, tailWord_3354638, baseEnd_3354638] using wordTrace_append hprefix tailTrace_3354638
  have hstable : (prefixWord ++ tailWord_3354638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354638).length < 2 ^ (prefixWord ++ tailWord_3354638).sum := by decide
  have hdescent : baseEnd_3354638 < baseStart_3354638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354644 : List Nat := [2, 4, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_3354644 : Nat := 118140960795 + 3354644 * 2 ^ 59
def prefixEnd_3354644 : Nat := 4983230072969 + 3 ^ 40 * 3354644 * 2
def baseEnd_3354644 : Nat := 1148363197814318782414853

theorem tailTrace_3354644 : CollatzResearch.WordTrace tailWord_3354644 prefixEnd_3354644 1148363197814318782414853 := by
  unfold tailWord_3354644
  simp only [CollatzResearch.WordTrace]
  refine ⟨61176959229352595213607493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81569278972470126951476657 61176959229352595213607493)
  ·
    refine ⟨11470679855503611602551405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61176959229352595213607493 11470679855503611602551405)
    ·
      refine ⟨4301504945813854350956777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11470679855503611602551405 4301504945813854350956777)
      ·
        refine ⟨3226128709360390763217583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4301504945813854350956777 3226128709360390763217583)
        ·
          refine ⟨4839193064040586144826375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3226128709360390763217583 4839193064040586144826375)
          ·
            refine ⟨7258789596060879217239563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4839193064040586144826375 7258789596060879217239563)
            ·
              refine ⟨10888184394091318825859345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7258789596060879217239563 10888184394091318825859345)
              ·
                refine ⟨8166138295568489119394509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10888184394091318825859345 8166138295568489119394509)
                ·
                  refine ⟨3062301860838183419772941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8166138295568489119394509 3062301860838183419772941)
                  ·
                    refine ⟨1148363197814318782414853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3062301860838183419772941 1148363197814318782414853)
                    ·
                      rfl

theorem cell22_3354644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_3354644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354644 prefixEnd_3354644 := by exact prefixLift 3354644
  have htrace : WordTrace (prefixWord ++ tailWord_3354644) baseStart_3354644 baseEnd_3354644 := by
    simpa [prefixWord, tailWord_3354644, baseEnd_3354644] using wordTrace_append hprefix tailTrace_3354644
  have hstable : (prefixWord ++ tailWord_3354644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354644).length < 2 ^ (prefixWord ++ tailWord_3354644).sum := by decide
  have hdescent : baseEnd_3354644 < baseStart_3354644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354683 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 4, 3]
def baseStart_3354683 : Nat := 118140960795 + 3354683 * 2 ^ 59
def prefixEnd_3354683 : Nat := 4983230072969 + 3 ^ 40 * 3354683 * 2
def baseEnd_3354683 : Nat := 1148376548311335680689733

theorem tailTrace_3354683 : CollatzResearch.WordTrace tailWord_3354683 prefixEnd_3354683 1148376548311335680689733 := by
  unfold tailWord_3354683
  simp only [CollatzResearch.WordTrace]
  refine ⟨122355340905563900087884703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81570227270375933391923135 122355340905563900087884703)
  ·
    refine ⟨183533011358345850131827055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122355340905563900087884703 183533011358345850131827055)
    ·
      refine ⟨275299517037518775197740583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183533011358345850131827055 275299517037518775197740583)
      ·
        refine ⟨412949275556278162796610875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275299517037518775197740583 412949275556278162796610875)
        ·
          refine ⟨619423913334417244194916313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412949275556278162796610875 619423913334417244194916313)
          ·
            refine ⟨464567935000812933146187235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 619423913334417244194916313 464567935000812933146187235)
            ·
              refine ⟨696851902501219399719280853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464567935000812933146187235 696851902501219399719280853)
              ·
                refine ⟨16332466464872329680920645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 696851902501219399719280853 16332466464872329680920645)
                ·
                  refine ⟨3062337462163561815172621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16332466464872329680920645 3062337462163561815172621)
                  ·
                    refine ⟨1148376548311335680689733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3062337462163561815172621 1148376548311335680689733)
                    ·
                      rfl

theorem cell22_3354683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 3].length) (baseStart_3354683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354683 prefixEnd_3354683 := by exact prefixLift 3354683
  have htrace : WordTrace (prefixWord ++ tailWord_3354683) baseStart_3354683 baseEnd_3354683 := by
    simpa [prefixWord, tailWord_3354683, baseEnd_3354683] using wordTrace_append hprefix tailTrace_3354683
  have hstable : (prefixWord ++ tailWord_3354683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354683).length < 2 ^ (prefixWord ++ tailWord_3354683).sum := by decide
  have hdescent : baseEnd_3354683 < baseStart_3354683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354685 : List Nat := [1, 4, 1, 3, 1, 1, 1, 6, 4]
def baseStart_3354685 : Nat := 118140960795 + 3354685 * 2 ^ 59
def prefixEnd_3354685 : Nat := 4983230072969 + 3 ^ 40 * 3354685 * 2
def baseEnd_3354685 : Nat := 382792410984069447379909

theorem tailTrace_3354685 : CollatzResearch.WordTrace tailWord_3354685 prefixEnd_3354685 382792410984069447379909 := by
  unfold tailWord_3354685
  simp only [CollatzResearch.WordTrace]
  refine ⟨122355413851556654429457509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81570275901037769619638339 122355413851556654429457509)
  ·
    refine ⟨22941640097166872705523283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122355413851556654429457509 22941640097166872705523283)
    ·
      refine ⟨34412460145750309058284925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22941640097166872705523283 34412460145750309058284925)
      ·
        refine ⟨12904672554656365896856847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34412460145750309058284925 12904672554656365896856847)
        ·
          refine ⟨19357008831984548845285271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12904672554656365896856847 19357008831984548845285271)
          ·
            refine ⟨29035513247976823267927907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19357008831984548845285271 29035513247976823267927907)
            ·
              refine ⟨43553269871965234901891861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29035513247976823267927907 43553269871965234901891861)
              ·
                refine ⟨2041559525248370386026181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43553269871965234901891861 2041559525248370386026181)
                ·
                  refine ⟨382792410984069447379909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2041559525248370386026181 382792410984069447379909)
                  ·
                    rfl

theorem cell22_3354685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_3354685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354685 prefixEnd_3354685 := by exact prefixLift 3354685
  have htrace : WordTrace (prefixWord ++ tailWord_3354685) baseStart_3354685 baseEnd_3354685 := by
    simpa [prefixWord, tailWord_3354685, baseEnd_3354685] using wordTrace_append hprefix tailTrace_3354685
  have hstable : (prefixWord ++ tailWord_3354685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354685).length < 2 ^ (prefixWord ++ tailWord_3354685).sum := by decide
  have hdescent : baseEnd_3354685 < baseStart_3354685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354700 : List Nat := [2, 2, 1, 3, 1, 1, 2, 5, 2, 3]
def baseStart_3354700 : Nat := 118140960795 + 3354700 * 2 ^ 59
def prefixEnd_3354700 : Nat := 4983230072969 + 3 ^ 40 * 3354700 * 2
def baseEnd_3354700 : Nat := 1148382367758753303014681

theorem tailTrace_3354700 : CollatzResearch.WordTrace tailWord_3354700 prefixEnd_3354700 1148382367758753303014681 := by
  unfold tailWord_3354700
  simp only [CollatzResearch.WordTrace]
  refine ⟨61177980473251155995626777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81570640631001541327502369 61177980473251155995626777)
  ·
    refine ⟨45883485354938366996720083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61177980473251155995626777 45883485354938366996720083)
    ·
      refine ⟨68825228032407550495080125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45883485354938366996720083 68825228032407550495080125)
      ·
        refine ⟨25809460512152831435655047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68825228032407550495080125 25809460512152831435655047)
        ·
          refine ⟨38714190768229247153482571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25809460512152831435655047 38714190768229247153482571)
          ·
            refine ⟨58071286152343870730223857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38714190768229247153482571 58071286152343870730223857)
            ·
              refine ⟨43553464614257903047667893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58071286152343870730223857 43553464614257903047667893)
              ·
                refine ⟨4083137307586678410718865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43553464614257903047667893 4083137307586678410718865)
                ·
                  refine ⟨3062352980690008808039149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4083137307586678410718865 3062352980690008808039149)
                  ·
                    refine ⟨1148382367758753303014681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3062352980690008808039149 1148382367758753303014681)
                    ·
                      rfl

theorem cell22_3354700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_3354700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354700 prefixEnd_3354700 := by exact prefixLift 3354700
  have htrace : WordTrace (prefixWord ++ tailWord_3354700) baseStart_3354700 baseEnd_3354700 := by
    simpa [prefixWord, tailWord_3354700, baseEnd_3354700] using wordTrace_append hprefix tailTrace_3354700
  have hstable : (prefixWord ++ tailWord_3354700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354700).length < 2 ^ (prefixWord ++ tailWord_3354700).sum := by decide
  have hdescent : baseEnd_3354700 < baseStart_3354700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354717 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 4, 3]
def baseStart_3354717 : Nat := 118140960795 + 3354717 * 2 ^ 59
def prefixEnd_3354717 : Nat := 4983230072969 + 3 ^ 40 * 3354717 * 2
def baseEnd_3354717 : Nat := 1148388187206170925339629

theorem tailTrace_3354717 : CollatzResearch.WordTrace tailWord_3354717 prefixEnd_3354717 1148388187206170925339629 := by
  unfold tailWord_3354717
  simp only [CollatzResearch.WordTrace]
  refine ⟨122356580987440723894622405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81571053991627149263081603 122356580987440723894622405)
  ·
    refine ⟨22941858935145135730241701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122356580987440723894622405 22941858935145135730241701)
    ·
      refine ⟨4301598550339712949420319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22941858935145135730241701 4301598550339712949420319)
      ·
        refine ⟨6452397825509569424130479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4301598550339712949420319 6452397825509569424130479)
        ·
          refine ⟨9678596738264354136195719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6452397825509569424130479 9678596738264354136195719)
          ·
            refine ⟨14517895107396531204293579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9678596738264354136195719 14517895107396531204293579)
            ·
              refine ⟨21776842661094796806440369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14517895107396531204293579 21776842661094796806440369)
              ·
                refine ⟨16332631995821097604830277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21776842661094796806440369 16332631995821097604830277)
                ·
                  refine ⟨3062368499216455800905677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16332631995821097604830277 3062368499216455800905677)
                  ·
                    refine ⟨1148388187206170925339629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3062368499216455800905677 1148388187206170925339629)
                    ·
                      rfl

theorem cell22_3354717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_3354717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354717 prefixEnd_3354717 := by exact prefixLift 3354717
  have htrace : WordTrace (prefixWord ++ tailWord_3354717) baseStart_3354717 baseEnd_3354717 := by
    simpa [prefixWord, tailWord_3354717, baseEnd_3354717] using wordTrace_append hprefix tailTrace_3354717
  have hstable : (prefixWord ++ tailWord_3354717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354717).length < 2 ^ (prefixWord ++ tailWord_3354717).sum := by decide
  have hdescent : baseEnd_3354717 < baseStart_3354717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354730 : List Nat := [3, 1, 3, 2, 3, 2, 8]
def baseStart_3354730 : Nat := 118140960795 + 3354730 * 2 ^ 59
def prefixEnd_3354730 : Nat := 4983230072969 + 3 ^ 40 * 3354730 * 2
def baseEnd_3354730 : Nat := 42533060643401600917207

theorem tailTrace_3354730 : CollatzResearch.WordTrace tailWord_3354730 prefixEnd_3354730 42533060643401600917207 := by
  unfold tailWord_3354730
  simp only [CollatzResearch.WordTrace]
  refine ⟨30589263784098406778711411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81571370090929084743230429 30589263784098406778711411)
  ·
    refine ⟨45883895676147610168067117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30589263784098406778711411 45883895676147610168067117)
    ·
      refine ⟨17206460878555353813025169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45883895676147610168067117 17206460878555353813025169)
      ·
        refine ⟨12904845658916515359768877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17206460878555353813025169 12904845658916515359768877)
        ·
          refine ⟨4839317122093693259913329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12904845658916515359768877 4839317122093693259913329)
          ·
            refine ⟨3629487841570269944934997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4839317122093693259913329 3629487841570269944934997)
            ·
              refine ⟨42533060643401600917207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3629487841570269944934997 42533060643401600917207)
              ·
                rfl

theorem cell22_3354730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 8].length) (baseStart_3354730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354730 prefixEnd_3354730 := by exact prefixLift 3354730
  have htrace : WordTrace (prefixWord ++ tailWord_3354730) baseStart_3354730 baseEnd_3354730 := by
    simpa [prefixWord, tailWord_3354730, baseEnd_3354730] using wordTrace_append hprefix tailTrace_3354730
  have hstable : (prefixWord ++ tailWord_3354730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354730).length < 2 ^ (prefixWord ++ tailWord_3354730).sum := by decide
  have hdescent : baseEnd_3354730 < baseStart_3354730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354803 : List Nat := [1, 1, 1, 2, 3, 2, 1, 5, 6]
def baseStart_3354803 : Nat := 118140960795 + 3354803 * 2 ^ 59
def prefixEnd_3354803 : Nat := 4983230072969 + 3 ^ 40 * 3354803 * 2
def baseEnd_3354803 : Nat := 382805875587898455896455

theorem tailTrace_3354803 : CollatzResearch.WordTrace tailWord_3354803 prefixEnd_3354803 382805875587898455896455 := by
  unfold tailWord_3354803
  simp only [CollatzResearch.WordTrace]
  refine ⟨122359717665129160582253063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81573145110086107054835375 122359717665129160582253063)
  ·
    refine ⟨183539576497693740873379595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122359717665129160582253063 183539576497693740873379595)
    ·
      refine ⟨275309364746540611310069393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183539576497693740873379595 275309364746540611310069393)
      ·
        refine ⟨206482023559905458482552045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275309364746540611310069393 206482023559905458482552045)
        ·
          refine ⟨77430758834964546930957017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206482023559905458482552045 77430758834964546930957017)
          ·
            refine ⟨58073069126223410198217763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77430758834964546930957017 58073069126223410198217763)
            ·
              refine ⟨87109603689335115297326645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58073069126223410198217763 87109603689335115297326645)
              ·
                refine ⟨8166525345875167059124373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87109603689335115297326645 8166525345875167059124373)
                ·
                  refine ⟨382805875587898455896455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8166525345875167059124373 382805875587898455896455)
                  ·
                    rfl

theorem cell22_3354803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 6].length) (baseStart_3354803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354803 prefixEnd_3354803 := by exact prefixLift 3354803
  have htrace : WordTrace (prefixWord ++ tailWord_3354803) baseStart_3354803 baseEnd_3354803 := by
    simpa [prefixWord, tailWord_3354803, baseEnd_3354803] using wordTrace_append hprefix tailTrace_3354803
  have hstable : (prefixWord ++ tailWord_3354803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354803).length < 2 ^ (prefixWord ++ tailWord_3354803).sum := by decide
  have hdescent : baseEnd_3354803 < baseStart_3354803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354820 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 8]
def baseStart_3354820 : Nat := 118140960795 + 3354820 * 2 ^ 59
def prefixEnd_3354820 : Nat := 4983230072969 + 3 ^ 40 * 3354820 * 2
def baseEnd_3354820 : Nat := 382807815403704330004771

theorem tailTrace_3354820 : CollatzResearch.WordTrace tailWord_3354820 prefixEnd_3354820 382807815403704330004771 := by
  unfold tailWord_3354820
  simp only [CollatzResearch.WordTrace]
  refine ⟨61180168853033786242810957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81573558470711714990414609 61180168853033786242810957)
  ·
    refine ⟨22942563319887669841054109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61180168853033786242810957 22942563319887669841054109)
    ·
      refine ⟨8603461244957876190395291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22942563319887669841054109 8603461244957876190395291)
      ·
        refine ⟨12905191867436814285592937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8603461244957876190395291 12905191867436814285592937)
        ·
          refine ⟨9678893900577610714194703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12905191867436814285592937 9678893900577610714194703)
          ·
            refine ⟨14518340850866416071292055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9678893900577610714194703 14518340850866416071292055)
            ·
              refine ⟨21777511276299624106938083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14518340850866416071292055 21777511276299624106938083)
              ·
                refine ⟨32666266914449436160407125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21777511276299624106938083 32666266914449436160407125)
                ·
                  refine ⟨382807815403704330004771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32666266914449436160407125 382807815403704330004771)
                  ·
                    rfl

theorem cell22_3354820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_3354820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354820 prefixEnd_3354820 := by exact prefixLift 3354820
  have htrace : WordTrace (prefixWord ++ tailWord_3354820) baseStart_3354820 baseEnd_3354820 := by
    simpa [prefixWord, tailWord_3354820, baseEnd_3354820] using wordTrace_append hprefix tailTrace_3354820
  have hstable : (prefixWord ++ tailWord_3354820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354820).length < 2 ^ (prefixWord ++ tailWord_3354820).sum := by decide
  have hdescent : baseEnd_3354820 < baseStart_3354820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354848 : List Nat := [2, 1, 1, 3, 1, 3, 11]
def baseStart_3354848 : Nat := 118140960795 + 3354848 * 2 ^ 59
def prefixEnd_3354848 : Nat := 4983230072969 + 3 ^ 40 * 3354848 * 2
def baseEnd_3354848 : Nat := 42534556710493712974601

theorem tailTrace_3354848 : CollatzResearch.WordTrace tailWord_3354848 prefixEnd_3354848 42534556710493712974601 := by
  unfold tailWord_3354848
  simp only [CollatzResearch.WordTrace]
  refine ⟨61180679474983066633820599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81574239299977422178427465 61180679474983066633820599)
  ·
    refine ⟨91771019212474599950730899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61180679474983066633820599 91771019212474599950730899)
    ·
      refine ⟨137656528818711899926096349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91771019212474599950730899 137656528818711899926096349)
      ·
        refine ⟨51621198307016962472286131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137656528818711899926096349 51621198307016962472286131)
        ·
          refine ⟨77431797460525443708429197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51621198307016962472286131 77431797460525443708429197)
          ·
            refine ⟨29036924047697041390660949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77431797460525443708429197 29036924047697041390660949)
            ·
              refine ⟨42534556710493712974601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29036924047697041390660949 42534556710493712974601)
              ·
                rfl

theorem cell22_3354848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 11].length) (baseStart_3354848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354848 prefixEnd_3354848 := by exact prefixLift 3354848
  have htrace : WordTrace (prefixWord ++ tailWord_3354848) baseStart_3354848 baseEnd_3354848 := by
    simpa [prefixWord, tailWord_3354848, baseEnd_3354848] using wordTrace_append hprefix tailTrace_3354848
  have hstable : (prefixWord ++ tailWord_3354848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354848).length < 2 ^ (prefixWord ++ tailWord_3354848).sum := by decide
  have hdescent : baseEnd_3354848 < baseStart_3354848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354882 : List Nat := [3, 4, 1, 1, 2, 2, 1, 8]
def baseStart_3354882 : Nat := 118140960795 + 3354882 * 2 ^ 59
def prefixEnd_3354882 : Nat := 4983230072969 + 3 ^ 40 * 3354882 * 2
def baseEnd_3354882 : Nat := 127604963342018388329347

theorem tailTrace_3354882 : CollatzResearch.WordTrace tailWord_3354882 prefixEnd_3354882 127604963342018388329347 := by
  unfold tailWord_3354882
  simp only [CollatzResearch.WordTrace]
  refine ⟨30590649757960739268594725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81575066021228638049585933 30590649757960739268594725)
  ·
    refine ⟨5735746829617638612861511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30590649757960739268594725 5735746829617638612861511)
    ·
      refine ⟨8603620244426457919292267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5735746829617638612861511 8603620244426457919292267)
      ·
        refine ⟨12905430366639686878938401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8603620244426457919292267 12905430366639686878938401)
        ·
          refine ⟨9679072774979765159203801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12905430366639686878938401 9679072774979765159203801)
          ·
            refine ⟨7259304581234823869402851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9679072774979765159203801 7259304581234823869402851)
            ·
              refine ⟨10888956871852235804104277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7259304581234823869402851 10888956871852235804104277)
              ·
                refine ⟨127604963342018388329347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10888956871852235804104277 127604963342018388329347)
                ·
                  rfl

theorem cell22_3354882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 8].length) (baseStart_3354882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354882 prefixEnd_3354882 := by exact prefixLift 3354882
  have htrace : WordTrace (prefixWord ++ tailWord_3354882) baseStart_3354882 baseEnd_3354882 := by
    simpa [prefixWord, tailWord_3354882, baseEnd_3354882] using wordTrace_append hprefix tailTrace_3354882
  have hstable : (prefixWord ++ tailWord_3354882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354882).length < 2 ^ (prefixWord ++ tailWord_3354882).sum := by decide
  have hdescent : baseEnd_3354882 < baseStart_3354882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354914 : List Nat := [3, 3, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_3354914 : Nat := 118140960795 + 3354914 * 2 ^ 59
def prefixEnd_3354914 : Nat := 4983230072969 + 3 ^ 40 * 3354914 * 2
def baseEnd_3354914 : Nat := 1148455624332128078164025

theorem tailTrace_3354914 : CollatzResearch.WordTrace tailWord_3354914 prefixEnd_3354914 1148455624332128078164025 := by
  unfold tailWord_3354914
  simp only [CollatzResearch.WordTrace]
  refine ⟨30590941541931756634885949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81575844111818017693029197 30590941541931756634885949)
  ·
    refine ⟨11471603078224408738082231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30590941541931756634885949 11471603078224408738082231)
    ·
      refine ⟨17207404617336613107123347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11471603078224408738082231 17207404617336613107123347)
      ·
        refine ⟨25811106926004919660685021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17207404617336613107123347 25811106926004919660685021)
        ·
          refine ⟨9679165097251844872756883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25811106926004919660685021 9679165097251844872756883)
          ·
            refine ⟨14518747645877767309135325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9679165097251844872756883 14518747645877767309135325)
            ·
              refine ⟨5444530367204162740925747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14518747645877767309135325 5444530367204162740925747)
              ·
                refine ⟨8166795550806244111388621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5444530367204162740925747 8166795550806244111388621)
                ·
                  refine ⟨3062548331552341541770733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8166795550806244111388621 3062548331552341541770733)
                  ·
                    refine ⟨1148455624332128078164025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3062548331552341541770733 1148455624332128078164025)
                    ·
                      rfl

theorem cell22_3354914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_3354914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354914 prefixEnd_3354914 := by exact prefixLift 3354914
  have htrace : WordTrace (prefixWord ++ tailWord_3354914) baseStart_3354914 baseEnd_3354914 := by
    simpa [prefixWord, tailWord_3354914, baseEnd_3354914] using wordTrace_append hprefix tailTrace_3354914
  have hstable : (prefixWord ++ tailWord_3354914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354914).length < 2 ^ (prefixWord ++ tailWord_3354914).sum := by decide
  have hdescent : baseEnd_3354914 < baseStart_3354914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354927 : List Nat := [1, 1, 2, 1, 2, 1, 8, 1, 5]
def baseStart_3354927 : Nat := 118140960795 + 3354927 * 2 ^ 59
def prefixEnd_3354927 : Nat := 4983230072969 + 3 ^ 40 * 3354927 * 2
def baseEnd_3354927 : Nat := 382820024832600125862995

theorem tailTrace_3354927 : CollatzResearch.WordTrace tailWord_3354927 prefixEnd_3354927 382820024832600125862995 := by
  unfold tailWord_3354927
  simp only [CollatzResearch.WordTrace]
  refine ⟨122364240316679929759767035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81576160211119953173178023 122364240316679929759767035)
  ·
    refine ⟨183546360475019894639650553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122364240316679929759767035 183546360475019894639650553)
    ·
      refine ⟨137659770356264920979737915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183546360475019894639650553 137659770356264920979737915)
      ·
        refine ⟨206489655534397381469606873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137659770356264920979737915 206489655534397381469606873)
        ·
          refine ⟨154867241650798036102205155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206489655534397381469606873 154867241650798036102205155)
          ·
            refine ⟨232300862476197054153307733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154867241650798036102205155 232300862476197054153307733)
            ·
              refine ⟨2722275732142934228359075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 232300862476197054153307733 2722275732142934228359075)
              ·
                refine ⟨4083413598214401342538613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2722275732142934228359075 4083413598214401342538613)
                ·
                  refine ⟨382820024832600125862995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4083413598214401342538613 382820024832600125862995)
                  ·
                    rfl

theorem cell22_3354927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 5].length) (baseStart_3354927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354927 prefixEnd_3354927 := by exact prefixLift 3354927
  have htrace : WordTrace (prefixWord ++ tailWord_3354927) baseStart_3354927 baseEnd_3354927 := by
    simpa [prefixWord, tailWord_3354927, baseEnd_3354927] using wordTrace_append hprefix tailTrace_3354927
  have hstable : (prefixWord ++ tailWord_3354927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354927).length < 2 ^ (prefixWord ++ tailWord_3354927).sum := by decide
  have hdescent : baseEnd_3354927 < baseStart_3354927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354965 : List Nat := [1, 3, 2, 2, 5, 1, 2, 2, 1, 3]
def baseStart_3354965 : Nat := 118140960795 + 3354965 * 2 ^ 59
def prefixEnd_3354965 : Nat := 4983230072969 + 3 ^ 40 * 3354965 * 2
def baseEnd_3354965 : Nat := 1148473082674380945138869

theorem tailTrace_3354965 : CollatzResearch.WordTrace tailWord_3354965 prefixEnd_3354965 1148473082674380945138869 := by
  unfold tailWord_3354965
  simp only [CollatzResearch.WordTrace]
  refine ⟨122365626290542262249650349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81577084193694841499766899 122365626290542262249650349)
  ·
    refine ⟨45887109858953348343618881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122365626290542262249650349 45887109858953348343618881)
    ·
      refine ⟨34415332394215011257714161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45887109858953348343618881 34415332394215011257714161)
      ·
        refine ⟨25811499295661258443285621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34415332394215011257714161 25811499295661258443285621)
        ·
          refine ⟨2419828058968242979058027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25811499295661258443285621 2419828058968242979058027)
          ·
            refine ⟨3629742088452364468587041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2419828058968242979058027 3629742088452364468587041)
            ·
              refine ⟨2722306566339273351440281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3629742088452364468587041 2722306566339273351440281)
              ·
                refine ⟨2041729924754455013580211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2722306566339273351440281 2041729924754455013580211)
                ·
                  refine ⟨3062594887131682520370317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2041729924754455013580211 3062594887131682520370317)
                  ·
                    refine ⟨1148473082674380945138869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3062594887131682520370317 1148473082674380945138869)
                    ·
                      rfl

theorem cell22_3354965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_3354965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354965 prefixEnd_3354965 := by exact prefixLift 3354965
  have htrace : WordTrace (prefixWord ++ tailWord_3354965) baseStart_3354965 baseEnd_3354965 := by
    simpa [prefixWord, tailWord_3354965, baseEnd_3354965] using wordTrace_append hprefix tailTrace_3354965
  have hstable : (prefixWord ++ tailWord_3354965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354965).length < 2 ^ (prefixWord ++ tailWord_3354965).sum := by decide
  have hdescent : baseEnd_3354965 < baseStart_3354965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354970 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 5, 5]
def baseStart_3354970 : Nat := 118140960795 + 3354970 * 2 ^ 59
def prefixEnd_3354970 : Nat := 4983230072969 + 3 ^ 40 * 3354970 * 2
def baseEnd_3354970 : Nat := 1148474794276562598763853

theorem tailTrace_3354970 : CollatzResearch.WordTrace tailWord_3354970 prefixEnd_3354970 1148474794276562598763853 := by
  unfold tailWord_3354970
  simp only [CollatzResearch.WordTrace]
  refine ⟨30591452163881037025895591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81577205770349432069054909 30591452163881037025895591)
  ·
    refine ⟨45887178245821555538843387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30591452163881037025895591 45887178245821555538843387)
    ·
      refine ⟨68830767368732333308265081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45887178245821555538843387 68830767368732333308265081)
      ·
        refine ⟨51623075526549249981198811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68830767368732333308265081 51623075526549249981198811)
        ·
          refine ⟨77434613289823874971798217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51623075526549249981198811 77434613289823874971798217)
          ·
            refine ⟨58075959967367906228848663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77434613289823874971798217 58075959967367906228848663)
            ·
              refine ⟨87113939951051859343272995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58075959967367906228848663 87113939951051859343272995)
              ·
                refine ⟨130670909926577789014909493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87113939951051859343272995 130670909926577789014909493)
                ·
                  refine ⟨12250397805616667720147765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130670909926577789014909493 12250397805616667720147765)
                  ·
                    refine ⟨1148474794276562598763853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12250397805616667720147765 1148474794276562598763853)
                    ·
                      rfl

theorem cell22_3354970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_3354970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354970 prefixEnd_3354970 := by exact prefixLift 3354970
  have htrace : WordTrace (prefixWord ++ tailWord_3354970) baseStart_3354970 baseEnd_3354970 := by
    simpa [prefixWord, tailWord_3354970, baseEnd_3354970] using wordTrace_append hprefix tailTrace_3354970
  have hstable : (prefixWord ++ tailWord_3354970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354970).length < 2 ^ (prefixWord ++ tailWord_3354970).sum := by decide
  have hdescent : baseEnd_3354970 < baseStart_3354970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354985 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 1, 6]
def baseStart_3354985 : Nat := 118140960795 + 3354985 * 2 ^ 59
def prefixEnd_3354985 : Nat := 4983230072969 + 3 ^ 40 * 3354985 * 2
def baseEnd_3354985 : Nat := 1148479929083107559638807

theorem tailTrace_3354985 : CollatzResearch.WordTrace tailWord_3354985 prefixEnd_3354985 1148479929083107559638807 := by
  unfold tailWord_3354985
  simp only [CollatzResearch.WordTrace]
  refine ⟨122366355750469805665378409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81577570500313203776918939 122366355750469805665378409)
  ·
    refine ⟨91774766812852354249033807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122366355750469805665378409 91774766812852354249033807)
    ·
      refine ⟨137662150219278531373550711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91774766812852354249033807 137662150219278531373550711)
      ·
        refine ⟨206493225328917797060326067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137662150219278531373550711 206493225328917797060326067)
        ·
          refine ⟨309739837993376695590489101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206493225328917797060326067 309739837993376695590489101)
          ·
            refine ⟨116152439247516260846433413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309739837993376695590489101 116152439247516260846433413)
            ·
              refine ⟨21778582358909298908706265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116152439247516260846433413 21778582358909298908706265)
              ·
                refine ⟨16333936769181974181529699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21778582358909298908706265 16333936769181974181529699)
                ·
                  refine ⟨24500905153772961272294549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16333936769181974181529699 24500905153772961272294549)
                  ·
                    refine ⟨1148479929083107559638807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24500905153772961272294549 1148479929083107559638807)
                    ·
                      rfl

theorem cell22_3354985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_3354985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3354985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3354985 prefixEnd_3354985 := by exact prefixLift 3354985
  have htrace : WordTrace (prefixWord ++ tailWord_3354985) baseStart_3354985 baseEnd_3354985 := by
    simpa [prefixWord, tailWord_3354985, baseEnd_3354985] using wordTrace_append hprefix tailTrace_3354985
  have hstable : (prefixWord ++ tailWord_3354985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354985).length < 2 ^ (prefixWord ++ tailWord_3354985).sum := by decide
  have hdescent : baseEnd_3354985 < baseStart_3354985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355094 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_3355094 : Nat := 118140960795 + 3355094 * 2 ^ 59
def prefixEnd_3355094 : Nat := 4983230072969 + 3 ^ 40 * 3355094 * 2
def baseEnd_3355094 : Nat := 1148517242010667608663473

theorem tailTrace_3355094 : CollatzResearch.WordTrace tailWord_3355094 prefixEnd_3355094 1148517242010667608663473 := by
  unfold tailWord_3355094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7648145706692182330068521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81580220871383278187397557 7648145706692182330068521)
  ·
    refine ⟨5736109280019136747551391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7648145706692182330068521 5736109280019136747551391)
    ·
      refine ⟨8604163920028705121327087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5736109280019136747551391 8604163920028705121327087)
      ·
        refine ⟨12906245880043057681990631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8604163920028705121327087 12906245880043057681990631)
        ·
          refine ⟨19359368820064586522985947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12906245880043057681990631 19359368820064586522985947)
          ·
            refine ⟨29039053230096879784478921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19359368820064586522985947 29039053230096879784478921)
            ·
              refine ⟨21779289922572659838359191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29039053230096879784478921 21779289922572659838359191)
              ·
                refine ⟨32668934883858989757538787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21779289922572659838359191 32668934883858989757538787)
                ·
                  refine ⟨49003402325788484636308181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32668934883858989757538787 49003402325788484636308181)
                  ·
                    refine ⟨1148517242010667608663473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49003402325788484636308181 1148517242010667608663473)
                    ·
                      rfl

theorem cell22_3355094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_3355094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355094 prefixEnd_3355094 := by exact prefixLift 3355094
  have htrace : WordTrace (prefixWord ++ tailWord_3355094) baseStart_3355094 baseEnd_3355094 := by
    simpa [prefixWord, tailWord_3355094, baseEnd_3355094] using wordTrace_append hprefix tailTrace_3355094
  have hstable : (prefixWord ++ tailWord_3355094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355094).length < 2 ^ (prefixWord ++ tailWord_3355094).sum := by decide
  have hdescent : baseEnd_3355094 < baseStart_3355094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355141 : List Nat := [1, 3, 1, 1, 2, 2, 6, 2, 4]
def baseStart_3355141 : Nat := 118140960795 + 3355141 * 2 ^ 59
def prefixEnd_3355141 : Nat := 4983230072969 + 3 ^ 40 * 3355141 * 2
def baseEnd_3355141 : Nat := 382844443690391717579443

theorem tailTrace_3355141 : CollatzResearch.WordTrace tailWord_3355141 prefixEnd_3355141 382844443690391717579443 := by
  unfold tailWord_3355141
  simp only [CollatzResearch.WordTrace]
  refine ⟨122372045537904644308057277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81581363691936429538704851 122372045537904644308057277)
  ·
    refine ⟨45889517076714241615521479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122372045537904644308057277 45889517076714241615521479)
    ·
      refine ⟨68834275615071362423282219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45889517076714241615521479 68834275615071362423282219)
      ·
        refine ⟨103251413422607043634923329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68834275615071362423282219 103251413422607043634923329)
        ·
          refine ⟨77438560066955282726192497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103251413422607043634923329 77438560066955282726192497)
          ·
            refine ⟨58078920050216462044644373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77438560066955282726192497 58078920050216462044644373)
            ·
              refine ⟨2722449377353896658342705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58078920050216462044644373 2722449377353896658342705)
              ·
                refine ⟨2041837033015422493757029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2722449377353896658342705 2041837033015422493757029)
                ·
                  refine ⟨382844443690391717579443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2041837033015422493757029 382844443690391717579443)
                  ·
                    rfl

theorem cell22_3355141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 4].length) (baseStart_3355141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355141 prefixEnd_3355141 := by exact prefixLift 3355141
  have htrace : WordTrace (prefixWord ++ tailWord_3355141) baseStart_3355141 baseEnd_3355141 := by
    simpa [prefixWord, tailWord_3355141, baseEnd_3355141] using wordTrace_append hprefix tailTrace_3355141
  have hstable : (prefixWord ++ tailWord_3355141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355141).length < 2 ^ (prefixWord ++ tailWord_3355141).sum := by decide
  have hdescent : baseEnd_3355141 < baseStart_3355141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355156 : List Nat := [2, 4, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3355156 : Nat := 118140960795 + 3355156 * 2 ^ 59
def prefixEnd_3355156 : Nat := 4983230072969 + 3 ^ 40 * 3355156 * 2
def baseEnd_3355156 : Nat := 1148538465877720113613283

theorem tailTrace_3355156 : CollatzResearch.WordTrace tailWord_3355156 prefixEnd_3355156 1148538465877720113613283 := by
  unfold tailWord_3355156
  simp only [CollatzResearch.WordTrace]
  refine ⟨61186296316425150934926661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81581728421900201246568881 61186296316425150934926661)
  ·
    refine ⟨11472430559329715800298749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61186296316425150934926661 11472430559329715800298749)
    ·
      refine ⟨4302161459748643425112031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11472430559329715800298749 4302161459748643425112031)
      ·
        refine ⟨6453242189622965137668047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4302161459748643425112031 6453242189622965137668047)
        ·
          refine ⟨9679863284434447706502071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6453242189622965137668047 9679863284434447706502071)
          ·
            refine ⟨14519794926651671559753107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9679863284434447706502071 14519794926651671559753107)
            ·
              refine ⟨21779692389977507339629661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14519794926651671559753107 21779692389977507339629661)
              ·
                refine ⟨8167384646241565252361123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21779692389977507339629661 8167384646241565252361123)
                ·
                  refine ⟨12251076969362347878541685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8167384646241565252361123 12251076969362347878541685)
                  ·
                    refine ⟨1148538465877720113613283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12251076969362347878541685 1148538465877720113613283)
                    ·
                      rfl

theorem cell22_3355156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3355156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355156 prefixEnd_3355156 := by exact prefixLift 3355156
  have htrace : WordTrace (prefixWord ++ tailWord_3355156) baseStart_3355156 baseEnd_3355156 := by
    simpa [prefixWord, tailWord_3355156, baseEnd_3355156] using wordTrace_append hprefix tailTrace_3355156
  have hstable : (prefixWord ++ tailWord_3355156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355156).length < 2 ^ (prefixWord ++ tailWord_3355156).sum := by decide
  have hdescent : baseEnd_3355156 < baseStart_3355156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355169 : List Nat := [1, 2, 3, 2, 2, 1, 5, 6]
def baseStart_3355169 : Nat := 118140960795 + 3355169 * 2 ^ 59
def prefixEnd_3355169 : Nat := 4983230072969 + 3 ^ 40 * 3355169 * 2
def baseEnd_3355169 : Nat := 127615879560376934782027

theorem tailTrace_3355169 : CollatzResearch.WordTrace tailWord_3355169 prefixEnd_3355169 127615879560376934782027 := by
  unfold tailWord_3355169
  simp only [CollatzResearch.WordTrace]
  refine ⟨122373066781803205090076561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81582044521202136726717707 122373066781803205090076561)
  ·
    refine ⟨91779800086352403817557421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122373066781803205090076561 91779800086352403817557421)
    ·
      refine ⟨34417425032382151431584033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91779800086352403817557421 34417425032382151431584033)
      ·
        refine ⟨25813068774286613573688025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34417425032382151431584033 25813068774286613573688025)
        ·
          refine ⟨19359801580714960180266019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25813068774286613573688025 19359801580714960180266019)
          ·
            refine ⟨29039702371072440270399029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19359801580714960180266019 29039702371072440270399029)
            ·
              refine ⟨2722472097288041275349909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29039702371072440270399029 2722472097288041275349909)
              ·
                refine ⟨127615879560376934782027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2722472097288041275349909 127615879560376934782027)
                ·
                  rfl

theorem cell22_3355169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 6].length) (baseStart_3355169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355169 prefixEnd_3355169 := by exact prefixLift 3355169
  have htrace : WordTrace (prefixWord ++ tailWord_3355169) baseStart_3355169 baseEnd_3355169 := by
    simpa [prefixWord, tailWord_3355169, baseEnd_3355169] using wordTrace_append hprefix tailTrace_3355169
  have hstable : (prefixWord ++ tailWord_3355169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355169).length < 2 ^ (prefixWord ++ tailWord_3355169).sum := by decide
  have hdescent : baseEnd_3355169 < baseStart_3355169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355171 : List Nat := [1, 1, 1, 4, 4, 3, 1, 1, 2, 4]
def baseStart_3355171 : Nat := 118140960795 + 3355171 * 2 ^ 59
def prefixEnd_3355171 : Nat := 4983230072969 + 3 ^ 40 * 3355171 * 2
def baseEnd_3355171 : Nat := 1148543600684265074488237

theorem tailTrace_3355171 : CollatzResearch.WordTrace tailWord_3355171 prefixEnd_3355171 1148543600684265074488237 := by
  unfold tailWord_3355171
  simp only [CollatzResearch.WordTrace]
  refine ⟨122373139727795959431649367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81582093151863972954432911 122373139727795959431649367)
  ·
    refine ⟨183559709591693939147474051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122373139727795959431649367 183559709591693939147474051)
    ·
      refine ⟨275339564387540908721211077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183559709591693939147474051 275339564387540908721211077)
      ·
        refine ⟨51626168322663920385227077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275339564387540908721211077 51626168322663920385227077)
        ·
          refine ⟨9679906560499485072230077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51626168322663920385227077 9679906560499485072230077)
          ·
            refine ⟨3629964960187306902086279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9679906560499485072230077 3629964960187306902086279)
            ·
              refine ⟨5444947440280960353129419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3629964960187306902086279 5444947440280960353129419)
              ·
                refine ⟨8167421160421440529694129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5444947440280960353129419 8167421160421440529694129)
                ·
                  refine ⟨6125565870316080397270597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8167421160421440529694129 6125565870316080397270597)
                  ·
                    refine ⟨1148543600684265074488237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6125565870316080397270597 1148543600684265074488237)
                    ·
                      rfl

theorem cell22_3355171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 4].length) (baseStart_3355171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355171 prefixEnd_3355171 := by exact prefixLift 3355171
  have htrace : WordTrace (prefixWord ++ tailWord_3355171) baseStart_3355171 baseEnd_3355171 := by
    simpa [prefixWord, tailWord_3355171, baseEnd_3355171] using wordTrace_append hprefix tailTrace_3355171
  have hstable : (prefixWord ++ tailWord_3355171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355171).length < 2 ^ (prefixWord ++ tailWord_3355171).sum := by decide
  have hdescent : baseEnd_3355171 < baseStart_3355171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355175 : List Nat := [1, 1, 7, 2, 1, 1, 2, 3, 4]
def baseStart_3355175 : Nat := 118140960795 + 3355175 * 2 ^ 59
def prefixEnd_3355175 : Nat := 4983230072969 + 3 ^ 40 * 3355175 * 2
def baseEnd_3355175 : Nat := 382848323322003465796075

theorem tailTrace_3355175 : CollatzResearch.WordTrace tailWord_3355175 prefixEnd_3355175 382848323322003465796075 := by
  unfold tailWord_3355175
  simp only [CollatzResearch.WordTrace]
  refine ⟨122373285619781468114794979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81582190413187645409863319 122373285619781468114794979)
  ·
    refine ⟨183559928429672202172192469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122373285619781468114794979 183559928429672202172192469)
    ·
      refine ⟨4302185822570442238410761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 183559928429672202172192469 4302185822570442238410761)
      ·
        refine ⟨3226639366927831678808071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4302185822570442238410761 3226639366927831678808071)
        ·
          refine ⟨4839959050391747518212107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3226639366927831678808071 4839959050391747518212107)
          ·
            refine ⟨7259938575587621277318161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4839959050391747518212107 7259938575587621277318161)
            ·
              refine ⟨5444953931690715957988621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7259938575587621277318161 5444953931690715957988621)
              ·
                refine ⟨2041857724384018484245733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5444953931690715957988621 2041857724384018484245733)
                ·
                  refine ⟨382848323322003465796075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2041857724384018484245733 382848323322003465796075)
                  ·
                    rfl

theorem cell22_3355175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 4].length) (baseStart_3355175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355175 prefixEnd_3355175 := by exact prefixLift 3355175
  have htrace : WordTrace (prefixWord ++ tailWord_3355175) baseStart_3355175 baseEnd_3355175 := by
    simpa [prefixWord, tailWord_3355175, baseEnd_3355175] using wordTrace_append hprefix tailTrace_3355175
  have hstable : (prefixWord ++ tailWord_3355175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355175).length < 2 ^ (prefixWord ++ tailWord_3355175).sum := by decide
  have hdescent : baseEnd_3355175 < baseStart_3355175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355190 : List Nat := [5, 1, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_3355190 : Nat := 118140960795 + 3355190 * 2 ^ 59
def prefixEnd_3355190 : Nat := 4983230072969 + 3 ^ 40 * 3355190 * 2
def baseEnd_3355190 : Nat := 1148550104772555358263179

theorem tailTrace_3355190 : CollatzResearch.WordTrace tailWord_3355190 prefixEnd_3355190 1148550104772555358263179 := by
  unfold tailWord_3355190
  simp only [CollatzResearch.WordTrace]
  refine ⟨7648364544670445354786939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81582555143151417117727349 7648364544670445354786939)
  ·
    refine ⟨11472546817005668032180409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7648364544670445354786939 11472546817005668032180409)
    ·
      refine ⟨8604410112754251024135307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11472546817005668032180409 8604410112754251024135307)
      ·
        refine ⟨12906615169131376536202961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8604410112754251024135307 12906615169131376536202961)
        ·
          refine ⟨9679961376848532402152221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12906615169131376536202961 9679961376848532402152221)
          ·
            refine ⟨3629985516318199650807083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9679961376848532402152221 3629985516318199650807083)
            ·
              refine ⟨5444978274477299476210625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3629985516318199650807083 5444978274477299476210625)
              ·
                refine ⟨4083733705857974607157969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5444978274477299476210625 4083733705857974607157969)
                ·
                  refine ⟨3062800279393480955368477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4083733705857974607157969 3062800279393480955368477)
                  ·
                    refine ⟨1148550104772555358263179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3062800279393480955368477 1148550104772555358263179)
                    ·
                      rfl

theorem cell22_3355190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_3355190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355190 prefixEnd_3355190 := by exact prefixLift 3355190
  have htrace : WordTrace (prefixWord ++ tailWord_3355190) baseStart_3355190 baseEnd_3355190 := by
    simpa [prefixWord, tailWord_3355190, baseEnd_3355190] using wordTrace_append hprefix tailTrace_3355190
  have hstable : (prefixWord ++ tailWord_3355190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355190).length < 2 ^ (prefixWord ++ tailWord_3355190).sum := by decide
  have hdescent : baseEnd_3355190 < baseStart_3355190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355201 : List Nat := [1, 2, 5, 1, 1, 2, 1, 3, 3, 3]
def baseStart_3355201 : Nat := 118140960795 + 3355201 * 2 ^ 59
def prefixEnd_3355201 : Nat := 4983230072969 + 3 ^ 40 * 3355201 * 2
def baseEnd_3355201 : Nat := 1148553870297354996238145

theorem tailTrace_3355201 : CollatzResearch.WordTrace tailWord_3355201 prefixEnd_3355201 1148553870297354996238145 := by
  unfold tailWord_3355201
  simp only [CollatzResearch.WordTrace]
  refine ⟨122374233917687274555241457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81582822611791516370160971 122374233917687274555241457)
  ·
    refine ⟨91780675438265455916431093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122374233917687274555241457 91780675438265455916431093)
    ·
      refine ⟨8604438322337386492165415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91780675438265455916431093 8604438322337386492165415)
      ·
        refine ⟨12906657483506079738248123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8604438322337386492165415 12906657483506079738248123)
        ·
          refine ⟨19359986225259119607372185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12906657483506079738248123 19359986225259119607372185)
          ·
            refine ⟨14519989668944339705529139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19359986225259119607372185 14519989668944339705529139)
            ·
              refine ⟨21779984503416509558293709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14519989668944339705529139 21779984503416509558293709)
              ·
                refine ⟨8167494188781191084360141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21779984503416509558293709 8167494188781191084360141)
                ·
                  refine ⟨3062810320792946656635053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8167494188781191084360141 3062810320792946656635053)
                  ·
                    refine ⟨1148553870297354996238145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3062810320792946656635053 1148553870297354996238145)
                    ·
                      rfl

theorem cell22_3355201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_3355201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355201 prefixEnd_3355201 := by exact prefixLift 3355201
  have htrace : WordTrace (prefixWord ++ tailWord_3355201) baseStart_3355201 baseEnd_3355201 := by
    simpa [prefixWord, tailWord_3355201, baseEnd_3355201] using wordTrace_append hprefix tailTrace_3355201
  have hstable : (prefixWord ++ tailWord_3355201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355201).length < 2 ^ (prefixWord ++ tailWord_3355201).sum := by decide
  have hdescent : baseEnd_3355201 < baseStart_3355201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355214 : List Nat := [4, 1, 1, 1, 1, 2, 2, 5, 5]
def baseStart_3355214 : Nat := 118140960795 + 3355214 * 2 ^ 59
def prefixEnd_3355214 : Nat := 4983230072969 + 3 ^ 40 * 3355214 * 2
def baseEnd_3355214 : Nat := 382852773487675765221035

theorem tailTrace_3355214 : CollatzResearch.WordTrace tailWord_3355214 prefixEnd_3355214 382852773487675765221035 := by
  unfold tailWord_3355214
  simp only [CollatzResearch.WordTrace]
  refine ⟨15296838508330022221933087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81583138711093451850309797 15296838508330022221933087)
  ·
    refine ⟨22945257762495033332899631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15296838508330022221933087 22945257762495033332899631)
    ·
      refine ⟨34417886643742549999349447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22945257762495033332899631 34417886643742549999349447)
      ·
        refine ⟨51626829965613824999024171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34417886643742549999349447 51626829965613824999024171)
        ·
          refine ⟨77440244948420737498536257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51626829965613824999024171 77440244948420737498536257)
          ·
            refine ⟨58080183711315553123902193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77440244948420737498536257 58080183711315553123902193)
            ·
              refine ⟨43560137783486664842926645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58080183711315553123902193 43560137783486664842926645)
              ·
                refine ⟨4083762917201874829024373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43560137783486664842926645 4083762917201874829024373)
                ·
                  refine ⟨382852773487675765221035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4083762917201874829024373 382852773487675765221035)
                  ·
                    rfl

theorem cell22_3355214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_3355214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355214 prefixEnd_3355214 := by exact prefixLift 3355214
  have htrace : WordTrace (prefixWord ++ tailWord_3355214) baseStart_3355214 baseEnd_3355214 := by
    simpa [prefixWord, tailWord_3355214, baseEnd_3355214] using wordTrace_append hprefix tailTrace_3355214
  have hstable : (prefixWord ++ tailWord_3355214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355214).length < 2 ^ (prefixWord ++ tailWord_3355214).sum := by decide
  have hdescent : baseEnd_3355214 < baseStart_3355214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355310 : List Nat := [4, 1, 4, 1, 1, 2, 1, 4, 4]
def baseStart_3355310 : Nat := 118140960795 + 3355310 * 2 ^ 59
def prefixEnd_3355310 : Nat := 4983230072969 + 3 ^ 40 * 3355310 * 2
def baseEnd_3355310 : Nat := 382863727741638348420937

theorem tailTrace_3355310 : CollatzResearch.WordTrace tailWord_3355310 prefixEnd_3355310 382863727741638348420937 := by
  unfold tailWord_3355310
  simp only [CollatzResearch.WordTrace]
  refine ⟨15297276184286548271369923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81585472982861590780639589 15297276184286548271369923)
  ·
    refine ⟨22945914276429822407054885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15297276184286548271369923 22945914276429822407054885)
    ·
      refine ⟨4302358926830591701322791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22945914276429822407054885 4302358926830591701322791)
      ·
        refine ⟨6453538390245887551984187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4302358926830591701322791 6453538390245887551984187)
        ·
          refine ⟨9680307585368831327976281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6453538390245887551984187 9680307585368831327976281)
          ·
            refine ⟨7260230689026623495982211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9680307585368831327976281 7260230689026623495982211)
            ·
              refine ⟨10890346033539935243973317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7260230689026623495982211 10890346033539935243973317)
              ·
                refine ⟨2041939881288737858244997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10890346033539935243973317 2041939881288737858244997)
                ·
                  refine ⟨382863727741638348420937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2041939881288737858244997 382863727741638348420937)
                  ·
                    rfl

theorem cell22_3355310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_3355310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355310 prefixEnd_3355310 := by exact prefixLift 3355310
  have htrace : WordTrace (prefixWord ++ tailWord_3355310) baseStart_3355310 baseEnd_3355310 := by
    simpa [prefixWord, tailWord_3355310, baseEnd_3355310] using wordTrace_append hprefix tailTrace_3355310
  have hstable : (prefixWord ++ tailWord_3355310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355310).length < 2 ^ (prefixWord ++ tailWord_3355310).sum := by decide
  have hdescent : baseEnd_3355310 < baseStart_3355310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355336 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 5, 3]
def baseStart_3355336 : Nat := 118140960795 + 3355336 * 2 ^ 59
def prefixEnd_3355336 : Nat := 4983230072969 + 3 ^ 40 * 3355336 * 2
def baseEnd_3355336 : Nat := 1148600083556259644112731

theorem tailTrace_3355336 : CollatzResearch.WordTrace tailWord_3355336 prefixEnd_3355336 1148600083556259644112731 := by
  unfold tailWord_3355336
  simp only [CollatzResearch.WordTrace]
  refine ⟨61189578886099096305702931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81586105181465461740937241 61189578886099096305702931)
  ·
    refine ⟨91784368329148644458554397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61189578886099096305702931 91784368329148644458554397)
    ·
      refine ⟨34419138123430741671957899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91784368329148644458554397 34419138123430741671957899)
      ·
        refine ⟨51628707185146112507936849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34419138123430741671957899 51628707185146112507936849)
        ·
          refine ⟨38721530388859584380952637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51628707185146112507936849 38721530388859584380952637)
          ·
            refine ⟨14520573895822344142857239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38721530388859584380952637 14520573895822344142857239)
            ·
              refine ⟨21780860843733516214285859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14520573895822344142857239 21780860843733516214285859)
              ·
                refine ⟨32671291265600274321428789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21780860843733516214285859 32671291265600274321428789)
                ·
                  refine ⟨3062933556150025717633949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32671291265600274321428789 3062933556150025717633949)
                  ·
                    refine ⟨1148600083556259644112731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3062933556150025717633949 1148600083556259644112731)
                    ·
                      rfl

theorem cell22_3355336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_3355336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355336 prefixEnd_3355336 := by exact prefixLift 3355336
  have htrace : WordTrace (prefixWord ++ tailWord_3355336) baseStart_3355336 baseEnd_3355336 := by
    simpa [prefixWord, tailWord_3355336, baseEnd_3355336] using wordTrace_append hprefix tailTrace_3355336
  have hstable : (prefixWord ++ tailWord_3355336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355336).length < 2 ^ (prefixWord ++ tailWord_3355336).sum := by decide
  have hdescent : baseEnd_3355336 < baseStart_3355336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355434 : List Nat := [3, 1, 4, 3, 2, 1, 2, 1, 5]
def baseStart_3355434 : Nat := 118140960795 + 3355434 * 2 ^ 59
def prefixEnd_3355434 : Nat := 4983230072969 + 3 ^ 40 * 3355434 * 2
def baseEnd_3355434 : Nat := 382877876986340018387477

theorem tailTrace_3355434 : CollatzResearch.WordTrace tailWord_3355434 prefixEnd_3355434 382877876986340018387477 := by
  unfold tailWord_3355434
  simp only [CollatzResearch.WordTrace]
  refine ⟨30595683031460788837118339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81588488083895436898982237 30595683031460788837118339)
  ·
    refine ⟨45893524547191183255677509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30595683031460788837118339 45893524547191183255677509)
    ·
      refine ⟨8605035852598346860439533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45893524547191183255677509 8605035852598346860439533)
      ·
        refine ⟨3226888444724380072664825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8605035852598346860439533 3226888444724380072664825)
        ·
          refine ⟨2420166333543285054498619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3226888444724380072664825 2420166333543285054498619)
          ·
            refine ⟨3630249500314927581747929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2420166333543285054498619 3630249500314927581747929)
            ·
              refine ⟨2722687125236195686310947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3630249500314927581747929 2722687125236195686310947)
              ·
                refine ⟨4084030687854293529466421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2722687125236195686310947 4084030687854293529466421)
                ·
                  refine ⟨382877876986340018387477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4084030687854293529466421 382877876986340018387477)
                  ·
                    rfl

theorem cell22_3355434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 5].length) (baseStart_3355434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355434 prefixEnd_3355434 := by exact prefixLift 3355434
  have htrace : WordTrace (prefixWord ++ tailWord_3355434) baseStart_3355434 baseEnd_3355434 := by
    simpa [prefixWord, tailWord_3355434, baseEnd_3355434] using wordTrace_append hprefix tailTrace_3355434
  have hstable : (prefixWord ++ tailWord_3355434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355434).length < 2 ^ (prefixWord ++ tailWord_3355434).sum := by decide
  have hdescent : baseEnd_3355434 < baseStart_3355434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355441 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 4, 4]
def baseStart_3355441 : Nat := 118140960795 + 3355441 * 2 ^ 59
def prefixEnd_3355441 : Nat := 4983230072969 + 3 ^ 40 * 3355441 * 2
def baseEnd_3355441 : Nat := 1148636027202074370237409

theorem tailTrace_3355441 : CollatzResearch.WordTrace tailWord_3355441 prefixEnd_3355441 1148636027202074370237409 := by
  unfold tailWord_3355441
  simp only [CollatzResearch.WordTrace]
  refine ⟨122382987436817795543978177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81588658291211863695985451 122382987436817795543978177)
  ·
    refine ⟨91787240577613346657983633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122382987436817795543978177 91787240577613346657983633)
    ·
      refine ⟨68840430433210009993487725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91787240577613346657983633 68840430433210009993487725)
      ·
        refine ⟨25815161412453753747557897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68840430433210009993487725 25815161412453753747557897)
        ·
          refine ⟨19361371059340315310668423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25815161412453753747557897 19361371059340315310668423)
          ·
            refine ⟨29042056589010472966002635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19361371059340315310668423 29042056589010472966002635)
            ·
              refine ⟨43563084883515709449003953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29042056589010472966002635 43563084883515709449003953)
              ·
                refine ⟨32672313662636782086752965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43563084883515709449003953 32672313662636782086752965)
                ·
                  refine ⟨6126058811744396641266181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32672313662636782086752965 6126058811744396641266181)
                  ·
                    refine ⟨1148636027202074370237409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6126058811744396641266181 1148636027202074370237409)
                    ·
                      rfl

theorem cell22_3355441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_3355441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355441 prefixEnd_3355441 := by exact prefixLift 3355441
  have htrace : WordTrace (prefixWord ++ tailWord_3355441) baseStart_3355441 baseEnd_3355441 := by
    simpa [prefixWord, tailWord_3355441, baseEnd_3355441] using wordTrace_append hprefix tailTrace_3355441
  have hstable : (prefixWord ++ tailWord_3355441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355441).length < 2 ^ (prefixWord ++ tailWord_3355441).sum := by decide
  have hdescent : baseEnd_3355441 < baseStart_3355441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355488 : List Nat := [2, 1, 1, 3, 3, 1, 2, 3, 3, 3]
def baseStart_3355488 : Nat := 118140960795 + 3355488 * 2 ^ 59
def prefixEnd_3355488 : Nat := 4983230072969 + 3 ^ 40 * 3355488 * 2
def baseEnd_3355488 : Nat := 1148652116262581914312265

theorem tailTrace_3355488 : CollatzResearch.WordTrace tailWord_3355488 prefixEnd_3355488 1148652116262581914312265 := by
  unfold tailWord_3355488
  simp only [CollatzResearch.WordTrace]
  refine ⟨61192350833823761285469559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81589801111765015047292745 61192350833823761285469559)
  ·
    refine ⟨91788526250735641928204339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61192350833823761285469559 91788526250735641928204339)
    ·
      refine ⟨137682789376103462892306509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91788526250735641928204339 137682789376103462892306509)
      ·
        refine ⟨51631046016038798584614941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137682789376103462892306509 51631046016038798584614941)
        ·
          refine ⟨19361642256014549469230603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51631046016038798584614941 19361642256014549469230603)
          ·
            refine ⟨29042463384021824203845905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19361642256014549469230603 29042463384021824203845905)
            ·
              refine ⟨21781847538016368152884429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29042463384021824203845905 21781847538016368152884429)
              ·
                refine ⟨8168192826756138057331661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21781847538016368152884429 8168192826756138057331661)
                ·
                  refine ⟨3063072310033551771499373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8168192826756138057331661 3063072310033551771499373)
                  ·
                    refine ⟨1148652116262581914312265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3063072310033551771499373 1148652116262581914312265)
                    ·
                      rfl

theorem cell22_3355488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 3, 3].length) (baseStart_3355488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355488 prefixEnd_3355488 := by exact prefixLift 3355488
  have htrace : WordTrace (prefixWord ++ tailWord_3355488) baseStart_3355488 baseEnd_3355488 := by
    simpa [prefixWord, tailWord_3355488, baseEnd_3355488] using wordTrace_append hprefix tailTrace_3355488
  have hstable : (prefixWord ++ tailWord_3355488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355488).length < 2 ^ (prefixWord ++ tailWord_3355488).sum := by decide
  have hdescent : baseEnd_3355488 < baseStart_3355488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355490 : List Nat := [3, 3, 2, 1, 3, 2, 1, 7]
def baseStart_3355490 : Nat := 118140960795 + 3355490 * 2 ^ 59
def prefixEnd_3355490 : Nat := 4983230072969 + 3 ^ 40 * 3355490 * 2
def baseEnd_3355490 : Nat := 127628088989272730640251

theorem tailTrace_3355490 : CollatzResearch.WordTrace tailWord_3355490 prefixEnd_3355490 127628088989272730640251 := by
  unfold tailWord_3355490
  simp only [CollatzResearch.WordTrace]
  refine ⟨30596193653410069228127981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81589849742426851275007949 30596193653410069228127981)
  ·
    refine ⟨11473572620028775960547993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30596193653410069228127981 11473572620028775960547993)
    ·
      refine ⟨8605179465021581970410995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11473572620028775960547993 8605179465021581970410995)
      ·
        refine ⟨12907769197532372955616493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8605179465021581970410995 12907769197532372955616493)
        ·
          refine ⟨4840413449074639858356185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12907769197532372955616493 4840413449074639858356185)
          ·
            refine ⟨3630310086805979893767139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4840413449074639858356185 3630310086805979893767139)
            ·
              refine ⟨5445465130208969840650709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3630310086805979893767139 5445465130208969840650709)
              ·
                refine ⟨127628088989272730640251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5445465130208969840650709 127628088989272730640251)
                ·
                  rfl

theorem cell22_3355490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 7].length) (baseStart_3355490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355490 prefixEnd_3355490 := by exact prefixLift 3355490
  have htrace : WordTrace (prefixWord ++ tailWord_3355490) baseStart_3355490 baseEnd_3355490 := by
    simpa [prefixWord, tailWord_3355490, baseEnd_3355490] using wordTrace_append hprefix tailTrace_3355490
  have hstable : (prefixWord ++ tailWord_3355490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355490).length < 2 ^ (prefixWord ++ tailWord_3355490).sum := by decide
  have hdescent : baseEnd_3355490 < baseStart_3355490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355501 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 9]
def baseStart_3355501 : Nat := 118140960795 + 3355501 * 2 ^ 59
def prefixEnd_3355501 : Nat := 4983230072969 + 3 ^ 40 * 3355501 * 2
def baseEnd_3355501 : Nat := 382885522142751404579075

theorem tailTrace_3355501 : CollatzResearch.WordTrace tailWord_3355501 prefixEnd_3355501 382885522142751404579075 := by
  unfold tailWord_3355501
  simp only [CollatzResearch.WordTrace]
  refine ⟨122385175816600425791162357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81590117211066950527441571 122385175816600425791162357)
  ·
    refine ⟨11473610232806289917921471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122385175816600425791162357 11473610232806289917921471)
    ·
      refine ⟨17210415349209434876882207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11473610232806289917921471 17210415349209434876882207)
      ·
        refine ⟨25815623023814152315323311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17210415349209434876882207 25815623023814152315323311)
        ·
          refine ⟨38723434535721228472984967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25815623023814152315323311 38723434535721228472984967)
          ·
            refine ⟨58085151803581842709477451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38723434535721228472984967 58085151803581842709477451)
            ·
              refine ⟨87127727705372764064216177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58085151803581842709477451 87127727705372764064216177)
              ·
                refine ⟨65345795779029573048162133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87127727705372764064216177 65345795779029573048162133)
                ·
                  refine ⟨382885522142751404579075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65345795779029573048162133 382885522142751404579075)
                  ·
                    rfl

theorem cell22_3355501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_3355501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355501 prefixEnd_3355501 := by exact prefixLift 3355501
  have htrace : WordTrace (prefixWord ++ tailWord_3355501) baseStart_3355501 baseEnd_3355501 := by
    simpa [prefixWord, tailWord_3355501, baseEnd_3355501] using wordTrace_append hprefix tailTrace_3355501
  have hstable : (prefixWord ++ tailWord_3355501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355501).length < 2 ^ (prefixWord ++ tailWord_3355501).sum := by decide
  have hdescent : baseEnd_3355501 < baseStart_3355501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355578 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 6, 3]
def baseStart_3355578 : Nat := 118140960795 + 3355578 * 2 ^ 59
def prefixEnd_3355578 : Nat := 4983230072969 + 3 ^ 40 * 3355578 * 2
def baseEnd_3355578 : Nat := 1148682925101851679561989

theorem tailTrace_3355578 : CollatzResearch.WordTrace tailWord_3355578 prefixEnd_3355578 1148682925101851679561989 := by
  unfold tailWord_3355578
  simp only [CollatzResearch.WordTrace]
  refine ⟨30596996059330366985428847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81591989491547645294476925 30596996059330366985428847)
  ·
    refine ⟨45895494088995550478143271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30596996059330366985428847 45895494088995550478143271)
    ·
      refine ⟨68843241133493325717214907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45895494088995550478143271 68843241133493325717214907)
      ·
        refine ⟨103264861700239988575822361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68843241133493325717214907 103264861700239988575822361)
        ·
          refine ⟨77448646275179991431866771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103264861700239988575822361 77448646275179991431866771)
          ·
            refine ⟨116172969412769987147800157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77448646275179991431866771 116172969412769987147800157)
            ·
              refine ⟨43564863529788745180425059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116172969412769987147800157 43564863529788745180425059)
              ·
                refine ⟨65347295294683117770637589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43564863529788745180425059 65347295294683117770637589)
                ·
                  refine ⟨3063154466938271145498637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65347295294683117770637589 3063154466938271145498637)
                  ·
                    refine ⟨1148682925101851679561989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3063154466938271145498637 1148682925101851679561989)
                    ·
                      rfl

theorem cell22_3355578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_3355578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355578 prefixEnd_3355578 := by exact prefixLift 3355578
  have htrace : WordTrace (prefixWord ++ tailWord_3355578) baseStart_3355578 baseEnd_3355578 := by
    simpa [prefixWord, tailWord_3355578, baseEnd_3355578] using wordTrace_append hprefix tailTrace_3355578
  have hstable : (prefixWord ++ tailWord_3355578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355578).length < 2 ^ (prefixWord ++ tailWord_3355578).sum := by decide
  have hdescent : baseEnd_3355578 < baseStart_3355578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355590 : List Nat := [6, 1, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_3355590 : Nat := 118140960795 + 3355590 * 2 ^ 59
def prefixEnd_3355590 : Nat := 4983230072969 + 3 ^ 40 * 3355590 * 2
def baseEnd_3355590 : Nat := 1148687032947087648261953

theorem tailTrace_3355590 : CollatzResearch.WordTrace tailWord_3355590 prefixEnd_3355590 1148687032947087648261953 := by
  unfold tailWord_3355590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3824638184789937312223507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81592281275518662660768149 3824638184789937312223507)
  ·
    refine ⟨5736957277184905968335261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3824638184789937312223507 5736957277184905968335261)
    ·
      refine ⟨2151358978944339738125723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5736957277184905968335261 2151358978944339738125723)
      ·
        refine ⟨3227038468416509607188585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2151358978944339738125723 3227038468416509607188585)
        ·
          refine ⟨2420278851312382205391439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3227038468416509607188585 2420278851312382205391439)
          ·
            refine ⟨3630418276968573308087159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2420278851312382205391439 3630418276968573308087159)
            ·
              refine ⟨5445627415452859962130739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3630418276968573308087159 5445627415452859962130739)
              ·
                refine ⟨8168441123179289943196109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5445627415452859962130739 8168441123179289943196109)
                ·
                  refine ⟨3063165421192233728698541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8168441123179289943196109 3063165421192233728698541)
                  ·
                    refine ⟨1148687032947087648261953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3063165421192233728698541 1148687032947087648261953)
                    ·
                      rfl

theorem cell22_3355590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_3355590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355590 prefixEnd_3355590 := by exact prefixLift 3355590
  have htrace : WordTrace (prefixWord ++ tailWord_3355590) baseStart_3355590 baseEnd_3355590 := by
    simpa [prefixWord, tailWord_3355590, baseEnd_3355590] using wordTrace_append hprefix tailTrace_3355590
  have hstable : (prefixWord ++ tailWord_3355590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355590).length < 2 ^ (prefixWord ++ tailWord_3355590).sum := by decide
  have hdescent : baseEnd_3355590 < baseStart_3355590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355591 : List Nat := [1, 1, 4, 1, 1, 2, 12]
def baseStart_3355591 : Nat := 118140960795 + 3355591 * 2 ^ 59
def prefixEnd_3355591 : Nat := 4983230072969 + 3 ^ 40 * 3355591 * 2
def baseEnd_3355591 : Nat := 42543976861760147369887

theorem tailTrace_3355591 : CollatzResearch.WordTrace tailWord_3355591 prefixEnd_3355591 42543976861760147369887 := by
  unfold tailWord_3355591
  simp only [CollatzResearch.WordTrace]
  refine ⟨122388458386274371161938627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81592305590849580774625751 122388458386274371161938627)
  ·
    refine ⟨183582687579411556742907941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122388458386274371161938627 183582687579411556742907941)
    ·
      refine ⟨34421753921139666889295239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183582687579411556742907941 34421753921139666889295239)
      ·
        refine ⟨51632630881709500333942859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34421753921139666889295239 51632630881709500333942859)
        ·
          refine ⟨77448946322564250500914289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51632630881709500333942859 77448946322564250500914289)
          ·
            refine ⟨58086709741923187875685717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77448946322564250500914289 58086709741923187875685717)
            ·
              refine ⟨42543976861760147369887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 58086709741923187875685717 42543976861760147369887)
              ·
                rfl

theorem cell22_3355591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 12].length) (baseStart_3355591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355591 prefixEnd_3355591 := by exact prefixLift 3355591
  have htrace : WordTrace (prefixWord ++ tailWord_3355591) baseStart_3355591 baseEnd_3355591 := by
    simpa [prefixWord, tailWord_3355591, baseEnd_3355591] using wordTrace_append hprefix tailTrace_3355591
  have hstable : (prefixWord ++ tailWord_3355591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355591).length < 2 ^ (prefixWord ++ tailWord_3355591).sum := by decide
  have hdescent : baseEnd_3355591 < baseStart_3355591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355608 : List Nat := [2, 1, 2, 2, 2, 4, 2, 7]
def baseStart_3355608 : Nat := 118140960795 + 3355608 * 2 ^ 59
def prefixEnd_3355608 : Nat := 4983230072969 + 3 ^ 40 * 3355608 * 2
def baseEnd_3355608 : Nat := 127632577190549066812433

theorem tailTrace_3355608 : CollatzResearch.WordTrace tailWord_3355608 prefixEnd_3355608 127632577190549066812433 := by
  unfold tailWord_3355608
  simp only [CollatzResearch.WordTrace]
  refine ⟨61194539213606391532653739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81592718951475188710204985 61194539213606391532653739)
  ·
    refine ⟨91791808820409587298980609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61194539213606391532653739 91791808820409587298980609)
    ·
      refine ⟨68843856615307190474235457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91791808820409587298980609 68843856615307190474235457)
      ·
        refine ⟨51632892461480392855676593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68843856615307190474235457 51632892461480392855676593)
        ·
          refine ⟨38724669346110294641757445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51632892461480392855676593 38724669346110294641757445)
          ·
            refine ⟨7260875502395680245329521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38724669346110294641757445 7260875502395680245329521)
            ·
              refine ⟨5445656626796760183997141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7260875502395680245329521 5445656626796760183997141)
              ·
                refine ⟨127632577190549066812433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5445656626796760183997141 127632577190549066812433)
                ·
                  rfl

theorem cell22_3355608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 7].length) (baseStart_3355608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355608 prefixEnd_3355608 := by exact prefixLift 3355608
  have htrace : WordTrace (prefixWord ++ tailWord_3355608) baseStart_3355608 baseEnd_3355608 := by
    simpa [prefixWord, tailWord_3355608, baseEnd_3355608] using wordTrace_append hprefix tailTrace_3355608
  have hstable : (prefixWord ++ tailWord_3355608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355608).length < 2 ^ (prefixWord ++ tailWord_3355608).sum := by decide
  have hdescent : baseEnd_3355608 < baseStart_3355608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355698 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 8]
def baseStart_3355698 : Nat := 118140960795 + 3355698 * 2 ^ 59
def prefixEnd_3355698 : Nat := 4983230072969 + 3 ^ 40 * 3355698 * 2
def baseEnd_3355698 : Nat := 382908001184737122187207

theorem tailTrace_3355698 : CollatzResearch.WordTrace tailWord_3355698 prefixEnd_3355698 382908001184737122187207 := by
  unfold tailWord_3355698
  simp only [CollatzResearch.WordTrace]
  refine ⟨30598090249221682109020937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81594907331257818957389165 30598090249221682109020937)
  ·
    refine ⟨22948567686916261581765703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30598090249221682109020937 22948567686916261581765703)
    ·
      refine ⟨34422851530374392372648555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22948567686916261581765703 34422851530374392372648555)
      ·
        refine ⟨51634277295561588558972833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34422851530374392372648555 51634277295561588558972833)
        ·
          refine ⟨38725707971671191419229625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51634277295561588558972833 38725707971671191419229625)
          ·
            refine ⟨29044280978753393564422219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38725707971671191419229625 29044280978753393564422219)
            ·
              refine ⟨43566421468130090346633329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29044280978753393564422219 43566421468130090346633329)
              ·
                refine ⟨32674816101097567759974997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43566421468130090346633329 32674816101097567759974997)
                ·
                  refine ⟨382908001184737122187207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32674816101097567759974997 382908001184737122187207)
                  ·
                    rfl

theorem cell22_3355698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_3355698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355698 prefixEnd_3355698 := by exact prefixLift 3355698
  have htrace : WordTrace (prefixWord ++ tailWord_3355698) baseStart_3355698 baseEnd_3355698 := by
    simpa [prefixWord, tailWord_3355698, baseEnd_3355698] using wordTrace_append hprefix tailTrace_3355698
  have hstable : (prefixWord ++ tailWord_3355698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355698).length < 2 ^ (prefixWord ++ tailWord_3355698).sum := by decide
  have hdescent : baseEnd_3355698 < baseStart_3355698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355715 : List Nat := [1, 1, 1, 3, 1, 2, 3, 6, 4]
def baseStart_3355715 : Nat := 118140960795 + 3355715 * 2 ^ 59
def prefixEnd_3355715 : Nat := 4983230072969 + 3 ^ 40 * 3355715 * 2
def baseEnd_3355715 : Nat := 382909941000542996295523

theorem tailTrace_3355715 : CollatzResearch.WordTrace tailWord_3355715 prefixEnd_3355715 382909941000542996295523 := by
  unfold tailWord_3355715
  simp only [CollatzResearch.WordTrace]
  refine ⟨122392981037825140339452599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81595320691883426892968399 122392981037825140339452599)
  ·
    refine ⟨183589471556737710509178899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122392981037825140339452599 183589471556737710509178899)
    ·
      refine ⟨275384207335106565763768349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183589471556737710509178899 275384207335106565763768349)
      ·
        refine ⟨103269077750664962161413131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275384207335106565763768349 103269077750664962161413131)
        ·
          refine ⟨154903616625997443242119697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103269077750664962161413131 154903616625997443242119697)
          ·
            refine ⟨116177712469498082431589773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154903616625997443242119697 116177712469498082431589773)
            ·
              refine ⟨43566642176061780911846165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116177712469498082431589773 43566642176061780911846165)
              ·
                refine ⟨2042186352002895980242789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43566642176061780911846165 2042186352002895980242789)
                ·
                  refine ⟨382909941000542996295523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2042186352002895980242789 382909941000542996295523)
                  ·
                    rfl

theorem cell22_3355715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 4].length) (baseStart_3355715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355715 prefixEnd_3355715 := by exact prefixLift 3355715
  have htrace : WordTrace (prefixWord ++ tailWord_3355715) baseStart_3355715 baseEnd_3355715 := by
    simpa [prefixWord, tailWord_3355715, baseEnd_3355715] using wordTrace_append hprefix tailTrace_3355715
  have hstable : (prefixWord ++ tailWord_3355715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355715).length < 2 ^ (prefixWord ++ tailWord_3355715).sum := by decide
  have hdescent : baseEnd_3355715 < baseStart_3355715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355743 : List Nat := [1, 1, 2, 3, 1, 1, 5, 8]
def baseStart_3355743 : Nat := 118140960795 + 3355743 * 2 ^ 59
def prefixEnd_3355743 : Nat := 4983230072969 + 3 ^ 40 * 3355743 * 2
def baseEnd_3355743 : Nat := 127637711997094027687387

theorem tailTrace_3355743 : CollatzResearch.WordTrace tailWord_3355743 prefixEnd_3355743 127637711997094027687387 := by
  unfold tailWord_3355743
  simp only [CollatzResearch.WordTrace]
  refine ⟨122394002281723701121471883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81596001521149134080981255 122394002281723701121471883)
  ·
    refine ⟨183591003422585551682207825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122394002281723701121471883 183591003422585551682207825)
    ·
      refine ⟨137693252566939163761655869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183591003422585551682207825 137693252566939163761655869)
      ·
        refine ⟨51634969712602186410620951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137693252566939163761655869 51634969712602186410620951)
        ·
          refine ⟨77452454568903279615931427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51634969712602186410620951 77452454568903279615931427)
          ·
            refine ⟨116178681853354919423897141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77452454568903279615931427 116178681853354919423897141)
            ·
              refine ⟨10891751423752023695990357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116178681853354919423897141 10891751423752023695990357)
              ·
                refine ⟨127637711997094027687387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10891751423752023695990357 127637711997094027687387)
                ·
                  rfl

theorem cell22_3355743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 8].length) (baseStart_3355743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355743 prefixEnd_3355743 := by exact prefixLift 3355743
  have htrace : WordTrace (prefixWord ++ tailWord_3355743) baseStart_3355743 baseEnd_3355743 := by
    simpa [prefixWord, tailWord_3355743, baseEnd_3355743] using wordTrace_append hprefix tailTrace_3355743
  have hstable : (prefixWord ++ tailWord_3355743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355743).length < 2 ^ (prefixWord ++ tailWord_3355743).sum := by decide
  have hdescent : baseEnd_3355743 < baseStart_3355743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355781 : List Nat := [1, 3, 1, 1, 6, 2, 2, 1, 2, 3]
def baseStart_3355781 : Nat := 118140960795 + 3355781 * 2 ^ 59
def prefixEnd_3355781 : Nat := 4983230072969 + 3 ^ 40 * 3355781 * 2
def baseEnd_3355781 : Nat := 1148752416150426816736367

theorem tailTrace_3355781 : CollatzResearch.WordTrace tailWord_3355781 prefixEnd_3355781 1148752416150426816736367 := by
  unfold tailWord_3355781
  simp only [CollatzResearch.WordTrace]
  refine ⟨122395388255586033611355197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81596925503724022407570131 122395388255586033611355197)
  ·
    refine ⟨45898270595844762604258199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122395388255586033611355197 45898270595844762604258199)
    ·
      refine ⟨68847405893767143906387299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45898270595844762604258199 68847405893767143906387299)
      ·
        refine ⟨103271108840650715859580949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68847405893767143906387299 103271108840650715859580949)
        ·
          refine ⟨4840833226905502305917857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 103271108840650715859580949 4840833226905502305917857)
          ·
            refine ⟨3630624920179126729438393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4840833226905502305917857 3630624920179126729438393)
            ·
              refine ⟨2722968690134345047078795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3630624920179126729438393 2722968690134345047078795)
              ·
                refine ⟨4084453035201517570618193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2722968690134345047078795 4084453035201517570618193)
                ·
                  refine ⟨3063339776401138177963645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4084453035201517570618193 3063339776401138177963645)
                  ·
                    refine ⟨1148752416150426816736367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3063339776401138177963645 1148752416150426816736367)
                    ·
                      rfl

theorem cell22_3355781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 2, 3].length) (baseStart_3355781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355781 prefixEnd_3355781 := by exact prefixLift 3355781
  have htrace : WordTrace (prefixWord ++ tailWord_3355781) baseStart_3355781 baseEnd_3355781 := by
    simpa [prefixWord, tailWord_3355781, baseEnd_3355781] using wordTrace_append hprefix tailTrace_3355781
  have hstable : (prefixWord ++ tailWord_3355781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355781).length < 2 ^ (prefixWord ++ tailWord_3355781).sum := by decide
  have hdescent : baseEnd_3355781 < baseStart_3355781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355809 : List Nat := [1, 2, 3, 3, 1, 1, 2, 5, 1, 3]
def baseStart_3355809 : Nat := 118140960795 + 3355809 * 2 ^ 59
def prefixEnd_3355809 : Nat := 4983230072969 + 3 ^ 40 * 3355809 * 2
def baseEnd_3355809 : Nat := 1148762001122644077036281

theorem tailTrace_3355809 : CollatzResearch.WordTrace tailWord_3355809 prefixEnd_3355809 1148762001122644077036281 := by
  unfold tailWord_3355809
  simp only [CollatzResearch.WordTrace]
  refine ⟨122396409499484594393374481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81597606332989729595582987 122396409499484594393374481)
  ·
    refine ⟨91797307124613445795030861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122396409499484594393374481 91797307124613445795030861)
    ·
      refine ⟨34423990171730042173136573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91797307124613445795030861 34423990171730042173136573)
      ·
        refine ⟨12908996314398765814926215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34423990171730042173136573 12908996314398765814926215)
        ·
          refine ⟨19363494471598148722389323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12908996314398765814926215 19363494471598148722389323)
          ·
            refine ⟨29045241707397223083583985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19363494471598148722389323 29045241707397223083583985)
            ·
              refine ⟨21783931280547917312687989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29045241707397223083583985 21783931280547917312687989)
              ·
                refine ⟨2042243557551367248064499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21783931280547917312687989 2042243557551367248064499)
                ·
                  refine ⟨3063365336327050872096749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2042243557551367248064499 3063365336327050872096749)
                  ·
                    refine ⟨1148762001122644077036281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3063365336327050872096749 1148762001122644077036281)
                    ·
                      rfl

theorem cell22_3355809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_3355809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355809 prefixEnd_3355809 := by exact prefixLift 3355809
  have htrace : WordTrace (prefixWord ++ tailWord_3355809) baseStart_3355809 baseEnd_3355809 := by
    simpa [prefixWord, tailWord_3355809, baseEnd_3355809] using wordTrace_append hprefix tailTrace_3355809
  have hstable : (prefixWord ++ tailWord_3355809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355809).length < 2 ^ (prefixWord ++ tailWord_3355809).sum := by decide
  have hdescent : baseEnd_3355809 < baseStart_3355809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355826 : List Nat := [3, 2, 1, 1, 1, 4, 4, 2, 1, 3]
def baseStart_3355826 : Nat := 118140960795 + 3355826 * 2 ^ 59
def prefixEnd_3355826 : Nat := 4983230072969 + 3 ^ 40 * 3355826 * 2
def baseEnd_3355826 : Nat := 1148767820570061699361229

theorem tailTrace_3355826 : CollatzResearch.WordTrace tailWord_3355826 prefixEnd_3355826 1148767820570061699361229 := by
  unfold tailWord_3355826
  simp only [CollatzResearch.WordTrace]
  refine ⟨30599257385105751574185833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81598019693615337531162221 30599257385105751574185833)
  ·
    refine ⟨22949443038829313680639375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30599257385105751574185833 22949443038829313680639375)
    ·
      refine ⟨34424164558243970520959063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22949443038829313680639375 34424164558243970520959063)
      ·
        refine ⟨51636246837365955781438595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34424164558243970520959063 51636246837365955781438595)
        ·
          refine ⟨77454370256048933672157893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51636246837365955781438595 77454370256048933672157893)
          ·
            refine ⟨14522694423009175063529605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77454370256048933672157893 14522694423009175063529605)
            ·
              refine ⟨2723005204314220324411801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14522694423009175063529605 2723005204314220324411801)
              ·
                refine ⟨2042253903235665243308851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2723005204314220324411801 2042253903235665243308851)
                ·
                  refine ⟨3063380854853497864963277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2042253903235665243308851 3063380854853497864963277)
                  ·
                    refine ⟨1148767820570061699361229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3063380854853497864963277 1148767820570061699361229)
                    ·
                      rfl

theorem cell22_3355826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_3355826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355826 prefixEnd_3355826 := by exact prefixLift 3355826
  have htrace : WordTrace (prefixWord ++ tailWord_3355826) baseStart_3355826 baseEnd_3355826 := by
    simpa [prefixWord, tailWord_3355826, baseEnd_3355826] using wordTrace_append hprefix tailTrace_3355826
  have hstable : (prefixWord ++ tailWord_3355826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355826).length < 2 ^ (prefixWord ++ tailWord_3355826).sum := by decide
  have hdescent : baseEnd_3355826 < baseStart_3355826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355850 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 8]
def baseStart_3355850 : Nat := 118140960795 + 3355850 * 2 ^ 59
def prefixEnd_3355850 : Nat := 4983230072969 + 3 ^ 40 * 3355850 * 2
def baseEnd_3355850 : Nat := 382925345420177878920385

theorem tailTrace_3355850 : CollatzResearch.WordTrace tailWord_3355850 prefixEnd_3355850 382925345420177878920385 := by
  unfold tailWord_3355850
  simp only [CollatzResearch.WordTrace]
  refine ⟨30599476223084014598904251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81598603261557372263744669 30599476223084014598904251)
  ·
    refine ⟨45899214334626021898356377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30599476223084014598904251 45899214334626021898356377)
    ·
      refine ⟨34424410750969516423767283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45899214334626021898356377 34424410750969516423767283)
      ·
        refine ⟨51636616126454274635650925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34424410750969516423767283 51636616126454274635650925)
        ·
          refine ⟨19363731047420352988369097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51636616126454274635650925 19363731047420352988369097)
          ·
            refine ⟨14522798285565264741276823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19363731047420352988369097 14522798285565264741276823)
            ·
              refine ⟨21784197428347897111915235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14522798285565264741276823 21784197428347897111915235)
              ·
                refine ⟨32676296142521845667872853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21784197428347897111915235 32676296142521845667872853)
                ·
                  refine ⟨382925345420177878920385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32676296142521845667872853 382925345420177878920385)
                  ·
                    rfl

theorem cell22_3355850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_3355850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355850 prefixEnd_3355850 := by exact prefixLift 3355850
  have htrace : WordTrace (prefixWord ++ tailWord_3355850) baseStart_3355850 baseEnd_3355850 := by
    simpa [prefixWord, tailWord_3355850, baseEnd_3355850] using wordTrace_append hprefix tailTrace_3355850
  have hstable : (prefixWord ++ tailWord_3355850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355850).length < 2 ^ (prefixWord ++ tailWord_3355850).sum := by decide
  have hdescent : baseEnd_3355850 < baseStart_3355850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355912 : List Nat := [2, 1, 3, 2, 4, 1, 1, 8]
def baseStart_3355912 : Nat := 118140960795 + 3355912 * 2 ^ 59
def prefixEnd_3355912 : Nat := 4983230072969 + 3 ^ 40 * 3355912 * 2
def baseEnd_3355912 : Nat := 127644140014176237967885

theorem tailTrace_3355912 : CollatzResearch.WordTrace tailWord_3355912 prefixEnd_3355912 127644140014176237967885 := by
  unfold tailWord_3355912
  simp only [CollatzResearch.WordTrace]
  refine ⟨61200083109055721492186995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81600110812074295322915993 61200083109055721492186995)
  ·
    refine ⟨91800124663583582238280493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61200083109055721492186995 91800124663583582238280493)
    ·
      refine ⟨34425046748843843339355185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91800124663583582238280493 34425046748843843339355185)
      ·
        refine ⟨25818785061632882504516389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34425046748843843339355185 25818785061632882504516389)
        ·
          refine ⟨4841022199056165469596823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25818785061632882504516389 4841022199056165469596823)
          ·
            refine ⟨7261533298584248204395235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4841022199056165469596823 7261533298584248204395235)
            ·
              refine ⟨10892299947876372306592853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7261533298584248204395235 10892299947876372306592853)
              ·
                refine ⟨127644140014176237967885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10892299947876372306592853 127644140014176237967885)
                ·
                  rfl

theorem cell22_3355912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 8].length) (baseStart_3355912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355912 prefixEnd_3355912 := by exact prefixLift 3355912
  have htrace : WordTrace (prefixWord ++ tailWord_3355912) baseStart_3355912 baseEnd_3355912 := by
    simpa [prefixWord, tailWord_3355912, baseEnd_3355912] using wordTrace_append hprefix tailTrace_3355912
  have hstable : (prefixWord ++ tailWord_3355912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355912).length < 2 ^ (prefixWord ++ tailWord_3355912).sum := by decide
  have hdescent : baseEnd_3355912 < baseStart_3355912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355925 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 1, 8]
def baseStart_3355925 : Nat := 118140960795 + 3355925 * 2 ^ 59
def prefixEnd_3355925 : Nat := 4983230072969 + 3 ^ 40 * 3355925 * 2
def baseEnd_3355925 : Nat := 1148801710293258441135925

theorem tailTrace_3355925 : CollatzResearch.WordTrace tailWord_3355925 prefixEnd_3355925 1148801710293258441135925 := by
  unfold tailWord_3355925
  simp only [CollatzResearch.WordTrace]
  refine ⟨122400640367064346204597229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81600426911376230803064819 122400640367064346204597229)
  ·
    refine ⟨45900240137649129826723961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122400640367064346204597229 45900240137649129826723961)
    ·
      refine ⟨34425180103236847370042971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45900240137649129826723961 34425180103236847370042971)
      ·
        refine ⟨51637770154855271055064457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34425180103236847370042971 51637770154855271055064457)
        ·
          refine ⟨38728327616141453291298343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51637770154855271055064457 38728327616141453291298343)
          ·
            refine ⟨58092491424212179936947515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38728327616141453291298343 58092491424212179936947515)
            ·
              refine ⟨87138737136318269905421273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58092491424212179936947515 87138737136318269905421273)
              ·
                refine ⟨65354052852238702429065955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87138737136318269905421273 65354052852238702429065955)
                ·
                  refine ⟨98031079278358053643598933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65354052852238702429065955 98031079278358053643598933)
                  ·
                    refine ⟨1148801710293258441135925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98031079278358053643598933 1148801710293258441135925)
                    ·
                      rfl

theorem cell22_3355925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_3355925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3355925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3355925 prefixEnd_3355925 := by exact prefixLift 3355925
  have htrace : WordTrace (prefixWord ++ tailWord_3355925) baseStart_3355925 baseEnd_3355925 := by
    simpa [prefixWord, tailWord_3355925, baseEnd_3355925] using wordTrace_append hprefix tailTrace_3355925
  have hstable : (prefixWord ++ tailWord_3355925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355925).length < 2 ^ (prefixWord ++ tailWord_3355925).sum := by decide
  have hdescent : baseEnd_3355925 < baseStart_3355925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356017 : List Nat := [1, 2, 2, 2, 1, 2, 3, 3, 1, 5]
def baseStart_3356017 : Nat := 118140960795 + 3356017 * 2 ^ 59
def prefixEnd_3356017 : Nat := 4983230072969 + 3 ^ 40 * 3356017 * 2
def baseEnd_3356017 : Nat := 1148833203773400867835643

theorem tailTrace_3356017 : CollatzResearch.WordTrace tailWord_3356017 prefixEnd_3356017 1148833203773400867835643 := by
  unfold tailWord_3356017
  simp only [CollatzResearch.WordTrace]
  refine ⟨122403995882731045916946305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81602663921820697277964203 122403995882731045916946305)
  ·
    refine ⟨91802996912048284437709729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122403995882731045916946305 91802996912048284437709729)
    ·
      refine ⟨68852247684036213328282297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91802996912048284437709729 68852247684036213328282297)
      ·
        refine ⟨51639185763027159996211723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68852247684036213328282297 51639185763027159996211723)
        ·
          refine ⟨77458778644540739994317585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51639185763027159996211723 77458778644540739994317585)
          ·
            refine ⟨58094083983405554995738189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77458778644540739994317585 58094083983405554995738189)
            ·
              refine ⟨21785281493777083123401821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58094083983405554995738189 21785281493777083123401821)
              ·
                refine ⟨8169480560166406171275683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21785281493777083123401821 8169480560166406171275683)
                ·
                  refine ⟨12254220840249609256913525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8169480560166406171275683 12254220840249609256913525)
                  ·
                    refine ⟨1148833203773400867835643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12254220840249609256913525 1148833203773400867835643)
                    ·
                      rfl

theorem cell22_3356017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_3356017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356017 prefixEnd_3356017 := by exact prefixLift 3356017
  have htrace : WordTrace (prefixWord ++ tailWord_3356017) baseStart_3356017 baseEnd_3356017 := by
    simpa [prefixWord, tailWord_3356017, baseEnd_3356017] using wordTrace_append hprefix tailTrace_3356017
  have hstable : (prefixWord ++ tailWord_3356017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356017).length < 2 ^ (prefixWord ++ tailWord_3356017).sum := by decide
  have hdescent : baseEnd_3356017 < baseStart_3356017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356036 : List Nat := [2, 3, 2, 1, 1, 4, 2, 3, 4]
def baseStart_3356036 : Nat := 118140960795 + 3356036 * 2 ^ 59
def prefixEnd_3356036 : Nat := 4983230072969 + 3 ^ 40 * 3356036 * 2
def baseEnd_3356036 : Nat := 382946569287230383870195

theorem tailTrace_3356036 : CollatzResearch.WordTrace tailWord_3356036 prefixEnd_3356036 382946569287230383870195 := by
  unfold tailWord_3356036
  simp only [CollatzResearch.WordTrace]
  refine ⟨61202344434831106080943981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81603125913108141441258641 61202344434831106080943981)
  ·
    refine ⟨22950879163061664780353993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61202344434831106080943981 22950879163061664780353993)
    ·
      refine ⟨17213159372296248585265495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22950879163061664780353993 17213159372296248585265495)
      ·
        refine ⟨25819739058444372877898243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17213159372296248585265495 25819739058444372877898243)
        ·
          refine ⟨38729608587666559316847365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25819739058444372877898243 38729608587666559316847365)
          ·
            refine ⟨7261801610187479871908881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38729608587666559316847365 7261801610187479871908881)
            ·
              refine ⟨5446351207640609903931661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7261801610187479871908881 5446351207640609903931661)
              ·
                refine ⟨2042381702865228713974373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5446351207640609903931661 2042381702865228713974373)
                ·
                  refine ⟨382946569287230383870195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2042381702865228713974373 382946569287230383870195)
                  ·
                    rfl

theorem cell22_3356036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_3356036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356036 prefixEnd_3356036 := by exact prefixLift 3356036
  have htrace : WordTrace (prefixWord ++ tailWord_3356036) baseStart_3356036 baseEnd_3356036 := by
    simpa [prefixWord, tailWord_3356036, baseEnd_3356036] using wordTrace_append hprefix tailTrace_3356036
  have hstable : (prefixWord ++ tailWord_3356036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356036).length < 2 ^ (prefixWord ++ tailWord_3356036).sum := by decide
  have hdescent : baseEnd_3356036 < baseStart_3356036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356107 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 4, 5]
def baseStart_3356107 : Nat := 118140960795 + 3356107 * 2 ^ 59
def prefixEnd_3356107 : Nat := 4983230072969 + 3 ^ 40 * 3356107 * 2
def baseEnd_3356107 : Nat := 1148864012612670633085367

theorem tailTrace_3356107 : CollatzResearch.WordTrace tailWord_3356107 prefixEnd_3356107 1148864012612670633085367 := by
  unfold tailWord_3356107
  simp only [CollatzResearch.WordTrace]
  refine ⟨122407278452404991287722575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81604852301603327525148383 122407278452404991287722575)
  ·
    refine ⟨183610917678607486931583863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122407278452404991287722575 183610917678607486931583863)
    ·
      refine ⟨275416376517911230397375795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183610917678607486931583863 275416376517911230397375795)
      ·
        refine ⟨413124564776866845596063693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275416376517911230397375795 413124564776866845596063693)
        ·
          refine ⟨154921711791325067098523885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 413124564776866845596063693 154921711791325067098523885)
          ·
            refine ⟨58095641921746900161946457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154921711791325067098523885 58095641921746900161946457)
            ·
              refine ⟨43571731441310175121459843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58095641921746900161946457 43571731441310175121459843)
              ·
                refine ⟨65357597161965262682189765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43571731441310175121459843 65357597161965262682189765)
                ·
                  refine ⟨12254549467868486752910581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65357597161965262682189765 12254549467868486752910581)
                  ·
                    refine ⟨1148864012612670633085367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12254549467868486752910581 1148864012612670633085367)
                    ·
                      rfl

theorem cell22_3356107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 5].length) (baseStart_3356107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356107 prefixEnd_3356107 := by exact prefixLift 3356107
  have htrace : WordTrace (prefixWord ++ tailWord_3356107) baseStart_3356107 baseEnd_3356107 := by
    simpa [prefixWord, tailWord_3356107, baseEnd_3356107] using wordTrace_append hprefix tailTrace_3356107
  have hstable : (prefixWord ++ tailWord_3356107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356107).length < 2 ^ (prefixWord ++ tailWord_3356107).sum := by decide
  have hdescent : baseEnd_3356107 < baseStart_3356107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356139 : List Nat := [1, 1, 1, 1, 2, 3, 2, 6, 1, 4]
def baseStart_3356139 : Nat := 118140960795 + 3356139 * 2 ^ 59
def prefixEnd_3356139 : Nat := 4983230072969 + 3 ^ 40 * 3356139 * 2
def baseEnd_3356139 : Nat := 1148874966866633216285269

theorem tailTrace_3356139 : CollatzResearch.WordTrace tailWord_3356139 prefixEnd_3356139 1148874966866633216285269 := by
  unfold tailWord_3356139
  simp only [CollatzResearch.WordTrace]
  refine ⟨122408445588289060752887471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81605630392192707168591647 122408445588289060752887471)
  ·
    refine ⟨183612668382433591129331207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122408445588289060752887471 183612668382433591129331207)
    ·
      refine ⟨275419002573650386693996811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183612668382433591129331207 275419002573650386693996811)
      ·
        refine ⟨413128503860475580040995217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275419002573650386693996811 413128503860475580040995217)
        ·
          refine ⟨309846377895356685030746413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413128503860475580040995217 309846377895356685030746413)
          ·
            refine ⟨116192391710758756886529905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309846377895356685030746413 116192391710758756886529905)
            ·
              refine ⟨87144293783069067664897429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116192391710758756886529905 87144293783069067664897429)
              ·
                refine ⟨4084888771081362546792067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87144293783069067664897429 4084888771081362546792067)
                ·
                  refine ⟨6127333156622043820188101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4084888771081362546792067 6127333156622043820188101)
                  ·
                    refine ⟨1148874966866633216285269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6127333156622043820188101 1148874966866633216285269)
                    ·
                      rfl

theorem cell22_3356139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 4].length) (baseStart_3356139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356139 prefixEnd_3356139 := by exact prefixLift 3356139
  have htrace : WordTrace (prefixWord ++ tailWord_3356139) baseStart_3356139 baseEnd_3356139 := by
    simpa [prefixWord, tailWord_3356139, baseEnd_3356139] using wordTrace_append hprefix tailTrace_3356139
  have hstable : (prefixWord ++ tailWord_3356139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356139).length < 2 ^ (prefixWord ++ tailWord_3356139).sum := by decide
  have hdescent : baseEnd_3356139 < baseStart_3356139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356164 : List Nat := [2, 3, 2, 3, 3, 1, 2, 2, 1, 3]
def baseStart_3356164 : Nat := 118140960795 + 3356164 * 2 ^ 59
def prefixEnd_3356164 : Nat := 4983230072969 + 3 ^ 40 * 3356164 * 2
def baseEnd_3356164 : Nat := 1148883524877541484410193

theorem tailTrace_3356164 : CollatzResearch.WordTrace tailWord_3356164 prefixEnd_3356164 1148883524877541484410193 := by
  unfold tailWord_3356164
  simp only [CollatzResearch.WordTrace]
  refine ⟨61204678706599245011273773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81606238275465660015031697 61204678706599245011273773)
  ·
    refine ⟨22951754514974716879227665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61204678706599245011273773 22951754514974716879227665)
    ·
      refine ⟨17213815886231037659420749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22951754514974716879227665 17213815886231037659420749)
      ·
        refine ⟨6455180957336639122282781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17213815886231037659420749 6455180957336639122282781)
        ·
          refine ⟨2420692859001239670856043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6455180957336639122282781 2420692859001239670856043)
          ·
            refine ⟨3631039288501859506284065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2420692859001239670856043 3631039288501859506284065)
            ·
              refine ⟨2723279466376394629713049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3631039288501859506284065 2723279466376394629713049)
              ·
                refine ⟨2042459599782295972284787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2723279466376394629713049 2042459599782295972284787)
                ·
                  refine ⟨3063689399673443958427181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2042459599782295972284787 3063689399673443958427181)
                  ·
                    refine ⟨1148883524877541484410193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3063689399673443958427181 1148883524877541484410193)
                    ·
                      rfl

theorem cell22_3356164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_3356164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356164 prefixEnd_3356164 := by exact prefixLift 3356164
  have htrace : WordTrace (prefixWord ++ tailWord_3356164) baseStart_3356164 baseEnd_3356164 := by
    simpa [prefixWord, tailWord_3356164, baseEnd_3356164] using wordTrace_append hprefix tailTrace_3356164
  have hstable : (prefixWord ++ tailWord_3356164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356164).length < 2 ^ (prefixWord ++ tailWord_3356164).sum := by decide
  have hdescent : baseEnd_3356164 < baseStart_3356164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356220 : List Nat := [2, 2, 2, 2, 4, 2, 1, 2, 2, 3]
def baseStart_3356220 : Nat := 118140960795 + 3356220 * 2 ^ 59
def prefixEnd_3356220 : Nat := 4983230072969 + 3 ^ 40 * 3356220 * 2
def baseEnd_3356220 : Nat := 1148902694821976005010021

theorem tailTrace_3356220 : CollatzResearch.WordTrace tailWord_3356220 prefixEnd_3356220 1148902694821976005010021 := by
  unfold tailWord_3356220
  simp only [CollatzResearch.WordTrace]
  refine ⟨61205699950497805793293057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81607599933997074391057409 61205699950497805793293057)
  ·
    refine ⟨45904274962873354344969793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61205699950497805793293057 45904274962873354344969793)
    ·
      refine ⟨34428206222155015758727345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45904274962873354344969793 34428206222155015758727345)
      ·
        refine ⟨25821154666616261819045509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34428206222155015758727345 25821154666616261819045509)
        ·
          refine ⟨4841466499990549091071033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25821154666616261819045509 4841466499990549091071033)
          ·
            refine ⟨3631099874992911818303275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4841466499990549091071033 3631099874992911818303275)
            ·
              refine ⟨5446649812489367727454913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3631099874992911818303275 5446649812489367727454913)
              ·
                refine ⟨4084987359367025795591185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5446649812489367727454913 4084987359367025795591185)
                ·
                  refine ⟨3063740519525269346693389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4084987359367025795591185 3063740519525269346693389)
                  ·
                    refine ⟨1148902694821976005010021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3063740519525269346693389 1148902694821976005010021)
                    ·
                      rfl

theorem cell22_3356220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_3356220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356220 prefixEnd_3356220 := by exact prefixLift 3356220
  have htrace : WordTrace (prefixWord ++ tailWord_3356220) baseStart_3356220 baseEnd_3356220 := by
    simpa [prefixWord, tailWord_3356220, baseEnd_3356220] using wordTrace_append hprefix tailTrace_3356220
  have hstable : (prefixWord ++ tailWord_3356220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356220).length < 2 ^ (prefixWord ++ tailWord_3356220).sum := by decide
  have hdescent : baseEnd_3356220 < baseStart_3356220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356237 : List Nat := [1, 6, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_3356237 : Nat := 118140960795 + 3356237 * 2 ^ 59
def prefixEnd_3356237 : Nat := 4983230072969 + 3 ^ 40 * 3356237 * 2
def baseEnd_3356237 : Nat := 1148908514269393627334969

theorem tailTrace_3356237 : CollatzResearch.WordTrace tailWord_3356237 prefixEnd_3356237 1148908514269393627334969 := by
  unfold tailWord_3356237
  simp only [CollatzResearch.WordTrace]
  refine ⟨122412019941934023489954965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81608013294622682326636643 122412019941934023489954965)
  ·
    refine ⟨5738063434778157351091639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122412019941934023489954965 5738063434778157351091639)
    ·
      refine ⟨8607095152167236026637459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5738063434778157351091639 8607095152167236026637459)
      ·
        refine ⟨12910642728250854039956189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8607095152167236026637459 12910642728250854039956189)
        ·
          refine ⟨4841491023094070264983571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12910642728250854039956189 4841491023094070264983571)
          ·
            refine ⟨7262236534641105397475357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4841491023094070264983571 7262236534641105397475357)
            ·
              refine ⟨2723338700490414524053259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7262236534641105397475357 2723338700490414524053259)
              ·
                refine ⟨4085008050735621786079889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2723338700490414524053259 4085008050735621786079889)
                ·
                  refine ⟨3063756038051716339559917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4085008050735621786079889 3063756038051716339559917)
                  ·
                    refine ⟨1148908514269393627334969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3063756038051716339559917 1148908514269393627334969)
                    ·
                      rfl

theorem cell22_3356237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_3356237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356237 prefixEnd_3356237 := by exact prefixLift 3356237
  have htrace : WordTrace (prefixWord ++ tailWord_3356237) baseStart_3356237 baseEnd_3356237 := by
    simpa [prefixWord, tailWord_3356237, baseEnd_3356237] using wordTrace_append hprefix tailTrace_3356237
  have hstable : (prefixWord ++ tailWord_3356237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356237).length < 2 ^ (prefixWord ++ tailWord_3356237).sum := by decide
  have hdescent : baseEnd_3356237 < baseStart_3356237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356304 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 5, 5]
def baseStart_3356304 : Nat := 118140960795 + 3356304 * 2 ^ 59
def prefixEnd_3356304 : Nat := 4983230072969 + 3 ^ 40 * 3356304 * 2
def baseEnd_3356304 : Nat := 1148931449738627785909763

theorem tailTrace_3356304 : CollatzResearch.WordTrace tailWord_3356304 prefixEnd_3356304 1148931449738627785909763 := by
  unfold tailWord_3356304
  simp only [CollatzResearch.WordTrace]
  refine ⟨61207231816345646966321983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81609642421794195955095977 61207231816345646966321983)
  ·
    refine ⟨91810847724518470449482975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61207231816345646966321983 91810847724518470449482975)
    ·
      refine ⟨137716271586777705674224463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91810847724518470449482975 137716271586777705674224463)
      ·
        refine ⟨206574407380166558511336695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137716271586777705674224463 206574407380166558511336695)
        ·
          refine ⟨309861611070249837767005043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206574407380166558511336695 309861611070249837767005043)
          ·
            refine ⟨464792416605374756650507565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309861611070249837767005043 464792416605374756650507565)
            ·
              refine ⟨174297156227015533743940337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 464792416605374756650507565 174297156227015533743940337)
              ·
                refine ⟨130722867170261650307955253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174297156227015533743940337 130722867170261650307955253)
                ·
                  refine ⟨12255268797212029716370805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130722867170261650307955253 12255268797212029716370805)
                  ·
                    refine ⟨1148931449738627785909763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12255268797212029716370805 1148931449738627785909763)
                    ·
                      rfl

theorem cell22_3356304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_3356304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356304 prefixEnd_3356304 := by exact prefixLift 3356304
  have htrace : WordTrace (prefixWord ++ tailWord_3356304) baseStart_3356304 baseEnd_3356304 := by
    simpa [prefixWord, tailWord_3356304, baseEnd_3356304] using wordTrace_append hprefix tailTrace_3356304
  have hstable : (prefixWord ++ tailWord_3356304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356304).length < 2 ^ (prefixWord ++ tailWord_3356304).sum := by decide
  have hdescent : baseEnd_3356304 < baseStart_3356304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356321 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 3, 5]
def baseStart_3356321 : Nat := 118140960795 + 3356321 * 2 ^ 59
def prefixEnd_3356321 : Nat := 4983230072969 + 3 ^ 40 * 3356321 * 2
def baseEnd_3356321 : Nat := 1148937269186045408234711

theorem tailTrace_3356321 : CollatzResearch.WordTrace tailWord_3356321 prefixEnd_3356321 1148937269186045408234711 := by
  unfold tailWord_3356321
  simp only [CollatzResearch.WordTrace]
  refine ⟨122415083673629705836012817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81610055782419803890675211 122415083673629705836012817)
  ·
    refine ⟨91811312755222279377009613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122415083673629705836012817 91811312755222279377009613)
    ·
      refine ⟨34429242283208354766378605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91811312755222279377009613 34429242283208354766378605)
      ·
        refine ⟨12910965856203133037391977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34429242283208354766378605 12910965856203133037391977)
        ·
          refine ⟨9683224392152349778043983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12910965856203133037391977 9683224392152349778043983)
          ·
            refine ⟨14524836588228524667065975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9683224392152349778043983 14524836588228524667065975)
            ·
              refine ⟨21787254882342787000598963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14524836588228524667065975 21787254882342787000598963)
              ·
                refine ⟨32680882323514180500898445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21787254882342787000598963 32680882323514180500898445)
                ·
                  refine ⟨12255330871317817687836917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32680882323514180500898445 12255330871317817687836917)
                  ·
                    refine ⟨1148937269186045408234711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12255330871317817687836917 1148937269186045408234711)
                    ·
                      rfl

theorem cell22_3356321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_3356321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356321 prefixEnd_3356321 := by exact prefixLift 3356321
  have htrace : WordTrace (prefixWord ++ tailWord_3356321) baseStart_3356321 baseEnd_3356321 := by
    simpa [prefixWord, tailWord_3356321, baseEnd_3356321] using wordTrace_append hprefix tailTrace_3356321
  have hstable : (prefixWord ++ tailWord_3356321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356321).length < 2 ^ (prefixWord ++ tailWord_3356321).sum := by decide
  have hdescent : baseEnd_3356321 < baseStart_3356321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356336 : List Nat := [2, 1, 1, 1, 2, 1, 6, 2, 2, 4]
def baseStart_3356336 : Nat := 118140960795 + 3356336 * 2 ^ 59
def prefixEnd_3356336 : Nat := 4983230072969 + 3 ^ 40 * 3356336 * 2
def baseEnd_3356336 : Nat := 1148942403992590369109665

theorem tailTrace_3356336 : CollatzResearch.WordTrace tailWord_3356336 prefixEnd_3356336 1148942403992590369109665 := by
  unfold tailWord_3356336
  simp only [CollatzResearch.WordTrace]
  refine ⟨61207815384287681698904431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81610420512383575598539241 61207815384287681698904431)
  ·
    refine ⟨91811723076431522548356647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61207815384287681698904431 91811723076431522548356647)
    ·
      refine ⟨137717584614647283822534971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91811723076431522548356647 137717584614647283822534971)
      ·
        refine ⟨206576376921970925733802457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137717584614647283822534971 206576376921970925733802457)
        ·
          refine ⟨154932282691478194300351843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206576376921970925733802457 154932282691478194300351843)
          ·
            refine ⟨232398424037217291450527765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154932282691478194300351843 232398424037217291450527765)
            ·
              refine ⟨10893676126744560536743489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 232398424037217291450527765 10893676126744560536743489)
              ·
                refine ⟨8170257095058420402557617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10893676126744560536743489 8170257095058420402557617)
                ·
                  refine ⟨6127692821293815301918213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8170257095058420402557617 6127692821293815301918213)
                  ·
                    refine ⟨1148942403992590369109665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6127692821293815301918213 1148942403992590369109665)
                    ·
                      rfl

theorem cell22_3356336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 2, 4].length) (baseStart_3356336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356336 prefixEnd_3356336 := by exact prefixLift 3356336
  have htrace : WordTrace (prefixWord ++ tailWord_3356336) baseStart_3356336 baseEnd_3356336 := by
    simpa [prefixWord, tailWord_3356336, baseEnd_3356336] using wordTrace_append hprefix tailTrace_3356336
  have hstable : (prefixWord ++ tailWord_3356336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356336).length < 2 ^ (prefixWord ++ tailWord_3356336).sum := by decide
  have hdescent : baseEnd_3356336 < baseStart_3356336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356338 : List Nat := [3, 2, 1, 1, 1, 2, 3, 4, 2, 3]
def baseStart_3356338 : Nat := 118140960795 + 3356338 * 2 ^ 59
def prefixEnd_3356338 : Nat := 4983230072969 + 3 ^ 40 * 3356338 * 2
def baseEnd_3356338 : Nat := 1148943088633463030559659

theorem tailTrace_3356338 : CollatzResearch.WordTrace tailWord_3356338 prefixEnd_3356338 1148943088633463030559659 := by
  unfold tailWord_3356338
  simp only [CollatzResearch.WordTrace]
  refine ⟨30603925928642029434845417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81610469143045411826254445 30603925928642029434845417)
  ·
    refine ⟨22952944446481522076134063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30603925928642029434845417 22952944446481522076134063)
    ·
      refine ⟨34429416669722283114201095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22952944446481522076134063 34429416669722283114201095)
      ·
        refine ⟨51644125004583424671301643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34429416669722283114201095 51644125004583424671301643)
        ·
          refine ⟨77466187506875137006952465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51644125004583424671301643 77466187506875137006952465)
          ·
            refine ⟨58099640630156352755214349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77466187506875137006952465 58099640630156352755214349)
            ·
              refine ⟨21787365236308632283205381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58099640630156352755214349 21787365236308632283205381)
              ·
                refine ⟨4085130981807868553101009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21787365236308632283205381 4085130981807868553101009)
                ·
                  refine ⟨3063848236355901414825757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4085130981807868553101009 3063848236355901414825757)
                  ·
                    refine ⟨1148943088633463030559659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3063848236355901414825757 1148943088633463030559659)
                    ·
                      rfl

theorem cell22_3356338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_3356338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356338 prefixEnd_3356338 := by exact prefixLift 3356338
  have htrace : WordTrace (prefixWord ++ tailWord_3356338) baseStart_3356338 baseEnd_3356338 := by
    simpa [prefixWord, tailWord_3356338, baseEnd_3356338] using wordTrace_append hprefix tailTrace_3356338
  have hstable : (prefixWord ++ tailWord_3356338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356338).length < 2 ^ (prefixWord ++ tailWord_3356338).sum := by decide
  have hdescent : baseEnd_3356338 < baseStart_3356338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356370 : List Nat := [3, 2, 2, 2, 2, 3, 1, 1, 2, 4]
def baseStart_3356370 : Nat := 118140960795 + 3356370 * 2 ^ 59
def prefixEnd_3356370 : Nat := 4983230072969 + 3 ^ 40 * 3356370 * 2
def baseEnd_3356370 : Nat := 1148954042887425613759561

theorem tailTrace_3356370 : CollatzResearch.WordTrace tailWord_3356370 prefixEnd_3356370 1148954042887425613759561 := by
  unfold tailWord_3356370
  simp only [CollatzResearch.WordTrace]
  refine ⟨30604217712613046801136641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81611247233634791469697709 30604217712613046801136641)
  ·
    refine ⟨22953163284459785100852481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30604217712613046801136641 22953163284459785100852481)
    ·
      refine ⟨17214872463344838825639361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22953163284459785100852481 17214872463344838825639361)
      ·
        refine ⟨12911154347508629119229521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17214872463344838825639361 12911154347508629119229521)
        ·
          refine ⟨9683365760631471839422141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12911154347508629119229521 9683365760631471839422141)
          ·
            refine ⟨3631262160236801939783303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9683365760631471839422141 3631262160236801939783303)
            ·
              refine ⟨5446893240355202909674955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3631262160236801939783303 5446893240355202909674955)
              ·
                refine ⟨8170339860532804364512433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5446893240355202909674955 8170339860532804364512433)
                ·
                  refine ⟨6127754895399603273384325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8170339860532804364512433 6127754895399603273384325)
                  ·
                    refine ⟨1148954042887425613759561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6127754895399603273384325 1148954042887425613759561)
                    ·
                      rfl

theorem cell22_3356370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_3356370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356370 prefixEnd_3356370 := by exact prefixLift 3356370
  have htrace : WordTrace (prefixWord ++ tailWord_3356370) baseStart_3356370 baseEnd_3356370 := by
    simpa [prefixWord, tailWord_3356370, baseEnd_3356370] using wordTrace_append hprefix tailTrace_3356370
  have hstable : (prefixWord ++ tailWord_3356370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356370).length < 2 ^ (prefixWord ++ tailWord_3356370).sum := by decide
  have hdescent : baseEnd_3356370 < baseStart_3356370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356374 : List Nat := [5, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_3356374 : Nat := 118140960795 + 3356374 * 2 ^ 59
def prefixEnd_3356374 : Nat := 4983230072969 + 3 ^ 40 * 3356374 * 2
def baseEnd_3356374 : Nat := 382985137389723645553183

theorem tailTrace_3356374 : CollatzResearch.WordTrace tailWord_3356374 prefixEnd_3356374 382985137389723645553183 := by
  unfold tailWord_3356374
  simp only [CollatzResearch.WordTrace]
  refine ⟨7651063546402355992980761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81611344494958463925128117 7651063546402355992980761)
  ·
    refine ⟨5738297659801766994735571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7651063546402355992980761 5738297659801766994735571)
    ·
      refine ⟨8607446489702650492103357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5738297659801766994735571 8607446489702650492103357)
      ·
        refine ⟨3227792433638493934538759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8607446489702650492103357 3227792433638493934538759)
        ·
          refine ⟨4841688650457740901808139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3227792433638493934538759 4841688650457740901808139)
          ·
            refine ⟨7262532975686611352712209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4841688650457740901808139 7262532975686611352712209)
            ·
              refine ⟨5446899731764958514534157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7262532975686611352712209 5446899731764958514534157)
              ·
                refine ⟨2042587399411859442950309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5446899731764958514534157 2042587399411859442950309)
                ·
                  refine ⟨382985137389723645553183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2042587399411859442950309 382985137389723645553183)
                  ·
                    rfl

theorem cell22_3356374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_3356374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356374 prefixEnd_3356374 := by exact prefixLift 3356374
  have htrace : WordTrace (prefixWord ++ tailWord_3356374) baseStart_3356374 baseEnd_3356374 := by
    simpa [prefixWord, tailWord_3356374, baseEnd_3356374] using wordTrace_append hprefix tailTrace_3356374
  have hstable : (prefixWord ++ tailWord_3356374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356374).length < 2 ^ (prefixWord ++ tailWord_3356374).sum := by decide
  have hdescent : baseEnd_3356374 < baseStart_3356374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356434 : List Nat := [3, 2, 4, 1, 1, 1, 3, 3, 1, 3]
def baseStart_3356434 : Nat := 118140960795 + 3356434 * 2 ^ 59
def prefixEnd_3356434 : Nat := 4983230072969 + 3 ^ 40 * 3356434 * 2
def baseEnd_3356434 : Nat := 1148975951395350780159365

theorem tailTrace_3356434 : CollatzResearch.WordTrace tailWord_3356434 prefixEnd_3356434 1148975951395350780159365 := by
  unfold tailWord_3356434
  simp only [CollatzResearch.WordTrace]
  refine ⟨30604801280555081533719089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81612803414813550756584237 30604801280555081533719089)
  ·
    refine ⟨22953600960416311150289317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30604801280555081533719089 22953600960416311150289317)
    ·
      refine ⟨4303800180078058340679247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22953600960416311150289317 4303800180078058340679247)
      ·
        refine ⟨6455700270117087511018871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4303800180078058340679247 6455700270117087511018871)
        ·
          refine ⟨9683550405175631266528307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6455700270117087511018871 9683550405175631266528307)
          ·
            refine ⟨14525325607763446899792461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9683550405175631266528307 14525325607763446899792461)
            ·
              refine ⟨5446997102911292587422173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14525325607763446899792461 5446997102911292587422173)
              ·
                refine ⟨2042623913591734720283315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5446997102911292587422173 2042623913591734720283315)
                ·
                  refine ⟨3063935870387602080424973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2042623913591734720283315 3063935870387602080424973)
                  ·
                    refine ⟨1148975951395350780159365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3063935870387602080424973 1148975951395350780159365)
                    ·
                      rfl

theorem cell22_3356434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_3356434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356434 prefixEnd_3356434 := by exact prefixLift 3356434
  have htrace : WordTrace (prefixWord ++ tailWord_3356434) baseStart_3356434 baseEnd_3356434 := by
    simpa [prefixWord, tailWord_3356434, baseEnd_3356434] using wordTrace_append hprefix tailTrace_3356434
  have hstable : (prefixWord ++ tailWord_3356434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356434).length < 2 ^ (prefixWord ++ tailWord_3356434).sum := by decide
  have hdescent : baseEnd_3356434 < baseStart_3356434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356471 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 1, 6]
def baseStart_3356471 : Nat := 118140960795 + 3356471 * 2 ^ 59
def prefixEnd_3356471 : Nat := 4983230072969 + 3 ^ 40 * 3356471 * 2
def baseEnd_3356471 : Nat := 1148988617251495016984251

theorem tailTrace_3356471 : CollatzResearch.WordTrace tailWord_3356471 prefixEnd_3356471 1148988617251495016984251 := by
  unfold tailWord_3356471
  simp only [CollatzResearch.WordTrace]
  refine ⟨122420554623086281453973267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81613703082057520969315511 122420554623086281453973267)
  ·
    refine ⟨183630831934629422180959901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122420554623086281453973267 183630831934629422180959901)
    ·
      refine ⟨68861561975486033317859963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183630831934629422180959901 68861561975486033317859963)
      ·
        refine ⟨103292342963229049976789945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68861561975486033317859963 103292342963229049976789945)
        ·
          refine ⟨77469257222421787482592459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103292342963229049976789945 77469257222421787482592459)
          ·
            refine ⟨116203885833632681223888689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77469257222421787482592459 116203885833632681223888689)
            ·
              refine ⟨87152914375224510917916517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116203885833632681223888689 87152914375224510917916517)
              ·
                refine ⟨16341171445354595797109347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87152914375224510917916517 16341171445354595797109347)
                ·
                  refine ⟨24511757168031893695664021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16341171445354595797109347 24511757168031893695664021)
                  ·
                    refine ⟨1148988617251495016984251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24511757168031893695664021 1148988617251495016984251)
                    ·
                      rfl

theorem cell22_3356471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_3356471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356471 prefixEnd_3356471 := by exact prefixLift 3356471
  have htrace : WordTrace (prefixWord ++ tailWord_3356471) baseStart_3356471 baseEnd_3356471 := by
    simpa [prefixWord, tailWord_3356471, baseEnd_3356471] using wordTrace_append hprefix tailTrace_3356471
  have hstable : (prefixWord ++ tailWord_3356471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356471).length < 2 ^ (prefixWord ++ tailWord_3356471).sum := by decide
  have hdescent : baseEnd_3356471 < baseStart_3356471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356477 : List Nat := [1, 4, 1, 4, 1, 3, 1, 2, 1, 4]
def baseStart_3356477 : Nat := 118140960795 + 3356477 * 2 ^ 59
def prefixEnd_3356477 : Nat := 4983230072969 + 3 ^ 40 * 3356477 * 2
def baseEnd_3356477 : Nat := 1148990671174113001334233

theorem tailTrace_3356477 : CollatzResearch.WordTrace tailWord_3356477 prefixEnd_3356477 1148990671174113001334233 := by
  unfold tailWord_3356477
  simp only [CollatzResearch.WordTrace]
  refine ⟨122420773461064544478691685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81613848974043029652461123 122420773461064544478691685)
  ·
    refine ⟨22953895023949602089754691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122420773461064544478691685 22953895023949602089754691)
    ·
      refine ⟨34430842535924403134632037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22953895023949602089754691 34430842535924403134632037)
      ·
        refine ⟨6455782975485825587743507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34430842535924403134632037 6455782975485825587743507)
        ·
          refine ⟨9683674463228738381615261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6455782975485825587743507 9683674463228738381615261)
          ·
            refine ⟨3631377923710776893105723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9683674463228738381615261 3631377923710776893105723)
            ·
              refine ⟨5447066885566165339658585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3631377923710776893105723 5447066885566165339658585)
              ·
                refine ⟨4085300164174624004743939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5447066885566165339658585 4085300164174624004743939)
                ·
                  refine ⟨6127950246261936007115909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4085300164174624004743939 6127950246261936007115909)
                  ·
                    refine ⟨1148990671174113001334233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6127950246261936007115909 1148990671174113001334233)
                    ·
                      rfl

theorem cell22_3356477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_3356477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356477 prefixEnd_3356477 := by exact prefixLift 3356477
  have htrace : WordTrace (prefixWord ++ tailWord_3356477) baseStart_3356477 baseEnd_3356477 := by
    simpa [prefixWord, tailWord_3356477, baseEnd_3356477] using wordTrace_append hprefix tailTrace_3356477
  have hstable : (prefixWord ++ tailWord_3356477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356477).length < 2 ^ (prefixWord ++ tailWord_3356477).sum := by decide
  have hdescent : baseEnd_3356477 < baseStart_3356477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356488 : List Nat := [2, 1, 3, 1, 1, 4, 1, 3, 2, 4]
def baseStart_3356488 : Nat := 118140960795 + 3356488 * 2 ^ 59
def prefixEnd_3356488 : Nat := 4983230072969 + 3 ^ 40 * 3356488 * 2
def baseEnd_3356488 : Nat := 1148994436698912639309199

theorem tailTrace_3356488 : CollatzResearch.WordTrace tailWord_3356488 prefixEnd_3356488 1148994436698912639309199 := by
  unfold tailWord_3356488
  simp only [CollatzResearch.WordTrace]
  refine ⟨61210587332012346678671059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81614116442683128904894745 61210587332012346678671059)
  ·
    refine ⟨91815880998018520018006589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61210587332012346678671059 91815880998018520018006589)
    ·
      refine ⟨34430955374256945006752471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91815880998018520018006589 34430955374256945006752471)
      ·
        refine ⟨51646433061385417510128707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34430955374256945006752471 51646433061385417510128707)
        ·
          refine ⟨77469649592078126265193061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51646433061385417510128707 77469649592078126265193061)
          ·
            refine ⟨14525559298514648674723699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77469649592078126265193061 14525559298514648674723699)
            ·
              refine ⟨21788338947771973012085549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14525559298514648674723699 21788338947771973012085549)
              ·
                refine ⟨8170627105414489879532081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21788338947771973012085549 8170627105414489879532081)
                ·
                  refine ⟨6127970329060867409649061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8170627105414489879532081 6127970329060867409649061)
                  ·
                    refine ⟨1148994436698912639309199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6127970329060867409649061 1148994436698912639309199)
                    ·
                      rfl

theorem cell22_3356488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_3356488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356488 prefixEnd_3356488 := by exact prefixLift 3356488
  have htrace : WordTrace (prefixWord ++ tailWord_3356488) baseStart_3356488 baseEnd_3356488 := by
    simpa [prefixWord, tailWord_3356488, baseEnd_3356488] using wordTrace_append hprefix tailTrace_3356488
  have hstable : (prefixWord ++ tailWord_3356488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356488).length < 2 ^ (prefixWord ++ tailWord_3356488).sum := by decide
  have hdescent : baseEnd_3356488 < baseStart_3356488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356503 : List Nat := [1, 1, 3, 2, 6, 9]
def baseStart_3356503 : Nat := 118140960795 + 3356503 * 2 ^ 59
def prefixEnd_3356503 : Nat := 4983230072969 + 3 ^ 40 * 3356503 * 2
def baseEnd_3356503 : Nat := 14185179895129106175113

theorem tailTrace_3356503 : CollatzResearch.WordTrace tailWord_3356503 prefixEnd_3356503 14185179895129106175113 := by
  unfold tailWord_3356503
  simp only [CollatzResearch.WordTrace]
  refine ⟨122421721758970350919138163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81614481172646900612758775 122421721758970350919138163)
  ·
    refine ⟨183632582638455526378707245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122421721758970350919138163 183632582638455526378707245)
    ·
      refine ⟨68862218489420822392015217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183632582638455526378707245 68862218489420822392015217)
      ·
        refine ⟨51646663867065616794011413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68862218489420822392015217 51646663867065616794011413)
        ·
          refine ⟨2420937368768700787219285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51646663867065616794011413 2420937368768700787219285)
          ·
            refine ⟨14185179895129106175113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2420937368768700787219285 14185179895129106175113)
            ·
              rfl

theorem cell22_3356503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 9].length) (baseStart_3356503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356503 prefixEnd_3356503 := by exact prefixLift 3356503
  have htrace : WordTrace (prefixWord ++ tailWord_3356503) baseStart_3356503 baseEnd_3356503 := by
    simpa [prefixWord, tailWord_3356503, baseEnd_3356503] using wordTrace_append hprefix tailTrace_3356503
  have hstable : (prefixWord ++ tailWord_3356503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356503).length < 2 ^ (prefixWord ++ tailWord_3356503).sum := by decide
  have hdescent : baseEnd_3356503 < baseStart_3356503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356531 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 9]
def baseStart_3356531 : Nat := 118140960795 + 3356531 * 2 ^ 59
def prefixEnd_3356531 : Nat := 4983230072969 + 3 ^ 40 * 3356531 * 2
def baseEnd_3356531 : Nat := 383003052159224953494689

theorem tailTrace_3356531 : CollatzResearch.WordTrace tailWord_3356531 prefixEnd_3356531 383003052159224953494689 := by
  unfold tailWord_3356531
  simp only [CollatzResearch.WordTrace]
  refine ⟨122422743002868911701157447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81615162001912607800771631 122422743002868911701157447)
  ·
    refine ⟨183634114504303367551736171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122422743002868911701157447 183634114504303367551736171)
    ·
      refine ⟨275451171756455051327604257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183634114504303367551736171 275451171756455051327604257)
      ·
        refine ⟨206588378817341288495703193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275451171756455051327604257 206588378817341288495703193)
        ·
          refine ⟨154941284113005966371777395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206588378817341288495703193 154941284113005966371777395)
          ·
            refine ⟨232411926169508949557666093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154941284113005966371777395 232411926169508949557666093)
            ·
              refine ⟨87154472313565856084124785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232411926169508949557666093 87154472313565856084124785)
              ·
                refine ⟨65365854235174392063093589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87154472313565856084124785 65365854235174392063093589)
                ·
                  refine ⟨383003052159224953494689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65365854235174392063093589 383003052159224953494689)
                  ·
                    rfl

theorem cell22_3356531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 9].length) (baseStart_3356531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356531 prefixEnd_3356531 := by exact prefixLift 3356531
  have htrace : WordTrace (prefixWord ++ tailWord_3356531) baseStart_3356531 baseEnd_3356531 := by
    simpa [prefixWord, tailWord_3356531, baseEnd_3356531] using wordTrace_append hprefix tailTrace_3356531
  have hstable : (prefixWord ++ tailWord_3356531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356531).length < 2 ^ (prefixWord ++ tailWord_3356531).sum := by decide
  have hdescent : baseEnd_3356531 < baseStart_3356531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356533 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3356533 : Nat := 118140960795 + 3356533 * 2 ^ 59
def prefixEnd_3356533 : Nat := 4983230072969 + 3 ^ 40 * 3356533 * 2
def baseEnd_3356533 : Nat := 1149009841118547521934061

theorem tailTrace_3356533 : CollatzResearch.WordTrace tailWord_3356533 prefixEnd_3356533 1149009841118547521934061 := by
  unfold tailWord_3356533
  simp only [CollatzResearch.WordTrace]
  refine ⟨122422815948861666042730253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81615210632574444028486835 122422815948861666042730253)
  ·
    refine ⟨45908555980823124766023845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122422815948861666042730253 45908555980823124766023845)
    ·
      refine ⟨8607854246404335893629471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45908555980823124766023845 8607854246404335893629471)
      ·
        refine ⟨12911781369606503840444207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8607854246404335893629471 12911781369606503840444207)
        ·
          refine ⟨19367672054409755760666311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12911781369606503840444207 19367672054409755760666311)
          ·
            refine ⟨29051508081614633640999467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19367672054409755760666311 29051508081614633640999467)
            ·
              refine ⟨43577262122421950461499201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29051508081614633640999467 43577262122421950461499201)
              ·
                refine ⟨32682946591816462846124401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43577262122421950461499201 32682946591816462846124401)
                ·
                  refine ⟨24512209943862347134593301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32682946591816462846124401 24512209943862347134593301)
                  ·
                    refine ⟨1149009841118547521934061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24512209943862347134593301 1149009841118547521934061)
                    ·
                      rfl

theorem cell22_3356533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3356533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356533 prefixEnd_3356533 := by exact prefixLift 3356533
  have htrace : WordTrace (prefixWord ++ tailWord_3356533) baseStart_3356533 baseEnd_3356533 := by
    simpa [prefixWord, tailWord_3356533, baseEnd_3356533] using wordTrace_append hprefix tailTrace_3356533
  have hstable : (prefixWord ++ tailWord_3356533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356533).length < 2 ^ (prefixWord ++ tailWord_3356533).sum := by decide
  have hdescent : baseEnd_3356533 < baseStart_3356533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356595 : List Nat := [1, 1, 1, 2, 3, 1, 6, 2, 1, 4]
def baseStart_3356595 : Nat := 118140960795 + 3356595 * 2 ^ 59
def prefixEnd_3356595 : Nat := 4983230072969 + 3 ^ 40 * 3356595 * 2
def baseEnd_3356595 : Nat := 1149031064985600026883871

theorem tailTrace_3356595 : CollatzResearch.WordTrace tailWord_3356595 prefixEnd_3356595 1149031064985600026883871 := by
  unfold tailWord_3356595
  simp only [CollatzResearch.WordTrace]
  refine ⟨122425077274637050631487239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81616718183091367087658159 122425077274637050631487239)
  ·
    refine ⟨183637615911955575947230859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122425077274637050631487239 183637615911955575947230859)
    ·
      refine ⟨275456423867933363920846289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183637615911955575947230859 275456423867933363920846289)
      ·
        refine ⟨206592317900950022940634717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275456423867933363920846289 206592317900950022940634717)
        ·
          refine ⟨77472119212856258602738019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206592317900950022940634717 77472119212856258602738019)
          ·
            refine ⟨116208178819284387904107029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77472119212856258602738019 116208178819284387904107029)
            ·
              refine ⟨5447258382153955683005017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116208178819284387904107029 5447258382153955683005017)
              ·
                refine ⟨4085443786615466762253763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5447258382153955683005017 4085443786615466762253763)
                ·
                  refine ⟨6128165679923200143380645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4085443786615466762253763 6128165679923200143380645)
                  ·
                    refine ⟨1149031064985600026883871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6128165679923200143380645 1149031064985600026883871)
                    ·
                      rfl

theorem cell22_3356595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 4].length) (baseStart_3356595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356595 prefixEnd_3356595 := by exact prefixLift 3356595
  have htrace : WordTrace (prefixWord ++ tailWord_3356595) baseStart_3356595 baseEnd_3356595 := by
    simpa [prefixWord, tailWord_3356595, baseEnd_3356595] using wordTrace_append hprefix tailTrace_3356595
  have hstable : (prefixWord ++ tailWord_3356595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356595).length < 2 ^ (prefixWord ++ tailWord_3356595).sum := by decide
  have hdescent : baseEnd_3356595 < baseStart_3356595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356608 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 3, 5]
def baseStart_3356608 : Nat := 118140960795 + 3356608 * 2 ^ 59
def prefixEnd_3356608 : Nat := 4983230072969 + 3 ^ 40 * 3356608 * 2
def baseEnd_3356608 : Nat := 1149035515151272326308831

theorem tailTrace_3356608 : CollatzResearch.WordTrace tailWord_3356608 prefixEnd_3356608 1149035515151272326308831 := by
  unfold tailWord_3356608
  simp only [CollatzResearch.WordTrace]
  refine ⟨61212775711794976925855239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81617034282393302567806985 61212775711794976925855239)
  ·
    refine ⟨91819163567692465388782859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61212775711794976925855239 91819163567692465388782859)
    ·
      refine ⟨137728745351538698083174289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91819163567692465388782859 137728745351538698083174289)
      ·
        refine ⟨103296559013654023562380717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137728745351538698083174289 103296559013654023562380717)
        ·
          refine ⟨38736209630120258835892769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103296559013654023562380717 38736209630120258835892769)
          ·
            refine ⟨29052157222590194126919577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38736209630120258835892769 29052157222590194126919577)
            ·
              refine ⟨21789117916942645595189683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29052157222590194126919577 21789117916942645595189683)
              ·
                refine ⟨32683676875413968392784525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21789117916942645595189683 32683676875413968392784525)
                ·
                  refine ⟨12256378828280238147294197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32683676875413968392784525 12256378828280238147294197)
                  ·
                    refine ⟨1149035515151272326308831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12256378828280238147294197 1149035515151272326308831)
                    ·
                      rfl

theorem cell22_3356608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_3356608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356608 prefixEnd_3356608 := by exact prefixLift 3356608
  have htrace : WordTrace (prefixWord ++ tailWord_3356608) baseStart_3356608 baseEnd_3356608 := by
    simpa [prefixWord, tailWord_3356608, baseEnd_3356608] using wordTrace_append hprefix tailTrace_3356608
  have hstable : (prefixWord ++ tailWord_3356608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356608).length < 2 ^ (prefixWord ++ tailWord_3356608).sum := by decide
  have hdescent : baseEnd_3356608 < baseStart_3356608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356657 : List Nat := [1, 2, 2, 2, 5, 1, 2, 1, 2, 4]
def baseStart_3356657 : Nat := 118140960795 + 3356657 * 2 ^ 59
def prefixEnd_3356657 : Nat := 4983230072969 + 3 ^ 40 * 3356657 * 2
def baseEnd_3356657 : Nat := 1149052288852652531833681

theorem tailTrace_3356657 : CollatzResearch.WordTrace tailWord_3356657 prefixEnd_3356657 1149052288852652531833681 := by
  unfold tailWord_3356657
  simp only [CollatzResearch.WordTrace]
  refine ⟨122427338600412435220244225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81618225733608290146829483 122427338600412435220244225)
  ·
    refine ⟨91820503950309326415183169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122427338600412435220244225 91820503950309326415183169)
    ·
      refine ⟨68865377962731994811387377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91820503950309326415183169 68865377962731994811387377)
      ·
        refine ⟨51649033472048996108540533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68865377962731994811387377 51649033472048996108540533)
        ·
          refine ⟨4842096888004593385175675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51649033472048996108540533 4842096888004593385175675)
          ·
            refine ⟨7263145332006890077763513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4842096888004593385175675 7263145332006890077763513)
            ·
              refine ⟨5447358999005167558322635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7263145332006890077763513 5447358999005167558322635)
              ·
                refine ⟨8171038498507751337483953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5447358999005167558322635 8171038498507751337483953)
                ·
                  refine ⟨6128278873880813503112965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8171038498507751337483953 6128278873880813503112965)
                  ·
                    refine ⟨1149052288852652531833681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6128278873880813503112965 1149052288852652531833681)
                    ·
                      rfl

theorem cell22_3356657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_3356657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356657 prefixEnd_3356657 := by exact prefixLift 3356657
  have htrace : WordTrace (prefixWord ++ tailWord_3356657) baseStart_3356657 baseEnd_3356657 := by
    simpa [prefixWord, tailWord_3356657, baseEnd_3356657] using wordTrace_append hprefix tailTrace_3356657
  have hstable : (prefixWord ++ tailWord_3356657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356657).length < 2 ^ (prefixWord ++ tailWord_3356657).sum := by decide
  have hdescent : baseEnd_3356657 < baseStart_3356657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356676 : List Nat := [2, 3, 2, 4, 1, 1, 2, 2, 2, 3]
def baseStart_3356676 : Nat := 118140960795 + 3356676 * 2 ^ 59
def prefixEnd_3356676 : Nat := 4983230072969 + 3 ^ 40 * 3356676 * 2
def baseEnd_3356676 : Nat := 1149058792940942815608623

theorem tailTrace_3356676 : CollatzResearch.WordTrace tailWord_3356676 prefixEnd_3356676 1149058792940942815608623 := by
  unfold tailWord_3356676
  simp only [CollatzResearch.WordTrace]
  refine ⟨61214015793671800732592941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81618687724895734310123921 61214015793671800732592941)
  ·
    refine ⟨22955255922626925274722353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61214015793671800732592941 22955255922626925274722353)
    ·
      refine ⟨17216441941970193956041765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22955255922626925274722353 17216441941970193956041765)
      ·
        refine ⟨3228082864119411366757831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17216441941970193956041765 3228082864119411366757831)
        ·
          refine ⟨4842124296179117050136747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3228082864119411366757831 4842124296179117050136747)
          ·
            refine ⟨7263186444268675575205121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4842124296179117050136747 7263186444268675575205121)
            ·
              refine ⟨5447389833201506681403841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7263186444268675575205121 5447389833201506681403841)
              ·
                refine ⟨4085542374901130011052881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5447389833201506681403841 4085542374901130011052881)
                ·
                  refine ⟨3064156781175847508289661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4085542374901130011052881 3064156781175847508289661)
                  ·
                    refine ⟨1149058792940942815608623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3064156781175847508289661 1149058792940942815608623)
                    ·
                      rfl

theorem cell22_3356676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_3356676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356676 prefixEnd_3356676 := by exact prefixLift 3356676
  have htrace : WordTrace (prefixWord ++ tailWord_3356676) baseStart_3356676 baseEnd_3356676 := by
    simpa [prefixWord, tailWord_3356676, baseEnd_3356676] using wordTrace_append hprefix tailTrace_3356676
  have hstable : (prefixWord ++ tailWord_3356676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356676).length < 2 ^ (prefixWord ++ tailWord_3356676).sum := by decide
  have hdescent : baseEnd_3356676 < baseStart_3356676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356745 : List Nat := [1, 2, 1, 1, 2, 2, 6, 1, 6]
def baseStart_3356745 : Nat := 118140960795 + 3356745 * 2 ^ 59
def prefixEnd_3356745 : Nat := 4983230072969 + 3 ^ 40 * 3356745 * 2
def baseEnd_3356745 : Nat := 383027471017016545211137

theorem tailTrace_3356745 : CollatzResearch.WordTrace tailWord_3356745 prefixEnd_3356745 383027471017016545211137 := by
  unfold tailWord_3356745
  simp only [CollatzResearch.WordTrace]
  refine ⟨122430548224093626249447689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81620365482729084166298459 122430548224093626249447689)
  ·
    refine ⟨91822911168070219687085767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122430548224093626249447689 91822911168070219687085767)
    ·
      refine ⟨137734366752105329530628651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91822911168070219687085767 137734366752105329530628651)
      ·
        refine ⟨206601550128157994295942977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137734366752105329530628651 206601550128157994295942977)
        ·
          refine ⟨154951162596118495721957233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206601550128157994295942977 154951162596118495721957233)
          ·
            refine ⟨116213371947088871791467925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154951162596118495721957233 116213371947088871791467925)
            ·
              refine ⟨5447501810019790865225059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116213371947088871791467925 5447501810019790865225059)
              ·
                refine ⟨8171252715029686297837589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5447501810019790865225059 8171252715029686297837589)
                ·
                  refine ⟨383027471017016545211137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8171252715029686297837589 383027471017016545211137)
                  ·
                    rfl

theorem cell22_3356745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 6].length) (baseStart_3356745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356745 prefixEnd_3356745 := by exact prefixLift 3356745
  have htrace : WordTrace (prefixWord ++ tailWord_3356745) baseStart_3356745 baseEnd_3356745 := by
    simpa [prefixWord, tailWord_3356745, baseEnd_3356745] using wordTrace_append hprefix tailTrace_3356745
  have hstable : (prefixWord ++ tailWord_3356745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356745).length < 2 ^ (prefixWord ++ tailWord_3356745).sum := by decide
  have hdescent : baseEnd_3356745 < baseStart_3356745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356764 : List Nat := [2, 2, 4, 1, 1, 3, 2, 2, 1, 4]
def baseStart_3356764 : Nat := 118140960795 + 3356764 * 2 ^ 59
def prefixEnd_3356764 : Nat := 4983230072969 + 3 ^ 40 * 3356764 * 2
def baseEnd_3356764 : Nat := 1149088917139339919408353

theorem tailTrace_3356764 : CollatzResearch.WordTrace tailWord_3356764 prefixEnd_3356764 1149088917139339919408353 := by
  unfold tailWord_3356764
  simp only [CollatzResearch.WordTrace]
  refine ⟨61215620605512396247194673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81620827474016528329592897 61215620605512396247194673)
  ·
    refine ⟨45911715454134297185396005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61215620605512396247194673 45911715454134297185396005)
    ·
      refine ⟨8608446647650180722261751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45911715454134297185396005 8608446647650180722261751)
      ·
        refine ⟨12912669971475271083392627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8608446647650180722261751 12912669971475271083392627)
        ·
          refine ⟨19369004957212906625088941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12912669971475271083392627 19369004957212906625088941)
          ·
            refine ⟨7263376858954839984408353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19369004957212906625088941 7263376858954839984408353)
            ·
              refine ⟨5447532644216129988306265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7263376858954839984408353 5447532644216129988306265)
              ·
                refine ⟨4085649483162097491229699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5447532644216129988306265 4085649483162097491229699)
                ·
                  refine ⟨6128474224743146236844549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4085649483162097491229699 6128474224743146236844549)
                  ·
                    refine ⟨1149088917139339919408353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6128474224743146236844549 1149088917139339919408353)
                    ·
                      rfl

theorem cell22_3356764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_3356764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356764 prefixEnd_3356764 := by exact prefixLift 3356764
  have htrace : WordTrace (prefixWord ++ tailWord_3356764) baseStart_3356764 baseEnd_3356764 := by
    simpa [prefixWord, tailWord_3356764, baseEnd_3356764] using wordTrace_append hprefix tailTrace_3356764
  have hstable : (prefixWord ++ tailWord_3356764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356764).length < 2 ^ (prefixWord ++ tailWord_3356764).sum := by decide
  have hdescent : baseEnd_3356764 < baseStart_3356764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356775 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 1, 6]
def baseStart_3356775 : Nat := 118140960795 + 3356775 * 2 ^ 59
def prefixEnd_3356775 : Nat := 4983230072969 + 3 ^ 40 * 3356775 * 2
def baseEnd_3356775 : Nat := 1149092682664139557383319

theorem tailTrace_3356775 : CollatzResearch.WordTrace tailWord_3356775 prefixEnd_3356775 1149092682664139557383319 := by
  unfold tailWord_3356775
  simp only [CollatzResearch.WordTrace]
  refine ⟨122431642413984941373039779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81621094942656627582026519 122431642413984941373039779)
  ·
    refine ⟨183647463620977412059559669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122431642413984941373039779 183647463620977412059559669)
    ·
      refine ⟨17216949714466632380583719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183647463620977412059559669 17216949714466632380583719)
      ·
        refine ⟨25825424571699948570875579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17216949714466632380583719 25825424571699948570875579)
        ·
          refine ⟨38738136857549922856313369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25825424571699948570875579 38738136857549922856313369)
          ·
            refine ⟨29053602643162442142235027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38738136857549922856313369 29053602643162442142235027)
            ·
              refine ⟨43580403964743663213352541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29053602643162442142235027 43580403964743663213352541)
              ·
                refine ⟨16342651486778873705007203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43580403964743663213352541 16342651486778873705007203)
                ·
                  refine ⟨24513977230168310557510805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16342651486778873705007203 24513977230168310557510805)
                  ·
                    refine ⟨1149092682664139557383319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24513977230168310557510805 1149092682664139557383319)
                    ·
                      rfl

theorem cell22_3356775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_3356775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356775 prefixEnd_3356775 := by exact prefixLift 3356775
  have htrace : WordTrace (prefixWord ++ tailWord_3356775) baseStart_3356775 baseEnd_3356775 := by
    simpa [prefixWord, tailWord_3356775, baseEnd_3356775] using wordTrace_append hprefix tailTrace_3356775
  have hstable : (prefixWord ++ tailWord_3356775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356775).length < 2 ^ (prefixWord ++ tailWord_3356775).sum := by decide
  have hdescent : baseEnd_3356775 < baseStart_3356775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356914 : List Nat := [3, 2, 1, 3, 2, 2, 2, 1, 6]
def baseStart_3356914 : Nat := 118140960795 + 3356914 * 2 ^ 59
def prefixEnd_3356914 : Nat := 4983230072969 + 3 ^ 40 * 3356914 * 2
def baseEnd_3356914 : Nat := 383046755068263176052631

theorem tailTrace_3356914 : CollatzResearch.WordTrace tailWord_3356914 prefixEnd_3356914 383046755068263176052631 := by
  unfold tailWord_3356914
  simp only [CollatzResearch.WordTrace]
  refine ⟨30609178040120342028087449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81624474773654245408233197 30609178040120342028087449)
  ·
    refine ⟨22956883530090256521065587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30609178040120342028087449 22956883530090256521065587)
    ·
      refine ⟨34435325295135384781598381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22956883530090256521065587 34435325295135384781598381)
      ·
        refine ⟨12913246985675769293099393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34435325295135384781598381 12913246985675769293099393)
        ·
          refine ⟨9684935239256826969824545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12913246985675769293099393 9684935239256826969824545)
          ·
            refine ⟨7263701429442620227368409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9684935239256826969824545 7263701429442620227368409)
            ·
              refine ⟨5447776072081965170526307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7263701429442620227368409 5447776072081965170526307)
              ·
                refine ⟨8171664108122947755789461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5447776072081965170526307 8171664108122947755789461)
                ·
                  refine ⟨383046755068263176052631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8171664108122947755789461 383046755068263176052631)
                  ·
                    rfl

theorem cell22_3356914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_3356914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356914 prefixEnd_3356914 := by exact prefixLift 3356914
  have htrace : WordTrace (prefixWord ++ tailWord_3356914) baseStart_3356914 baseEnd_3356914 := by
    simpa [prefixWord, tailWord_3356914, baseEnd_3356914] using wordTrace_append hprefix tailTrace_3356914
  have hstable : (prefixWord ++ tailWord_3356914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356914).length < 2 ^ (prefixWord ++ tailWord_3356914).sum := by decide
  have hdescent : baseEnd_3356914 < baseStart_3356914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356942 : List Nat := [4, 1, 1, 2, 1, 2, 3, 8]
def baseStart_3356942 : Nat := 118140960795 + 3356942 * 2 ^ 59
def prefixEnd_3356942 : Nat := 4983230072969 + 3 ^ 40 * 3356942 * 2
def baseEnd_3356942 : Nat := 127683316686334087606423

theorem tailTrace_3356942 : CollatzResearch.WordTrace tailWord_3356942 prefixEnd_3356942 127683316686334087606423 := by
  unfold tailWord_3356942
  simp only [CollatzResearch.WordTrace]
  refine ⟨15304716675547491111796135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81625155602919952596246053 15304716675547491111796135)
  ·
    refine ⟨22957075013321236667694203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15304716675547491111796135 22957075013321236667694203)
    ·
      refine ⟨34435612519981855001541305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22957075013321236667694203 34435612519981855001541305)
      ·
        refine ⟨25826709389986391251155979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34435612519981855001541305 25826709389986391251155979)
        ·
          refine ⟨38740064084979586876733969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25826709389986391251155979 38740064084979586876733969)
          ·
            refine ⟨29055048063734690157550477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38740064084979586876733969 29055048063734690157550477)
            ·
              refine ⟨10895643023900508809081429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29055048063734690157550477 10895643023900508809081429)
              ·
                refine ⟨127683316686334087606423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10895643023900508809081429 127683316686334087606423)
                ·
                  rfl

theorem cell22_3356942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_3356942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356942 prefixEnd_3356942 := by exact prefixLift 3356942
  have htrace : WordTrace (prefixWord ++ tailWord_3356942) baseStart_3356942 baseEnd_3356942 := by
    simpa [prefixWord, tailWord_3356942, baseEnd_3356942] using wordTrace_append hprefix tailTrace_3356942
  have hstable : (prefixWord ++ tailWord_3356942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356942).length < 2 ^ (prefixWord ++ tailWord_3356942).sum := by decide
  have hdescent : baseEnd_3356942 < baseStart_3356942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356980 : List Nat := [2, 5, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_3356980 : Nat := 118140960795 + 3356980 * 2 ^ 59
def prefixEnd_3356980 : Nat := 4983230072969 + 3 ^ 40 * 3356980 * 2
def baseEnd_3356980 : Nat := 1149162858353587356007691

theorem tailTrace_3356980 : CollatzResearch.WordTrace tailWord_3356980 prefixEnd_3356980 1149162858353587356007691 := by
  unfold tailWord_3356980
  simp only [CollatzResearch.WordTrace]
  refine ⟨61219559689121130692126197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81626079585494840922834929 61219559689121130692126197)
  ·
    refine ⟨5739333720855106002386831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61219559689121130692126197 5739333720855106002386831)
    ·
      refine ⟨8609000581282659003580247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5739333720855106002386831 8609000581282659003580247)
      ·
        refine ⟨12913500871923988505370371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8609000581282659003580247 12913500871923988505370371)
        ·
          refine ⟨19370251307885982758055557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12913500871923988505370371 19370251307885982758055557)
          ·
            refine ⟨3631922120228621767135417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19370251307885982758055557 3631922120228621767135417)
            ·
              refine ⟨2723941590171466325351563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3631922120228621767135417 2723941590171466325351563)
              ·
                refine ⟨4085912385257199488027345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2723941590171466325351563 4085912385257199488027345)
                ·
                  refine ⟨3064434288942899616020509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4085912385257199488027345 3064434288942899616020509)
                  ·
                    refine ⟨1149162858353587356007691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3064434288942899616020509 1149162858353587356007691)
                    ·
                      rfl

theorem cell22_3356980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_3356980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3356980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3356980 prefixEnd_3356980 := by exact prefixLift 3356980
  have htrace : WordTrace (prefixWord ++ tailWord_3356980) baseStart_3356980 baseEnd_3356980 := by
    simpa [prefixWord, tailWord_3356980, baseEnd_3356980] using wordTrace_append hprefix tailTrace_3356980
  have hstable : (prefixWord ++ tailWord_3356980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356980).length < 2 ^ (prefixWord ++ tailWord_3356980).sum := by decide
  have hdescent : baseEnd_3356980 < baseStart_3356980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357002 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 6, 5]
def baseStart_3357002 : Nat := 118140960795 + 3357002 * 2 ^ 59
def prefixEnd_3357002 : Nat := 4983230072969 + 3 ^ 40 * 3357002 * 2
def baseEnd_3357002 : Nat := 1149170389403186631957623

theorem tailTrace_3357002 : CollatzResearch.WordTrace tailWord_3357002 prefixEnd_3357002 1149170389403186631957623 := by
  unfold tailWord_3357002
  simp only [CollatzResearch.WordTrace]
  refine ⟨30609980446040639785388315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81626614522775039427702173 30609980446040639785388315)
  ·
    refine ⟨45914970669060959678082473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30609980446040639785388315 45914970669060959678082473)
    ·
      refine ⟨34436228001795719758561855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45914970669060959678082473 34436228001795719758561855)
      ·
        refine ⟨51654342002693579637842783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34436228001795719758561855 51654342002693579637842783)
        ·
          refine ⟨77481513004040369456764175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51654342002693579637842783 77481513004040369456764175)
          ·
            refine ⟨116222269506060554185146263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77481513004040369456764175 116222269506060554185146263)
            ·
              refine ⟨174333404259090831277719395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116222269506060554185146263 174333404259090831277719395)
              ·
                refine ⟨261500106388636246916579093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174333404259090831277719395 261500106388636246916579093)
                ·
                  refine ⟨12257817486967324074214645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 261500106388636246916579093 12257817486967324074214645)
                  ·
                    refine ⟨1149170389403186631957623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12257817486967324074214645 1149170389403186631957623)
                    ·
                      rfl

theorem cell22_3357002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_3357002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357002 prefixEnd_3357002 := by exact prefixLift 3357002
  have htrace : WordTrace (prefixWord ++ tailWord_3357002) baseStart_3357002 baseEnd_3357002 := by
    simpa [prefixWord, tailWord_3357002, baseEnd_3357002] using wordTrace_append hprefix tailTrace_3357002
  have hstable : (prefixWord ++ tailWord_3357002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357002).length < 2 ^ (prefixWord ++ tailWord_3357002).sum := by decide
  have hdescent : baseEnd_3357002 < baseStart_3357002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357064 : List Nat := [2, 1, 3, 3, 1, 1, 1, 4, 1, 5]
def baseStart_3357064 : Nat := 118140960795 + 3357064 * 2 ^ 59
def prefixEnd_3357064 : Nat := 4983230072969 + 3 ^ 40 * 3357064 * 2
def baseEnd_3357064 : Nat := 1149191613270239136907433

theorem tailTrace_3357064 : CollatzResearch.WordTrace tailWord_3357064 prefixEnd_3357064 1149191613270239136907433 := by
  unfold tailWord_3357064
  simp only [CollatzResearch.WordTrace]
  refine ⟨61221091554968971865155123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81628122073291962486873497 61221091554968971865155123)
  ·
    refine ⟨91831637332453457797732685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61221091554968971865155123 91831637332453457797732685)
    ·
      refine ⟨34436863999670046674149757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91831637332453457797732685 34436863999670046674149757)
      ·
        refine ⟨12913823999876267502806159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34436863999670046674149757 12913823999876267502806159)
        ·
          refine ⟨19370735999814401254209239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12913823999876267502806159 19370735999814401254209239)
          ·
            refine ⟨29056103999721601881313859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19370735999814401254209239 29056103999721601881313859)
            ·
              refine ⟨43584155999582402821970789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29056103999721601881313859 43584155999582402821970789)
              ·
                refine ⟨8172029249921700529119523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43584155999582402821970789 8172029249921700529119523)
                ·
                  refine ⟨12258043874882550793679285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8172029249921700529119523 12258043874882550793679285)
                  ·
                    refine ⟨1149191613270239136907433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12258043874882550793679285 1149191613270239136907433)
                    ·
                      rfl

theorem cell22_3357064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_3357064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357064 prefixEnd_3357064 := by exact prefixLift 3357064
  have htrace : WordTrace (prefixWord ++ tailWord_3357064) baseStart_3357064 baseEnd_3357064 := by
    simpa [prefixWord, tailWord_3357064, baseEnd_3357064] using wordTrace_append hprefix tailTrace_3357064
  have hstable : (prefixWord ++ tailWord_3357064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357064).length < 2 ^ (prefixWord ++ tailWord_3357064).sum := by decide
  have hdescent : baseEnd_3357064 < baseStart_3357064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357068 : List Nat := [2, 2, 1, 2, 1, 6, 2, 1, 1, 4]
def baseStart_3357068 : Nat := 118140960795 + 3357068 * 2 ^ 59
def prefixEnd_3357068 : Nat := 4983230072969 + 3 ^ 40 * 3357068 * 2
def baseEnd_3357068 : Nat := 1149192982551984459807421

theorem tailTrace_3357068 : CollatzResearch.WordTrace tailWord_3357068 prefixEnd_3357068 1149192982551984459807421 := by
  unfold tailWord_3357068
  simp only [CollatzResearch.WordTrace]
  refine ⟨61221164500961726206727929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81628219334615634942303905 61221164500961726206727929)
  ·
    refine ⟨45915873375721294655045947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61221164500961726206727929 45915873375721294655045947)
    ·
      refine ⟨68873810063581941982568921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45915873375721294655045947 68873810063581941982568921)
      ·
        refine ⟨51655357547686456486926691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68873810063581941982568921 51655357547686456486926691)
        ·
          refine ⟨77483036321529684730390037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51655357547686456486926691 77483036321529684730390037)
          ·
            refine ⟨3632017327571703971737033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77483036321529684730390037 3632017327571703971737033)
            ·
              refine ⟨2724012995678777978802775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3632017327571703971737033 2724012995678777978802775)
              ·
                refine ⟨4086019493518166968204163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2724012995678777978802775 4086019493518166968204163)
                ·
                  refine ⟨6129029240277250452306245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4086019493518166968204163 6129029240277250452306245)
                  ·
                    refine ⟨1149192982551984459807421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6129029240277250452306245 1149192982551984459807421)
                    ·
                      rfl

theorem cell22_3357068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 1, 4].length) (baseStart_3357068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357068 prefixEnd_3357068 := by exact prefixLift 3357068
  have htrace : WordTrace (prefixWord ++ tailWord_3357068) baseStart_3357068 baseEnd_3357068 := by
    simpa [prefixWord, tailWord_3357068, baseEnd_3357068] using wordTrace_append hprefix tailTrace_3357068
  have hstable : (prefixWord ++ tailWord_3357068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357068).length < 2 ^ (prefixWord ++ tailWord_3357068).sum := by decide
  have hdescent : baseEnd_3357068 < baseStart_3357068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357079 : List Nat := [1, 1, 3, 3, 1, 1, 2, 4, 2, 4]
def baseStart_3357079 : Nat := 118140960795 + 3357079 * 2 ^ 59
def prefixEnd_3357079 : Nat := 4983230072969 + 3 ^ 40 * 3357079 * 2
def baseEnd_3357079 : Nat := 1149196748076784097782387

theorem tailTrace_3357079 : CollatzResearch.WordTrace tailWord_3357079 prefixEnd_3357079 1149196748076784097782387 := by
  unfold tailWord_3357079
  simp only [CollatzResearch.WordTrace]
  refine ⟨122442730204883601292106291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81628486803255734194737527 122442730204883601292106291)
  ·
    refine ⟨183664095307325401938159437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122442730204883601292106291 183664095307325401938159437)
    ·
      refine ⟨68874035740247025726809789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183664095307325401938159437 68874035740247025726809789)
      ·
        refine ⟨25827763402592634647553671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68874035740247025726809789 25827763402592634647553671)
        ·
          refine ⟨38741645103888951971330507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25827763402592634647553671 38741645103888951971330507)
          ·
            refine ⟨58112467655833427956995761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38741645103888951971330507 58112467655833427956995761)
            ·
              refine ⟨43584350741875070967746821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58112467655833427956995761 43584350741875070967746821)
              ·
                refine ⟨8172065764101575806452529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43584350741875070967746821 8172065764101575806452529)
                ·
                  refine ⟨6129049323076181854839397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8172065764101575806452529 6129049323076181854839397)
                  ·
                    refine ⟨1149196748076784097782387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6129049323076181854839397 1149196748076784097782387)
                    ·
                      rfl

theorem cell22_3357079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_3357079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357079 prefixEnd_3357079 := by exact prefixLift 3357079
  have htrace : WordTrace (prefixWord ++ tailWord_3357079) baseStart_3357079 baseEnd_3357079 := by
    simpa [prefixWord, tailWord_3357079, baseEnd_3357079] using wordTrace_append hprefix tailTrace_3357079
  have hstable : (prefixWord ++ tailWord_3357079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357079).length < 2 ^ (prefixWord ++ tailWord_3357079).sum := by decide
  have hdescent : baseEnd_3357079 < baseStart_3357079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357096 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 1, 6]
def baseStart_3357096 : Nat := 118140960795 + 3357096 * 2 ^ 59
def prefixEnd_3357096 : Nat := 4983230072969 + 3 ^ 40 * 3357096 * 2
def baseEnd_3357096 : Nat := 1149202567524201720107335

theorem tailTrace_3357096 : CollatzResearch.WordTrace tailWord_3357096 prefixEnd_3357096 1149202567524201720107335 := by
  unfold tailWord_3357096
  simp only [CollatzResearch.WordTrace]
  refine ⟨61221675122911006597737571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81628900163881342130316761 61221675122911006597737571)
  ·
    refine ⟨91832512684366509896606357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61221675122911006597737571 91832512684366509896606357)
    ·
      refine ⟨4304649032079680151403423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 91832512684366509896606357 4304649032079680151403423)
      ·
        refine ⟨6456973548119520227105135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4304649032079680151403423 6456973548119520227105135)
        ·
          refine ⟨9685460322179280340657703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6456973548119520227105135 9685460322179280340657703)
          ·
            refine ⟨14528190483268920510986555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9685460322179280340657703 14528190483268920510986555)
            ·
              refine ⟨21792285724903380766479833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14528190483268920510986555 21792285724903380766479833)
              ·
                refine ⟨16344214293677535574859875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21792285724903380766479833 16344214293677535574859875)
                ·
                  refine ⟨24516321440516303362289813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16344214293677535574859875 24516321440516303362289813)
                  ·
                    refine ⟨1149202567524201720107335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24516321440516303362289813 1149202567524201720107335)
                    ·
                      rfl

theorem cell22_3357096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_3357096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357096 prefixEnd_3357096 := by exact prefixLift 3357096
  have htrace : WordTrace (prefixWord ++ tailWord_3357096) baseStart_3357096 baseEnd_3357096 := by
    simpa [prefixWord, tailWord_3357096, baseEnd_3357096] using wordTrace_append hprefix tailTrace_3357096
  have hstable : (prefixWord ++ tailWord_3357096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357096).length < 2 ^ (prefixWord ++ tailWord_3357096).sum := by decide
  have hdescent : baseEnd_3357096 < baseStart_3357096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357111 : List Nat := [1, 1, 3, 1, 3, 5, 2, 6]
def baseStart_3357111 : Nat := 118140960795 + 3357111 * 2 ^ 59
def prefixEnd_3357111 : Nat := 4983230072969 + 3 ^ 40 * 3357111 * 2
def baseEnd_3357111 : Nat := 127689744703416297886921

theorem tailTrace_3357111 : CollatzResearch.WordTrace tailWord_3357111 prefixEnd_3357111 127689744703416297886921 := by
  unfold tailWord_3357111
  simp only [CollatzResearch.WordTrace]
  refine ⟨122443897340767670757271187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81629264893845113838180791 122443897340767670757271187)
  ·
    refine ⟨183665846011151506135906781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122443897340767670757271187 183665846011151506135906781)
    ·
      refine ⟨68874692254181814800965043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183665846011151506135906781 68874692254181814800965043)
      ·
        refine ⟨103312038381272722201447565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68874692254181814800965043 103312038381272722201447565)
        ·
          refine ⟨38742014392977270825542837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103312038381272722201447565 38742014392977270825542837)
          ·
            refine ⟨3632063849341619139894641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38742014392977270825542837 3632063849341619139894641)
            ·
              refine ⟨2724047887006214354920981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3632063849341619139894641 2724047887006214354920981)
              ·
                refine ⟨127689744703416297886921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2724047887006214354920981 127689744703416297886921)
                ·
                  rfl

theorem cell22_3357111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 6].length) (baseStart_3357111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357111 prefixEnd_3357111 := by exact prefixLift 3357111
  have htrace : WordTrace (prefixWord ++ tailWord_3357111) baseStart_3357111 baseEnd_3357111 := by
    simpa [prefixWord, tailWord_3357111, baseEnd_3357111] using wordTrace_append hprefix tailTrace_3357111
  have hstable : (prefixWord ++ tailWord_3357111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357111).length < 2 ^ (prefixWord ++ tailWord_3357111).sum := by decide
  have hdescent : baseEnd_3357111 < baseStart_3357111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357252 : List Nat := [2, 3, 5, 1, 1, 1, 2, 1, 6]
def baseStart_3357252 : Nat := 118140960795 + 3357252 * 2 ^ 59
def prefixEnd_3357252 : Nat := 4983230072969 + 3 ^ 40 * 3357252 * 2
def baseEnd_3357252 : Nat := 383085323170756437735619

theorem tailTrace_3357252 : CollatzResearch.WordTrace tailWord_3357252 prefixEnd_3357252 383085323170756437735619 := by
  unfold tailWord_3357252
  simp only [CollatzResearch.WordTrace]
  refine ⟨61224520016628425919077005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81632693355504567892102673 61224520016628425919077005)
  ·
    refine ⟨22959195006235659719653877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61224520016628425919077005 22959195006235659719653877)
    ·
      refine ⟨2152424531834593098717551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22959195006235659719653877 2152424531834593098717551)
      ·
        refine ⟨3228636797751889648076327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2152424531834593098717551 3228636797751889648076327)
        ·
          refine ⟨4842955196627834472114491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3228636797751889648076327 4842955196627834472114491)
          ·
            refine ⟨7264432794941751708171737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4842955196627834472114491 7264432794941751708171737)
            ·
              refine ⟨5448324596206313781128803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7264432794941751708171737 5448324596206313781128803)
              ·
                refine ⟨8172486894309470671693205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5448324596206313781128803 8172486894309470671693205)
                ·
                  refine ⟨383085323170756437735619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8172486894309470671693205 383085323170756437735619)
                  ·
                    rfl

theorem cell22_3357252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_3357252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357252 prefixEnd_3357252 := by exact prefixLift 3357252
  have htrace : WordTrace (prefixWord ++ tailWord_3357252) baseStart_3357252 baseEnd_3357252 := by
    simpa [prefixWord, tailWord_3357252, baseEnd_3357252] using wordTrace_append hprefix tailTrace_3357252
  have hstable : (prefixWord ++ tailWord_3357252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357252).length < 2 ^ (prefixWord ++ tailWord_3357252).sum := by decide
  have hdescent : baseEnd_3357252 < baseStart_3357252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357259 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 1, 8]
def baseStart_3357259 : Nat := 118140960795 + 3357259 * 2 ^ 59
def prefixEnd_3357259 : Nat := 4983230072969 + 3 ^ 40 * 3357259 * 2
def baseEnd_3357259 : Nat := 1149258365755323628281835

theorem tailTrace_3357259 : CollatzResearch.WordTrace tailWord_3357259 prefixEnd_3357259 1149258365755323628281835 := by
  unfold tailWord_3357259
  simp only [CollatzResearch.WordTrace]
  refine ⟨122449295344231492033658831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81632863562820994689105887 122449295344231492033658831)
  ·
    refine ⟨183673943016347238050488247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122449295344231492033658831 183673943016347238050488247)
    ·
      refine ⟨275510914524520857075732371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183673943016347238050488247 275510914524520857075732371)
      ·
        refine ⟨413266371786781285613598557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275510914524520857075732371 413266371786781285613598557)
        ·
          refine ⟨154974889420042982105099459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 413266371786781285613598557 154974889420042982105099459)
          ·
            refine ⟨232462334130064473157649189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154974889420042982105099459 232462334130064473157649189)
            ·
              refine ⟨43586687649387088717059223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232462334130064473157649189 43586687649387088717059223)
              ·
                refine ⟨65380031474080633075588835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43586687649387088717059223 65380031474080633075588835)
                ·
                  refine ⟨98070047211120949613383253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65380031474080633075588835 98070047211120949613383253)
                  ·
                    refine ⟨1149258365755323628281835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98070047211120949613383253 1149258365755323628281835)
                    ·
                      rfl

theorem cell22_3357259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 8].length) (baseStart_3357259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357259 prefixEnd_3357259 := by exact prefixLift 3357259
  have htrace : WordTrace (prefixWord ++ tailWord_3357259) baseStart_3357259 baseEnd_3357259 := by
    simpa [prefixWord, tailWord_3357259, baseEnd_3357259] using wordTrace_append hprefix tailTrace_3357259
  have hstable : (prefixWord ++ tailWord_3357259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357259).length < 2 ^ (prefixWord ++ tailWord_3357259).sum := by decide
  have hdescent : baseEnd_3357259 < baseStart_3357259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357295 : List Nat := [1, 1, 2, 1, 3, 2, 5, 3, 1, 3]
def baseStart_3357295 : Nat := 118140960795 + 3357295 * 2 ^ 59
def prefixEnd_3357295 : Nat := 4983230072969 + 3 ^ 40 * 3357295 * 2
def baseEnd_3357295 : Nat := 1149270689291031534381725

theorem tailTrace_3357295 : CollatzResearch.WordTrace tailWord_3357295 prefixEnd_3357295 1149270689291031534381725 := by
  unfold tailWord_3357295
  simp only [CollatzResearch.WordTrace]
  refine ⟨122450608372101070181969339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81633738914734046787979559 122450608372101070181969339)
  ·
    refine ⟨183675912558151605272954009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122450608372101070181969339 183675912558151605272954009)
    ·
      refine ⟨137756934418613703954715507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183675912558151605272954009 137756934418613703954715507)
      ·
        refine ⟨206635401627920555932073261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137756934418613703954715507 206635401627920555932073261)
        ·
          refine ⟨77488275610470208474527473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206635401627920555932073261 77488275610470208474527473)
          ·
            refine ⟨58116206707852656355895605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77488275610470208474527473 58116206707852656355895605)
            ·
              refine ⟨5448394378861186533365213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58116206707852656355895605 5448394378861186533365213)
              ·
                refine ⟨2043147892072944950011955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5448394378861186533365213 2043147892072944950011955)
                ·
                  refine ⟨3064721838109417425017933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043147892072944950011955 3064721838109417425017933)
                  ·
                    refine ⟨1149270689291031534381725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3064721838109417425017933 1149270689291031534381725)
                    ·
                      rfl

theorem cell22_3357295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 1, 3].length) (baseStart_3357295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357295 prefixEnd_3357295 := by exact prefixLift 3357295
  have htrace : WordTrace (prefixWord ++ tailWord_3357295) baseStart_3357295 baseEnd_3357295 := by
    simpa [prefixWord, tailWord_3357295, baseEnd_3357295] using wordTrace_append hprefix tailTrace_3357295
  have hstable : (prefixWord ++ tailWord_3357295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357295).length < 2 ^ (prefixWord ++ tailWord_3357295).sum := by decide
  have hdescent : baseEnd_3357295 < baseStart_3357295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357312 : List Nat := [2, 1, 1, 2, 1, 6, 3, 2, 1, 3]
def baseStart_3357312 : Nat := 118140960795 + 3357312 * 2 ^ 59
def prefixEnd_3357312 : Nat := 4983230072969 + 3 ^ 40 * 3357312 * 2
def baseEnd_3357312 : Nat := 1149276508738449156706673

theorem tailTrace_3357312 : CollatzResearch.WordTrace tailWord_3357312 prefixEnd_3357312 1149276508738449156706673 := by
  unfold tailWord_3357312
  simp only [CollatzResearch.WordTrace]
  refine ⟨61225614206519741042669095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81634152275359654723558793 61225614206519741042669095)
  ·
    refine ⟨91838421309779611564003643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61225614206519741042669095 91838421309779611564003643)
    ·
      refine ⟨137757631964669417346005465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91838421309779611564003643 137757631964669417346005465)
      ·
        refine ⟨103318223973502063009504099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137757631964669417346005465 103318223973502063009504099)
        ·
          refine ⟨154977335960253094514256149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103318223973502063009504099 154977335960253094514256149)
          ·
            refine ⟨7264562623136863805355757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 154977335960253094514256149 7264562623136863805355757)
            ·
              refine ⟨2724210983676323927008409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7264562623136863805355757 2724210983676323927008409)
              ·
                refine ⟨2043158237757242945256307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2724210983676323927008409 2043158237757242945256307)
                ·
                  refine ⟨3064737356635864417884461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043158237757242945256307 3064737356635864417884461)
                  ·
                    refine ⟨1149276508738449156706673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3064737356635864417884461 1149276508738449156706673)
                    ·
                      rfl

theorem cell22_3357312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 1, 3].length) (baseStart_3357312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357312 prefixEnd_3357312 := by exact prefixLift 3357312
  have htrace : WordTrace (prefixWord ++ tailWord_3357312) baseStart_3357312 baseEnd_3357312 := by
    simpa [prefixWord, tailWord_3357312, baseEnd_3357312] using wordTrace_append hprefix tailTrace_3357312
  have hstable : (prefixWord ++ tailWord_3357312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357312).length < 2 ^ (prefixWord ++ tailWord_3357312).sum := by decide
  have hdescent : baseEnd_3357312 < baseStart_3357312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357321 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 3, 4]
def baseStart_3357321 : Nat := 118140960795 + 3357321 * 2 ^ 59
def prefixEnd_3357321 : Nat := 4983230072969 + 3 ^ 40 * 3357321 * 2
def baseEnd_3357321 : Nat := 1149279589622376133231645

theorem tailTrace_3357321 : CollatzResearch.WordTrace tailWord_3357321 prefixEnd_3357321 1149279589622376133231645 := by
  unfold tailWord_3357321
  simp only [CollatzResearch.WordTrace]
  refine ⟨122451556670006876622415817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81634371113337917748277211 122451556670006876622415817)
  ·
    refine ⟨91838667502505157466811863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122451556670006876622415817 91838667502505157466811863)
    ·
      refine ⟨137758001253757736200217795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91838667502505157466811863 137758001253757736200217795)
      ·
        refine ⟨206637001880636604300326693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137758001253757736200217795 206637001880636604300326693)
        ·
          refine ⟨38744437852619363306311255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206637001880636604300326693 38744437852619363306311255)
          ·
            refine ⟨58116656778929044959466883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38744437852619363306311255 58116656778929044959466883)
            ·
              refine ⟨87174985168393567439200325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58116656778929044959466883 87174985168393567439200325)
              ·
                refine ⟨16345309719073793894850061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87174985168393567439200325 16345309719073793894850061)
                ·
                  refine ⟨6129491144652672710568773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16345309719073793894850061 6129491144652672710568773)
                  ·
                    refine ⟨1149279589622376133231645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6129491144652672710568773 1149279589622376133231645)
                    ·
                      rfl

theorem cell22_3357321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 4].length) (baseStart_3357321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357321 prefixEnd_3357321 := by exact prefixLift 3357321
  have htrace : WordTrace (prefixWord ++ tailWord_3357321) baseStart_3357321 baseEnd_3357321 := by
    simpa [prefixWord, tailWord_3357321, baseEnd_3357321] using wordTrace_append hprefix tailTrace_3357321
  have hstable : (prefixWord ++ tailWord_3357321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357321).length < 2 ^ (prefixWord ++ tailWord_3357321).sum := by decide
  have hdescent : baseEnd_3357321 < baseStart_3357321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357336 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 8]
def baseStart_3357336 : Nat := 118140960795 + 3357336 * 2 ^ 59
def prefixEnd_3357336 : Nat := 4983230072969 + 3 ^ 40 * 3357336 * 2
def baseEnd_3357336 : Nat := 383094908142973698035533

theorem tailTrace_3357336 : CollatzResearch.WordTrace tailWord_3357336 prefixEnd_3357336 383094908142973698035533 := by
  unfold tailWord_3357336
  simp only [CollatzResearch.WordTrace]
  refine ⟨61226051882476267092105931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81634735843301689456141241 61226051882476267092105931)
  ·
    refine ⟨91839077823714400638158897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61226051882476267092105931 91839077823714400638158897)
    ·
      refine ⟨68879308367785800478619173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91839077823714400638158897 68879308367785800478619173)
      ·
        refine ⟨12914870318959837589741095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68879308367785800478619173 12914870318959837589741095)
        ·
          refine ⟨19372305478439756384611643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12914870318959837589741095 19372305478439756384611643)
          ·
            refine ⟨29058458217659634576917465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19372305478439756384611643 29058458217659634576917465)
            ·
              refine ⟨21793843663244725932688099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29058458217659634576917465 21793843663244725932688099)
              ·
                refine ⟨32690765494867088899032149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21793843663244725932688099 32690765494867088899032149)
                ·
                  refine ⟨383094908142973698035533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32690765494867088899032149 383094908142973698035533)
                  ·
                    rfl

theorem cell22_3357336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 8].length) (baseStart_3357336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357336 prefixEnd_3357336 := by exact prefixLift 3357336
  have htrace : WordTrace (prefixWord ++ tailWord_3357336) baseStart_3357336 baseEnd_3357336 := by
    simpa [prefixWord, tailWord_3357336, baseEnd_3357336] using wordTrace_append hprefix tailTrace_3357336
  have hstable : (prefixWord ++ tailWord_3357336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357336).length < 2 ^ (prefixWord ++ tailWord_3357336).sum := by decide
  have hdescent : baseEnd_3357336 < baseStart_3357336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357400 : List Nat := [2, 1, 2, 2, 3, 4, 1, 1, 2, 4]
def baseStart_3357400 : Nat := 118140960795 + 3357400 * 2 ^ 59
def prefixEnd_3357400 : Nat := 4983230072969 + 3 ^ 40 * 3357400 * 2
def baseEnd_3357400 : Nat := 1149306632936846260506403

theorem tailTrace_3357400 : CollatzResearch.WordTrace tailWord_3357400 prefixEnd_3357400 1149306632936846260506403 := by
  unfold tailWord_3357400
  simp only [CollatzResearch.WordTrace]
  refine ⟨61227219018360336557270827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81636292024480448743027769 61227219018360336557270827)
  ·
    refine ⟨91840828527540504835906241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61227219018360336557270827 91840828527540504835906241)
    ·
      refine ⟨68880621395655378626929681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91840828527540504835906241 68880621395655378626929681)
      ·
        refine ⟨51660466046741533970197261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68880621395655378626929681 51660466046741533970197261)
        ·
          refine ⟨19372674767528075238823973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51660466046741533970197261 19372674767528075238823973)
          ·
            refine ⟨3632376518911514107279495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19372674767528075238823973 3632376518911514107279495)
            ·
              refine ⟨5448564778367271160919243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3632376518911514107279495 5448564778367271160919243)
              ·
                refine ⟨8172847167550906741378865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5448564778367271160919243 8172847167550906741378865)
                ·
                  refine ⟨6129635375663180056034149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8172847167550906741378865 6129635375663180056034149)
                  ·
                    refine ⟨1149306632936846260506403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6129635375663180056034149 1149306632936846260506403)
                    ·
                      rfl

theorem cell22_3357400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_3357400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357400 prefixEnd_3357400 := by exact prefixLift 3357400
  have htrace : WordTrace (prefixWord ++ tailWord_3357400) baseStart_3357400 baseEnd_3357400 := by
    simpa [prefixWord, tailWord_3357400, baseEnd_3357400] using wordTrace_append hprefix tailTrace_3357400
  have hstable : (prefixWord ++ tailWord_3357400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357400).length < 2 ^ (prefixWord ++ tailWord_3357400).sum := by decide
  have hdescent : baseEnd_3357400 < baseStart_3357400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357518 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_3357518 : Nat := 118140960795 + 3357518 * 2 ^ 59
def prefixEnd_3357518 : Nat := 4983230072969 + 3 ^ 40 * 3357518 * 2
def baseEnd_3357518 : Nat := 1149347026748333286056041

theorem tailTrace_3357518 : CollatzResearch.WordTrace tailWord_3357518 prefixEnd_3357518 1149347026748333286056041 := by
  unfold tailWord_3357518
  simp only [CollatzResearch.WordTrace]
  refine ⟨15307342731286647408417151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81639161233528786178224805 15307342731286647408417151)
  ·
    refine ⟨22961014096929971112625727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15307342731286647408417151 22961014096929971112625727)
    ·
      refine ⟨34441521145394956668938591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22961014096929971112625727 34441521145394956668938591)
      ·
        refine ⟨51662281718092435003407887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34441521145394956668938591 51662281718092435003407887)
        ·
          refine ⟨77493422577138652505111831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51662281718092435003407887 77493422577138652505111831)
          ·
            refine ⟨116240133865707978757667747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77493422577138652505111831 116240133865707978757667747)
            ·
              refine ⟨174360200798561968136501621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116240133865707978757667747 174360200798561968136501621)
              ·
                refine ⟨16346268824865184512797027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174360200798561968136501621 16346268824865184512797027)
                ·
                  refine ⟨24519403237297776769195541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16346268824865184512797027 24519403237297776769195541)
                  ·
                    refine ⟨1149347026748333286056041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24519403237297776769195541 1149347026748333286056041)
                    ·
                      rfl

theorem cell22_3357518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_3357518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357518 prefixEnd_3357518 := by exact prefixLift 3357518
  have htrace : WordTrace (prefixWord ++ tailWord_3357518) baseStart_3357518 baseEnd_3357518 := by
    simpa [prefixWord, tailWord_3357518, baseEnd_3357518] using wordTrace_append hprefix tailTrace_3357518
  have hstable : (prefixWord ++ tailWord_3357518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357518).length < 2 ^ (prefixWord ++ tailWord_3357518).sum := by decide
  have hdescent : baseEnd_3357518 < baseStart_3357518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357524 : List Nat := [2, 4, 1, 1, 4, 1, 3, 1, 1, 4]
def baseStart_3357524 : Nat := 118140960795 + 3357524 * 2 ^ 59
def prefixEnd_3357524 : Nat := 4983230072969 + 3 ^ 40 * 3357524 * 2
def baseEnd_3357524 : Nat := 1149349080670951270406023

theorem tailTrace_3357524 : CollatzResearch.WordTrace tailWord_3357524 prefixEnd_3357524 1149349080670951270406023 := by
  unfold tailWord_3357524
  simp only [CollatzResearch.WordTrace]
  refine ⟨61229480344135721146027813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81639307125514294861370417 61229480344135721146027813)
  ·
    refine ⟨11480527564525447714880215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61229480344135721146027813 11480527564525447714880215)
    ·
      refine ⟨17220791346788171572320323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11480527564525447714880215 17220791346788171572320323)
      ·
        refine ⟨25831187020182257358480485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17220791346788171572320323 25831187020182257358480485)
        ·
          refine ⟨4843347566284173254715091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25831187020182257358480485 4843347566284173254715091)
          ·
            refine ⟨7265021349426259882072637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4843347566284173254715091 7265021349426259882072637)
            ·
              refine ⟨2724383006034847455777239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7265021349426259882072637 2724383006034847455777239)
              ·
                refine ⟨4086574509052271183665859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2724383006034847455777239 4086574509052271183665859)
                ·
                  refine ⟨6129861763578406775498789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4086574509052271183665859 6129861763578406775498789)
                  ·
                    refine ⟨1149349080670951270406023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6129861763578406775498789 1149349080670951270406023)
                    ·
                      rfl

theorem cell22_3357524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_3357524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357524 prefixEnd_3357524 := by exact prefixLift 3357524
  have htrace : WordTrace (prefixWord ++ tailWord_3357524) baseStart_3357524 baseEnd_3357524 := by
    simpa [prefixWord, tailWord_3357524, baseEnd_3357524] using wordTrace_append hprefix tailTrace_3357524
  have hstable : (prefixWord ++ tailWord_3357524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357524).length < 2 ^ (prefixWord ++ tailWord_3357524).sum := by decide
  have hdescent : baseEnd_3357524 < baseStart_3357524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357539 : List Nat := [1, 1, 1, 5, 3, 3, 2, 2, 4]
def baseStart_3357539 : Nat := 118140960795 + 3357539 * 2 ^ 59
def prefixEnd_3357539 : Nat := 4983230072969 + 3 ^ 40 * 3357539 * 2
def baseEnd_3357539 : Nat := 383118071825832077093659

theorem tailTrace_3357539 : CollatzResearch.WordTrace tailWord_3357539 prefixEnd_3357539 383118071825832077093659 := by
  unfold tailWord_3357539
  simp only [CollatzResearch.WordTrace]
  refine ⟨122459507783217099853851671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81639671855478066569234447 122459507783217099853851671)
  ·
    refine ⟨183689261674825649780777507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122459507783217099853851671 183689261674825649780777507)
    ·
      refine ⟨275533892512238474671166261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183689261674825649780777507 275533892512238474671166261)
      ·
        refine ⟨25831302423022357000421837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 275533892512238474671166261 25831302423022357000421837)
        ·
          refine ⟨9686738408633383875158189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25831302423022357000421837 9686738408633383875158189)
          ·
            refine ⟨3632526903237518953184321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9686738408633383875158189 3632526903237518953184321)
            ·
              refine ⟨2724395177428139214888241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3632526903237518953184321 2724395177428139214888241)
              ·
                refine ⟨2043296383071104411166181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2724395177428139214888241 2043296383071104411166181)
                ·
                  refine ⟨383118071825832077093659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2043296383071104411166181 383118071825832077093659)
                  ·
                    rfl

theorem cell22_3357539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 4].length) (baseStart_3357539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357539 prefixEnd_3357539 := by exact prefixLift 3357539
  have htrace : WordTrace (prefixWord ++ tailWord_3357539) baseStart_3357539 baseEnd_3357539 := by
    simpa [prefixWord, tailWord_3357539, baseEnd_3357539] using wordTrace_append hprefix tailTrace_3357539
  have hstable : (prefixWord ++ tailWord_3357539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357539).length < 2 ^ (prefixWord ++ tailWord_3357539).sum := by decide
  have hdescent : baseEnd_3357539 < baseStart_3357539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357565 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 5, 3]
def baseStart_3357565 : Nat := 118140960795 + 3357565 * 2 ^ 59
def prefixEnd_3357565 : Nat := 4983230072969 + 3 ^ 40 * 3357565 * 2
def baseEnd_3357565 : Nat := 1149363115808840830130897

theorem tailTrace_3357565 : CollatzResearch.WordTrace tailWord_3357565 prefixEnd_3357565 1149363115808840830130897 := by
  unfold tailWord_3357565
  simp only [CollatzResearch.WordTrace]
  refine ⟨122460456081122906294298149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81640304054081937529532099 122460456081122906294298149)
  ·
    refine ⟨22961335515210544930180903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122460456081122906294298149 22961335515210544930180903)
    ·
      refine ⟨34442003272815817395271355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22961335515210544930180903 34442003272815817395271355)
      ·
        refine ⟨51663004909223726092907033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34442003272815817395271355 51663004909223726092907033)
        ·
          refine ⟨38747253681917794569680275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51663004909223726092907033 38747253681917794569680275)
          ·
            refine ⟨58120880522876691854520413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38747253681917794569680275 58120880522876691854520413)
            ·
              refine ⟨21795330196078759445445155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58120880522876691854520413 21795330196078759445445155)
              ·
                refine ⟨32692995294118139168167733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21795330196078759445445155 32692995294118139168167733)
                ·
                  refine ⟨3064968308823575547015725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32692995294118139168167733 3064968308823575547015725)
                  ·
                    refine ⟨1149363115808840830130897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3064968308823575547015725 1149363115808840830130897)
                    ·
                      rfl

theorem cell22_3357565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_3357565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357565 prefixEnd_3357565 := by exact prefixLift 3357565
  have htrace : WordTrace (prefixWord ++ tailWord_3357565) baseStart_3357565 baseEnd_3357565 := by
    simpa [prefixWord, tailWord_3357565, baseEnd_3357565] using wordTrace_append hprefix tailTrace_3357565
  have hstable : (prefixWord ++ tailWord_3357565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357565).length < 2 ^ (prefixWord ++ tailWord_3357565).sum := by decide
  have hdescent : baseEnd_3357565 < baseStart_3357565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357599 : List Nat := [1, 1, 2, 5, 2, 1, 2, 4, 1, 3]
def baseStart_3357599 : Nat := 118140960795 + 3357599 * 2 ^ 59
def prefixEnd_3357599 : Nat := 4983230072969 + 3 ^ 40 * 3357599 * 2
def baseEnd_3357599 : Nat := 1149374754703676074780793

theorem tailTrace_3357599 : CollatzResearch.WordTrace tailWord_3357599 prefixEnd_3357599 1149374754703676074780793 := by
  unfold tailWord_3357599
  simp only [CollatzResearch.WordTrace]
  refine ⟨122461696162999730101035851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81641130775333153400690567 122461696162999730101035851)
  ·
    refine ⟨183692544244499595151553777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122461696162999730101035851 183692544244499595151553777)
    ·
      refine ⟨137769408183374696363665333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183692544244499595151553777 137769408183374696363665333)
      ·
        refine ⟨12915882017191377784093625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137769408183374696363665333 12915882017191377784093625)
        ·
          refine ⟨9686911512893533338070219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12915882017191377784093625 9686911512893533338070219)
          ·
            refine ⟨14530367269340300007105329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9686911512893533338070219 14530367269340300007105329)
            ·
              refine ⟨10897775452005225005328997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14530367269340300007105329 10897775452005225005328997)
              ·
                refine ⟨2043332897250979688499187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10897775452005225005328997 2043332897250979688499187)
                ·
                  refine ⟨3064999345876469532748781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043332897250979688499187 3064999345876469532748781)
                  ·
                    refine ⟨1149374754703676074780793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3064999345876469532748781 1149374754703676074780793)
                    ·
                      rfl

theorem cell22_3357599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 1, 3].length) (baseStart_3357599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357599 prefixEnd_3357599 := by exact prefixLift 3357599
  have htrace : WordTrace (prefixWord ++ tailWord_3357599) baseStart_3357599 baseEnd_3357599 := by
    simpa [prefixWord, tailWord_3357599, baseEnd_3357599] using wordTrace_append hprefix tailTrace_3357599
  have hstable : (prefixWord ++ tailWord_3357599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357599).length < 2 ^ (prefixWord ++ tailWord_3357599).sum := by decide
  have hdescent : baseEnd_3357599 < baseStart_3357599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357657 : List Nat := [1, 2, 1, 2, 5, 3, 1, 1, 6]
def baseStart_3357657 : Nat := 118140960795 + 3357657 * 2 ^ 59
def prefixEnd_3357657 : Nat := 4983230072969 + 3 ^ 40 * 3357657 * 2
def baseEnd_3357657 : Nat := 383131536429661085610205

theorem tailTrace_3357657 : CollatzResearch.WordTrace tailWord_3357657 prefixEnd_3357657 383131536429661085610205 := by
  unfold tailWord_3357657
  simp only [CollatzResearch.WordTrace]
  refine ⟨122463811596789606006647225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81642541064526404004431483 122463811596789606006647225)
  ·
    refine ⟨91847858697592204504985419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122463811596789606006647225 91847858697592204504985419)
    ·
      refine ⟨137771788046388306757478129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91847858697592204504985419 137771788046388306757478129)
      ·
        refine ⟨103328841034791230068108597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137771788046388306757478129 103328841034791230068108597)
        ·
          refine ⟨9687078847011677818885181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103328841034791230068108597 9687078847011677818885181)
          ·
            refine ⟨3632654567629379182081943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9687078847011677818885181 3632654567629379182081943)
            ·
              refine ⟨5448981851444068773122915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3632654567629379182081943 5448981851444068773122915)
              ·
                refine ⟨8173472777166103159684373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5448981851444068773122915 8173472777166103159684373)
                ·
                  refine ⟨383131536429661085610205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8173472777166103159684373 383131536429661085610205)
                  ·
                    rfl

theorem cell22_3357657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 6].length) (baseStart_3357657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357657 prefixEnd_3357657 := by exact prefixLift 3357657
  have htrace : WordTrace (prefixWord ++ tailWord_3357657) baseStart_3357657 baseEnd_3357657 := by
    simpa [prefixWord, tailWord_3357657, baseEnd_3357657] using wordTrace_append hprefix tailTrace_3357657
  have hstable : (prefixWord ++ tailWord_3357657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357657).length < 2 ^ (prefixWord ++ tailWord_3357657).sum := by decide
  have hdescent : baseEnd_3357657 < baseStart_3357657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357745 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 1, 7]
def baseStart_3357745 : Nat := 118140960795 + 3357745 * 2 ^ 59
def prefixEnd_3357745 : Nat := 4983230072969 + 3 ^ 40 * 3357745 * 2
def baseEnd_3357745 : Nat := 1149424733487380360630345

theorem tailTrace_3357745 : CollatzResearch.WordTrace tailWord_3357745 prefixEnd_3357745 1149424733487380360630345 := by
  unfold tailWord_3357745
  simp only [CollatzResearch.WordTrace]
  refine ⟨122467021220470797035850689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81644680813647198023900459 122467021220470797035850689)
  ·
    refine ⟨91850265915353097776888017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122467021220470797035850689 91850265915353097776888017)
    ·
      refine ⟨68887699436514823332666013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91850265915353097776888017 68887699436514823332666013)
      ·
        refine ⟨25832887288693058749749755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68887699436514823332666013 25832887288693058749749755)
        ·
          refine ⟨38749330933039588124624633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25832887288693058749749755 38749330933039588124624633)
          ·
            refine ⟨29061998199779691093468475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38749330933039588124624633 29061998199779691093468475)
            ·
              refine ⟨43592997299669536640202713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29061998199779691093468475 43592997299669536640202713)
              ·
                refine ⟨32694747974752152480152035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43592997299669536640202713 32694747974752152480152035)
                ·
                  refine ⟨49042121962128228720228053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32694747974752152480152035 49042121962128228720228053)
                  ·
                    refine ⟨1149424733487380360630345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49042121962128228720228053 1149424733487380360630345)
                    ·
                      rfl

theorem cell22_3357745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_3357745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357745 prefixEnd_3357745 := by exact prefixLift 3357745
  have htrace : WordTrace (prefixWord ++ tailWord_3357745) baseStart_3357745 baseEnd_3357745 := by
    simpa [prefixWord, tailWord_3357745, baseEnd_3357745] using wordTrace_append hprefix tailTrace_3357745
  have hstable : (prefixWord ++ tailWord_3357745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357745).length < 2 ^ (prefixWord ++ tailWord_3357745).sum := by decide
  have hdescent : baseEnd_3357745 < baseStart_3357745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357807 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 6, 3]
def baseStart_3357807 : Nat := 118140960795 + 3357807 * 2 ^ 59
def prefixEnd_3357807 : Nat := 4983230072969 + 3 ^ 40 * 3357807 * 2
def baseEnd_3357807 : Nat := 1149445957354432865580155

theorem tailTrace_3357807 : CollatzResearch.WordTrace tailWord_3357807 prefixEnd_3357807 1149445957354432865580155 := by
  unfold tailWord_3357807
  simp only [CollatzResearch.WordTrace]
  refine ⟨122469282546246181624607675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81646188364164121083071783 122469282546246181624607675)
  ·
    refine ⟨183703923819369272436911513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122469282546246181624607675 183703923819369272436911513)
    ·
      refine ⟨137777942864526954327683635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183703923819369272436911513 137777942864526954327683635)
      ·
        refine ⟨206666914296790431491525453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137777942864526954327683635 206666914296790431491525453)
        ·
          refine ⟨77500092861296411809322045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206666914296790431491525453 77500092861296411809322045)
          ·
            refine ⟨29062534822986154428495767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77500092861296411809322045 29062534822986154428495767)
            ·
              refine ⟨43593802234479231642743651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29062534822986154428495767 43593802234479231642743651)
              ·
                refine ⟨65390703351718847464115477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43593802234479231642743651 65390703351718847464115477)
                ·
                  refine ⟨3065189219611820974880413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65390703351718847464115477 3065189219611820974880413)
                  ·
                    refine ⟨1149445957354432865580155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3065189219611820974880413 1149445957354432865580155)
                    ·
                      rfl

theorem cell22_3357807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 3].length) (baseStart_3357807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357807 prefixEnd_3357807 := by exact prefixLift 3357807
  have htrace : WordTrace (prefixWord ++ tailWord_3357807) baseStart_3357807 baseEnd_3357807 := by
    simpa [prefixWord, tailWord_3357807, baseEnd_3357807] using wordTrace_append hprefix tailTrace_3357807
  have hstable : (prefixWord ++ tailWord_3357807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357807).length < 2 ^ (prefixWord ++ tailWord_3357807).sum := by decide
  have hdescent : baseEnd_3357807 < baseStart_3357807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357854 : List Nat := [4, 3, 1, 1, 2, 1, 2, 8]
def baseStart_3357854 : Nat := 118140960795 + 3357854 * 2 ^ 59
def prefixEnd_3357854 : Nat := 4983230072969 + 3 ^ 40 * 3357854 * 2
def baseEnd_3357854 : Nat := 127718005157215601072779

theorem tailTrace_3357854 : CollatzResearch.WordTrace tailWord_3357854 prefixEnd_3357854 127718005157215601072779 := by
  unfold tailWord_3357854
  simp only [CollatzResearch.WordTrace]
  refine ⟨15308874597134488581446077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81647331184717272434379077 15308874597134488581446077)
  ·
    refine ⟨5740827973925433218042279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15308874597134488581446077 5740827973925433218042279)
    ·
      refine ⟨8611241960888149827063419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5740827973925433218042279 8611241960888149827063419)
      ·
        refine ⟨12916862941332224740595129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8611241960888149827063419 12916862941332224740595129)
        ·
          refine ⟨9687647205999168555446347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12916862941332224740595129 9687647205999168555446347)
          ·
            refine ⟨14531470808998752833169521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9687647205999168555446347 14531470808998752833169521)
            ·
              refine ⟨10898603106749064624877141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14531470808998752833169521 10898603106749064624877141)
              ·
                refine ⟨127718005157215601072779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10898603106749064624877141 127718005157215601072779)
                ·
                  rfl

theorem cell22_3357854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_3357854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357854 prefixEnd_3357854 := by exact prefixLift 3357854
  have htrace : WordTrace (prefixWord ++ tailWord_3357854) baseStart_3357854 baseEnd_3357854 := by
    simpa [prefixWord, tailWord_3357854, baseEnd_3357854] using wordTrace_append hprefix tailTrace_3357854
  have hstable : (prefixWord ++ tailWord_3357854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357854).length < 2 ^ (prefixWord ++ tailWord_3357854).sum := by decide
  have hdescent : baseEnd_3357854 < baseStart_3357854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357957 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 3, 6]
def baseStart_3357957 : Nat := 118140960795 + 3357957 * 2 ^ 59
def prefixEnd_3357957 : Nat := 4983230072969 + 3 ^ 40 * 3357957 * 2
def baseEnd_3357957 : Nat := 1149497305419882474329695

theorem tailTrace_3357957 : CollatzResearch.WordTrace tailWord_3357957 prefixEnd_3357957 1149497305419882474329695 := by
  unfold tailWord_3357957
  simp only [CollatzResearch.WordTrace]
  refine ⟨122474753495702757242568125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81649835663801838161712083 122474753495702757242568125)
  ·
    refine ⟨45928032560888533965963047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122474753495702757242568125 45928032560888533965963047)
    ·
      refine ⟨68892048841332800948944571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45928032560888533965963047 68892048841332800948944571)
      ·
        refine ⟨103338073261999201423416857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68892048841332800948944571 103338073261999201423416857)
        ·
          refine ⟨77503554946499401067562643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103338073261999201423416857 77503554946499401067562643)
          ·
            refine ⟨116255332419749101601343965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77503554946499401067562643 116255332419749101601343965)
            ·
              refine ⟨43595749657405913100503987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116255332419749101601343965 43595749657405913100503987)
              ·
                refine ⟨65393624486108869650755981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43595749657405913100503987 65393624486108869650755981)
                ·
                  refine ⟨24522609182290826119033493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65393624486108869650755981 24522609182290826119033493)
                  ·
                    refine ⟨1149497305419882474329695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24522609182290826119033493 1149497305419882474329695)
                    ·
                      rfl

theorem cell22_3357957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_3357957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357957 prefixEnd_3357957 := by exact prefixLift 3357957
  have htrace : WordTrace (prefixWord ++ tailWord_3357957) baseStart_3357957 baseEnd_3357957 := by
    simpa [prefixWord, tailWord_3357957, baseEnd_3357957] using wordTrace_append hprefix tailTrace_3357957
  have hstable : (prefixWord ++ tailWord_3357957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357957).length < 2 ^ (prefixWord ++ tailWord_3357957).sum := by decide
  have hdescent : baseEnd_3357957 < baseStart_3357957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357978 : List Nat := [3, 1, 1, 3, 3, 3, 1, 3, 4]
def baseStart_3357978 : Nat := 118140960795 + 3357978 * 2 ^ 59
def prefixEnd_3357978 : Nat := 4983230072969 + 3 ^ 40 * 3357978 * 2
def baseEnd_3357978 : Nat := 383168164716348473184877

theorem tailTrace_3357978 : CollatzResearch.WordTrace tailWord_3357978 prefixEnd_3357978 383168164716348473184877 := by
  unfold tailWord_3357978
  simp only [CollatzResearch.WordTrace]
  refine ⟨30618879857156669457270647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81650346285751118552721725 30618879857156669457270647)
  ·
    refine ⟨45928319785735004185905971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30618879857156669457270647 45928319785735004185905971)
    ·
      refine ⟨68892479678602506278858957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45928319785735004185905971 68892479678602506278858957)
      ·
        refine ⟨25834679879475939854572109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68892479678602506278858957 25834679879475939854572109)
        ·
          refine ⟨9688004954803477445464541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25834679879475939854572109 9688004954803477445464541)
          ·
            refine ⟨3633001858051304042049203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9688004954803477445464541 3633001858051304042049203)
            ·
              refine ⟨5449502787076956063073805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3633001858051304042049203 5449502787076956063073805)
              ·
                refine ⟨2043563545153858523652677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5449502787076956063073805 2043563545153858523652677)
                ·
                  refine ⟨383168164716348473184877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2043563545153858523652677 383168164716348473184877)
                  ·
                    rfl

theorem cell22_3357978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 4].length) (baseStart_3357978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357978 prefixEnd_3357978 := by exact prefixLift 3357978
  have htrace : WordTrace (prefixWord ++ tailWord_3357978) baseStart_3357978 baseEnd_3357978 := by
    simpa [prefixWord, tailWord_3357978, baseEnd_3357978] using wordTrace_append hprefix tailTrace_3357978
  have hstable : (prefixWord ++ tailWord_3357978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357978).length < 2 ^ (prefixWord ++ tailWord_3357978).sum := by decide
  have hdescent : baseEnd_3357978 < baseStart_3357978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357989 : List Nat := [1, 3, 1, 2, 4, 3, 8]
def baseStart_3357989 : Nat := 118140960795 + 3357989 * 2 ^ 59
def prefixEnd_3357989 : Nat := 4983230072969 + 3 ^ 40 * 3357989 * 2
def baseEnd_3357989 : Nat := 42574379987920187315911

theorem tailTrace_3357989 : CollatzResearch.WordTrace tailWord_3357989 prefixEnd_3357989 42574379987920187315911 := by
  unfold tailWord_3357989
  simp only [CollatzResearch.WordTrace]
  refine ⟨122475920631586826707733021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81650613754391217805155347 122475920631586826707733021)
  ·
    refine ⟨45928470236845060015399883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122475920631586826707733021 45928470236845060015399883)
    ·
      refine ⟨68892705355267590023099825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45928470236845060015399883 68892705355267590023099825)
      ·
        refine ⟨51669529016450692517324869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68892705355267590023099825 51669529016450692517324869)
        ·
          refine ⟨9688036690584504846998413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51669529016450692517324869 9688036690584504846998413)
          ·
            refine ⟨3633013758969189317624405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9688036690584504846998413 3633013758969189317624405)
            ·
              refine ⟨42574379987920187315911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3633013758969189317624405 42574379987920187315911)
              ·
                rfl

theorem cell22_3357989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 8].length) (baseStart_3357989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3357989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3357989 prefixEnd_3357989 := by exact prefixLift 3357989
  have htrace : WordTrace (prefixWord ++ tailWord_3357989) baseStart_3357989 baseEnd_3357989 := by
    simpa [prefixWord, tailWord_3357989, baseEnd_3357989] using wordTrace_append hprefix tailTrace_3357989
  have hstable : (prefixWord ++ tailWord_3357989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357989).length < 2 ^ (prefixWord ++ tailWord_3357989).sum := by decide
  have hdescent : baseEnd_3357989 < baseStart_3357989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358051 : List Nat := [1, 1, 1, 5, 2, 3, 2, 2, 5]
def baseStart_3358051 : Nat := 118140960795 + 3358051 * 2 ^ 59
def prefixEnd_3358051 : Nat := 4983230072969 + 3 ^ 40 * 3358051 * 2
def baseEnd_3358051 : Nat := 383176494513632520826469

theorem tailTrace_3358051 : CollatzResearch.WordTrace tailWord_3358051 prefixEnd_3358051 383176494513632520826469 := by
  unfold tailWord_3358051
  simp only [CollatzResearch.WordTrace]
  refine ⟨122478181957362211296490007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81652121304908140864326671 122478181957362211296490007)
  ·
    refine ⟨183717272936043316944735011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122478181957362211296490007 183717272936043316944735011)
    ·
      refine ⟨275575909404064975417102517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183717272936043316944735011 275575909404064975417102517)
      ·
        refine ⟨25835241506631091445353361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 275575909404064975417102517 25835241506631091445353361)
        ·
          refine ⟨19376431129973318584015021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25835241506631091445353361 19376431129973318584015021)
          ·
            refine ⟨7266161673739994469005633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19376431129973318584015021 7266161673739994469005633)
            ·
              refine ⟨5449621255304995851754225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7266161673739994469005633 5449621255304995851754225)
              ·
                refine ⟨4087215941478746888815669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5449621255304995851754225 4087215941478746888815669)
                ·
                  refine ⟨383176494513632520826469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4087215941478746888815669 383176494513632520826469)
                  ·
                    rfl

theorem cell22_3358051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 5].length) (baseStart_3358051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3358051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3358051 prefixEnd_3358051 := by exact prefixLift 3358051
  have htrace : WordTrace (prefixWord ++ tailWord_3358051) baseStart_3358051 baseEnd_3358051 := by
    simpa [prefixWord, tailWord_3358051, baseEnd_3358051] using wordTrace_append hprefix tailTrace_3358051
  have hstable : (prefixWord ++ tailWord_3358051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358051).length < 2 ^ (prefixWord ++ tailWord_3358051).sum := by decide
  have hdescent : baseEnd_3358051 < baseStart_3358051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358055 : List Nat := [1, 1, 5, 1, 4, 1, 1, 4, 1, 3]
def baseStart_3358055 : Nat := 118140960795 + 3358055 * 2 ^ 59
def prefixEnd_3358055 : Nat := 4983230072969 + 3 ^ 40 * 3358055 * 2
def baseEnd_3358055 : Nat := 1149530852822642885379395

theorem tailTrace_3358055 : CollatzResearch.WordTrace tailWord_3358055 prefixEnd_3358055 1149530852822642885379395 := by
  unfold tailWord_3358055
  simp only [CollatzResearch.WordTrace]
  refine ⟨122478327849347719979635619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81652218566231813319757079 122478327849347719979635619)
  ·
    refine ⟨183717491774021579969453429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122478327849347719979635619 183717491774021579969453429)
    ·
      refine ⟨17223514853814523122136259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183717491774021579969453429 17223514853814523122136259)
      ·
        refine ⟨25835272280721784683204389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17223514853814523122136259 25835272280721784683204389)
        ·
          refine ⟨4844113552635334628100823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25835272280721784683204389 4844113552635334628100823)
          ·
            refine ⟨7266170328953001942151235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4844113552635334628100823 7266170328953001942151235)
            ·
              refine ⟨10899255493429502913226853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7266170328953001942151235 10899255493429502913226853)
              ·
                refine ⟨2043610405018031796230035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10899255493429502913226853 2043610405018031796230035)
                ·
                  refine ⟨3065415607527047694345053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043610405018031796230035 3065415607527047694345053)
                  ·
                    refine ⟨1149530852822642885379395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3065415607527047694345053 1149530852822642885379395)
                    ·
                      rfl

theorem cell22_3358055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_3358055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3358055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3358055 prefixEnd_3358055 := by exact prefixLift 3358055
  have htrace : WordTrace (prefixWord ++ tailWord_3358055) baseStart_3358055 baseEnd_3358055 := by
    simpa [prefixWord, tailWord_3358055, baseEnd_3358055] using wordTrace_append hprefix tailTrace_3358055
  have hstable : (prefixWord ++ tailWord_3358055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358055).length < 2 ^ (prefixWord ++ tailWord_3358055).sum := by decide
  have hdescent : baseEnd_3358055 < baseStart_3358055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358064 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 5, 4]
def baseStart_3358064 : Nat := 118140960795 + 3358064 * 2 ^ 59
def prefixEnd_3358064 : Nat := 4983230072969 + 3 ^ 40 * 3358064 * 2
def baseEnd_3358064 : Nat := 1149533933706569861904367

theorem tailTrace_3358064 : CollatzResearch.WordTrace tailWord_3358064 prefixEnd_3358064 1149533933706569861904367 := by
  unfold tailWord_3358064
  simp only [CollatzResearch.WordTrace]
  refine ⟨61239328053157557258356623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81652437404210076344475497 61239328053157557258356623)
  ·
    refine ⟨91858992079736335887534935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61239328053157557258356623 91858992079736335887534935)
    ·
      refine ⟨137788488119604503831302403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91858992079736335887534935 137788488119604503831302403)
      ·
        refine ⟨206682732179406755746953605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137788488119604503831302403 206682732179406755746953605)
        ·
          refine ⟨38753012283638766702553801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206682732179406755746953605 38753012283638766702553801)
          ·
            refine ⟨29064759212729075026915351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38753012283638766702553801 29064759212729075026915351)
            ·
              refine ⟨43597138819093612540373027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29064759212729075026915351 43597138819093612540373027)
              ·
                refine ⟨65395708228640418810559541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43597138819093612540373027 65395708228640418810559541)
                ·
                  refine ⟨6130847646435039263489957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65395708228640418810559541 6130847646435039263489957)
                  ·
                    refine ⟨1149533933706569861904367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6130847646435039263489957 1149533933706569861904367)
                    ·
                      rfl

theorem cell22_3358064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 5, 4].length) (baseStart_3358064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3358064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3358064 prefixEnd_3358064 := by exact prefixLift 3358064
  have htrace : WordTrace (prefixWord ++ tailWord_3358064) baseStart_3358064 baseEnd_3358064 := by
    simpa [prefixWord, tailWord_3358064, baseEnd_3358064] using wordTrace_append hprefix tailTrace_3358064
  have hstable : (prefixWord ++ tailWord_3358064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358064).length < 2 ^ (prefixWord ++ tailWord_3358064).sum := by decide
  have hdescent : baseEnd_3358064 < baseStart_3358064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358265 : List Nat := [1, 2, 1, 5, 1, 3, 2, 3, 4]
def baseStart_3358265 : Nat := 118140960795 + 3358265 * 2 ^ 59
def prefixEnd_3358265 : Nat := 4983230072969 + 3 ^ 40 * 3358265 * 2
def baseEnd_3358265 : Nat := 383200913371424112542917

theorem tailTrace_3358265 : CollatzResearch.WordTrace tailWord_3358265 prefixEnd_3358265 383200913371424112542917 := by
  unfold tailWord_3358265
  simp only [CollatzResearch.WordTrace]
  refine ⟨122485987178586925844780249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81657324785724617229853499 122485987178586925844780249)
  ·
    refine ⟨91864490383940194383585187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122485987178586925844780249 91864490383940194383585187)
    ·
      refine ⟨137796735575910291575377781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91864490383940194383585187 137796735575910291575377781)
      ·
        refine ⟨12918443960241589835191667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137796735575910291575377781 12918443960241589835191667)
        ·
          refine ⟨19377665940362384752787501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12918443960241589835191667 19377665940362384752787501)
          ·
            refine ⟨7266624727635894282295313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19377665940362384752787501 7266624727635894282295313)
            ·
              refine ⟨5449968545726920711721485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7266624727635894282295313 5449968545726920711721485)
              ·
                refine ⟨2043738204647595266895557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5449968545726920711721485 2043738204647595266895557)
                ·
                  refine ⟨383200913371424112542917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2043738204647595266895557 383200913371424112542917)
                  ·
                    rfl

theorem cell22_3358265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 4].length) (baseStart_3358265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3358265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3358265 prefixEnd_3358265 := by exact prefixLift 3358265
  have htrace : WordTrace (prefixWord ++ tailWord_3358265) baseStart_3358265 baseEnd_3358265 := by
    simpa [prefixWord, tailWord_3358265, baseEnd_3358265] using wordTrace_append hprefix tailTrace_3358265
  have hstable : (prefixWord ++ tailWord_3358265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358265).length < 2 ^ (prefixWord ++ tailWord_3358265).sum := by decide
  have hdescent : baseEnd_3358265 < baseStart_3358265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358400 : List Nat := [2, 1, 1, 2, 4, 1, 3, 4, 4]
def baseStart_3358400 : Nat := 118140960795 + 3358400 * 2 ^ 59
def prefixEnd_3358400 : Nat := 4983230072969 + 3 ^ 40 * 3358400 * 2
def baseEnd_3358400 : Nat := 383216317791058995167779

theorem tailTrace_3358400 : CollatzResearch.WordTrace tailWord_3358400 prefixEnd_3358400 383216317791058995167779 := by
  unfold tailWord_3358400
  simp only [CollatzResearch.WordTrace]
  refine ⟨61245455516548921950472327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81660607355398562600629769 61245455516548921950472327)
  ·
    refine ⟨91868183274823382925708491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61245455516548921950472327 91868183274823382925708491)
    ·
      refine ⟨137802274912235074388562737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91868183274823382925708491 137802274912235074388562737)
      ·
        refine ⟨103351706184176305791422053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137802274912235074388562737 103351706184176305791422053)
        ·
          refine ⟨19378444909533057335891635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103351706184176305791422053 19378444909533057335891635)
          ·
            refine ⟨29067667364299586003837453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19378444909533057335891635 29067667364299586003837453)
            ·
              refine ⟨10900375261612344751439045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29067667364299586003837453 10900375261612344751439045)
              ·
                refine ⟨2043820361552314640894821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10900375261612344751439045 2043820361552314640894821)
                ·
                  refine ⟨383216317791058995167779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2043820361552314640894821 383216317791058995167779)
                  ·
                    rfl

theorem cell22_3358400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 4].length) (baseStart_3358400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3358400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3358400 prefixEnd_3358400 := by exact prefixLift 3358400
  have htrace : WordTrace (prefixWord ++ tailWord_3358400) baseStart_3358400 baseEnd_3358400 := by
    simpa [prefixWord, tailWord_3358400, baseEnd_3358400] using wordTrace_append hprefix tailTrace_3358400
  have hstable : (prefixWord ++ tailWord_3358400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358400).length < 2 ^ (prefixWord ++ tailWord_3358400).sum := by decide
  have hdescent : baseEnd_3358400 < baseStart_3358400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358470 : List Nat := [6, 2, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3358470 : Nat := 118140960795 + 3358470 * 2 ^ 59
def prefixEnd_3358470 : Nat := 4983230072969 + 3 ^ 40 * 3358470 * 2
def baseEnd_3358470 : Nat := 1149672915803720136253123

theorem tailTrace_3358470 : CollatzResearch.WordTrace tailWord_3358470 prefixEnd_3358470 1149672915803720136253123 := by
  unfold tailWord_3358470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3827920754463882682999777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81662309428562830570661909 3827920754463882682999777)
  ·
    refine ⟨2870940565847912012249833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3827920754463882682999777 2870940565847912012249833)
    ·
      refine ⟨2153205424385934009187375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2870940565847912012249833 2153205424385934009187375)
      ·
        refine ⟨3229808136578901013781063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2153205424385934009187375 3229808136578901013781063)
        ·
          refine ⟨4844712204868351520671595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3229808136578901013781063 4844712204868351520671595)
          ·
            refine ⟨7267068307302527281007393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4844712204868351520671595 7267068307302527281007393)
            ·
              refine ⟨5450301230476895460755545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7267068307302527281007393 5450301230476895460755545)
              ·
                refine ⟨4087725922857671595566659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5450301230476895460755545 4087725922857671595566659)
                ·
                  refine ⟨6131588884286507393349989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4087725922857671595566659 6131588884286507393349989)
                  ·
                    refine ⟨1149672915803720136253123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6131588884286507393349989 1149672915803720136253123)
                    ·
                      rfl

theorem cell22_3358470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3358470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3358470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3358470 prefixEnd_3358470 := by exact prefixLift 3358470
  have htrace : WordTrace (prefixWord ++ tailWord_3358470) baseStart_3358470 baseEnd_3358470 := by
    simpa [prefixWord, tailWord_3358470, baseEnd_3358470] using wordTrace_append hprefix tailTrace_3358470
  have hstable : (prefixWord ++ tailWord_3358470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358470).length < 2 ^ (prefixWord ++ tailWord_3358470).sum := by decide
  have hdescent : baseEnd_3358470 < baseStart_3358470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358488 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 1, 7]
def baseStart_3358488 : Nat := 118140960795 + 3358488 * 2 ^ 59
def prefixEnd_3358488 : Nat := 4983230072969 + 3 ^ 40 * 3358488 * 2
def baseEnd_3358488 : Nat := 1149679077571574089303067

theorem tailTrace_3358488 : CollatzResearch.WordTrace tailWord_3358488 prefixEnd_3358488 1149679077571574089303067 := by
  unfold tailWord_3358488
  simp only [CollatzResearch.WordTrace]
  refine ⟨61247060328389517465074059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81662747104519356620098745 61247060328389517465074059)
  ·
    refine ⟨91870590492584276197611089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61247060328389517465074059 91870590492584276197611089)
    ·
      refine ⟨68902942869438207148208317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91870590492584276197611089 68902942869438207148208317)
      ·
        refine ⟨25838603576039327680578119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68902942869438207148208317 25838603576039327680578119)
        ·
          refine ⟨38757905364058991520867179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25838603576039327680578119 38757905364058991520867179)
          ·
            refine ⟨58136858046088487281300769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38757905364058991520867179 58136858046088487281300769)
            ·
              refine ⟨43602643534566365460975577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58136858046088487281300769 43602643534566365460975577)
              ·
                refine ⟨32701982650924774095731683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43602643534566365460975577 32701982650924774095731683)
                ·
                  refine ⟨49052973976387161143597525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32701982650924774095731683 49052973976387161143597525)
                  ·
                    refine ⟨1149679077571574089303067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49052973976387161143597525 1149679077571574089303067)
                    ·
                      rfl

theorem cell22_3358488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_3358488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3358488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3358488 prefixEnd_3358488 := by exact prefixLift 3358488
  have htrace : WordTrace (prefixWord ++ tailWord_3358488) baseStart_3358488 baseEnd_3358488 := by
    simpa [prefixWord, tailWord_3358488, baseEnd_3358488] using wordTrace_append hprefix tailTrace_3358488
  have hstable : (prefixWord ++ tailWord_3358488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358488).length < 2 ^ (prefixWord ++ tailWord_3358488).sum := by decide
  have hdescent : baseEnd_3358488 < baseStart_3358488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358563 : List Nat := [1, 1, 1, 5, 14]
def baseStart_3358563 : Nat := 118140960795 + 3358563 * 2 ^ 59
def prefixEnd_3358563 : Nat := 4983230072969 + 3 ^ 40 * 3358563 * 2
def baseEnd_3358563 : Nat := 4731295274091764994559

theorem tailTrace_3358563 : CollatzResearch.WordTrace tailWord_3358563 prefixEnd_3358563 4731295274091764994559 := by
  unfold tailWord_3358563
  simp only [CollatzResearch.WordTrace]
  refine ⟨122496856131507322739128343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81664570754338215159418895 122496856131507322739128343)
  ·
    refine ⟨183745284197260984108692515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122496856131507322739128343 183745284197260984108692515)
    ·
      refine ⟨275617926295891476163038773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183745284197260984108692515 275617926295891476163038773)
      ·
        refine ⟨25839180590239825890284885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 275617926295891476163038773 25839180590239825890284885)
        ·
          refine ⟨4731295274091764994559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 25839180590239825890284885 4731295274091764994559)
          ·
            rfl

theorem cell22_3358563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 14].length) (baseStart_3358563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3358563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3358563 prefixEnd_3358563 := by exact prefixLift 3358563
  have htrace : WordTrace (prefixWord ++ tailWord_3358563) baseStart_3358563 baseEnd_3358563 := by
    simpa [prefixWord, tailWord_3358563, baseEnd_3358563] using wordTrace_append hprefix tailTrace_3358563
  have hstable : (prefixWord ++ tailWord_3358563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358563).length < 2 ^ (prefixWord ++ tailWord_3358563).sum := by decide
  have hdescent : baseEnd_3358563 < baseStart_3358563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358599 : List Nat := [1, 1, 4, 2, 4, 2, 1, 1, 2, 4]
def baseStart_3358599 : Nat := 118140960795 + 3358599 * 2 ^ 59
def prefixEnd_3358599 : Nat := 4983230072969 + 3 ^ 40 * 3358599 * 2
def baseEnd_3358599 : Nat := 1149717075140006799777727

theorem tailTrace_3358599 : CollatzResearch.WordTrace tailWord_3358599 prefixEnd_3358599 1149717075140006799777727 := by
  unfold tailWord_3358599
  simp only [CollatzResearch.WordTrace]
  refine ⟨122498169159376900887438851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81665446106251267258292567 122498169159376900887438851)
  ·
    refine ⟨183747253739065351331158277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122498169159376900887438851 183747253739065351331158277)
    ·
      refine ⟨34452610076074753374592177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183747253739065351331158277 34452610076074753374592177)
      ·
        refine ⟨25839457557056065030944133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34452610076074753374592177 25839457557056065030944133)
        ·
          refine ⟨4844898291948012193302025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25839457557056065030944133 4844898291948012193302025)
          ·
            refine ⟨3633673718961009144976519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4844898291948012193302025 3633673718961009144976519)
            ·
              refine ⟨5450510578441513717464779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3633673718961009144976519 5450510578441513717464779)
              ·
                refine ⟨8175765867662270576197169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5450510578441513717464779 8175765867662270576197169)
                ·
                  refine ⟨6131824400746702932147877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8175765867662270576197169 6131824400746702932147877)
                  ·
                    refine ⟨1149717075140006799777727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6131824400746702932147877 1149717075140006799777727)
                    ·
                      rfl

theorem cell22_3358599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_3358599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3358599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3358599 prefixEnd_3358599 := by exact prefixLift 3358599
  have htrace : WordTrace (prefixWord ++ tailWord_3358599) baseStart_3358599 baseEnd_3358599 := by
    simpa [prefixWord, tailWord_3358599, baseEnd_3358599] using wordTrace_append hprefix tailTrace_3358599
  have hstable : (prefixWord ++ tailWord_3358599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358599).length < 2 ^ (prefixWord ++ tailWord_3358599).sum := by decide
  have hdescent : baseEnd_3358599 < baseStart_3358599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358672 : List Nat := [2, 1, 1, 1, 1, 2, 6, 3, 1, 4]
def baseStart_3358672 : Nat := 118140960795 + 3358672 * 2 ^ 59
def prefixEnd_3358672 : Nat := 4983230072969 + 3 ^ 40 * 3358672 * 2
def baseEnd_3358672 : Nat := 1149742064531858942702503

theorem tailTrace_3358672 : CollatzResearch.WordTrace tailWord_3358672 prefixEnd_3358672 1149742064531858942702503 := by
  unfold tailWord_3358672
  simp only [CollatzResearch.WordTrace]
  refine ⟨61250415844056217177423135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81667221125408289569897513 61250415844056217177423135)
  ·
    refine ⟨91875623766084325766134703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61250415844056217177423135 91875623766084325766134703)
    ·
      refine ⟨137813435649126488649202055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91875623766084325766134703 137813435649126488649202055)
      ·
        refine ⟨206720153473689732973803083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137813435649126488649202055 206720153473689732973803083)
        ·
          refine ⟨310080230210534599460704625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206720153473689732973803083 310080230210534599460704625)
          ·
            refine ⟨232560172657900949595528469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310080230210534599460704625 232560172657900949595528469)
            ·
              refine ⟨10901258093339107012290397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 232560172657900949595528469 10901258093339107012290397)
              ·
                refine ⟨4087971785002165129608899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10901258093339107012290397 4087971785002165129608899)
                ·
                  refine ⟨6131957677503247694413349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4087971785002165129608899 6131957677503247694413349)
                  ·
                    refine ⟨1149742064531858942702503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6131957677503247694413349 1149742064531858942702503)
                    ·
                      rfl

theorem cell22_3358672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 1, 4].length) (baseStart_3358672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3358672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3358672 prefixEnd_3358672 := by exact prefixLift 3358672
  have htrace : WordTrace (prefixWord ++ tailWord_3358672) baseStart_3358672 baseEnd_3358672 := by
    simpa [prefixWord, tailWord_3358672, baseEnd_3358672] using wordTrace_append hprefix tailTrace_3358672
  have hstable : (prefixWord ++ tailWord_3358672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358672).length < 2 ^ (prefixWord ++ tailWord_3358672).sum := by decide
  have hdescent : baseEnd_3358672 < baseStart_3358672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358687 : List Nat := [1, 1, 2, 3, 4, 1, 3, 1, 6]
def baseStart_3358687 : Nat := 118140960795 + 3358687 * 2 ^ 59
def prefixEnd_3358687 : Nat := 4983230072969 + 3 ^ 40 * 3358687 * 2
def baseEnd_3358687 : Nat := 383249066446134634525819

theorem tailTrace_3358687 : CollatzResearch.WordTrace tailWord_3358687 prefixEnd_3358687 383249066446134634525819 := by
  unfold tailWord_3358687
  simp only [CollatzResearch.WordTrace]
  refine ⟨122501378783058091916642315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81667585855372061277761543 122501378783058091916642315)
  ·
    refine ⟨183752068174587137874963473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122501378783058091916642315 183752068174587137874963473)
    ·
      refine ⟨137814051130940353406222605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183752068174587137874963473 137814051130940353406222605)
      ·
        refine ⟨51680269174102632527333477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137814051130940353406222605 51680269174102632527333477)
        ·
          refine ⟨9690050470144243598875027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51680269174102632527333477 9690050470144243598875027)
          ·
            refine ⟨14535075705216365398312541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9690050470144243598875027 14535075705216365398312541)
            ·
              refine ⟨5450653389456137024367203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14535075705216365398312541 5450653389456137024367203)
              ·
                refine ⟨8175980084184205536550805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5450653389456137024367203 8175980084184205536550805)
                ·
                  refine ⟨383249066446134634525819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8175980084184205536550805 383249066446134634525819)
                  ·
                    rfl

theorem cell22_3358687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 6].length) (baseStart_3358687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3358687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3358687 prefixEnd_3358687 := by exact prefixLift 3358687
  have htrace : WordTrace (prefixWord ++ tailWord_3358687) baseStart_3358687 baseEnd_3358687 := by
    simpa [prefixWord, tailWord_3358687, baseEnd_3358687] using wordTrace_append hprefix tailTrace_3358687
  have hstable : (prefixWord ++ tailWord_3358687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358687).length < 2 ^ (prefixWord ++ tailWord_3358687).sum := by decide
  have hdescent : baseEnd_3358687 < baseStart_3358687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358700 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 3, 6]
def baseStart_3358700 : Nat := 118140960795 + 3358700 * 2 ^ 59
def prefixEnd_3358700 : Nat := 4983230072969 + 3 ^ 40 * 3358700 * 2
def baseEnd_3358700 : Nat := 1149751649504076203002417

theorem tailTrace_3358700 : CollatzResearch.WordTrace tailWord_3358700 prefixEnd_3358700 1149751649504076203002417 := by
  unfold tailWord_3358700
  simp only [CollatzResearch.WordTrace]
  refine ⟨61250926466005497568432777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81667901954673996757910369 61250926466005497568432777)
  ·
    refine ⟨45938194849504123176324583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61250926466005497568432777 45938194849504123176324583)
    ·
      refine ⟨68907292274256184764486875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45938194849504123176324583 68907292274256184764486875)
      ·
        refine ⟨103360938411384277146730313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68907292274256184764486875 103360938411384277146730313)
        ·
          refine ⟨77520703808538207860047735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103360938411384277146730313 77520703808538207860047735)
          ·
            refine ⟨116281055712807311790071603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77520703808538207860047735 116281055712807311790071603)
            ·
              refine ⟨174421583569210967685107405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116281055712807311790071603 174421583569210967685107405)
              ·
                refine ⟨65408093838454112881915277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174421583569210967685107405 65408093838454112881915277)
                ·
                  refine ⟨24528035189420292330718229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65408093838454112881915277 24528035189420292330718229)
                  ·
                    refine ⟨1149751649504076203002417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24528035189420292330718229 1149751649504076203002417)
                    ·
                      rfl

theorem cell22_3358700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_3358700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3358700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3358700 prefixEnd_3358700 := by exact prefixLift 3358700
  have htrace : WordTrace (prefixWord ++ tailWord_3358700) baseStart_3358700 baseEnd_3358700 := by
    simpa [prefixWord, tailWord_3358700, baseEnd_3358700] using wordTrace_append hprefix tailTrace_3358700
  have hstable : (prefixWord ++ tailWord_3358700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358700).length < 2 ^ (prefixWord ++ tailWord_3358700).sum := by decide
  have hdescent : baseEnd_3358700 < baseStart_3358700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358715 : List Nat := [1, 1, 1, 1, 1, 3, 6, 8]
def baseStart_3358715 : Nat := 118140960795 + 3358715 * 2 ^ 59
def prefixEnd_3358715 : Nat := 4983230072969 + 3 ^ 40 * 3358715 * 2
def baseEnd_3358715 : Nat := 127750753812291240430819

theorem tailTrace_3358715 : CollatzResearch.WordTrace tailWord_3358715 prefixEnd_3358715 127750753812291240430819 := by
  unfold tailWord_3358715
  simp only [CollatzResearch.WordTrace]
  refine ⟨122502400026956652698661599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81668266684637768465774399 122502400026956652698661599)
  ·
    refine ⟨183753600040434979047992399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122502400026956652698661599 183753600040434979047992399)
    ·
      refine ⟨275630400060652468571988599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183753600040434979047992399 275630400060652468571988599)
      ·
        refine ⟨413445600090978702857982899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275630400060652468571988599 413445600090978702857982899)
        ·
          refine ⟨620168400136468054286974349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413445600090978702857982899 620168400136468054286974349)
          ·
            refine ⟨232563150051175520357615381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 620168400136468054286974349 232563150051175520357615381)
            ·
              refine ⟨10901397658648852516763221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 232563150051175520357615381 10901397658648852516763221)
              ·
                refine ⟨127750753812291240430819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10901397658648852516763221 127750753812291240430819)
                ·
                  rfl

theorem cell22_3358715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 8].length) (baseStart_3358715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3358715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3358715 prefixEnd_3358715 := by exact prefixLift 3358715
  have htrace : WordTrace (prefixWord ++ tailWord_3358715) baseStart_3358715 baseEnd_3358715 := by
    simpa [prefixWord, tailWord_3358715, baseEnd_3358715] using wordTrace_append hprefix tailTrace_3358715
  have hstable : (prefixWord ++ tailWord_3358715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358715).length < 2 ^ (prefixWord ++ tailWord_3358715).sum := by decide
  have hdescent : baseEnd_3358715 < baseStart_3358715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358717 : List Nat := [1, 4, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_3358717 : Nat := 118140960795 + 3358717 * 2 ^ 59
def prefixEnd_3358717 : Nat := 4983230072969 + 3 ^ 40 * 3358717 * 2
def baseEnd_3358717 : Nat := 1149757468951493825327365

theorem tailTrace_3358717 : CollatzResearch.WordTrace tailWord_3358717 prefixEnd_3358717 1149757468951493825327365 := by
  unfold tailWord_3358717
  simp only [CollatzResearch.WordTrace]
  refine ⟨122502472972949407040234405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81668315315299604693489603 122502472972949407040234405)
  ·
    refine ⟨22969213682428013820043951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122502472972949407040234405 22969213682428013820043951)
    ·
      refine ⟨34453820523642020730065927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22969213682428013820043951 34453820523642020730065927)
      ·
        refine ⟨51680730785463031095098891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34453820523642020730065927 51680730785463031095098891)
        ·
          refine ⟨77521096178194546642648337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51680730785463031095098891 77521096178194546642648337)
          ·
            refine ⟨58140822133645909981986253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77521096178194546642648337 58140822133645909981986253)
            ·
              refine ⟨21802808300117216243244845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58140822133645909981986253 21802808300117216243244845)
              ·
                refine ⟨8176053112543956091216817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21802808300117216243244845 8176053112543956091216817)
                ·
                  refine ⟨6132039834407967068412613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8176053112543956091216817 6132039834407967068412613)
                  ·
                    refine ⟨1149757468951493825327365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6132039834407967068412613 1149757468951493825327365)
                    ·
                      rfl

theorem cell22_3358717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_3358717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3358717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3358717 prefixEnd_3358717 := by exact prefixLift 3358717
  have htrace : WordTrace (prefixWord ++ tailWord_3358717) baseStart_3358717 baseEnd_3358717 := by
    simpa [prefixWord, tailWord_3358717, baseEnd_3358717] using wordTrace_append hprefix tailTrace_3358717
  have hstable : (prefixWord ++ tailWord_3358717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358717).length < 2 ^ (prefixWord ++ tailWord_3358717).sum := by decide
  have hdescent : baseEnd_3358717 < baseStart_3358717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358749 : List Nat := [1, 4, 2, 2, 2, 3, 1, 7]
def baseStart_3358749 : Nat := 118140960795 + 3358749 * 2 ^ 59
def prefixEnd_3358749 : Nat := 4983230072969 + 3 ^ 40 * 3358749 * 2
def baseEnd_3358749 : Nat := 127752047022828489836363

theorem tailTrace_3358749 : CollatzResearch.WordTrace tailWord_3358749 prefixEnd_3358749 127752047022828489836363 := by
  unfold tailWord_3358749
  simp only [CollatzResearch.WordTrace]
  refine ⟨122503640108833476505399301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81669093405888984336932867 122503640108833476505399301)
  ·
    refine ⟨22969432520406276844762369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122503640108833476505399301 22969432520406276844762369)
    ·
      refine ⟨17227074390304707633571777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22969432520406276844762369 17227074390304707633571777)
      ·
        refine ⟨12920305792728530725178833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17227074390304707633571777 12920305792728530725178833)
        ·
          refine ⟨9690229344546398043884125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12920305792728530725178833 9690229344546398043884125)
          ·
            refine ⟨3633836004204899266456547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9690229344546398043884125 3633836004204899266456547)
            ·
              refine ⟨5450754006307348899684821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3633836004204899266456547 5450754006307348899684821)
              ·
                refine ⟨127752047022828489836363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5450754006307348899684821 127752047022828489836363)
                ·
                  rfl

theorem cell22_3358749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 7].length) (baseStart_3358749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3358749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3358749 prefixEnd_3358749 := by exact prefixLift 3358749
  have htrace : WordTrace (prefixWord ++ tailWord_3358749) baseStart_3358749 baseEnd_3358749 := by
    simpa [prefixWord, tailWord_3358749, baseEnd_3358749] using wordTrace_append hprefix tailTrace_3358749
  have hstable : (prefixWord ++ tailWord_3358749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358749).length < 2 ^ (prefixWord ++ tailWord_3358749).sum := by decide
  have hdescent : baseEnd_3358749 < baseStart_3358749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358807 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 5, 4]
def baseStart_3358807 : Nat := 118140960795 + 3358807 * 2 ^ 59
def prefixEnd_3358807 : Nat := 4983230072969 + 3 ^ 40 * 3358807 * 2
def baseEnd_3358807 : Nat := 1149788277790763590577089

theorem tailTrace_3358807 : CollatzResearch.WordTrace tailWord_3358807 prefixEnd_3358807 1149788277790763590577089 := by
  unfold tailWord_3358807
  simp only [CollatzResearch.WordTrace]
  refine ⟨122505755542623352411010675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81670503695082234940673783 122505755542623352411010675)
  ·
    refine ⟨183758633313935028616516013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122505755542623352411010675 183758633313935028616516013)
    ·
      refine ⟨68909487492725635731193505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183758633313935028616516013 68909487492725635731193505)
      ·
        refine ⟨51682115619544226798395129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68909487492725635731193505 51682115619544226798395129)
        ·
          refine ⟨38761586714658170098796347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51682115619544226798395129 38761586714658170098796347)
          ·
            refine ⟨58142380071987255148194521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38761586714658170098796347 58142380071987255148194521)
            ·
              refine ⟨43606785053990441361145891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58142380071987255148194521 43606785053990441361145891)
              ·
                refine ⟨65410177580985662041718837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43606785053990441361145891 65410177580985662041718837)
                ·
                  refine ⟨6132204148217405816411141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65410177580985662041718837 6132204148217405816411141)
                  ·
                    refine ⟨1149788277790763590577089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6132204148217405816411141 1149788277790763590577089)
                    ·
                      rfl

theorem cell22_3358807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_3358807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3358807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3358807 prefixEnd_3358807 := by exact prefixLift 3358807
  have htrace : WordTrace (prefixWord ++ tailWord_3358807) baseStart_3358807 baseEnd_3358807 := by
    simpa [prefixWord, tailWord_3358807, baseEnd_3358807] using wordTrace_append hprefix tailTrace_3358807
  have hstable : (prefixWord ++ tailWord_3358807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358807).length < 2 ^ (prefixWord ++ tailWord_3358807).sum := by decide
  have hdescent : baseEnd_3358807 < baseStart_3358807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358856 : List Nat := [2, 1, 3, 4, 1, 3, 1, 1, 6]
def baseStart_3358856 : Nat := 118140960795 + 3358856 * 2 ^ 59
def prefixEnd_3358856 : Nat := 4983230072969 + 3 ^ 40 * 3358856 * 2
def baseEnd_3358856 : Nat := 383268350497381265367313

theorem tailTrace_3358856 : CollatzResearch.WordTrace tailWord_3358856 prefixEnd_3358856 383268350497381265367313 := by
  unfold tailWord_3358856
  simp only [CollatzResearch.WordTrace]
  refine ⟨61253771359722916889772211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81671695146297222519696281 61253771359722916889772211)
  ·
    refine ⟨91880657039584375334658317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61253771359722916889772211 91880657039584375334658317)
    ·
      refine ⟨34455246389844140750496869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91880657039584375334658317 34455246389844140750496869)
      ·
        refine ⟨6460358698095776390718163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34455246389844140750496869 6460358698095776390718163)
        ·
          refine ⟨9690538047143664586077245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6460358698095776390718163 9690538047143664586077245)
          ·
            refine ⟨3633951767678874219778967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9690538047143664586077245 3633951767678874219778967)
            ·
              refine ⟨5450927651518311329668451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3633951767678874219778967 5450927651518311329668451)
              ·
                refine ⟨8176391477277466994502677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5450927651518311329668451 8176391477277466994502677)
                ·
                  refine ⟨383268350497381265367313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8176391477277466994502677 383268350497381265367313)
                  ·
                    rfl

theorem cell22_3358856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 6].length) (baseStart_3358856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3358856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3358856 prefixEnd_3358856 := by exact prefixLift 3358856
  have htrace : WordTrace (prefixWord ++ tailWord_3358856) baseStart_3358856 baseEnd_3358856 := by
    simpa [prefixWord, tailWord_3358856, baseEnd_3358856] using wordTrace_append hprefix tailTrace_3358856
  have hstable : (prefixWord ++ tailWord_3358856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358856).length < 2 ^ (prefixWord ++ tailWord_3358856).sum := by decide
  have hdescent : baseEnd_3358856 < baseStart_3358856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358901 : List Nat := [1, 3, 3, 4, 2, 9]
def baseStart_3358901 : Nat := 118140960795 + 3358901 * 2 ^ 59
def prefixEnd_3358901 : Nat := 4983230072969 + 3 ^ 40 * 3358901 * 2
def baseEnd_3358901 : Nat := 14195314270515786157121

theorem tailTrace_3358901 : CollatzResearch.WordTrace tailWord_3358901 prefixEnd_3358901 14195314270515786157121 := by
  unfold tailWord_3358901
  simp only [CollatzResearch.WordTrace]
  refine ⟨122509184004282806464932557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81672789336188537643288371 122509184004282806464932557)
  ·
    refine ⟨45940944001606052424349709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122509184004282806464932557 45940944001606052424349709)
    ·
      refine ⟨17227854000602269659131141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45940944001606052424349709 17227854000602269659131141)
      ·
        refine ⟨3230222625112925561087089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17227854000602269659131141 3230222625112925561087089)
        ·
          refine ⟨2422666968834694170815317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3230222625112925561087089 2422666968834694170815317)
          ·
            refine ⟨14195314270515786157121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2422666968834694170815317 14195314270515786157121)
            ·
              rfl

theorem cell22_3358901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 9].length) (baseStart_3358901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3358901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3358901 prefixEnd_3358901 := by exact prefixLift 3358901
  have htrace : WordTrace (prefixWord ++ tailWord_3358901) baseStart_3358901 baseEnd_3358901 := by
    simpa [prefixWord, tailWord_3358901, baseEnd_3358901] using wordTrace_append hprefix tailTrace_3358901
  have hstable : (prefixWord ++ tailWord_3358901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358901).length < 2 ^ (prefixWord ++ tailWord_3358901).sum := by decide
  have hdescent : baseEnd_3358901 < baseStart_3358901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358929 : List Nat := [1, 2, 2, 1, 2, 2, 4, 3, 5]
def baseStart_3358929 : Nat := 118140960795 + 3358929 * 2 ^ 59
def prefixEnd_3358929 : Nat := 4983230072969 + 3 ^ 40 * 3358929 * 2
def baseEnd_3358929 : Nat := 383276680294665313008905

theorem tailTrace_3358929 : CollatzResearch.WordTrace tailWord_3358929 prefixEnd_3358929 383276680294665313008905 := by
  unfold tailWord_3358929
  simp only [CollatzResearch.WordTrace]
  refine ⟨122510205248181367246951841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81673470165454244831301227 122510205248181367246951841)
  ·
    refine ⟨91882653936136025435213881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122510205248181367246951841 91882653936136025435213881)
    ·
      refine ⟨68911990452102019076410411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91882653936136025435213881 68911990452102019076410411)
      ·
        refine ⟨103367985678153028614615617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68911990452102019076410411 103367985678153028614615617)
        ·
          refine ⟨77525989258614771460961713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103367985678153028614615617 77525989258614771460961713)
          ·
            refine ⟨58144491943961078595721285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77525989258614771460961713 58144491943961078595721285)
            ·
              refine ⟨10902092239492702236697741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58144491943961078595721285 10902092239492702236697741)
              ·
                refine ⟨4088284589809763338761653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10902092239492702236697741 4088284589809763338761653)
                ·
                  refine ⟨383276680294665313008905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4088284589809763338761653 383276680294665313008905)
                  ·
                    rfl

theorem cell22_3358929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 5].length) (baseStart_3358929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3358929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3358929 prefixEnd_3358929 := by exact prefixLift 3358929
  have htrace : WordTrace (prefixWord ++ tailWord_3358929) baseStart_3358929 baseEnd_3358929 := by
    simpa [prefixWord, tailWord_3358929, baseEnd_3358929] using wordTrace_append hprefix tailTrace_3358929
  have hstable : (prefixWord ++ tailWord_3358929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358929).length < 2 ^ (prefixWord ++ tailWord_3358929).sum := by decide
  have hdescent : baseEnd_3358929 < baseStart_3358929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358933 : List Nat := [1, 3, 2, 4, 2, 1, 1, 2, 3, 3]
def baseStart_3358933 : Nat := 118140960795 + 3358933 * 2 ^ 59
def prefixEnd_3358933 : Nat := 4983230072969 + 3 ^ 40 * 3358933 * 2
def baseEnd_3358933 : Nat := 1149831410165741261926703

theorem tailTrace_3358933 : CollatzResearch.WordTrace tailWord_3358933 prefixEnd_3358933 1149831410165741261926703 := by
  unfold tailWord_3358933
  simp only [CollatzResearch.WordTrace]
  refine ⟨122510351140166875930097453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81673567426777917286731635 122510351140166875930097453)
  ·
    refine ⟨45941381677562578473786545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122510351140166875930097453 45941381677562578473786545)
    ·
      refine ⟨34456036258171933855339909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45941381677562578473786545 34456036258171933855339909)
      ·
        refine ⟨6460506798407237597876233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34456036258171933855339909 6460506798407237597876233)
        ·
          refine ⟨4845380098805428198407175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6460506798407237597876233 4845380098805428198407175)
          ·
            refine ⟨7268070148208142297610763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4845380098805428198407175 7268070148208142297610763)
            ·
              refine ⟨10902105222312213446416145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7268070148208142297610763 10902105222312213446416145)
              ·
                refine ⟨8176578916734160084812109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10902105222312213446416145 8176578916734160084812109)
                ·
                  refine ⟨3066217093775310031804541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8176578916734160084812109 3066217093775310031804541)
                  ·
                    refine ⟨1149831410165741261926703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3066217093775310031804541 1149831410165741261926703)
                    ·
                      rfl

theorem cell22_3358933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_3358933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3358933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3358933 prefixEnd_3358933 := by exact prefixLift 3358933
  have htrace : WordTrace (prefixWord ++ tailWord_3358933) baseStart_3358933 baseEnd_3358933 := by
    simpa [prefixWord, tailWord_3358933, baseEnd_3358933] using wordTrace_append hprefix tailTrace_3358933
  have hstable : (prefixWord ++ tailWord_3358933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358933).length < 2 ^ (prefixWord ++ tailWord_3358933).sum := by decide
  have hdescent : baseEnd_3358933 < baseStart_3358933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359008 : List Nat := [2, 1, 1, 5, 2, 1, 3, 3, 4]
def baseStart_3359008 : Nat := 118140960795 + 3359008 * 2 ^ 59
def prefixEnd_3359008 : Nat := 4983230072969 + 3 ^ 40 * 3359008 * 2
def baseEnd_3359008 : Nat := 383285694732822022100491

theorem tailTrace_3359008 : CollatzResearch.WordTrace tailWord_3359008 prefixEnd_3359008 383285694732822022100491 := by
  unfold tailWord_3359008
  simp only [CollatzResearch.WordTrace]
  refine ⟨61256543307447581869538839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81675391076596775826051785 61256543307447581869538839)
  ·
    refine ⟨91884814961171372804308259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61256543307447581869538839 91884814961171372804308259)
    ·
      refine ⟨137827222441757059206462389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91884814961171372804308259 137827222441757059206462389)
      ·
        refine ⟨12921302103914724300605849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137827222441757059206462389 12921302103914724300605849)
        ·
          refine ⟨9690976577936043225454387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12921302103914724300605849 9690976577936043225454387)
          ·
            refine ⟨14536464866904064838181581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9690976577936043225454387 14536464866904064838181581)
            ·
              refine ⟨5451174325089024314318093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14536464866904064838181581 5451174325089024314318093)
              ·
                refine ⟨2044190371908384117869285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5451174325089024314318093 2044190371908384117869285)
                ·
                  refine ⟨383285694732822022100491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2044190371908384117869285 383285694732822022100491)
                  ·
                    rfl

theorem cell22_3359008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 4].length) (baseStart_3359008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359008 prefixEnd_3359008 := by exact prefixLift 3359008
  have htrace : WordTrace (prefixWord ++ tailWord_3359008) baseStart_3359008 baseEnd_3359008 := by
    simpa [prefixWord, tailWord_3359008, baseEnd_3359008] using wordTrace_append hprefix tailTrace_3359008
  have hstable : (prefixWord ++ tailWord_3359008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359008).length < 2 ^ (prefixWord ++ tailWord_3359008).sum := by decide
  have hdescent : baseEnd_3359008 < baseStart_3359008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359025 : List Nat := [1, 2, 2, 3, 4, 1, 3, 2, 4]
def baseStart_3359025 : Nat := 118140960795 + 3359025 * 2 ^ 59
def prefixEnd_3359025 : Nat := 4983230072969 + 3 ^ 40 * 3359025 * 2
def baseEnd_3359025 : Nat := 383287634548627896208807

theorem tailTrace_3359025 : CollatzResearch.WordTrace tailWord_3359025 prefixEnd_3359025 383287634548627896208807 := by
  unfold tailWord_3359025
  simp only [CollatzResearch.WordTrace]
  refine ⟨122513706655833575642446529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81675804437222383761631019 122513706655833575642446529)
  ·
    refine ⟨91885279991875181731834897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122513706655833575642446529 91885279991875181731834897)
    ·
      refine ⟨68913959993906386298876173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91885279991875181731834897 68913959993906386298876173)
      ·
        refine ⟨25842734997714894862078565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68913959993906386298876173 25842734997714894862078565)
        ·
          refine ⟨4845512812071542786639731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25842734997714894862078565 4845512812071542786639731)
          ·
            refine ⟨7268269218107314179959597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4845512812071542786639731 7268269218107314179959597)
            ·
              refine ⟨2725600956790242817484849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7268269218107314179959597 2725600956790242817484849)
              ·
                refine ⟨2044200717592682113113637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2725600956790242817484849 2044200717592682113113637)
                ·
                  refine ⟨383287634548627896208807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2044200717592682113113637 383287634548627896208807)
                  ·
                    rfl

theorem cell22_3359025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 4].length) (baseStart_3359025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359025 prefixEnd_3359025 := by exact prefixLift 3359025
  have htrace : WordTrace (prefixWord ++ tailWord_3359025) baseStart_3359025 baseEnd_3359025 := by
    simpa [prefixWord, tailWord_3359025, baseEnd_3359025] using wordTrace_append hprefix tailTrace_3359025
  have hstable : (prefixWord ++ tailWord_3359025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359025).length < 2 ^ (prefixWord ++ tailWord_3359025).sum := by decide
  have hdescent : baseEnd_3359025 < baseStart_3359025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359064 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 7]
def baseStart_3359064 : Nat := 118140960795 + 3359064 * 2 ^ 59
def prefixEnd_3359064 : Nat := 4983230072969 + 3 ^ 40 * 3359064 * 2
def baseEnd_3359064 : Nat := 383292084714300195633767

theorem tailTrace_3359064 : CollatzResearch.WordTrace tailWord_3359064 prefixEnd_3359064 383292084714300195633767 := by
  unfold tailWord_3359064
  simp only [CollatzResearch.WordTrace]
  refine ⟨61257564551346142651558123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81676752735128190202077497 61257564551346142651558123)
  ·
    refine ⟨91886346827019213977337185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61257564551346142651558123 91886346827019213977337185)
    ·
      refine ⟨68914760120264410483002889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91886346827019213977337185 68914760120264410483002889)
      ·
        refine ⟨51686070090198307862252167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68914760120264410483002889 51686070090198307862252167)
        ·
          refine ⟨77529105135297461793378251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51686070090198307862252167 77529105135297461793378251)
          ·
            refine ⟨116293657702946192690067377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77529105135297461793378251 116293657702946192690067377)
            ·
              refine ⟨87220243277209644517550533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116293657702946192690067377 87220243277209644517550533)
              ·
                refine ⟨16353795614476808347040725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87220243277209644517550533 16353795614476808347040725)
                ·
                  refine ⟨383292084714300195633767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16353795614476808347040725 383292084714300195633767)
                  ·
                    rfl

theorem cell22_3359064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 7].length) (baseStart_3359064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359064 prefixEnd_3359064 := by exact prefixLift 3359064
  have htrace : WordTrace (prefixWord ++ tailWord_3359064) baseStart_3359064 baseEnd_3359064 := by
    simpa [prefixWord, tailWord_3359064, baseEnd_3359064] using wordTrace_append hprefix tailTrace_3359064
  have hstable : (prefixWord ++ tailWord_3359064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359064).length < 2 ^ (prefixWord ++ tailWord_3359064).sum := by decide
  have hdescent : baseEnd_3359064 < baseStart_3359064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359070 : List Nat := [4, 4, 2, 1, 11]
def baseStart_3359070 : Nat := 118140960795 + 3359070 * 2 ^ 59
def prefixEnd_3359070 : Nat := 4983230072969 + 3 ^ 40 * 3359070 * 2
def baseEnd_3359070 : Nat := 4732009498212010581281

theorem tailTrace_3359070 : CollatzResearch.WordTrace tailWord_3359070 prefixEnd_3359070 4732009498212010581281 := by
  unfold tailWord_3359070
  simp only [CollatzResearch.WordTrace]
  refine ⟨15314418492583818540979333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81676898627113698885223109 15314418492583818540979333)
  ·
    refine ⟨2871453467359465976433625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15314418492583818540979333 2871453467359465976433625)
    ·
      refine ⟨2153590100519599482325219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2871453467359465976433625 2153590100519599482325219)
      ·
        refine ⟨3230385150779399223487829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2153590100519599482325219 3230385150779399223487829)
        ·
          refine ⟨4732009498212010581281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3230385150779399223487829 4732009498212010581281)
          ·
            rfl

theorem cell22_3359070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 11].length) (baseStart_3359070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359070 prefixEnd_3359070 := by exact prefixLift 3359070
  have htrace : WordTrace (prefixWord ++ tailWord_3359070) baseStart_3359070 baseEnd_3359070 := by
    simpa [prefixWord, tailWord_3359070, baseEnd_3359070] using wordTrace_append hprefix tailTrace_3359070
  have hstable : (prefixWord ++ tailWord_3359070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359070).length < 2 ^ (prefixWord ++ tailWord_3359070).sum := by decide
  have hdescent : baseEnd_3359070 < baseStart_3359070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359081 : List Nat := [1, 2, 1, 1, 1, 3, 6, 2, 5]
def baseStart_3359081 : Nat := 118140960795 + 3359081 * 2 ^ 59
def prefixEnd_3359081 : Nat := 4983230072969 + 3 ^ 40 * 3359081 * 2
def baseEnd_3359081 : Nat := 383294024530106069742083

theorem tailTrace_3359081 : CollatzResearch.WordTrace tailWord_3359081 prefixEnd_3359081 383294024530106069742083 := by
  unfold tailWord_3359081
  simp only [CollatzResearch.WordTrace]
  refine ⟨122515749143630697206485097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81677166095753798137656731 122515749143630697206485097)
  ·
    refine ⟨91886811857723022904863823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122515749143630697206485097 91886811857723022904863823)
    ·
      refine ⟨137830217786584534357295735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91886811857723022904863823 137830217786584534357295735)
      ·
        refine ⟨206745326679876801535943603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137830217786584534357295735 206745326679876801535943603)
        ·
          refine ⟨310117990019815202303915405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206745326679876801535943603 310117990019815202303915405)
          ·
            refine ⟨116294246257430700863968277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 310117990019815202303915405 116294246257430700863968277)
            ·
              refine ⟨5451292793317064102998513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116294246257430700863968277 5451292793317064102998513)
              ·
                refine ⟨4088469594987798077248885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5451292793317064102998513 4088469594987798077248885)
                ·
                  refine ⟨383294024530106069742083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4088469594987798077248885 383294024530106069742083)
                  ·
                    rfl

theorem cell22_3359081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 5].length) (baseStart_3359081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359081 prefixEnd_3359081 := by exact prefixLift 3359081
  have htrace : WordTrace (prefixWord ++ tailWord_3359081) baseStart_3359081 baseEnd_3359081 := by
    simpa [prefixWord, tailWord_3359081, baseEnd_3359081] using wordTrace_append hprefix tailTrace_3359081
  have hstable : (prefixWord ++ tailWord_3359081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359081).length < 2 ^ (prefixWord ++ tailWord_3359081).sum := by decide
  have hdescent : baseEnd_3359081 < baseStart_3359081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359085 : List Nat := [1, 5, 1, 1, 1, 2, 3, 4, 1, 3]
def baseStart_3359085 : Nat := 118140960795 + 3359085 * 2 ^ 59
def prefixEnd_3359085 : Nat := 4983230072969 + 3 ^ 40 * 3359085 * 2
def baseEnd_3359085 : Nat := 1149883442872063532126237

theorem tailTrace_3359085 : CollatzResearch.WordTrace tailWord_3359085 prefixEnd_3359085 1149883442872063532126237 := by
  unfold tailWord_3359085
  simp only [CollatzResearch.WordTrace]
  refine ⟨122515895035616205889630709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81677263357077470593087139 122515895035616205889630709)
  ·
    refine ⟨11485865159589019302152879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122515895035616205889630709 11485865159589019302152879)
    ·
      refine ⟨17228797739383528953229319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11485865159589019302152879 17228797739383528953229319)
      ·
        refine ⟨25843196609075293429843979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17228797739383528953229319 25843196609075293429843979)
        ·
          refine ⟨38764794913612940144765969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25843196609075293429843979 38764794913612940144765969)
          ·
            refine ⟨29073596185209705108574477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38764794913612940144765969 29073596185209705108574477)
            ·
              refine ⟨10902598569453639415715429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29073596185209705108574477 10902598569453639415715429)
              ·
                refine ⟨2044237231772557390446643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10902598569453639415715429 2044237231772557390446643)
                ·
                  refine ⟨3066355847658836085669965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2044237231772557390446643 3066355847658836085669965)
                  ·
                    refine ⟨1149883442872063532126237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3066355847658836085669965 1149883442872063532126237)
                    ·
                      rfl

theorem cell22_3359085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_3359085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359085 prefixEnd_3359085 := by exact prefixLift 3359085
  have htrace : WordTrace (prefixWord ++ tailWord_3359085) baseStart_3359085 baseEnd_3359085 := by
    simpa [prefixWord, tailWord_3359085, baseEnd_3359085] using wordTrace_append hprefix tailTrace_3359085
  have hstable : (prefixWord ++ tailWord_3359085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359085).length < 2 ^ (prefixWord ++ tailWord_3359085).sum := by decide
  have hdescent : baseEnd_3359085 < baseStart_3359085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359111 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 3, 4]
def baseStart_3359111 : Nat := 118140960795 + 3359111 * 2 ^ 59
def prefixEnd_3359111 : Nat := 4983230072969 + 3 ^ 40 * 3359111 * 2
def baseEnd_3359111 : Nat := 1149892343203408130976157

theorem tailTrace_3359111 : CollatzResearch.WordTrace tailWord_3359111 prefixEnd_3359111 1149892343203408130976157 := by
  unfold tailWord_3359111
  simp only [CollatzResearch.WordTrace]
  refine ⟨122516843333522012330077187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81677895555681341553384791 122516843333522012330077187)
  ·
    refine ⟨183775265000283018495115781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122516843333522012330077187 183775265000283018495115781)
    ·
      refine ⟨34457862187553065967834209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183775265000283018495115781 34457862187553065967834209)
      ·
        refine ⟨25843396640664799475875657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34457862187553065967834209 25843396640664799475875657)
        ·
          refine ⟨19382547480498599606906743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25843396640664799475875657 19382547480498599606906743)
          ·
            refine ⟨29073821220747899410360115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19382547480498599606906743 29073821220747899410360115)
            ·
              refine ⟨43610731831121849115540173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29073821220747899410360115 43610731831121849115540173)
              ·
                refine ⟨16354024436670693418327565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43610731831121849115540173 16354024436670693418327565)
                ·
                  refine ⟨6132759163751510031872837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16354024436670693418327565 6132759163751510031872837)
                  ·
                    refine ⟨1149892343203408130976157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6132759163751510031872837 1149892343203408130976157)
                    ·
                      rfl

theorem cell22_3359111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_3359111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359111 prefixEnd_3359111 := by exact prefixLift 3359111
  have htrace : WordTrace (prefixWord ++ tailWord_3359111) baseStart_3359111 baseEnd_3359111 := by
    simpa [prefixWord, tailWord_3359111, baseEnd_3359111] using wordTrace_append hprefix tailTrace_3359111
  have hstable : (prefixWord ++ tailWord_3359111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359111).length < 2 ^ (prefixWord ++ tailWord_3359111).sum := by decide
  have hdescent : baseEnd_3359111 < baseStart_3359111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359143 : List Nat := [1, 1, 6, 1, 1, 3, 2, 1, 6]
def baseStart_3359143 : Nat := 118140960795 + 3359143 * 2 ^ 59
def prefixEnd_3359143 : Nat := 4983230072969 + 3 ^ 40 * 3359143 * 2
def baseEnd_3359143 : Nat := 383301099152456904725353

theorem tailTrace_3359143 : CollatzResearch.WordTrace tailWord_3359143 prefixEnd_3359143 383301099152456904725353 := by
  unfold tailWord_3359143
  simp only [CollatzResearch.WordTrace]
  refine ⟨122518010469406081795242083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81678673646270721196828055 122518010469406081795242083)
  ·
    refine ⟨183777015704109122692863125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122518010469406081795242083 183777015704109122692863125)
    ·
      refine ⟨8614547611130115126227959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 183777015704109122692863125 8614547611130115126227959)
      ·
        refine ⟨12921821416695172689341939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8614547611130115126227959 12921821416695172689341939)
        ·
          refine ⟨19382732125042759034012909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12921821416695172689341939 19382732125042759034012909)
          ·
            refine ⟨7268524546891034637754841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19382732125042759034012909 7268524546891034637754841)
            ·
              refine ⟨5451393410168275978316131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7268524546891034637754841 5451393410168275978316131)
              ·
                refine ⟨8177090115252413967474197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5451393410168275978316131 8177090115252413967474197)
                ·
                  refine ⟨383301099152456904725353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8177090115252413967474197 383301099152456904725353)
                  ·
                    rfl

theorem cell22_3359143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 6].length) (baseStart_3359143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359143 prefixEnd_3359143 := by exact prefixLift 3359143
  have htrace : WordTrace (prefixWord ++ tailWord_3359143) baseStart_3359143 baseEnd_3359143 := by
    simpa [prefixWord, tailWord_3359143, baseEnd_3359143] using wordTrace_append hprefix tailTrace_3359143
  have hstable : (prefixWord ++ tailWord_3359143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359143).length < 2 ^ (prefixWord ++ tailWord_3359143).sum := by decide
  have hdescent : baseEnd_3359143 < baseStart_3359143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359188 : List Nat := [2, 4, 1, 2, 2, 3, 8]
def baseStart_3359188 : Nat := 118140960795 + 3359188 * 2 ^ 59
def prefixEnd_3359188 : Nat := 4983230072969 + 3 ^ 40 * 3359188 * 2
def baseEnd_3359188 : Nat := 42589581551000207288923

theorem tailTrace_3359188 : CollatzResearch.WordTrace tailWord_3359188 prefixEnd_3359188 42589581551000207288923 := by
  unfold tailWord_3359188
  simp only [CollatzResearch.WordTrace]
  refine ⟨61259825877121527240315109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81679767836162036320420145 61259825877121527240315109)
  ·
    refine ⟨11486217351960286357559083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61259825877121527240315109 11486217351960286357559083)
    ·
      refine ⟨17229326027940429536338625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11486217351960286357559083 17229326027940429536338625)
      ·
        refine ⟨12921994520955322152253969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17229326027940429536338625 12921994520955322152253969)
        ·
          refine ⟨9691495890716491614190477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12921994520955322152253969 9691495890716491614190477)
          ·
            refine ⟨3634310959018684355321429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9691495890716491614190477 3634310959018684355321429)
            ·
              refine ⟨42589581551000207288923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3634310959018684355321429 42589581551000207288923)
              ·
                rfl

theorem cell22_3359188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 8].length) (baseStart_3359188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359188 prefixEnd_3359188 := by exact prefixLift 3359188
  have htrace : WordTrace (prefixWord ++ tailWord_3359188) baseStart_3359188 baseEnd_3359188 := by
    simpa [prefixWord, tailWord_3359188, baseEnd_3359188] using wordTrace_append hprefix tailTrace_3359188
  have hstable : (prefixWord ++ tailWord_3359188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359188).length < 2 ^ (prefixWord ++ tailWord_3359188).sum := by decide
  have hdescent : baseEnd_3359188 < baseStart_3359188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359190 : List Nat := [5, 2, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_3359190 : Nat := 118140960795 + 3359190 * 2 ^ 59
def prefixEnd_3359190 : Nat := 4983230072969 + 3 ^ 40 * 3359190 * 2
def baseEnd_3359190 : Nat := 1149919386517878258250915

theorem tailTrace_3359190 : CollatzResearch.WordTrace tailWord_3359190 prefixEnd_3359190 1149919386517878258250915 := by
  unfold tailWord_3359190
  simp only [CollatzResearch.WordTrace]
  refine ⟨7657482793764738051387689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81679816466823872548135349 7657482793764738051387689)
  ·
    refine ⟨5743112095323553538540767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7657482793764738051387689 5743112095323553538540767)
    ·
      refine ⟨8614668142985330307811151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5743112095323553538540767 8614668142985330307811151)
      ·
        refine ⟨12922002214477995461716727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8614668142985330307811151 12922002214477995461716727)
        ·
          refine ⟨19383003321716993192575091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12922002214477995461716727 19383003321716993192575091)
          ·
            refine ⟨29074504982575489788862637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19383003321716993192575091 29074504982575489788862637)
            ·
              refine ⟨10902939368465808670823489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29074504982575489788862637 10902939368465808670823489)
              ·
                refine ⟨8177204526349356503117617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10902939368465808670823489 8177204526349356503117617)
                ·
                  refine ⟨6132903394762017377338213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8177204526349356503117617 6132903394762017377338213)
                  ·
                    refine ⟨1149919386517878258250915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6132903394762017377338213 1149919386517878258250915)
                    ·
                      rfl

theorem cell22_3359190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_3359190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359190 prefixEnd_3359190 := by exact prefixLift 3359190
  have htrace : WordTrace (prefixWord ++ tailWord_3359190) baseStart_3359190 baseEnd_3359190 := by
    simpa [prefixWord, tailWord_3359190, baseEnd_3359190] using wordTrace_append hprefix tailTrace_3359190
  have hstable : (prefixWord ++ tailWord_3359190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359190).length < 2 ^ (prefixWord ++ tailWord_3359190).sum := by decide
  have hdescent : baseEnd_3359190 < baseStart_3359190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359201 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 2, 6]
def baseStart_3359201 : Nat := 118140960795 + 3359201 * 2 ^ 59
def prefixEnd_3359201 : Nat := 4983230072969 + 3 ^ 40 * 3359201 * 2
def baseEnd_3359201 : Nat := 1149923152042677896225881

theorem tailTrace_3359201 : CollatzResearch.WordTrace tailWord_3359201 prefixEnd_3359201 1149923152042677896225881 := by
  unfold tailWord_3359201
  simp only [CollatzResearch.WordTrace]
  refine ⟨122520125903195957700853457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81680083935463971800568971 122520125903195957700853457)
  ·
    refine ⟨91890094427396968275640093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122520125903195957700853457 91890094427396968275640093)
    ·
      refine ⟨34458785410273863103365035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91890094427396968275640093 34458785410273863103365035)
      ·
        refine ⟨51688178115410794655047553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34458785410273863103365035 51688178115410794655047553)
        ·
          refine ⟨38766133586558095991285665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51688178115410794655047553 38766133586558095991285665)
          ·
            refine ⟨29074600189918571993464249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38766133586558095991285665 29074600189918571993464249)
            ·
              refine ⟨21805950142438928995098187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29074600189918571993464249 21805950142438928995098187)
              ·
                refine ⟨32708925213658393492647281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21805950142438928995098187 32708925213658393492647281)
                ·
                  refine ⟨24531693910243795119485461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32708925213658393492647281 24531693910243795119485461)
                  ·
                    refine ⟨1149923152042677896225881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24531693910243795119485461 1149923152042677896225881)
                    ·
                      rfl

theorem cell22_3359201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_3359201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359201 prefixEnd_3359201 := by exact prefixLift 3359201
  have htrace : WordTrace (prefixWord ++ tailWord_3359201) baseStart_3359201 baseEnd_3359201 := by
    simpa [prefixWord, tailWord_3359201, baseEnd_3359201] using wordTrace_append hprefix tailTrace_3359201
  have hstable : (prefixWord ++ tailWord_3359201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359201).length < 2 ^ (prefixWord ++ tailWord_3359201).sum := by decide
  have hdescent : baseEnd_3359201 < baseStart_3359201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359295 : List Nat := [1, 1, 2, 2, 3, 2, 4, 3, 4]
def baseStart_3359295 : Nat := 118140960795 + 3359295 * 2 ^ 59
def prefixEnd_3359295 : Nat := 4983230072969 + 3 ^ 40 * 3359295 * 2
def baseEnd_3359295 : Nat := 383318443387897661458531

theorem tailTrace_3359295 : CollatzResearch.WordTrace tailWord_3359295 prefixEnd_3359295 383318443387897661458531 := by
  unfold tailWord_3359295
  simp only [CollatzResearch.WordTrace]
  refine ⟨122523554364855411754775339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81682369576570274503183559 122523554364855411754775339)
  ·
    refine ⟨183785331547283117632163009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122523554364855411754775339 183785331547283117632163009)
    ·
      refine ⟨137838998660462338224122257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183785331547283117632163009 137838998660462338224122257)
      ·
        refine ⟨103379248995346753668091693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137838998660462338224122257 103379248995346753668091693)
        ·
          refine ⟨38767218373255032625534385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103379248995346753668091693 38767218373255032625534385)
          ·
            refine ⟨29075413779941274469150789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38767218373255032625534385 29075413779941274469150789)
            ·
              refine ⟨5451640083738988962965773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29075413779941274469150789 5451640083738988962965773)
              ·
                refine ⟨2044365031402120861112165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5451640083738988962965773 2044365031402120861112165)
                ·
                  refine ⟨383318443387897661458531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2044365031402120861112165 383318443387897661458531)
                  ·
                    rfl

theorem cell22_3359295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 4].length) (baseStart_3359295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359295 prefixEnd_3359295 := by exact prefixLift 3359295
  have htrace : WordTrace (prefixWord ++ tailWord_3359295) baseStart_3359295 baseEnd_3359295 := by
    simpa [prefixWord, tailWord_3359295, baseEnd_3359295] using wordTrace_append hprefix tailTrace_3359295
  have hstable : (prefixWord ++ tailWord_3359295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359295).length < 2 ^ (prefixWord ++ tailWord_3359295).sum := by decide
  have hdescent : baseEnd_3359295 < baseStart_3359295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359297 : List Nat := [1, 2, 5, 1, 1, 2, 4, 1, 1, 4]
def baseStart_3359297 : Nat := 118140960795 + 3359297 * 2 ^ 59
def prefixEnd_3359297 : Nat := 4983230072969 + 3 ^ 40 * 3359297 * 2
def baseEnd_3359297 : Nat := 1149956014804565645825587

theorem tailTrace_3359297 : CollatzResearch.WordTrace tailWord_3359297 prefixEnd_3359297 1149956014804565645825587 := by
  unfold tailWord_3359297
  simp only [CollatzResearch.WordTrace]
  refine ⟨122523627310848166096348145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81682418207232110730898763 122523627310848166096348145)
  ·
    refine ⟨91892720483136124572261109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122523627310848166096348145 91892720483136124572261109)
    ·
      refine ⟨8614942545294011678649479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91892720483136124572261109 8614942545294011678649479)
      ·
        refine ⟨12922413817941017517974219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8614942545294011678649479 12922413817941017517974219)
        ·
          refine ⟨19383620726911526276961329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12922413817941017517974219 19383620726911526276961329)
          ·
            refine ⟨14537715545183644707720997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19383620726911526276961329 14537715545183644707720997)
            ·
              refine ⟨2725821664721933382697687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14537715545183644707720997 2725821664721933382697687)
              ·
                refine ⟨4088732497082900074046531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2725821664721933382697687 4088732497082900074046531)
                ·
                  refine ⟨6133098745624350111069797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4088732497082900074046531 6133098745624350111069797)
                  ·
                    refine ⟨1149956014804565645825587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6133098745624350111069797 1149956014804565645825587)
                    ·
                      rfl

theorem cell22_3359297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_3359297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359297 prefixEnd_3359297 := by exact prefixLift 3359297
  have htrace : WordTrace (prefixWord ++ tailWord_3359297) baseStart_3359297 baseEnd_3359297 := by
    simpa [prefixWord, tailWord_3359297, baseEnd_3359297] using wordTrace_append hprefix tailTrace_3359297
  have hstable : (prefixWord ++ tailWord_3359297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359297).length < 2 ^ (prefixWord ++ tailWord_3359297).sum := by decide
  have hdescent : baseEnd_3359297 < baseStart_3359297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359308 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 4, 4]
def baseStart_3359308 : Nat := 118140960795 + 3359308 * 2 ^ 59
def prefixEnd_3359308 : Nat := 4983230072969 + 3 ^ 40 * 3359308 * 2
def baseEnd_3359308 : Nat := 1149959780329365283800553

theorem tailTrace_3359308 : CollatzResearch.WordTrace tailWord_3359308 prefixEnd_3359308 1149959780329365283800553 := by
  unfold tailWord_3359308
  simp only [CollatzResearch.WordTrace]
  refine ⟨61262014256904157487499289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81682685675872209983332385 61262014256904157487499289)
  ·
    refine ⟨45946510692678118115624467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61262014256904157487499289 45946510692678118115624467)
    ·
      refine ⟨68919766039017177173436701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45946510692678118115624467 68919766039017177173436701)
      ·
        refine ⟨25844912264631441440038763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68919766039017177173436701 25844912264631441440038763)
        ·
          refine ⟨38767368396947162160058145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25844912264631441440038763 38767368396947162160058145)
          ·
            refine ⟨29075526297710371620043609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38767368396947162160058145 29075526297710371620043609)
            ·
              refine ⟨21806644723282778715032707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29075526297710371620043609 21806644723282778715032707)
              ·
                refine ⟨32709967084924168072549061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21806644723282778715032707 32709967084924168072549061)
                ·
                  refine ⟨6133118828423281513602949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32709967084924168072549061 6133118828423281513602949)
                  ·
                    refine ⟨1149959780329365283800553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6133118828423281513602949 1149959780329365283800553)
                    ·
                      rfl

theorem cell22_3359308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_3359308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359308 prefixEnd_3359308 := by exact prefixLift 3359308
  have htrace : WordTrace (prefixWord ++ tailWord_3359308) baseStart_3359308 baseEnd_3359308 := by
    simpa [prefixWord, tailWord_3359308, baseEnd_3359308] using wordTrace_append hprefix tailTrace_3359308
  have hstable : (prefixWord ++ tailWord_3359308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359308).length < 2 ^ (prefixWord ++ tailWord_3359308).sum := by decide
  have hdescent : baseEnd_3359308 < baseStart_3359308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359338 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 2, 7]
def baseStart_3359338 : Nat := 118140960795 + 3359338 * 2 ^ 59
def prefixEnd_3359338 : Nat := 4983230072969 + 3 ^ 40 * 3359338 * 2
def baseEnd_3359338 : Nat := 1149970049942455205550461

theorem tailTrace_3359338 : CollatzResearch.WordTrace tailWord_3359338 prefixEnd_3359338 1149970049942455205550461 := by
  unfold tailWord_3359338
  simp only [CollatzResearch.WordTrace]
  refine ⟨30631280675924907524647667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81683415135799753399060445 30631280675924907524647667)
  ·
    refine ⟨45946921013887361286971501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30631280675924907524647667 45946921013887361286971501)
    ·
      refine ⟨17230095380207760482614313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45946921013887361286971501 17230095380207760482614313)
      ·
        refine ⟨12922571535155820361960735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17230095380207760482614313 12922571535155820361960735)
        ·
          refine ⟨19383857302733730542941103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12922571535155820361960735 19383857302733730542941103)
          ·
            refine ⟨29075785954100595814411655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19383857302733730542941103 29075785954100595814411655)
            ·
              refine ⟨43613678931150893721617483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29075785954100595814411655 43613678931150893721617483)
              ·
                refine ⟨65420518396726340582426225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43613678931150893721617483 65420518396726340582426225)
                ·
                  refine ⟨49065388797544755436819669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65420518396726340582426225 49065388797544755436819669)
                  ·
                    refine ⟨1149970049942455205550461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49065388797544755436819669 1149970049942455205550461)
                    ·
                      rfl

theorem cell22_3359338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_3359338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359338 prefixEnd_3359338 := by exact prefixLift 3359338
  have htrace : WordTrace (prefixWord ++ tailWord_3359338) baseStart_3359338 baseEnd_3359338 := by
    simpa [prefixWord, tailWord_3359338, baseEnd_3359338] using wordTrace_append hprefix tailTrace_3359338
  have hstable : (prefixWord ++ tailWord_3359338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359338).length < 2 ^ (prefixWord ++ tailWord_3359338).sum := by decide
  have hdescent : baseEnd_3359338 < baseStart_3359338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359383 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 1, 7]
def baseStart_3359383 : Nat := 118140960795 + 3359383 * 2 ^ 59
def prefixEnd_3359383 : Nat := 4983230072969 + 3 ^ 40 * 3359383 * 2
def baseEnd_3359383 : Nat := 1149985454362090088175323

theorem tailTrace_3359383 : CollatzResearch.WordTrace tailWord_3359383 prefixEnd_3359383 1149985454362090088175323 := by
  unfold tailWord_3359383
  simp only [CollatzResearch.WordTrace]
  refine ⟨122526763988536602783978803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81684509325691068522652535 122526763988536602783978803)
  ·
    refine ⟨183790145982804904175968205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122526763988536602783978803 183790145982804904175968205)
    ·
      refine ⟨68921304743551839065988077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183790145982804904175968205 68921304743551839065988077)
      ·
        refine ⟨25845489278831939649745529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68921304743551839065988077 25845489278831939649745529)
        ·
          refine ⟨19384116959123954737309147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25845489278831939649745529 19384116959123954737309147)
          ·
            refine ⟨29076175438685932105963721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19384116959123954737309147 29076175438685932105963721)
            ·
              refine ⟨21807131579014449079472791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29076175438685932105963721 21807131579014449079472791)
              ·
                refine ⟨32710697368521673619209187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21807131579014449079472791 32710697368521673619209187)
                ·
                  refine ⟨49066046052782510428813781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32710697368521673619209187 49066046052782510428813781)
                  ·
                    refine ⟨1149985454362090088175323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49066046052782510428813781 1149985454362090088175323)
                    ·
                      rfl

theorem cell22_3359383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_3359383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359383 prefixEnd_3359383 := by exact prefixLift 3359383
  have htrace : WordTrace (prefixWord ++ tailWord_3359383) baseStart_3359383 baseEnd_3359383 := by
    simpa [prefixWord, tailWord_3359383, baseEnd_3359383] using wordTrace_append hprefix tailTrace_3359383
  have hstable : (prefixWord ++ tailWord_3359383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359383).length < 2 ^ (prefixWord ++ tailWord_3359383).sum := by decide
  have hdescent : baseEnd_3359383 < baseStart_3359383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359460 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_3359460 : Nat := 118140960795 + 3359460 * 2 ^ 59
def prefixEnd_3359460 : Nat := 4983230072969 + 3 ^ 40 * 3359460 * 2
def baseEnd_3359460 : Nat := 1150011813035687554000087

theorem tailTrace_3359460 : CollatzResearch.WordTrace tailWord_3359460 prefixEnd_3359460 1150011813035687554000087 := by
  unfold tailWord_3359460
  simp only [CollatzResearch.WordTrace]
  refine ⟨61264786204628822467265917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81686381606171763289687889 61264786204628822467265917)
  ·
    refine ⟨22974294826735808425224719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61264786204628822467265917 22974294826735808425224719)
    ·
      refine ⟨34461442240103712637837079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22974294826735808425224719 34461442240103712637837079)
      ·
        refine ⟨51692163360155568956755619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34461442240103712637837079 51692163360155568956755619)
        ·
          refine ⟨77538245040233353435133429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51692163360155568956755619 77538245040233353435133429)
          ·
            refine ⟨7269210472521876884543759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77538245040233353435133429 7269210472521876884543759)
            ·
              refine ⟨10903815708782815326815639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7269210472521876884543759 10903815708782815326815639)
              ·
                refine ⟨16355723563174222990223459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10903815708782815326815639 16355723563174222990223459)
                ·
                  refine ⟨24533585344761334485335189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16355723563174222990223459 24533585344761334485335189)
                  ·
                    refine ⟨1150011813035687554000087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24533585344761334485335189 1150011813035687554000087)
                    ·
                      rfl

theorem cell22_3359460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_3359460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359460 prefixEnd_3359460 := by exact prefixLift 3359460
  have htrace : WordTrace (prefixWord ++ tailWord_3359460) baseStart_3359460 baseEnd_3359460 := by
    simpa [prefixWord, tailWord_3359460, baseEnd_3359460] using wordTrace_append hprefix tailTrace_3359460
  have hstable : (prefixWord ++ tailWord_3359460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359460).length < 2 ^ (prefixWord ++ tailWord_3359460).sum := by decide
  have hdescent : baseEnd_3359460 < baseStart_3359460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359464 : List Nat := [2, 1, 4, 1, 4, 1, 2, 3, 4]
def baseStart_3359464 : Nat := 118140960795 + 3359464 * 2 ^ 59
def prefixEnd_3359464 : Nat := 4983230072969 + 3 ^ 40 * 3359464 * 2
def baseEnd_3359464 : Nat := 383337727439144292300025

theorem tailTrace_3359464 : CollatzResearch.WordTrace tailWord_3359464 prefixEnd_3359464 383337727439144292300025 := by
  unfold tailWord_3359464
  simp only [CollatzResearch.WordTrace]
  refine ⟨61264859150621576808838723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81686478867495435745118297 61264859150621576808838723)
  ·
    refine ⟨91897288725932365213258085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61264859150621576808838723 91897288725932365213258085)
    ·
      refine ⟨17230741636112318477485891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91897288725932365213258085 17230741636112318477485891)
      ·
        refine ⟨25846112454168477716228837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17230741636112318477485891 25846112454168477716228837)
        ·
          refine ⟨4846146085156589571792907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25846112454168477716228837 4846146085156589571792907)
          ·
            refine ⟨7269219127734884357689361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4846146085156589571792907 7269219127734884357689361)
            ·
              refine ⟨5451914345801163268267021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7269219127734884357689361 5451914345801163268267021)
              ·
                refine ⟨2044467879675436225600133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5451914345801163268267021 2044467879675436225600133)
                ·
                  refine ⟨383337727439144292300025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2044467879675436225600133 383337727439144292300025)
                  ·
                    rfl

theorem cell22_3359464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 4].length) (baseStart_3359464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359464 prefixEnd_3359464 := by exact prefixLift 3359464
  have htrace : WordTrace (prefixWord ++ tailWord_3359464) baseStart_3359464 baseEnd_3359464 := by
    simpa [prefixWord, tailWord_3359464, baseEnd_3359464] using wordTrace_append hprefix tailTrace_3359464
  have hstable : (prefixWord ++ tailWord_3359464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359464).length < 2 ^ (prefixWord ++ tailWord_3359464).sum := by decide
  have hdescent : baseEnd_3359464 < baseStart_3359464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359520 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 7]
def baseStart_3359520 : Nat := 118140960795 + 3359520 * 2 ^ 59
def prefixEnd_3359520 : Nat := 4983230072969 + 3 ^ 40 * 3359520 * 2
def baseEnd_3359520 : Nat := 383344117420622465833301

theorem tailTrace_3359520 : CollatzResearch.WordTrace tailWord_3359520 prefixEnd_3359520 383344117420622465833301 := by
  unfold tailWord_3359520
  simp only [CollatzResearch.WordTrace]
  refine ⟨61265880394520137590858007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81687840526026850121144009 61265880394520137590858007)
  ·
    refine ⟨91898820591780206386287011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61265880394520137590858007 91898820591780206386287011)
    ·
      refine ⟨137848230887670309579430517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91898820591780206386287011 137848230887670309579430517)
      ·
        refine ⟨12923271645719091523071611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137848230887670309579430517 12923271645719091523071611)
        ·
          refine ⟨19384907468578637284607417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12923271645719091523071611 19384907468578637284607417)
          ·
            refine ⟨14538680601433977963455563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19384907468578637284607417 14538680601433977963455563)
            ·
              refine ⟨21808020902150966945183345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14538680601433977963455563 21808020902150966945183345)
              ·
                refine ⟨16356015676613225208887509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21808020902150966945183345 16356015676613225208887509)
                ·
                  refine ⟨383344117420622465833301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16356015676613225208887509 383344117420622465833301)
                  ·
                    rfl

theorem cell22_3359520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 7].length) (baseStart_3359520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359520 prefixEnd_3359520 := by exact prefixLift 3359520
  have htrace : WordTrace (prefixWord ++ tailWord_3359520) baseStart_3359520 baseEnd_3359520 := by
    simpa [prefixWord, tailWord_3359520, baseEnd_3359520] using wordTrace_append hprefix tailTrace_3359520
  have hstable : (prefixWord ++ tailWord_3359520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359520).length < 2 ^ (prefixWord ++ tailWord_3359520).sum := by decide
  have hdescent : baseEnd_3359520 < baseStart_3359520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359584 : List Nat := [2, 1, 1, 3, 3, 1, 5, 1, 1, 4]
def baseStart_3359584 : Nat := 118140960795 + 3359584 * 2 ^ 59
def prefixEnd_3359584 : Nat := 4983230072969 + 3 ^ 40 * 3359584 * 2
def baseEnd_3359584 : Nat := 1150054260769792563899707

theorem tailTrace_3359584 : CollatzResearch.WordTrace tailWord_3359584 prefixEnd_3359584 1150054260769792563899707 := by
  unfold tailWord_3359584
  simp only [CollatzResearch.WordTrace]
  refine ⟨61267047530404207056022903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81689396707205609408030537 61267047530404207056022903)
  ·
    refine ⟨91900571295606310584034355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61267047530404207056022903 91900571295606310584034355)
    ·
      refine ⟨137850856943409465876051533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91900571295606310584034355 137850856943409465876051533)
      ·
        refine ⟨51694071353778549703519325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137850856943409465876051533 51694071353778549703519325)
        ·
          refine ⟨19385276757666956138819747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51694071353778549703519325 19385276757666956138819747)
          ·
            refine ⟨29077915136500434208229621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19385276757666956138819747 29077915136500434208229621)
            ·
              refine ⟨2726054544046915707021527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29077915136500434208229621 2726054544046915707021527)
              ·
                refine ⟨4089081816070373560532291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2726054544046915707021527 4089081816070373560532291)
                ·
                  refine ⟨6133622724105560340798437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4089081816070373560532291 6133622724105560340798437)
                  ·
                    refine ⟨1150054260769792563899707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6133622724105560340798437 1150054260769792563899707)
                    ·
                      rfl

theorem cell22_3359584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 1, 4].length) (baseStart_3359584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359584 prefixEnd_3359584 := by exact prefixLift 3359584
  have htrace : WordTrace (prefixWord ++ tailWord_3359584) baseStart_3359584 baseEnd_3359584 := by
    simpa [prefixWord, tailWord_3359584, baseEnd_3359584] using wordTrace_append hprefix tailTrace_3359584
  have hstable : (prefixWord ++ tailWord_3359584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359584).length < 2 ^ (prefixWord ++ tailWord_3359584).sum := by decide
  have hdescent : baseEnd_3359584 < baseStart_3359584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359768 : List Nat := [2, 1, 2, 3, 2, 4, 2, 2, 4]
def baseStart_3359768 : Nat := 118140960795 + 3359768 * 2 ^ 59
def prefixEnd_3359768 : Nat := 4983230072969 + 3 ^ 40 * 3359768 * 2
def baseEnd_3359768 : Nat := 383372415910025805766381

theorem tailTrace_3359768 : CollatzResearch.WordTrace tailWord_3359768 prefixEnd_3359768 383372415910025805766381 := by
  unfold tailWord_3359768
  simp only [CollatzResearch.WordTrace]
  refine ⟨61270403046070906768371979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81693870728094542357829305 61270403046070906768371979)
  ·
    refine ⟨91905604569106360152557969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61270403046070906768371979 91905604569106360152557969)
    ·
      refine ⟨68929203426829770114418477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91905604569106360152557969 68929203426829770114418477)
      ·
        refine ⟨25848451285061163792906929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68929203426829770114418477 25848451285061163792906929)
        ·
          refine ⟨19386338463795872844680197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25848451285061163792906929 19386338463795872844680197)
          ·
            refine ⟨3634938461961726158377537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19386338463795872844680197 3634938461961726158377537)
            ·
              refine ⟨2726203846471294618783153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3634938461961726158377537 2726203846471294618783153)
              ·
                refine ⟨2044652884853470964087365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2726203846471294618783153 2044652884853470964087365)
                ·
                  refine ⟨383372415910025805766381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2044652884853470964087365 383372415910025805766381)
                  ·
                    rfl

theorem cell22_3359768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 4].length) (baseStart_3359768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359768 prefixEnd_3359768 := by exact prefixLift 3359768
  have htrace : WordTrace (prefixWord ++ tailWord_3359768) baseStart_3359768 baseEnd_3359768 := by
    simpa [prefixWord, tailWord_3359768, baseEnd_3359768] using wordTrace_append hprefix tailTrace_3359768
  have hstable : (prefixWord ++ tailWord_3359768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359768).length < 2 ^ (prefixWord ++ tailWord_3359768).sum := by decide
  have hdescent : baseEnd_3359768 < baseStart_3359768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359779 : List Nat := [1, 1, 1, 4, 3, 4, 1, 7]
def baseStart_3359779 : Nat := 118140960795 + 3359779 * 2 ^ 59
def prefixEnd_3359779 : Nat := 4983230072969 + 3 ^ 40 * 3359779 * 2
def baseEnd_3359779 : Nat := 127791223694986339474901

theorem tailTrace_3359779 : CollatzResearch.WordTrace tailWord_3359779 prefixEnd_3359779 127791223694986339474901 := by
  unfold tailWord_3359779
  simp only [CollatzResearch.WordTrace]
  refine ⟨122541207295101962415394391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81694138196734641610262927 122541207295101962415394391)
  ·
    refine ⟨183811810942652943623091587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122541207295101962415394391 183811810942652943623091587)
    ·
      refine ⟨275717716413979415434637381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183811810942652943623091587 275717716413979415434637381)
      ·
        refine ⟨51697071827621140393994509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275717716413979415434637381 51697071827621140393994509)
        ·
          refine ⟨19386401935357927647747941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51697071827621140393994509 19386401935357927647747941)
          ·
            refine ⟨3634950362879611433952739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19386401935357927647747941 3634950362879611433952739)
            ·
              refine ⟨5452425544319417150929109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3634950362879611433952739 5452425544319417150929109)
              ·
                refine ⟨127791223694986339474901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5452425544319417150929109 127791223694986339474901)
                ·
                  rfl

theorem cell22_3359779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 7].length) (baseStart_3359779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359779 prefixEnd_3359779 := by exact prefixLift 3359779
  have htrace : WordTrace (prefixWord ++ tailWord_3359779) baseStart_3359779 baseEnd_3359779 := by
    simpa [prefixWord, tailWord_3359779, baseEnd_3359779] using wordTrace_append hprefix tailTrace_3359779
  have hstable : (prefixWord ++ tailWord_3359779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359779).length < 2 ^ (prefixWord ++ tailWord_3359779).sum := by decide
  have hdescent : baseEnd_3359779 < baseStart_3359779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359783 : List Nat := [1, 1, 7, 1, 1, 1, 2, 3, 2, 3]
def baseStart_3359783 : Nat := 118140960795 + 3359783 * 2 ^ 59
def prefixEnd_3359783 : Nat := 4983230072969 + 3 ^ 40 * 3359783 * 2
def baseEnd_3359783 : Nat := 1150122382536622378174097

theorem tailTrace_3359783 : CollatzResearch.WordTrace tailWord_3359783 prefixEnd_3359783 1150122382536622378174097 := by
  unfold tailWord_3359783
  simp only [CollatzResearch.WordTrace]
  refine ⟨122541353187087471098540003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81694235458058314065693335 122541353187087471098540003)
  ·
    refine ⟨183812029780631206647810005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122541353187087471098540003 183812029780631206647810005)
    ·
      refine ⟨4308094447983543905808047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 183812029780631206647810005 4308094447983543905808047)
      ·
        refine ⟨6462141671975315858712071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4308094447983543905808047 6462141671975315858712071)
        ·
          refine ⟨9693212507962973788068107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6462141671975315858712071 9693212507962973788068107)
          ·
            refine ⟨14539818761944460682102161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9693212507962973788068107 14539818761944460682102161)
            ·
              refine ⟨10904864071458345511576621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14539818761944460682102161 10904864071458345511576621)
              ·
                refine ⟨4089324026796879566841233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10904864071458345511576621 4089324026796879566841233)
                ·
                  refine ⟨3066993020097659675130925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4089324026796879566841233 3066993020097659675130925)
                  ·
                    refine ⟨1150122382536622378174097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3066993020097659675130925 1150122382536622378174097)
                    ·
                      rfl

theorem cell22_3359783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_3359783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359783 prefixEnd_3359783 := by exact prefixLift 3359783
  have htrace : WordTrace (prefixWord ++ tailWord_3359783) baseStart_3359783 baseEnd_3359783 := by
    simpa [prefixWord, tailWord_3359783, baseEnd_3359783] using wordTrace_append hprefix tailTrace_3359783
  have hstable : (prefixWord ++ tailWord_3359783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359783).length < 2 ^ (prefixWord ++ tailWord_3359783).sum := by decide
  have hdescent : baseEnd_3359783 < baseStart_3359783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359792 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 2, 6]
def baseStart_3359792 : Nat := 118140960795 + 3359792 * 2 ^ 59
def prefixEnd_3359792 : Nat := 4983230072969 + 3 ^ 40 * 3359792 * 2
def baseEnd_3359792 : Nat := 1150125463420549354699069

theorem tailTrace_3359792 : CollatzResearch.WordTrace tailWord_3359792 prefixEnd_3359792 1150125463420549354699069 := by
  unfold tailWord_3359792
  simp only [CollatzResearch.WordTrace]
  refine ⟨61270840722027432817808815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81694454296036577090411753 61270840722027432817808815)
  ·
    refine ⟨91906261083041149226713223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61270840722027432817808815 91906261083041149226713223)
    ·
      refine ⟨137859391624561723840069835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91906261083041149226713223 137859391624561723840069835)
      ·
        refine ⟨206789087436842585760104753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137859391624561723840069835 206789087436842585760104753)
        ·
          refine ⟨155091815577631939320078565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206789087436842585760104753 155091815577631939320078565)
          ·
            refine ⟨29079715420805988622514731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155091815577631939320078565 29079715420805988622514731)
            ·
              refine ⟨43619573131208982933772097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29079715420805988622514731 43619573131208982933772097)
              ·
                refine ⟨32714679848406737200329073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43619573131208982933772097 32714679848406737200329073)
                ·
                  refine ⟨24536009886305052900246805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32714679848406737200329073 24536009886305052900246805)
                  ·
                    refine ⟨1150125463420549354699069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24536009886305052900246805 1150125463420549354699069)
                    ·
                      rfl

theorem cell22_3359792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_3359792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359792 prefixEnd_3359792 := by exact prefixLift 3359792
  have htrace : WordTrace (prefixWord ++ tailWord_3359792) baseStart_3359792 baseEnd_3359792 := by
    simpa [prefixWord, tailWord_3359792, baseEnd_3359792] using wordTrace_append hprefix tailTrace_3359792
  have hstable : (prefixWord ++ tailWord_3359792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359792).length < 2 ^ (prefixWord ++ tailWord_3359792).sum := by decide
  have hdescent : baseEnd_3359792 < baseStart_3359792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359798 : List Nat := [5, 1, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_3359798 : Nat := 118140960795 + 3359798 * 2 ^ 59
def prefixEnd_3359798 : Nat := 4983230072969 + 3 ^ 40 * 3359798 * 2
def baseEnd_3359798 : Nat := 1150127517343167339049051

theorem tailTrace_3359798 : CollatzResearch.WordTrace tailWord_3359798 prefixEnd_3359798 1150127517343167339049051 := by
  unfold tailWord_3359798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7658868767627070541271003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81694600188022085773557365 7658868767627070541271003)
  ·
    refine ⟨11488303151440605811906505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7658868767627070541271003 11488303151440605811906505)
    ·
      refine ⟨8616227363580454358929879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11488303151440605811906505 8616227363580454358929879)
      ·
        refine ⟨12924341045370681538394819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8616227363580454358929879 12924341045370681538394819)
        ·
          refine ⟨19386511568056022307592229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12924341045370681538394819 19386511568056022307592229)
          ·
            refine ⟨3634970919010504182673543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19386511568056022307592229 3634970919010504182673543)
            ·
              refine ⟨5452456378515756274010315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3634970919010504182673543 5452456378515756274010315)
              ·
                refine ⟨8178684567773634411015473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5452456378515756274010315 8178684567773634411015473)
                ·
                  refine ⟨6134013425830225808261605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8178684567773634411015473 6134013425830225808261605)
                  ·
                    refine ⟨1150127517343167339049051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6134013425830225808261605 1150127517343167339049051)
                    ·
                      rfl

theorem cell22_3359798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_3359798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359798 prefixEnd_3359798 := by exact prefixLift 3359798
  have htrace : WordTrace (prefixWord ++ tailWord_3359798) baseStart_3359798 baseEnd_3359798 := by
    simpa [prefixWord, tailWord_3359798, baseEnd_3359798] using wordTrace_append hprefix tailTrace_3359798
  have hstable : (prefixWord ++ tailWord_3359798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359798).length < 2 ^ (prefixWord ++ tailWord_3359798).sum := by decide
  have hdescent : baseEnd_3359798 < baseStart_3359798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359807 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 7]
def baseStart_3359807 : Nat := 118140960795 + 3359807 * 2 ^ 59
def prefixEnd_3359807 : Nat := 4983230072969 + 3 ^ 40 * 3359807 * 2
def baseEnd_3359807 : Nat := 383376866075698105191341

theorem tailTrace_3359807 : CollatzResearch.WordTrace tailWord_3359807 prefixEnd_3359807 383376866075698105191341 := by
  unfold tailWord_3359807
  simp only [CollatzResearch.WordTrace]
  refine ⟨122542228539000523197413675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81694819026000348798275783 122542228539000523197413675)
  ·
    refine ⟨183813342808500784796120513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122542228539000523197413675 183813342808500784796120513)
    ·
      refine ⟨137860007106375588597090385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183813342808500784796120513 137860007106375588597090385)
      ·
        refine ⟨103395005329781691447817789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137860007106375588597090385 103395005329781691447817789)
        ·
          refine ⟨38773126998668134292931671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103395005329781691447817789 38773126998668134292931671)
          ·
            refine ⟨58159690498002201439397507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38773126998668134292931671 58159690498002201439397507)
            ·
              refine ⟨87239535747003302159096261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58159690498002201439397507 87239535747003302159096261)
              ·
                refine ⟨16357412952563119154830549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87239535747003302159096261 16357412952563119154830549)
                ·
                  refine ⟨383376866075698105191341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16357412952563119154830549 383376866075698105191341)
                  ·
                    rfl

theorem cell22_3359807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 7].length) (baseStart_3359807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359807 prefixEnd_3359807 := by exact prefixLift 3359807
  have htrace : WordTrace (prefixWord ++ tailWord_3359807) baseStart_3359807 baseEnd_3359807 := by
    simpa [prefixWord, tailWord_3359807, baseEnd_3359807] using wordTrace_append hprefix tailTrace_3359807
  have hstable : (prefixWord ++ tailWord_3359807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359807).length < 2 ^ (prefixWord ++ tailWord_3359807).sum := by decide
  have hdescent : baseEnd_3359807 < baseStart_3359807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359828 : List Nat := [2, 4, 1, 1, 1, 1, 4, 4, 1, 3]
def baseStart_3359828 : Nat := 118140960795 + 3359828 * 2 ^ 59
def prefixEnd_3359828 : Nat := 4983230072969 + 3 ^ 40 * 3359828 * 2
def baseEnd_3359828 : Nat := 1150137786956257260798959

theorem tailTrace_3359828 : CollatzResearch.WordTrace tailWord_3359828 prefixEnd_3359828 1150137786956257260798959 := by
  unfold tailWord_3359828
  simp only [CollatzResearch.WordTrace]
  refine ⟨61271497235962221891964069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81695329647949629189285425 61271497235962221891964069)
  ·
    refine ⟨11488405731742916604743263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61271497235962221891964069 11488405731742916604743263)
    ·
      refine ⟨17232608597614374907114895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11488405731742916604743263 17232608597614374907114895)
      ·
        refine ⟨25848912896421562360672343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17232608597614374907114895 25848912896421562360672343)
        ·
          refine ⟨38773369344632343541008515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25848912896421562360672343 38773369344632343541008515)
          ·
            refine ⟨58160054016948515311512773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38773369344632343541008515 58160054016948515311512773)
            ·
              refine ⟨10905010128177846620908645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58160054016948515311512773 10905010128177846620908645)
              ·
                refine ⟨2044689399033346241420371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10905010128177846620908645 2044689399033346241420371)
                ·
                  refine ⟨3067034098550019362130557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2044689399033346241420371 3067034098550019362130557)
                  ·
                    refine ⟨1150137786956257260798959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3067034098550019362130557 1150137786956257260798959)
                    ·
                      rfl

theorem cell22_3359828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_3359828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359828 prefixEnd_3359828 := by exact prefixLift 3359828
  have htrace : WordTrace (prefixWord ++ tailWord_3359828) baseStart_3359828 baseEnd_3359828 := by
    simpa [prefixWord, tailWord_3359828, baseEnd_3359828] using wordTrace_append hprefix tailTrace_3359828
  have hstable : (prefixWord ++ tailWord_3359828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359828).length < 2 ^ (prefixWord ++ tailWord_3359828).sum := by decide
  have hdescent : baseEnd_3359828 < baseStart_3359828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359886 : List Nat := [4, 1, 1, 3, 2, 1, 3, 1, 6]
def baseStart_3359886 : Nat := 118140960795 + 3359886 * 2 ^ 59
def prefixEnd_3359886 : Nat := 4983230072969 + 3 ^ 40 * 3359886 * 2
def baseEnd_3359886 : Nat := 383385880513854814282927

theorem tailTrace_3359886 : CollatzResearch.WordTrace tailWord_3359886 prefixEnd_3359886 383385880513854814282927 := by
  unfold tailWord_3359886
  simp only [CollatzResearch.WordTrace]
  refine ⟨15318138738214289961192439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81696739937142879793026341 15318138738214289961192439)
  ·
    refine ⟨22977208107321434941788659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15318138738214289961192439 22977208107321434941788659)
    ·
      refine ⟨34465812160982152412682989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22977208107321434941788659 34465812160982152412682989)
      ·
        refine ⟨12924679560368307154756121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34465812160982152412682989 12924679560368307154756121)
        ·
          refine ⟨9693509670276230366067091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12924679560368307154756121 9693509670276230366067091)
          ·
            refine ⟨14540264505414345549100637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9693509670276230366067091 14540264505414345549100637)
            ·
              refine ⟨5452599189530379580912739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14540264505414345549100637 5452599189530379580912739)
              ·
                refine ⟨8178898784295569371369109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5452599189530379580912739 8178898784295569371369109)
                ·
                  refine ⟨383385880513854814282927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8178898784295569371369109 383385880513854814282927)
                  ·
                    rfl

theorem cell22_3359886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_3359886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359886 prefixEnd_3359886 := by exact prefixLift 3359886
  have htrace : WordTrace (prefixWord ++ tailWord_3359886) baseStart_3359886 baseEnd_3359886 := by
    simpa [prefixWord, tailWord_3359886, baseEnd_3359886] using wordTrace_append hprefix tailTrace_3359886
  have hstable : (prefixWord ++ tailWord_3359886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359886).length < 2 ^ (prefixWord ++ tailWord_3359886).sum := by decide
  have hdescent : baseEnd_3359886 < baseStart_3359886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359937 : List Nat := [1, 2, 6, 1, 1, 3, 2, 2, 4]
def baseStart_3359937 : Nat := 118140960795 + 3359937 * 2 ^ 59
def prefixEnd_3359937 : Nat := 4983230072969 + 3 ^ 40 * 3359937 * 2
def baseEnd_3359937 : Nat := 383391699961272436607875

theorem tailTrace_3359937 : CollatzResearch.WordTrace tailWord_3359937 prefixEnd_3359937 383391699961272436607875 := by
  unfold tailWord_3359937
  simp only [CollatzResearch.WordTrace]
  refine ⟨122546970028529555399646065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81697980019019703599764043 122546970028529555399646065)
  ·
    refine ⟨91910227521397166549734549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122546970028529555399646065 91910227521397166549734549)
    ·
      refine ⟨4308291915065492182018807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 91910227521397166549734549 4308291915065492182018807)
      ·
        refine ⟨6462437872598238273028211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4308291915065492182018807 6462437872598238273028211)
        ·
          refine ⟨9693656808897357409542317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6462437872598238273028211 9693656808897357409542317)
          ·
            refine ⟨3635121303336509028578369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9693656808897357409542317 3635121303336509028578369)
            ·
              refine ⟨2726340977502381771433777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3635121303336509028578369 2726340977502381771433777)
              ·
                refine ⟨2044755733126786328575333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2726340977502381771433777 2044755733126786328575333)
                ·
                  refine ⟨383391699961272436607875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2044755733126786328575333 383391699961272436607875)
                  ·
                    rfl

theorem cell22_3359937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 4].length) (baseStart_3359937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359937 prefixEnd_3359937 := by exact prefixLift 3359937
  have htrace : WordTrace (prefixWord ++ tailWord_3359937) baseStart_3359937 baseEnd_3359937 := by
    simpa [prefixWord, tailWord_3359937, baseEnd_3359937] using wordTrace_append hprefix tailTrace_3359937
  have hstable : (prefixWord ++ tailWord_3359937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359937).length < 2 ^ (prefixWord ++ tailWord_3359937).sum := by decide
  have hdescent : baseEnd_3359937 < baseStart_3359937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359944 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 2, 6]
def baseStart_3359944 : Nat := 118140960795 + 3359944 * 2 ^ 59
def prefixEnd_3359944 : Nat := 4983230072969 + 3 ^ 40 * 3359944 * 2
def baseEnd_3359944 : Nat := 1150177496126871624898603

theorem tailTrace_3359944 : CollatzResearch.WordTrace tailWord_3359944 prefixEnd_3359944 1150177496126871624898603 := by
  unfold tailWord_3359944
  simp only [CollatzResearch.WordTrace]
  refine ⟨61273612669752097797575443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81698150226336130396767257 61273612669752097797575443)
  ·
    refine ⟨91910419004628146696363165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61273612669752097797575443 91910419004628146696363165)
    ·
      refine ⟨34466407126735555011136187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91910419004628146696363165 34466407126735555011136187)
      ·
        refine ⟨51699610690103332516704281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34466407126735555011136187 51699610690103332516704281)
        ·
          refine ⟨38774708017577499387528211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51699610690103332516704281 38774708017577499387528211)
          ·
            refine ⟨58162062026366249081292317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38774708017577499387528211 58162062026366249081292317)
            ·
              refine ⟨21810773259887343405484619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58162062026366249081292317 21810773259887343405484619)
              ·
                refine ⟨32716159889831015108226929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21810773259887343405484619 32716159889831015108226929)
                ·
                  refine ⟨24537119917373261331170197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32716159889831015108226929 24537119917373261331170197)
                  ·
                    refine ⟨1150177496126871624898603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24537119917373261331170197 1150177496126871624898603)
                    ·
                      rfl

theorem cell22_3359944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_3359944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359944 prefixEnd_3359944 := by exact prefixLift 3359944
  have htrace : WordTrace (prefixWord ++ tailWord_3359944) baseStart_3359944 baseEnd_3359944 := by
    simpa [prefixWord, tailWord_3359944, baseEnd_3359944] using wordTrace_append hprefix tailTrace_3359944
  have hstable : (prefixWord ++ tailWord_3359944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359944).length < 2 ^ (prefixWord ++ tailWord_3359944).sum := by decide
  have hdescent : baseEnd_3359944 < baseStart_3359944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359980 : List Nat := [2, 2, 1, 1, 2, 5, 2, 3, 1, 3]
def baseStart_3359980 : Nat := 118140960795 + 3359980 * 2 ^ 59
def prefixEnd_3359980 : Nat := 4983230072969 + 3 ^ 40 * 3359980 * 2
def baseEnd_3359980 : Nat := 1150189819662579530998493

theorem tailTrace_3359980 : CollatzResearch.WordTrace tailWord_3359980 prefixEnd_3359980 1150189819662579530998493 := by
  unfold tailWord_3359980
  simp only [CollatzResearch.WordTrace]
  refine ⟨61274269183686886871730697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81699025578249182495640929 61274269183686886871730697)
  ·
    refine ⟨45955701887765165153798023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61274269183686886871730697 45955701887765165153798023)
    ·
      refine ⟨68933552831647747730697035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45955701887765165153798023 68933552831647747730697035)
      ·
        refine ⟨103400329247471621596045553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68933552831647747730697035 103400329247471621596045553)
        ·
          refine ⟨77550246935603716197034165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103400329247471621596045553 77550246935603716197034165)
          ·
            refine ⟨7270335650212848393471953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77550246935603716197034165 7270335650212848393471953)
            ·
              refine ⟨5452751737659636295103965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7270335650212848393471953 5452751737659636295103965)
              ·
                refine ⟨2044781901622363610663987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5452751737659636295103965 2044781901622363610663987)
                ·
                  refine ⟨3067172852433545415995981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2044781901622363610663987 3067172852433545415995981)
                  ·
                    refine ⟨1150189819662579530998493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3067172852433545415995981 1150189819662579530998493)
                    ·
                      rfl

theorem cell22_3359980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 1, 3].length) (baseStart_3359980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3359980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3359980 prefixEnd_3359980 := by exact prefixLift 3359980
  have htrace : WordTrace (prefixWord ++ tailWord_3359980) baseStart_3359980 baseEnd_3359980 := by
    simpa [prefixWord, tailWord_3359980, baseEnd_3359980] using wordTrace_append hprefix tailTrace_3359980
  have hstable : (prefixWord ++ tailWord_3359980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359980).length < 2 ^ (prefixWord ++ tailWord_3359980).sum := by decide
  have hdescent : baseEnd_3359980 < baseStart_3359980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360023 : List Nat := [1, 1, 3, 4, 1, 1, 4, 2, 1, 4]
def baseStart_3360023 : Nat := 118140960795 + 3360023 * 2 ^ 59
def prefixEnd_3360023 : Nat := 4983230072969 + 3 ^ 40 * 3360023 * 2
def baseEnd_3360023 : Nat := 1150204539441341752173361

theorem tailTrace_3360023 : CollatzResearch.WordTrace tailWord_3360023 prefixEnd_3360023 1150204539441341752173361 := by
  unfold tailWord_3360023
  simp only [CollatzResearch.WordTrace]
  refine ⟨122550106706217992087276723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81700071137478661391517815 122550106706217992087276723)
  ·
    refine ⟨183825160059326988130915085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122550106706217992087276723 183825160059326988130915085)
    ·
      refine ⟨68934435022247620549093157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183825160059326988130915085 68934435022247620549093157)
      ·
        refine ⟨12925206566671428852954967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68934435022247620549093157 12925206566671428852954967)
        ·
          refine ⟨19387809850007143279432451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12925206566671428852954967 19387809850007143279432451)
          ·
            refine ⟨29081714775010714919148677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19387809850007143279432451 29081714775010714919148677)
            ·
              refine ⟨5452821520314509047340377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29081714775010714919148677 5452821520314509047340377)
              ·
                refine ⟨4089616140235881785505283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5452821520314509047340377 4089616140235881785505283)
                ·
                  refine ⟨6134424210353822678257925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4089616140235881785505283 6134424210353822678257925)
                  ·
                    refine ⟨1150204539441341752173361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6134424210353822678257925 1150204539441341752173361)
                    ·
                      rfl

theorem cell22_3360023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_3360023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360023 prefixEnd_3360023 := by exact prefixLift 3360023
  have htrace : WordTrace (prefixWord ++ tailWord_3360023) baseStart_3360023 baseEnd_3360023 := by
    simpa [prefixWord, tailWord_3360023, baseEnd_3360023] using wordTrace_append hprefix tailTrace_3360023
  have hstable : (prefixWord ++ tailWord_3360023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360023).length < 2 ^ (prefixWord ++ tailWord_3360023).sum := by decide
  have hdescent : baseEnd_3360023 < baseStart_3360023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360036 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_3360036 : Nat := 118140960795 + 3360036 * 2 ^ 59
def prefixEnd_3360036 : Nat := 4983230072969 + 3 ^ 40 * 3360036 * 2
def baseEnd_3360036 : Nat := 1150208989607014051598321

theorem tailTrace_3360036 : CollatzResearch.WordTrace tailWord_3360036 prefixEnd_3360036 1150208989607014051598321 := by
  unfold tailWord_3360036
  simp only [CollatzResearch.WordTrace]
  refine ⟨61275290427585447653749981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81700387236780596871666641 61275290427585447653749981)
  ·
    refine ⟨22978233910344542870156243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61275290427585447653749981 22978233910344542870156243)
    ·
      refine ⟨34467350865516814305234365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22978233910344542870156243 34467350865516814305234365)
      ·
        refine ⟨12925256574568805364462887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34467350865516814305234365 12925256574568805364462887)
        ·
          refine ⟨19387884861853208046694331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12925256574568805364462887 19387884861853208046694331)
          ·
            refine ⟨29081827292779812070041497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19387884861853208046694331 29081827292779812070041497)
            ·
              refine ⟨21811370469584859052531123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29081827292779812070041497 21811370469584859052531123)
              ·
                refine ⟨32717055704377288578796685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21811370469584859052531123 32717055704377288578796685)
                ·
                  refine ⟨12268895889141483217048757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32717055704377288578796685 12268895889141483217048757)
                  ·
                    refine ⟨1150208989607014051598321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12268895889141483217048757 1150208989607014051598321)
                    ·
                      rfl

theorem cell22_3360036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_3360036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360036 prefixEnd_3360036 := by exact prefixLift 3360036
  have htrace : WordTrace (prefixWord ++ tailWord_3360036) baseStart_3360036 baseEnd_3360036 := by
    simpa [prefixWord, tailWord_3360036, baseEnd_3360036] using wordTrace_append hprefix tailTrace_3360036
  have hstable : (prefixWord ++ tailWord_3360036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360036).length < 2 ^ (prefixWord ++ tailWord_3360036).sum := by decide
  have hdescent : baseEnd_3360036 < baseStart_3360036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360051 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 4, 4]
def baseStart_3360051 : Nat := 118140960795 + 3360051 * 2 ^ 59
def prefixEnd_3360051 : Nat := 4983230072969 + 3 ^ 40 * 3360051 * 2
def baseEnd_3360051 : Nat := 1150214124413559012473275

theorem tailTrace_3360051 : CollatzResearch.WordTrace tailWord_3360051 prefixEnd_3360051 1150214124413559012473275 := by
  unfold tailWord_3360051
  simp only [CollatzResearch.WordTrace]
  refine ⟨122551127950116552869296007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81700751966744368579530671 122551127950116552869296007)
  ·
    refine ⟨183826691925174829303944011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122551127950116552869296007 183826691925174829303944011)
    ·
      refine ⟨275740037887762243955916017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183826691925174829303944011 275740037887762243955916017)
      ·
        refine ⟨206805028415821682966937013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275740037887762243955916017 206805028415821682966937013)
        ·
          refine ⟨19387971413983282778150345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 206805028415821682966937013 19387971413983282778150345)
          ·
            refine ⟨14540978560487462083612759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19387971413983282778150345 14540978560487462083612759)
            ·
              refine ⟨21811467840731193125419139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14540978560487462083612759 21811467840731193125419139)
              ·
                refine ⟨32717201761096789688128709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21811467840731193125419139 32717201761096789688128709)
                ·
                  refine ⟨6134475330205648066524133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32717201761096789688128709 6134475330205648066524133)
                  ·
                    refine ⟨1150214124413559012473275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6134475330205648066524133 1150214124413559012473275)
                    ·
                      rfl

theorem cell22_3360051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 4].length) (baseStart_3360051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360051 prefixEnd_3360051 := by exact prefixLift 3360051
  have htrace : WordTrace (prefixWord ++ tailWord_3360051) baseStart_3360051 baseEnd_3360051 := by
    simpa [prefixWord, tailWord_3360051, baseEnd_3360051] using wordTrace_append hprefix tailTrace_3360051
  have hstable : (prefixWord ++ tailWord_3360051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360051).length < 2 ^ (prefixWord ++ tailWord_3360051).sum := by decide
  have hdescent : baseEnd_3360051 < baseStart_3360051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360053 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 4, 3]
def baseStart_3360053 : Nat := 118140960795 + 3360053 * 2 ^ 59
def prefixEnd_3360053 : Nat := 4983230072969 + 3 ^ 40 * 3360053 * 2
def baseEnd_3360053 : Nat := 1150214809054431673923269

theorem tailTrace_3360053 : CollatzResearch.WordTrace tailWord_3360053 prefixEnd_3360053 1150214809054431673923269 := by
  unfold tailWord_3360053
  simp only [CollatzResearch.WordTrace]
  refine ⟨122551200896109307210868813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81700800597406204807245875 122551200896109307210868813)
  ·
    refine ⟨45956700336040990204075805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122551200896109307210868813 45956700336040990204075805)
    ·
      refine ⟨17233762626015371326528427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45956700336040990204075805 17233762626015371326528427)
      ·
        refine ⟨25850643939023056989792641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17233762626015371326528427 25850643939023056989792641)
        ·
          refine ⟨19387982954267292742344481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25850643939023056989792641 19387982954267292742344481)
          ·
            refine ⟨14540987215700469556758361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19387982954267292742344481 14540987215700469556758361)
            ·
              refine ⟨10905740411775352167568771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14540987215700469556758361 10905740411775352167568771)
              ·
                refine ⟨16358610617663028251353157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10905740411775352167568771 16358610617663028251353157)
                ·
                  refine ⟨3067239490811817797128717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16358610617663028251353157 3067239490811817797128717)
                  ·
                    refine ⟨1150214809054431673923269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3067239490811817797128717 1150214809054431673923269)
                    ·
                      rfl

theorem cell22_3360053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_3360053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360053 prefixEnd_3360053 := by exact prefixLift 3360053
  have htrace : WordTrace (prefixWord ++ tailWord_3360053) baseStart_3360053 baseEnd_3360053 := by
    simpa [prefixWord, tailWord_3360053, baseEnd_3360053] using wordTrace_append hprefix tailTrace_3360053
  have hstable : (prefixWord ++ tailWord_3360053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360053).length < 2 ^ (prefixWord ++ tailWord_3360053).sum := by decide
  have hdescent : baseEnd_3360053 < baseStart_3360053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360218 : List Nat := [3, 1, 1, 2, 3, 4, 8]
def baseStart_3360218 : Nat := 118140960795 + 3360218 * 2 ^ 59
def prefixEnd_3360218 : Nat := 4983230072969 + 3 ^ 40 * 3360218 * 2
def baseEnd_3360218 : Nat := 42602640441719490501769

theorem tailTrace_3360218 : CollatzResearch.WordTrace tailWord_3360218 prefixEnd_3360218 42602640441719490501769 := by
  unfold tailWord_3360218
  simp only [CollatzResearch.WordTrace]
  refine ⟨30639304735127885097656327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81704812627007693593750205 30639304735127885097656327)
  ·
    refine ⟨45958957102691827646484491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30639304735127885097656327 45958957102691827646484491)
    ·
      refine ⟨68938435654037741469726737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45958957102691827646484491 68938435654037741469726737)
      ·
        refine ⟨51703826740528306102295053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68938435654037741469726737 51703826740528306102295053)
        ·
          refine ⟨19388935027698114788360645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51703826740528306102295053 19388935027698114788360645)
          ·
            refine ⟨3635425317693396522817621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19388935027698114788360645 3635425317693396522817621)
            ·
              refine ⟨42602640441719490501769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3635425317693396522817621 42602640441719490501769)
              ·
                rfl

theorem cell22_3360218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 8].length) (baseStart_3360218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360218 prefixEnd_3360218 := by exact prefixLift 3360218
  have htrace : WordTrace (prefixWord ++ tailWord_3360218) baseStart_3360218 baseEnd_3360218 := by
    simpa [prefixWord, tailWord_3360218, baseEnd_3360218] using wordTrace_append hprefix tailTrace_3360218
  have hstable : (prefixWord ++ tailWord_3360218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360218).length < 2 ^ (prefixWord ++ tailWord_3360218).sum := by decide
  have hdescent : baseEnd_3360218 < baseStart_3360218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360254 : List Nat := [4, 2, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_3360254 : Nat := 118140960795 + 3360254 * 2 ^ 59
def prefixEnd_3360254 : Nat := 4983230072969 + 3 ^ 40 * 3360254 * 2
def baseEnd_3360254 : Nat := 1150283615462134149647653

theorem tailTrace_3360254 : CollatzResearch.WordTrace tailWord_3360254 prefixEnd_3360254 1150283615462134149647653 := by
  unfold tailWord_3360254
  simp only [CollatzResearch.WordTrace]
  refine ⟨15319816496047639817366977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81705687978920745692623877 15319816496047639817366977)
  ·
    refine ⟨11489862372035729863025233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15319816496047639817366977 11489862372035729863025233)
    ·
      refine ⟨8617396779026797397268925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11489862372035729863025233 8617396779026797397268925)
      ·
        refine ⟨3231523792135049023975847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8617396779026797397268925 3231523792135049023975847)
        ·
          refine ⟨4847285688202573535963771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3231523792135049023975847 4847285688202573535963771)
          ·
            refine ⟨7270928532303860303945657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4847285688202573535963771 7270928532303860303945657)
            ·
              refine ⟨5453196399227895227959243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7270928532303860303945657 5453196399227895227959243)
              ·
                refine ⟨8179794598841842841938865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5453196399227895227959243 8179794598841842841938865)
                ·
                  refine ⟨6134845949131382131454149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8179794598841842841938865 6134845949131382131454149)
                  ·
                    refine ⟨1150283615462134149647653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6134845949131382131454149 1150283615462134149647653)
                    ·
                      rfl

theorem cell22_3360254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_3360254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360254 prefixEnd_3360254 := by exact prefixLift 3360254
  have htrace : WordTrace (prefixWord ++ tailWord_3360254) baseStart_3360254 baseEnd_3360254 := by
    simpa [prefixWord, tailWord_3360254, baseEnd_3360254] using wordTrace_append hprefix tailTrace_3360254
  have hstable : (prefixWord ++ tailWord_3360254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360254).length < 2 ^ (prefixWord ++ tailWord_3360254).sum := by decide
  have hdescent : baseEnd_3360254 < baseStart_3360254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360286 : List Nat := [4, 3, 3, 1, 1, 2, 1, 7]
def baseStart_3360286 : Nat := 118140960795 + 3360286 * 2 ^ 59
def prefixEnd_3360286 : Nat := 4983230072969 + 3 ^ 40 * 3360286 * 2
def baseEnd_3360286 : Nat := 127810507746232970316395

theorem tailTrace_3360286 : CollatzResearch.WordTrace tailWord_3360286 prefixEnd_3360286 127810507746232970316395 := by
  unfold tailWord_3360286
  simp only [CollatzResearch.WordTrace]
  refine ⟨15319962388033148500512589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81706466069510125336067141 15319962388033148500512589)
  ·
    refine ⟨5744985895512430687692221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15319962388033148500512589 5744985895512430687692221)
    ·
      refine ⟨2154369710817161507884583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5744985895512430687692221 2154369710817161507884583)
      ·
        refine ⟨3231554566225742261826875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2154369710817161507884583 3231554566225742261826875)
        ·
          refine ⟨4847331849338613392740313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3231554566225742261826875 4847331849338613392740313)
          ·
            refine ⟨3635498887003960044555235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4847331849338613392740313 3635498887003960044555235)
            ·
              refine ⟨5453248330505940066832853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3635498887003960044555235 5453248330505940066832853)
              ·
                refine ⟨127810507746232970316395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5453248330505940066832853 127810507746232970316395)
                ·
                  rfl

theorem cell22_3360286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_3360286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360286 prefixEnd_3360286 := by exact prefixLift 3360286
  have htrace : WordTrace (prefixWord ++ tailWord_3360286) baseStart_3360286 baseEnd_3360286 := by
    simpa [prefixWord, tailWord_3360286, baseEnd_3360286] using wordTrace_append hprefix tailTrace_3360286
  have hstable : (prefixWord ++ tailWord_3360286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360286).length < 2 ^ (prefixWord ++ tailWord_3360286).sum := by decide
  have hdescent : baseEnd_3360286 < baseStart_3360286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360327 : List Nat := [1, 1, 4, 1, 5, 1, 1, 3, 1, 4]
def baseStart_3360327 : Nat := 118140960795 + 3360327 * 2 ^ 59
def prefixEnd_3360327 : Nat := 4983230072969 + 3 ^ 40 * 3360327 * 2
def baseEnd_3360327 : Nat := 1150308604853986292572429

theorem tailTrace_3360327 : CollatzResearch.WordTrace tailWord_3360327 prefixEnd_3360327 1150308604853986292572429 := by
  unfold tailWord_3360327
  simp only [CollatzResearch.WordTrace]
  refine ⟨122561194497116652006343235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81707462998077768004228823 122561194497116652006343235)
  ·
    refine ⟨183841791745674978009514853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122561194497116652006343235 183841791745674978009514853)
    ·
      refine ⟨34470335952314058376784035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183841791745674978009514853 34470335952314058376784035)
      ·
        refine ⟨51705503928471087565176053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34470335952314058376784035 51705503928471087565176053)
        ·
          refine ⟨4847390993294164459235255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51705503928471087565176053 4847390993294164459235255)
          ·
            refine ⟨7271086489941246688852883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4847390993294164459235255 7271086489941246688852883)
            ·
              refine ⟨10906629734911870033279325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7271086489941246688852883 10906629734911870033279325)
              ·
                refine ⟨4089986150591951262479747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10906629734911870033279325 4089986150591951262479747)
                ·
                  refine ⟨6134979225887926893719621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4089986150591951262479747 6134979225887926893719621)
                  ·
                    refine ⟨1150308604853986292572429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6134979225887926893719621 1150308604853986292572429)
                    ·
                      rfl

theorem cell22_3360327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_3360327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360327 prefixEnd_3360327 := by exact prefixLift 3360327
  have htrace : WordTrace (prefixWord ++ tailWord_3360327) baseStart_3360327 baseEnd_3360327 := by
    simpa [prefixWord, tailWord_3360327, baseEnd_3360327] using wordTrace_append hprefix tailTrace_3360327
  have hstable : (prefixWord ++ tailWord_3360327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360327).length < 2 ^ (prefixWord ++ tailWord_3360327).sum := by decide
  have hdescent : baseEnd_3360327 < baseStart_3360327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360353 : List Nat := [1, 2, 3, 1, 1, 3, 2, 9]
def baseStart_3360353 : Nat := 118140960795 + 3360353 * 2 ^ 59
def prefixEnd_3360353 : Nat := 4983230072969 + 3 ^ 40 * 3360353 * 2
def baseEnd_3360353 : Nat := 127813056131703432380261

theorem tailTrace_3360353 : CollatzResearch.WordTrace tailWord_3360353 prefixEnd_3360353 127813056131703432380261 := by
  unfold tailWord_3360353
  simp only [CollatzResearch.WordTrace]
  refine ⟨122562142795022458446789713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81708095196681638964526475 122562142795022458446789713)
  ·
    refine ⟨91921607096266843835092285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122562142795022458446789713 91921607096266843835092285)
    ·
      refine ⟨34470602661100066438159607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91921607096266843835092285 34470602661100066438159607)
      ·
        refine ⟨51705903991650099657239411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34470602661100066438159607 51705903991650099657239411)
        ·
          refine ⟨77558855987475149485859117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51705903991650099657239411 77558855987475149485859117)
          ·
            refine ⟨29084570995303181057197169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77558855987475149485859117 29084570995303181057197169)
            ·
              refine ⟨21813428246477385792897877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29084570995303181057197169 21813428246477385792897877)
              ·
                refine ⟨127813056131703432380261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21813428246477385792897877 127813056131703432380261)
                ·
                  rfl

theorem cell22_3360353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 9].length) (baseStart_3360353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360353 prefixEnd_3360353 := by exact prefixLift 3360353
  have htrace : WordTrace (prefixWord ++ tailWord_3360353) baseStart_3360353 baseEnd_3360353 := by
    simpa [prefixWord, tailWord_3360353, baseEnd_3360353] using wordTrace_append hprefix tailTrace_3360353
  have hstable : (prefixWord ++ tailWord_3360353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360353).length < 2 ^ (prefixWord ++ tailWord_3360353).sum := by decide
  have hdescent : baseEnd_3360353 < baseStart_3360353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360357 : List Nat := [1, 3, 1, 3, 3, 3, 1, 1, 1, 5]
def baseStart_3360357 : Nat := 118140960795 + 3360357 * 2 ^ 59
def prefixEnd_3360357 : Nat := 4983230072969 + 3 ^ 40 * 3360357 * 2
def baseEnd_3360357 : Nat := 1150318874467076214322337

theorem tailTrace_3360357 : CollatzResearch.WordTrace tailWord_3360357 prefixEnd_3360357 1150318874467076214322337 := by
  unfold tailWord_3360357
  simp only [CollatzResearch.WordTrace]
  refine ⟨122562288687007967129935325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81708192458005311419956883 122562288687007967129935325)
  ·
    refine ⟨45960858257627987673725747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122562288687007967129935325 45960858257627987673725747)
    ·
      refine ⟨68941287386441981510588621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45960858257627987673725747 68941287386441981510588621)
      ·
        refine ⟨25852982769915743066470733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68941287386441981510588621 25852982769915743066470733)
        ·
          refine ⟨9694868538718403649926525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25852982769915743066470733 9694868538718403649926525)
          ·
            refine ⟨3635575702019401368722447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9694868538718403649926525 3635575702019401368722447)
            ·
              refine ⟨5453363553029102053083671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3635575702019401368722447 5453363553029102053083671)
              ·
                refine ⟨8180045329543653079625507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5453363553029102053083671 8180045329543653079625507)
                ·
                  refine ⟨12270067994315479619438261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8180045329543653079625507 12270067994315479619438261)
                  ·
                    refine ⟨1150318874467076214322337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12270067994315479619438261 1150318874467076214322337)
                    ·
                      rfl

theorem cell22_3360357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_3360357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360357 prefixEnd_3360357 := by exact prefixLift 3360357
  have htrace : WordTrace (prefixWord ++ tailWord_3360357) baseStart_3360357 baseEnd_3360357 := by
    simpa [prefixWord, tailWord_3360357, baseEnd_3360357] using wordTrace_append hprefix tailTrace_3360357
  have hstable : (prefixWord ++ tailWord_3360357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360357).length < 2 ^ (prefixWord ++ tailWord_3360357).sum := by decide
  have hdescent : baseEnd_3360357 < baseStart_3360357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360370 : List Nat := [3, 2, 1, 2, 3, 2, 1, 8]
def baseStart_3360370 : Nat := 118140960795 + 3360370 * 2 ^ 59
def prefixEnd_3360370 : Nat := 4983230072969 + 3 ^ 40 * 3360370 * 2
def baseEnd_3360370 : Nat := 127813702736972057083033

theorem tailTrace_3360370 : CollatzResearch.WordTrace tailWord_3360370 prefixEnd_3360370 127813702736972057083033 := by
  unfold tailWord_3360370
  simp only [CollatzResearch.WordTrace]
  refine ⟨30640690708990217587539641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81708508557307246900105709 30640690708990217587539641)
  ·
    refine ⟨22980518031742663190654731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30640690708990217587539641 22980518031742663190654731)
    ·
      refine ⟨34470777047613994785982097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22980518031742663190654731 34470777047613994785982097)
      ·
        refine ⟨25853082785710496089486573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34470777047613994785982097 25853082785710496089486573)
        ·
          refine ⟨9694906044641436033557465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25853082785710496089486573 9694906044641436033557465)
          ·
            refine ⟨7271179533481077025168099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9694906044641436033557465 7271179533481077025168099)
            ·
              refine ⟨10906769300221615537752149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7271179533481077025168099 10906769300221615537752149)
              ·
                refine ⟨127813702736972057083033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10906769300221615537752149 127813702736972057083033)
                ·
                  rfl

theorem cell22_3360370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 8].length) (baseStart_3360370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360370 prefixEnd_3360370 := by exact prefixLift 3360370
  have htrace : WordTrace (prefixWord ++ tailWord_3360370) baseStart_3360370 baseEnd_3360370 := by
    simpa [prefixWord, tailWord_3360370, baseEnd_3360370] using wordTrace_append hprefix tailTrace_3360370
  have hstable : (prefixWord ++ tailWord_3360370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360370).length < 2 ^ (prefixWord ++ tailWord_3360370).sum := by decide
  have hdescent : baseEnd_3360370 < baseStart_3360370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360494 : List Nat := [4, 1, 2, 1, 1, 2, 4, 3, 4]
def baseStart_3360494 : Nat := 118140960795 + 3360494 * 2 ^ 59
def prefixEnd_3360494 : Nat := 4983230072969 + 3 ^ 40 * 3360494 * 2
def baseEnd_3360494 : Nat := 383455257455617841215639

theorem tailTrace_3360494 : CollatzResearch.WordTrace tailWord_3360494 prefixEnd_3360494 383455257455617841215639 := by
  unfold tailWord_3360494
  simp only [CollatzResearch.WordTrace]
  refine ⟨15320910685938954940959067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81711523658341093018448357 15320910685938954940959067)
  ·
    refine ⟨22981366028908432411438601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15320910685938954940959067 22981366028908432411438601)
    ·
      refine ⟨17236024521681324308578951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22981366028908432411438601 17236024521681324308578951)
      ·
        refine ⟨25854036782521986462868427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17236024521681324308578951 25854036782521986462868427)
        ·
          refine ⟨38781055173782979694302641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25854036782521986462868427 38781055173782979694302641)
          ·
            refine ⟨29085791380337234770726981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38781055173782979694302641 29085791380337234770726981)
            ·
              refine ⟨5453585883813231519511309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29085791380337234770726981 5453585883813231519511309)
              ·
                refine ⟨2045094706429961819816741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5453585883813231519511309 2045094706429961819816741)
                ·
                  refine ⟨383455257455617841215639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2045094706429961819816741 383455257455617841215639)
                  ·
                    rfl

theorem cell22_3360494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_3360494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360494 prefixEnd_3360494 := by exact prefixLift 3360494
  have htrace : WordTrace (prefixWord ++ tailWord_3360494) baseStart_3360494 baseEnd_3360494 := by
    simpa [prefixWord, tailWord_3360494, baseEnd_3360494] using wordTrace_append hprefix tailTrace_3360494
  have hstable : (prefixWord ++ tailWord_3360494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360494).length < 2 ^ (prefixWord ++ tailWord_3360494).sum := by decide
  have hdescent : baseEnd_3360494 < baseStart_3360494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360584 : List Nat := [2, 1, 3, 1, 1, 4, 4, 1, 5]
def baseStart_3360584 : Nat := 118140960795 + 3360584 * 2 ^ 59
def prefixEnd_3360584 : Nat := 4983230072969 + 3 ^ 40 * 3360584 * 2
def baseEnd_3360584 : Nat := 383465527068707762965547

theorem tailTrace_3360584 : CollatzResearch.WordTrace tailWord_3360584 prefixEnd_3360584 383465527068707762965547 := by
  unfold tailWord_3360584
  simp only [CollatzResearch.WordTrace]
  refine ⟨61285284028592792449224403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81713712038123723265632537 61285284028592792449224403)
  ·
    refine ⟨91927926042889188673836605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61285284028592792449224403 91927926042889188673836605)
    ·
      refine ⟨34472972266083445752688727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91927926042889188673836605 34472972266083445752688727)
      ·
        refine ⟨51709458399125168629033091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34472972266083445752688727 51709458399125168629033091)
        ·
          refine ⟨77564187598687752943549637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51709458399125168629033091 77564187598687752943549637)
          ·
            refine ⟨14543285174753953676915557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77564187598687752943549637 14543285174753953676915557)
            ·
              refine ⟨2726865970266366314421667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14543285174753953676915557 2726865970266366314421667)
              ·
                refine ⟨4090298955399549471632501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2726865970266366314421667 4090298955399549471632501)
                ·
                  refine ⟨383465527068707762965547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4090298955399549471632501 383465527068707762965547)
                  ·
                    rfl

theorem cell22_3360584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 5].length) (baseStart_3360584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360584 prefixEnd_3360584 := by exact prefixLift 3360584
  have htrace : WordTrace (prefixWord ++ tailWord_3360584) baseStart_3360584 baseEnd_3360584 := by
    simpa [prefixWord, tailWord_3360584, baseEnd_3360584] using wordTrace_append hprefix tailTrace_3360584
  have hstable : (prefixWord ++ tailWord_3360584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360584).length < 2 ^ (prefixWord ++ tailWord_3360584).sum := by decide
  have hdescent : baseEnd_3360584 < baseStart_3360584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360674 : List Nat := [3, 3, 1, 2, 3, 1, 9]
def baseStart_3360674 : Nat := 118140960795 + 3360674 * 2 ^ 59
def prefixEnd_3360674 : Nat := 4983230072969 + 3 ^ 40 * 3360674 * 2
def baseEnd_3360674 : Nat := 42608421853533076079495

theorem tailTrace_3360674 : CollatzResearch.WordTrace tailWord_3360674 prefixEnd_3360674 42608421853533076079495 := by
  unfold tailWord_3360674
  simp only [CollatzResearch.WordTrace]
  refine ⟨30643462656714882567306269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81715900417906353512816717 30643462656714882567306269)
  ·
    refine ⟨11491298496268080962739851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30643462656714882567306269 11491298496268080962739851)
    ·
      refine ⟨17236947744402121444109777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11491298496268080962739851 17236947744402121444109777)
      ·
        refine ⟨12927710808301591083082333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17236947744402121444109777 12927710808301591083082333)
        ·
          refine ⟨4847891553113096656155875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12927710808301591083082333 4847891553113096656155875)
          ·
            refine ⟨7271837329669644984233813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4847891553113096656155875 7271837329669644984233813)
            ·
              refine ⟨42608421853533076079495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7271837329669644984233813 42608421853533076079495)
              ·
                rfl

theorem cell22_3360674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 9].length) (baseStart_3360674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360674 prefixEnd_3360674 := by exact prefixLift 3360674
  have htrace : WordTrace (prefixWord ++ tailWord_3360674) baseStart_3360674 baseEnd_3360674 := by
    simpa [prefixWord, tailWord_3360674, baseEnd_3360674] using wordTrace_append hprefix tailTrace_3360674
  have hstable : (prefixWord ++ tailWord_3360674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360674).length < 2 ^ (prefixWord ++ tailWord_3360674).sum := by decide
  have hdescent : baseEnd_3360674 < baseStart_3360674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360753 : List Nat := [1, 2, 2, 2, 5, 2, 2, 1, 5]
def baseStart_3360753 : Nat := 118140960795 + 3360753 * 2 ^ 59
def prefixEnd_3360753 : Nat := 4983230072969 + 3 ^ 40 * 3360753 * 2
def baseEnd_3360753 : Nat := 383484811119954393807041

theorem tailTrace_3360753 : CollatzResearch.WordTrace tailWord_3360753 prefixEnd_3360753 383484811119954393807041 := by
  unfold tailWord_3360753
  simp only [CollatzResearch.WordTrace]
  refine ⟨122576731993573326761350913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81717821329048884507567275 122576731993573326761350913)
  ·
    refine ⟨91932548995179995071013185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122576731993573326761350913 91932548995179995071013185)
    ·
      refine ⟨68949411746384996303259889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91932548995179995071013185 68949411746384996303259889)
      ·
        refine ⟨51712058809788747227444917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68949411746384996303259889 51712058809788747227444917)
        ·
          refine ⟨4848005513417695052572961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51712058809788747227444917 4848005513417695052572961)
          ·
            refine ⟨3636004135063271289429721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4848005513417695052572961 3636004135063271289429721)
            ·
              refine ⟨2727003101297453467072291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3636004135063271289429721 2727003101297453467072291)
              ·
                refine ⟨4090504651946180200608437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2727003101297453467072291 4090504651946180200608437)
                ·
                  refine ⟨383484811119954393807041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4090504651946180200608437 383484811119954393807041)
                  ·
                    rfl

theorem cell22_3360753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 5].length) (baseStart_3360753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360753 prefixEnd_3360753 := by exact prefixLift 3360753
  have htrace : WordTrace (prefixWord ++ tailWord_3360753) baseStart_3360753 baseEnd_3360753 := by
    simpa [prefixWord, tailWord_3360753, baseEnd_3360753] using wordTrace_append hprefix tailTrace_3360753
  have hstable : (prefixWord ++ tailWord_3360753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360753).length < 2 ^ (prefixWord ++ tailWord_3360753).sum := by decide
  have hdescent : baseEnd_3360753 < baseStart_3360753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360779 : List Nat := [1, 1, 1, 1, 6, 1, 3, 2, 1, 5]
def baseStart_3360779 : Nat := 118140960795 + 3360779 * 2 ^ 59
def prefixEnd_3360779 : Nat := 4983230072969 + 3 ^ 40 * 3360779 * 2
def baseEnd_3360779 : Nat := 1150463333691207780271043

theorem tailTrace_3360779 : CollatzResearch.WordTrace tailWord_3360779 prefixEnd_3360779 1150463333691207780271043 := by
  unfold tailWord_3360779
  simp only [CollatzResearch.WordTrace]
  refine ⟨122577680291479133201797391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81718453527652755467864927 122577680291479133201797391)
  ·
    refine ⟨183866520437218699802696087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122577680291479133201797391 183866520437218699802696087)
    ·
      refine ⟨275799780655828049704044131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183866520437218699802696087 275799780655828049704044131)
      ·
        refine ⟨413699670983742074556066197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275799780655828049704044131 413699670983742074556066197)
        ·
          refine ⟨19392172077362909744815603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 413699670983742074556066197 19392172077362909744815603)
          ·
            refine ⟨29088258116044364617223405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19392172077362909744815603 29088258116044364617223405)
            ·
              refine ⟨10908096793516636731458777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29088258116044364617223405 10908096793516636731458777)
              ·
                refine ⟨8181072595137477548594083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10908096793516636731458777 8181072595137477548594083)
                ·
                  refine ⟨12271608892706216322891125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8181072595137477548594083 12271608892706216322891125)
                  ·
                    refine ⟨1150463333691207780271043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12271608892706216322891125 1150463333691207780271043)
                    ·
                      rfl

theorem cell22_3360779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 5].length) (baseStart_3360779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360779 prefixEnd_3360779 := by exact prefixLift 3360779
  have htrace : WordTrace (prefixWord ++ tailWord_3360779) baseStart_3360779 baseEnd_3360779 := by
    simpa [prefixWord, tailWord_3360779, baseEnd_3360779] using wordTrace_append hprefix tailTrace_3360779
  have hstable : (prefixWord ++ tailWord_3360779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360779).length < 2 ^ (prefixWord ++ tailWord_3360779).sum := by decide
  have hdescent : baseEnd_3360779 < baseStart_3360779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360858 : List Nat := [3, 1, 1, 2, 1, 1, 3, 6, 1, 3]
def baseStart_3360858 : Nat := 118140960795 + 3360858 * 2 ^ 59
def prefixEnd_3360858 : Nat := 4983230072969 + 3 ^ 40 * 3360858 * 2
def baseEnd_3360858 : Nat := 1150490377005677907545801

theorem tailTrace_3360858 : CollatzResearch.WordTrace tailWord_3360858 prefixEnd_3360858 1150490377005677907545801 := by
  unfold tailWord_3360858
  simp only [CollatzResearch.WordTrace]
  refine ⟨30645140414548232423480807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81720374438795286462615485 30645140414548232423480807)
  ·
    refine ⟨45967710621822348635221211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30645140414548232423480807 45967710621822348635221211)
    ·
      refine ⟨68951565932733522952831817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45967710621822348635221211 68951565932733522952831817)
      ·
        refine ⟨51713674449550142214623863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68951565932733522952831817 51713674449550142214623863)
        ·
          refine ⟨77570511674325213321935795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51713674449550142214623863 77570511674325213321935795)
          ·
            refine ⟨116355767511487819982903693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77570511674325213321935795 116355767511487819982903693)
            ·
              refine ⟨43633412816807932493588885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116355767511487819982903693 43633412816807932493588885)
              ·
                refine ⟨2045316225787871835636979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43633412816807932493588885 2045316225787871835636979)
                ·
                  refine ⟨3067974338681807753455469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2045316225787871835636979 3067974338681807753455469)
                  ·
                    refine ⟨1150490377005677907545801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3067974338681807753455469 1150490377005677907545801)
                    ·
                      rfl

theorem cell22_3360858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 1, 3].length) (baseStart_3360858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360858 prefixEnd_3360858 := by exact prefixLift 3360858
  have htrace : WordTrace (prefixWord ++ tailWord_3360858) baseStart_3360858 baseEnd_3360858 := by
    simpa [prefixWord, tailWord_3360858, baseEnd_3360858] using wordTrace_append hprefix tailTrace_3360858
  have hstable : (prefixWord ++ tailWord_3360858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360858).length < 2 ^ (prefixWord ++ tailWord_3360858).sum := by decide
  have hdescent : baseEnd_3360858 < baseStart_3360858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360922 : List Nat := [3, 1, 1, 5, 3, 1, 2, 1, 5]
def baseStart_3360922 : Nat := 118140960795 + 3360922 * 2 ^ 59
def prefixEnd_3360922 : Nat := 4983230072969 + 3 ^ 40 * 3360922 * 2
def baseEnd_3360922 : Nat := 383504095171201024648535

theorem tailTrace_3360922 : CollatzResearch.WordTrace tailWord_3360922 prefixEnd_3360922 383504095171201024648535 := by
  unfold tailWord_3360922
  simp only [CollatzResearch.WordTrace]
  refine ⟨30645723982490267156063255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81721930619974045749502013 30645723982490267156063255)
  ·
    refine ⟨45968585973735400734094883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30645723982490267156063255 45968585973735400734094883)
    ·
      refine ⟨68952878960603101101142325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45968585973735400734094883 68952878960603101101142325)
      ·
        refine ⟨6464332402556540728232093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68952878960603101101142325 6464332402556540728232093)
        ·
          refine ⟨2424124650958702773087035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6464332402556540728232093 2424124650958702773087035)
          ·
            refine ⟨3636186976438054159630553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2424124650958702773087035 3636186976438054159630553)
            ·
              refine ⟨2727140232328540619722915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3636186976438054159630553 2727140232328540619722915)
              ·
                refine ⟨4090710348492810929584373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2727140232328540619722915 4090710348492810929584373)
                ·
                  refine ⟨383504095171201024648535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4090710348492810929584373 383504095171201024648535)
                  ·
                    rfl

theorem cell22_3360922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 5].length) (baseStart_3360922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360922 prefixEnd_3360922 := by exact prefixLift 3360922
  have htrace : WordTrace (prefixWord ++ tailWord_3360922) baseStart_3360922 baseEnd_3360922 := by
    simpa [prefixWord, tailWord_3360922, baseEnd_3360922] using wordTrace_append hprefix tailTrace_3360922
  have hstable : (prefixWord ++ tailWord_3360922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360922).length < 2 ^ (prefixWord ++ tailWord_3360922).sum := by decide
  have hdescent : baseEnd_3360922 < baseStart_3360922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360961 : List Nat := [1, 2, 6, 1, 12]
def baseStart_3360961 : Nat := 118140960795 + 3360961 * 2 ^ 59
def prefixEnd_3360961 : Nat := 4983230072969 + 3 ^ 40 * 3360961 * 2
def baseEnd_3360961 : Nat := 4734673399220658321895

theorem tailTrace_3360961 : CollatzResearch.WordTrace tailWord_3360961 prefixEnd_3360961 4734673399220658321895 := by
  unfold tailWord_3360961
  simp only [CollatzResearch.WordTrace]
  refine ⟨122584318376819778284922737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81722878917879852189948491 122584318376819778284922737)
  ·
    refine ⟨91938238782614833713692053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122584318376819778284922737 91938238782614833713692053)
    ·
      refine ⟨4309604942935070330329315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 91938238782614833713692053 4309604942935070330329315)
      ·
        refine ⟨6464407414402605495493973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4309604942935070330329315 6464407414402605495493973)
        ·
          refine ⟨4734673399220658321895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6464407414402605495493973 4734673399220658321895)
          ·
            rfl

theorem cell22_3360961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 12].length) (baseStart_3360961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360961 prefixEnd_3360961 := by exact prefixLift 3360961
  have htrace : WordTrace (prefixWord ++ tailWord_3360961) baseStart_3360961 baseEnd_3360961 := by
    simpa [prefixWord, tailWord_3360961, baseEnd_3360961] using wordTrace_append hprefix tailTrace_3360961
  have hstable : (prefixWord ++ tailWord_3360961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360961).length < 2 ^ (prefixWord ++ tailWord_3360961).sum := by decide
  have hdescent : baseEnd_3360961 < baseStart_3360961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360976 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 9, 3]
def baseStart_3360976 : Nat := 118140960795 + 3360976 * 2 ^ 59
def prefixEnd_3360976 : Nat := 4983230072969 + 3 ^ 40 * 3360976 * 2
def baseEnd_3360976 : Nat := 1150530770817164933095439

theorem tailTrace_3360976 : CollatzResearch.WordTrace tailWord_3360976 prefixEnd_3360976 1150530770817164933095439 := by
  unfold tailWord_3360976
  simp only [CollatzResearch.WordTrace]
  refine ⟨61292432735882717923359391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81723243647843623897812521 61292432735882717923359391)
  ·
    refine ⟨91938649103824076885039087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61292432735882717923359391 91938649103824076885039087)
    ·
      refine ⟨137907973655736115327558631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91938649103824076885039087 137907973655736115327558631)
      ·
        refine ⟨206861960483604172991337947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137907973655736115327558631 206861960483604172991337947)
        ·
          refine ⟨310292940725406259487006921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206861960483604172991337947 310292940725406259487006921)
          ·
            refine ⟨232719705544054694615255191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310292940725406259487006921 232719705544054694615255191)
            ·
              refine ⟨349079558316082041922882787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232719705544054694615255191 349079558316082041922882787)
              ·
                refine ⟨523619337474123062884324181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349079558316082041922882787 523619337474123062884324181)
                ·
                  refine ⟨3068082055512439821587837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 523619337474123062884324181 3068082055512439821587837)
                  ·
                    refine ⟨1150530770817164933095439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3068082055512439821587837 1150530770817164933095439)
                    ·
                      rfl

theorem cell22_3360976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 9, 3].length) (baseStart_3360976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360976 prefixEnd_3360976 := by exact prefixLift 3360976
  have htrace : WordTrace (prefixWord ++ tailWord_3360976) baseStart_3360976 baseEnd_3360976 := by
    simpa [prefixWord, tailWord_3360976, baseEnd_3360976] using wordTrace_append hprefix tailTrace_3360976
  have hstable : (prefixWord ++ tailWord_3360976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360976).length < 2 ^ (prefixWord ++ tailWord_3360976).sum := by decide
  have hdescent : baseEnd_3360976 < baseStart_3360976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360978 : List Nat := [3, 2, 2, 2, 1, 4, 1, 7]
def baseStart_3360978 : Nat := 118140960795 + 3360978 * 2 ^ 59
def prefixEnd_3360978 : Nat := 4983230072969 + 3 ^ 40 * 3360978 * 2
def baseEnd_3360978 : Nat := 127836828384226399393937

theorem tailTrace_3360978 : CollatzResearch.WordTrace tailWord_3360978 prefixEnd_3360978 127836828384226399393937 := by
  unfold tailWord_3360978
  simp only [CollatzResearch.WordTrace]
  refine ⟨30646234604439547547072897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81723292278505460125527725 30646234604439547547072897)
  ·
    refine ⟨22984675953329660660304673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30646234604439547547072897 22984675953329660660304673)
    ·
      refine ⟨17238506964997245495228505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22984675953329660660304673 17238506964997245495228505)
      ·
        refine ⟨12928880223747934121421379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17238506964997245495228505 12928880223747934121421379)
        ·
          refine ⟨19393320335621901182132069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12928880223747934121421379 19393320335621901182132069)
          ·
            refine ⟨3636247562929106471649763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19393320335621901182132069 3636247562929106471649763)
            ·
              refine ⟨5454371344393659707474645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3636247562929106471649763 5454371344393659707474645)
              ·
                refine ⟨127836828384226399393937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5454371344393659707474645 127836828384226399393937)
                ·
                  rfl

theorem cell22_3360978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 7].length) (baseStart_3360978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360978 prefixEnd_3360978 := by exact prefixLift 3360978
  have htrace : WordTrace (prefixWord ++ tailWord_3360978) baseStart_3360978 baseEnd_3360978 := by
    simpa [prefixWord, tailWord_3360978, baseEnd_3360978] using wordTrace_append hprefix tailTrace_3360978
  have hstable : (prefixWord ++ tailWord_3360978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360978).length < 2 ^ (prefixWord ++ tailWord_3360978).sum := by decide
  have hdescent : baseEnd_3360978 < baseStart_3360978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360982 : List Nat := [5, 2, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_3360982 : Nat := 118140960795 + 3360982 * 2 ^ 59
def prefixEnd_3360982 : Nat := 4983230072969 + 3 ^ 40 * 3360982 * 2
def baseEnd_3360982 : Nat := 1150532824739782917445421

theorem tailTrace_3360982 : CollatzResearch.WordTrace tailWord_3360982 prefixEnd_3360982 1150532824739782917445421 := by
  unfold tailWord_3360982
  simp only [CollatzResearch.WordTrace]
  refine ⟨7661567769358981179464825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81723389539829132580958133 7661567769358981179464825)
  ·
    refine ⟨5746175827019235884598619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7661567769358981179464825 5746175827019235884598619)
    ·
      refine ⟨8619263740528853826897929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5746175827019235884598619 8619263740528853826897929)
      ·
        refine ⟨6464447805396640370173447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8619263740528853826897929 6464447805396640370173447)
        ·
          refine ⟨9696671708094960555260171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6464447805396640370173447 9696671708094960555260171)
          ·
            refine ⟨14545007562142440832890257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9696671708094960555260171 14545007562142440832890257)
            ·
              refine ⟨10908755671606830624667693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14545007562142440832890257 10908755671606830624667693)
              ·
                refine ⟨4090783376852561484250385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10908755671606830624667693 4090783376852561484250385)
                ·
                  refine ⟨3068087532639421113187789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4090783376852561484250385 3068087532639421113187789)
                  ·
                    refine ⟨1150532824739782917445421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3068087532639421113187789 1150532824739782917445421)
                    ·
                      rfl

theorem cell22_3360982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_3360982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360982 prefixEnd_3360982 := by exact prefixLift 3360982
  have htrace : WordTrace (prefixWord ++ tailWord_3360982) baseStart_3360982 baseEnd_3360982 := by
    simpa [prefixWord, tailWord_3360982, baseEnd_3360982] using wordTrace_append hprefix tailTrace_3360982
  have hstable : (prefixWord ++ tailWord_3360982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360982).length < 2 ^ (prefixWord ++ tailWord_3360982).sum := by decide
  have hdescent : baseEnd_3360982 < baseStart_3360982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360993 : List Nat := [1, 2, 3, 1, 3, 1, 3, 2, 3, 3]
def baseStart_3360993 : Nat := 118140960795 + 3360993 * 2 ^ 59
def prefixEnd_3360993 : Nat := 4983230072969 + 3 ^ 40 * 3360993 * 2
def baseEnd_3360993 : Nat := 1150536590264582555420387

theorem tailTrace_3360993 : CollatzResearch.WordTrace tailWord_3360993 prefixEnd_3360993 1150536590264582555420387 := by
  unfold tailWord_3360993
  simp only [CollatzResearch.WordTrace]
  refine ⟨122585485512703847750087633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81723657008469231833391755 122585485512703847750087633)
  ·
    refine ⟨91939114134527885812565725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122585485512703847750087633 91939114134527885812565725)
    ·
      refine ⟨34477167800447957179712147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91939114134527885812565725 34477167800447957179712147)
      ·
        refine ⟨51715751700671935769568221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34477167800447957179712147 51715751700671935769568221)
        ·
          refine ⟨19393406887751975913588083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51715751700671935769568221 19393406887751975913588083)
          ·
            refine ⟨29090110331627963870382125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19393406887751975913588083 29090110331627963870382125)
            ·
              refine ⟨10908791374360486451393297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29090110331627963870382125 10908791374360486451393297)
              ·
                refine ⟨8181593530770364838544973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10908791374360486451393297 8181593530770364838544973)
                ·
                  refine ⟨3068097574038886814454365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8181593530770364838544973 3068097574038886814454365)
                  ·
                    refine ⟨1150536590264582555420387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3068097574038886814454365 1150536590264582555420387)
                    ·
                      rfl

theorem cell22_3360993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_3360993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360993 prefixEnd_3360993 := by exact prefixLift 3360993
  have htrace : WordTrace (prefixWord ++ tailWord_3360993) baseStart_3360993 baseEnd_3360993 := by
    simpa [prefixWord, tailWord_3360993, baseEnd_3360993] using wordTrace_append hprefix tailTrace_3360993
  have hstable : (prefixWord ++ tailWord_3360993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360993).length < 2 ^ (prefixWord ++ tailWord_3360993).sum := by decide
  have hdescent : baseEnd_3360993 < baseStart_3360993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360995 : List Nat := [1, 1, 1, 8, 1, 1, 3, 6]
def baseStart_3360995 : Nat := 118140960795 + 3360995 * 2 ^ 59
def prefixEnd_3360995 : Nat := 4983230072969 + 3 ^ 40 * 3360995 * 2
def baseEnd_3360995 : Nat := 127837474989495024096709

theorem tailTrace_3360995 : CollatzResearch.WordTrace tailWord_3360995 prefixEnd_3360995 127837474989495024096709 := by
  unfold tailWord_3360995
  simp only [CollatzResearch.WordTrace]
  refine ⟨122585558458696602091660439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81723705639131068061106959 122585558458696602091660439)
  ·
    refine ⟨183878337688044903137490659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122585558458696602091660439 183878337688044903137490659)
    ·
      refine ⟨275817506532067354706235989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183878337688044903137490659 275817506532067354706235989)
      ·
        refine ⟨3232236404672664312963703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 275817506532067354706235989 3232236404672664312963703)
        ·
          refine ⟨4848354607008996469445555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3232236404672664312963703 4848354607008996469445555)
          ·
            refine ⟨7272531910513494704168333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4848354607008996469445555 7272531910513494704168333)
            ·
              refine ⟨2727199466442560514063125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7272531910513494704168333 2727199466442560514063125)
              ·
                refine ⟨127837474989495024096709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2727199466442560514063125 127837474989495024096709)
                ·
                  rfl

theorem cell22_3360995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 6].length) (baseStart_3360995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3360995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3360995 prefixEnd_3360995 := by exact prefixLift 3360995
  have htrace : WordTrace (prefixWord ++ tailWord_3360995) baseStart_3360995 baseEnd_3360995 := by
    simpa [prefixWord, tailWord_3360995, baseEnd_3360995] using wordTrace_append hprefix tailTrace_3360995
  have hstable : (prefixWord ++ tailWord_3360995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360995).length < 2 ^ (prefixWord ++ tailWord_3360995).sum := by decide
  have hdescent : baseEnd_3360995 < baseStart_3360995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361006 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 7]
def baseStart_3361006 : Nat := 118140960795 + 3361006 * 2 ^ 59
def prefixEnd_3361006 : Nat := 4983230072969 + 3 ^ 40 * 3361006 * 2
def baseEnd_3361006 : Nat := 383513680143418284948449

theorem tailTrace_3361006 : CollatzResearch.WordTrace tailWord_3361006 prefixEnd_3361006 383513680143418284948449 := by
  unfold tailWord_3361006
  simp only [CollatzResearch.WordTrace]
  refine ⟨15323244957707093871288859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81723973107771167313540581 15323244957707093871288859)
  ·
    refine ⟨22984867436560640806933289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15323244957707093871288859 22984867436560640806933289)
    ·
      refine ⟨17238650577420480605199967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22984867436560640806933289 17238650577420480605199967)
      ·
        refine ⟨25857975866130720907799951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17238650577420480605199967 25857975866130720907799951)
        ·
          refine ⟨38786963799196081361699927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25857975866130720907799951 38786963799196081361699927)
          ·
            refine ⟨58180445698794122042549891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38786963799196081361699927 58180445698794122042549891)
            ·
              refine ⟨87270668548191183063824837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58180445698794122042549891 87270668548191183063824837)
              ·
                refine ⟨16363250352785846824467157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87270668548191183063824837 16363250352785846824467157)
                ·
                  refine ⟨383513680143418284948449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16363250352785846824467157 383513680143418284948449)
                  ·
                    rfl

theorem cell22_3361006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_3361006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3361006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3361006 prefixEnd_3361006 := by exact prefixLift 3361006
  have htrace : WordTrace (prefixWord ++ tailWord_3361006) baseStart_3361006 baseEnd_3361006 := by
    simpa [prefixWord, tailWord_3361006, baseEnd_3361006] using wordTrace_append hprefix tailTrace_3361006
  have hstable : (prefixWord ++ tailWord_3361006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361006).length < 2 ^ (prefixWord ++ tailWord_3361006).sum := by decide
  have hdescent : baseEnd_3361006 < baseStart_3361006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361051 : List Nat := [1, 1, 1, 1, 1, 1, 8, 2, 6]
def baseStart_3361051 : Nat := 118140960795 + 3361051 * 2 ^ 59
def prefixEnd_3361051 : Nat := 4983230072969 + 3 ^ 40 * 3361051 * 2
def baseEnd_3361051 : Nat := 383518814949963245823403

theorem tailTrace_3361051 : CollatzResearch.WordTrace tailWord_3361051 prefixEnd_3361051 383518814949963245823403 := by
  unfold tailWord_3361051
  simp only [CollatzResearch.WordTrace]
  refine ⟨122587600946493723655699007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81725067297662482437132671 122587600946493723655699007)
  ·
    refine ⟨183881401419740585483548511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122587600946493723655699007 183881401419740585483548511)
    ·
      refine ⟨275822102129610878225322767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183881401419740585483548511 275822102129610878225322767)
      ·
        refine ⟨413733153194416317337984151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275822102129610878225322767 413733153194416317337984151)
        ·
          refine ⟨620599729791624476006976227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413733153194416317337984151 620599729791624476006976227)
          ·
            refine ⟨930899594687436714010464341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620599729791624476006976227 930899594687436714010464341)
            ·
              refine ⟨10908979625243398992310129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 930899594687436714010464341 10908979625243398992310129)
              ·
                refine ⟨8181734718932549244232597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10908979625243398992310129 8181734718932549244232597)
                ·
                  refine ⟨383518814949963245823403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8181734718932549244232597 383518814949963245823403)
                  ·
                    rfl

theorem cell22_3361051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 6].length) (baseStart_3361051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3361051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3361051 prefixEnd_3361051 := by exact prefixLift 3361051
  have htrace : WordTrace (prefixWord ++ tailWord_3361051) baseStart_3361051 baseEnd_3361051 := by
    simpa [prefixWord, tailWord_3361051, baseEnd_3361051] using wordTrace_append hprefix tailTrace_3361051
  have hstable : (prefixWord ++ tailWord_3361051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361051).length < 2 ^ (prefixWord ++ tailWord_3361051).sum := by decide
  have hdescent : baseEnd_3361051 < baseStart_3361051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361096 : List Nat := [2, 1, 3, 1, 1, 2, 3, 9]
def baseStart_3361096 : Nat := 118140960795 + 3361096 * 2 ^ 59
def prefixEnd_3361096 : Nat := 4983230072969 + 3 ^ 40 * 3361096 * 2
def baseEnd_3361096 : Nat := 127841316585502735566119

theorem tailTrace_3361096 : CollatzResearch.WordTrace tailWord_3361096 prefixEnd_3361096 127841316585502735566119 := by
  unfold tailWord_3361096
  simp only [CollatzResearch.WordTrace]
  refine ⟨61294621115665348170543571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81726161487553797560724761 61294621115665348170543571)
  ·
    refine ⟨91941931673498022255815357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61294621115665348170543571 91941931673498022255815357)
    ·
      refine ⟨34478224377561758345930759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91941931673498022255815357 34478224377561758345930759)
      ·
        refine ⟨51717336566342637518896139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34478224377561758345930759 51717336566342637518896139)
        ·
          refine ⟨77576004849513956278344209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51717336566342637518896139 77576004849513956278344209)
          ·
            refine ⟨58182003637135467208758157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77576004849513956278344209 58182003637135467208758157)
            ·
              refine ⟨21818251363925800203284309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58182003637135467208758157 21818251363925800203284309)
              ·
                refine ⟨127841316585502735566119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21818251363925800203284309 127841316585502735566119)
                ·
                  rfl

theorem cell22_3361096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 9].length) (baseStart_3361096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3361096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3361096 prefixEnd_3361096 := by exact prefixLift 3361096
  have htrace : WordTrace (prefixWord ++ tailWord_3361096) baseStart_3361096 baseEnd_3361096 := by
    simpa [prefixWord, tailWord_3361096, baseEnd_3361096] using wordTrace_append hprefix tailTrace_3361096
  have hstable : (prefixWord ++ tailWord_3361096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361096).length < 2 ^ (prefixWord ++ tailWord_3361096).sum := by decide
  have hdescent : baseEnd_3361096 < baseStart_3361096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361100 : List Nat := [2, 2, 1, 3, 2, 1, 3, 3, 2, 3]
def baseStart_3361100 : Nat := 118140960795 + 3361100 * 2 ^ 59
def prefixEnd_3361100 : Nat := 4983230072969 + 3 ^ 40 * 3361100 * 2
def baseEnd_3361100 : Nat := 1150573218551269942995059

theorem tailTrace_3361100 : CollatzResearch.WordTrace tailWord_3361100 prefixEnd_3361100 1150573218551269942995059 := by
  unfold tailWord_3361100
  simp only [CollatzResearch.WordTrace]
  refine ⟨61294694061658102512116377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81726258748877470016155169 61294694061658102512116377)
  ·
    refine ⟨45971020546243576884087283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61294694061658102512116377 45971020546243576884087283)
    ·
      refine ⟨68956530819365365326130925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45971020546243576884087283 68956530819365365326130925)
      ·
        refine ⟨25858699057262011997299097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68956530819365365326130925 25858699057262011997299097)
        ·
          refine ⟨19394024292946508997974323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25858699057262011997299097 19394024292946508997974323)
          ·
            refine ⟨29091036439419763496961485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19394024292946508997974323 29091036439419763496961485)
            ·
              refine ⟨10909138664782411311360557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29091036439419763496961485 10909138664782411311360557)
              ·
                refine ⟨4090926999293404241760209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10909138664782411311360557 4090926999293404241760209)
                ·
                  refine ⟨3068195249470053181320157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4090926999293404241760209 3068195249470053181320157)
                  ·
                    refine ⟨1150573218551269942995059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3068195249470053181320157 1150573218551269942995059)
                    ·
                      rfl

theorem cell22_3361100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_3361100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3361100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3361100 prefixEnd_3361100 := by exact prefixLift 3361100
  have htrace : WordTrace (prefixWord ++ tailWord_3361100) baseStart_3361100 baseEnd_3361100 := by
    simpa [prefixWord, tailWord_3361100, baseEnd_3361100] using wordTrace_append hprefix tailTrace_3361100
  have hstable : (prefixWord ++ tailWord_3361100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361100).length < 2 ^ (prefixWord ++ tailWord_3361100).sum := by decide
  have hdescent : baseEnd_3361100 < baseStart_3361100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361192 : List Nat := [2, 1, 6, 1, 1, 1, 3, 2, 5]
def baseStart_3361192 : Nat := 118140960795 + 3361192 * 2 ^ 59
def prefixEnd_3361192 : Nat := 4983230072969 + 3 ^ 40 * 3361192 * 2
def baseEnd_3361192 : Nat := 383534904010470789898259

theorem tailTrace_3361192 : CollatzResearch.WordTrace tailWord_3361192 prefixEnd_3361192 383534904010470789898259 := by
  unfold tailWord_3361192
  simp only [CollatzResearch.WordTrace]
  refine ⟨61296371819491452368290915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81728495759321936491054553 61296371819491452368290915)
  ·
    refine ⟨91944557729237178552436373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61296371819491452368290915 91944557729237178552436373)
    ·
      refine ⟨4309901143557992744645455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 91944557729237178552436373 4309901143557992744645455)
      ·
        refine ⟨6464851715336989116968183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4309901143557992744645455 6464851715336989116968183)
        ·
          refine ⟨9697277573005483675452275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6464851715336989116968183 9697277573005483675452275)
          ·
            refine ⟨14545916359508225513178413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9697277573005483675452275 14545916359508225513178413)
            ·
              refine ⟨5454718634815584567441905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14545916359508225513178413 5454718634815584567441905)
              ·
                refine ⟨4091038976111688425581429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5454718634815584567441905 4091038976111688425581429)
                ·
                  refine ⟨383534904010470789898259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4091038976111688425581429 383534904010470789898259)
                  ·
                    rfl

theorem cell22_3361192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 5].length) (baseStart_3361192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3361192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3361192 prefixEnd_3361192 := by exact prefixLift 3361192
  have htrace : WordTrace (prefixWord ++ tailWord_3361192) baseStart_3361192 baseEnd_3361192 := by
    simpa [prefixWord, tailWord_3361192, baseEnd_3361192] using wordTrace_append hprefix tailTrace_3361192
  have hstable : (prefixWord ++ tailWord_3361192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361192).length < 2 ^ (prefixWord ++ tailWord_3361192).sum := by decide
  have hdescent : baseEnd_3361192 < baseStart_3361192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361233 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 6, 4]
def baseStart_3361233 : Nat := 118140960795 + 3361233 * 2 ^ 59
def prefixEnd_3361233 : Nat := 4983230072969 + 3 ^ 40 * 3361233 * 2
def baseEnd_3361233 : Nat := 1150618747169301929419651

theorem tailTrace_3361233 : CollatzResearch.WordTrace tailWord_3361233 prefixEnd_3361233 1150618747169301929419651 := by
  unfold tailWord_3361233
  simp only [CollatzResearch.WordTrace]
  refine ⟨122594239031834368738824353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81729492687889579159216235 122594239031834368738824353)
  ·
    refine ⟨91945679273875776554118265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122594239031834368738824353 91945679273875776554118265)
    ·
      refine ⟨68959259455406832415588699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91945679273875776554118265 68959259455406832415588699)
      ·
        refine ⟨103438889183110248623383049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68959259455406832415588699 103438889183110248623383049)
        ·
          refine ⟨77579166887332686467537287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103438889183110248623383049 77579166887332686467537287)
          ·
            refine ⟨116368750330999029701305931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77579166887332686467537287 116368750330999029701305931)
            ·
              refine ⟨174553125496498544551958897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116368750330999029701305931 174553125496498544551958897)
              ·
                refine ⟨130914844122373908413969173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174553125496498544551958897 130914844122373908413969173)
                ·
                  refine ⟨6136633318236276956904805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130914844122373908413969173 6136633318236276956904805)
                  ·
                    refine ⟨1150618747169301929419651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6136633318236276956904805 1150618747169301929419651)
                    ·
                      rfl

theorem cell22_3361233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_3361233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3361233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3361233 prefixEnd_3361233 := by exact prefixLift 3361233
  have htrace : WordTrace (prefixWord ++ tailWord_3361233) baseStart_3361233 baseEnd_3361233 := by
    simpa [prefixWord, tailWord_3361233, baseEnd_3361233] using wordTrace_append hprefix tailTrace_3361233
  have hstable : (prefixWord ++ tailWord_3361233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361233).length < 2 ^ (prefixWord ++ tailWord_3361233).sum := by decide
  have hdescent : baseEnd_3361233 < baseStart_3361233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361237 : List Nat := [1, 3, 2, 3, 1, 2, 3, 3, 4]
def baseStart_3361237 : Nat := 118140960795 + 3361237 * 2 ^ 59
def prefixEnd_3361237 : Nat := 4983230072969 + 3 ^ 40 * 3361237 * 2
def baseEnd_3361237 : Nat := 383540038817015750773213

theorem tailTrace_3361237 : CollatzResearch.WordTrace tailWord_3361237 prefixEnd_3361237 383540038817015750773213 := by
  unfold tailWord_3361237
  simp only [CollatzResearch.WordTrace]
  refine ⟨122594384923819877421969965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81729589949213251614646643 122594384923819877421969965)
  ·
    refine ⟨45972894346432454033238737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122594384923819877421969965 45972894346432454033238737)
    ·
      refine ⟨34479670759824340524929053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45972894346432454033238737 34479670759824340524929053)
      ·
        refine ⟨12929876534934127696848395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34479670759824340524929053 12929876534934127696848395)
        ·
          refine ⟨19394814802401191545272593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12929876534934127696848395 19394814802401191545272593)
          ·
            refine ⟨14546111101800893658954445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19394814802401191545272593 14546111101800893658954445)
            ·
              refine ⟨5454791663175335122107917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14546111101800893658954445 5454791663175335122107917)
              ·
                refine ⟨2045546873690750670790469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5454791663175335122107917 2045546873690750670790469)
                ·
                  refine ⟨383540038817015750773213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2045546873690750670790469 383540038817015750773213)
                  ·
                    rfl

theorem cell22_3361237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 4].length) (baseStart_3361237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3361237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3361237 prefixEnd_3361237 := by exact prefixLift 3361237
  have htrace : WordTrace (prefixWord ++ tailWord_3361237) baseStart_3361237 baseEnd_3361237 := by
    simpa [prefixWord, tailWord_3361237, baseEnd_3361237] using wordTrace_append hprefix tailTrace_3361237
  have hstable : (prefixWord ++ tailWord_3361237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361237).length < 2 ^ (prefixWord ++ tailWord_3361237).sum := by decide
  have hdescent : baseEnd_3361237 < baseStart_3361237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361286 : List Nat := [6, 2, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_3361286 : Nat := 118140960795 + 3361286 * 2 ^ 59
def prefixEnd_3361286 : Nat := 4983230072969 + 3 ^ 40 * 3361286 * 2
def baseEnd_3361286 : Nat := 1150636890152427457844489

theorem tailTrace_3361286 : CollatzResearch.WordTrace tailWord_3361286 prefixEnd_3361286 1150636890152427457844489 := by
  unfold tailWord_3361286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3831130378145073712203241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81730781400428239193669141 3831130378145073712203241)
  ·
    refine ⟨2873347783608805284152431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3831130378145073712203241 2873347783608805284152431)
    ·
      refine ⟨4310021675413207926228647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2873347783608805284152431 4310021675413207926228647)
      ·
        refine ⟨6465032513119811889342971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4310021675413207926228647 6465032513119811889342971)
        ·
          refine ⟨9697548769679717834014457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6465032513119811889342971 9697548769679717834014457)
          ·
            refine ⟨7273161577259788375510843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9697548769679717834014457 7273161577259788375510843)
            ·
              refine ⟨10909742365889682563266265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7273161577259788375510843 10909742365889682563266265)
              ·
                refine ⟨8182306774417261922449699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10909742365889682563266265 8182306774417261922449699)
                ·
                  refine ⟨12273460161625892883674549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8182306774417261922449699 12273460161625892883674549)
                  ·
                    refine ⟨1150636890152427457844489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12273460161625892883674549 1150636890152427457844489)
                    ·
                      rfl

theorem cell22_3361286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_3361286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3361286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3361286 prefixEnd_3361286 := by exact prefixLift 3361286
  have htrace : WordTrace (prefixWord ++ tailWord_3361286) baseStart_3361286 baseEnd_3361286 := by
    simpa [prefixWord, tailWord_3361286, baseEnd_3361286] using wordTrace_append hprefix tailTrace_3361286
  have hstable : (prefixWord ++ tailWord_3361286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361286).length < 2 ^ (prefixWord ++ tailWord_3361286).sum := by decide
  have hdescent : baseEnd_3361286 < baseStart_3361286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361434 : List Nat := [3, 1, 1, 6, 1, 1, 2, 7]
def baseStart_3361434 : Nat := 118140960795 + 3361434 * 2 ^ 59
def prefixEnd_3361434 : Nat := 4983230072969 + 3 ^ 40 * 3361434 * 2
def baseEnd_3361434 : Nat := 127854172619667156127115

theorem tailTrace_3361434 : CollatzResearch.WordTrace tailWord_3361434 prefixEnd_3361434 127854172619667156127115 := by
  unfold tailWord_3361434
  simp only [CollatzResearch.WordTrace]
  refine ⟨30650392526026545016722839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81734380069404120044594237 30650392526026545016722839)
  ·
    refine ⟨45975588789039817525084259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30650392526026545016722839 45975588789039817525084259)
    ·
      refine ⟨68963383183559726287626389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45975588789039817525084259 68963383183559726287626389)
      ·
        refine ⟨3232658586729362169732487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68963383183559726287626389 3232658586729362169732487)
        ·
          refine ⟨4848987880094043254598731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3232658586729362169732487 4848987880094043254598731)
          ·
            refine ⟨7273481820141064881898097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4848987880094043254598731 7273481820141064881898097)
            ·
              refine ⟨5455111365105798661423573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7273481820141064881898097 5455111365105798661423573)
              ·
                refine ⟨127854172619667156127115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5455111365105798661423573 127854172619667156127115)
                ·
                  rfl

theorem cell22_3361434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 7].length) (baseStart_3361434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3361434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3361434 prefixEnd_3361434 := by exact prefixLift 3361434
  have htrace : WordTrace (prefixWord ++ tailWord_3361434) baseStart_3361434 baseEnd_3361434 := by
    simpa [prefixWord, tailWord_3361434, baseEnd_3361434] using wordTrace_append hprefix tailTrace_3361434
  have hstable : (prefixWord ++ tailWord_3361434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361434).length < 2 ^ (prefixWord ++ tailWord_3361434).sum := by decide
  have hdescent : baseEnd_3361434 < baseStart_3361434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361507 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 8]
def baseStart_3361507 : Nat := 118140960795 + 3361507 * 2 ^ 59
def prefixEnd_3361507 : Nat := 4983230072969 + 3 ^ 40 * 3361507 * 2
def baseEnd_3361507 : Nat := 383570847656285516022937

theorem tailTrace_3361507 : CollatzResearch.WordTrace tailWord_3361507 prefixEnd_3361507 383570847656285516022937 := by
  unfold tailWord_3361507
  simp only [CollatzResearch.WordTrace]
  refine ⟨122604232632841713534298775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81736155088561142356199183 122604232632841713534298775)
  ·
    refine ⟨183906348949262570301448163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122604232632841713534298775 183906348949262570301448163)
    ·
      refine ⟨275859523423893855452172245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183906348949262570301448163 275859523423893855452172245)
      ·
        refine ⟨6465457580247512237160287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 275859523423893855452172245 6465457580247512237160287)
        ·
          refine ⟨9698186370371268355740431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6465457580247512237160287 9698186370371268355740431)
          ·
            refine ⟨14547279555556902533610647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9698186370371268355740431 14547279555556902533610647)
            ·
              refine ⟨21820919333335353800415971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14547279555556902533610647 21820919333335353800415971)
              ·
                refine ⟨32731379000003030700623957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21820919333335353800415971 32731379000003030700623957)
                ·
                  refine ⟨383570847656285516022937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32731379000003030700623957 383570847656285516022937)
                  ·
                    rfl

theorem cell22_3361507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 8].length) (baseStart_3361507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3361507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3361507 prefixEnd_3361507 := by exact prefixLift 3361507
  have htrace : WordTrace (prefixWord ++ tailWord_3361507) baseStart_3361507 baseEnd_3361507 := by
    simpa [prefixWord, tailWord_3361507, baseEnd_3361507] using wordTrace_append hprefix tailTrace_3361507
  have hstable : (prefixWord ++ tailWord_3361507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361507).length < 2 ^ (prefixWord ++ tailWord_3361507).sum := by decide
  have hdescent : baseEnd_3361507 < baseStart_3361507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361537 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 4, 4]
def baseStart_3361537 : Nat := 118140960795 + 3361537 * 2 ^ 59
def prefixEnd_3361537 : Nat := 4983230072969 + 3 ^ 40 * 3361537 * 2
def baseEnd_3361537 : Nat := 1150722812581946469818719

theorem tailTrace_3361537 : CollatzResearch.WordTrace tailWord_3361537 prefixEnd_3361537 1150722812581946469818719 := by
  unfold tailWord_3361537
  simp only [CollatzResearch.WordTrace]
  refine ⟨122605326822733028657890865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81736884548488685771927243 122605326822733028657890865)
  ·
    refine ⟨91953995117049771493418149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122605326822733028657890865 91953995117049771493418149)
    ·
      refine ⟨17241374084446832155015903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91953995117049771493418149 17241374084446832155015903)
      ·
        refine ⟨25862061126670248232523855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17241374084446832155015903 25862061126670248232523855)
        ·
          refine ⟨38793091690005372348785783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25862061126670248232523855 38793091690005372348785783)
          ·
            refine ⟨58189637535008058523178675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38793091690005372348785783 58189637535008058523178675)
            ·
              refine ⟨87284456302512087784768013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58189637535008058523178675 87284456302512087784768013)
              ·
                refine ⟨32731671113442032919288005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87284456302512087784768013 32731671113442032919288005)
                ·
                  refine ⟨6137188333770381172366501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32731671113442032919288005 6137188333770381172366501)
                  ·
                    refine ⟨1150722812581946469818719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6137188333770381172366501 1150722812581946469818719)
                    ·
                      rfl

theorem cell22_3361537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_3361537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3361537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3361537 prefixEnd_3361537 := by exact prefixLift 3361537
  have htrace : WordTrace (prefixWord ++ tailWord_3361537) baseStart_3361537 baseEnd_3361537 := by
    simpa [prefixWord, tailWord_3361537, baseEnd_3361537] using wordTrace_append hprefix tailTrace_3361537
  have hstable : (prefixWord ++ tailWord_3361537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361537).length < 2 ^ (prefixWord ++ tailWord_3361537).sum := by decide
  have hdescent : baseEnd_3361537 < baseStart_3361537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
