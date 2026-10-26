import V185TrunkScan23Chunk0018

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_112261 : List Nat := [1, 3, 1, 1, 4, 1, 1, 6, 5]
def baseStart_112261 : Nat := 118140960795 + 112261 * 2 ^ 59
def prefixEnd_112261 : Nat := 4983230072969 + 3 ^ 40 * 112261 * 2
def baseEnd_112261 : Nat := 6404872417165612446803

theorem tailTrace_112261 : CollatzResearch.WordTrace tailWord_112261 prefixEnd_112261 6404872417165612446803 := by
  unfold tailWord_112261
  simp only [CollatzResearch.WordTrace]
  refine ⟨4094495046305044497496637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2729663364203362998331091 4094495046305044497496637)
  ·
    refine ⟨1535435642364391686561239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4094495046305044497496637 1535435642364391686561239)
    ·
      refine ⟨2303153463546587529841859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1535435642364391686561239 2303153463546587529841859)
      ·
        refine ⟨3454730195319881294762789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2303153463546587529841859 3454730195319881294762789)
        ·
          refine ⟨647761911622477742768023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3454730195319881294762789 647761911622477742768023)
          ·
            refine ⟨971642867433716614152035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647761911622477742768023 971642867433716614152035)
            ·
              refine ⟨1457464301150574921228053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 971642867433716614152035 1457464301150574921228053)
              ·
                refine ⟨68318639116433199432565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1457464301150574921228053 68318639116433199432565)
                ·
                  refine ⟨6404872417165612446803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68318639116433199432565 6404872417165612446803)
                  ·
                    rfl

theorem cell23_112261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 5].length) (baseStart_112261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112261 prefixEnd_112261 := by exact prefixLift 112261
  have htrace : WordTrace (prefixWord ++ tailWord_112261) baseStart_112261 baseEnd_112261 := by
    simpa [prefixWord, tailWord_112261, baseEnd_112261] using wordTrace_append hprefix tailTrace_112261
  have hstable : (prefixWord ++ tailWord_112261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112261).length < 2 ^ (prefixWord ++ tailWord_112261).sum := by decide
  have hdescent : baseEnd_112261 < baseStart_112261 := by decide
  rcases family_descends (prefixWord ++ tailWord_112261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112301 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_112301 : Nat := 118140960795 + 112301 * 2 ^ 59
def prefixEnd_112301 : Nat := 4983230072969 + 3 ^ 40 * 112301 * 2
def baseEnd_112301 : Nat := 57664390980670355521043

theorem tailTrace_112301 : CollatzResearch.WordTrace tailWord_112301 prefixEnd_112301 57664390980670355521043 := by
  unfold tailWord_112301
  simp only [CollatzResearch.WordTrace]
  refine ⟨4095953966160131328952757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2730635977440087552635171 4095953966160131328952757)
  ·
    refine ⟨383995684327512312089321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4095953966160131328952757 383995684327512312089321)
    ·
      refine ⟨287996763245634234066991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383995684327512312089321 287996763245634234066991)
      ·
        refine ⟨431995144868451351100487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287996763245634234066991 431995144868451351100487)
        ·
          refine ⟨647992717302677026650731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431995144868451351100487 647992717302677026650731)
          ·
            refine ⟨971989075954015539976097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647992717302677026650731 971989075954015539976097)
            ·
              refine ⟨728991806965511654982073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 971989075954015539976097 728991806965511654982073)
              ·
                refine ⟨546743855224133741236555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728991806965511654982073 546743855224133741236555)
                ·
                  refine ⟨820115782836200611854833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 546743855224133741236555 820115782836200611854833)
                  ·
                    refine ⟨615086837127150458891125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 820115782836200611854833 615086837127150458891125)
                    ·
                      refine ⟨57664390980670355521043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 615086837127150458891125 57664390980670355521043)
                      ·
                        rfl

theorem cell23_112301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_112301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112301 prefixEnd_112301 := by exact prefixLift 112301
  have htrace : WordTrace (prefixWord ++ tailWord_112301) baseStart_112301 baseEnd_112301 := by
    simpa [prefixWord, tailWord_112301, baseEnd_112301] using wordTrace_append hprefix tailTrace_112301
  have hstable : (prefixWord ++ tailWord_112301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112301).length < 2 ^ (prefixWord ++ tailWord_112301).sum := by decide
  have hdescent : baseEnd_112301 < baseStart_112301 := by decide
  rcases family_descends (prefixWord ++ tailWord_112301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112311 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 4]
def baseStart_112311 : Nat := 118140960795 + 112311 * 2 ^ 59
def prefixEnd_112311 : Nat := 4983230072969 + 3 ^ 40 * 112311 * 2
def baseEnd_112311 : Nat := 57669525787215316395997

theorem tailTrace_112311 : CollatzResearch.WordTrace tailWord_112311 prefixEnd_112311 57669525787215316395997 := by
  unfold tailWord_112311
  simp only [CollatzResearch.WordTrace]
  refine ⟨4096318696123903036816787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2730879130749268691211191 4096318696123903036816787)
  ·
    refine ⟨6144478044185854555225181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4096318696123903036816787 6144478044185854555225181)
    ·
      refine ⟨2304179266569695458209443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6144478044185854555225181 2304179266569695458209443)
      ·
        refine ⟨3456268899854543187314165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2304179266569695458209443 3456268899854543187314165)
        ·
          refine ⟨324025209361363423810703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3456268899854543187314165 324025209361363423810703)
          ·
            refine ⟨486037814042045135716055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324025209361363423810703 486037814042045135716055)
            ·
              refine ⟨729056721063067703574083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486037814042045135716055 729056721063067703574083)
              ·
                refine ⟨1093585081594601555361125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 729056721063067703574083 1093585081594601555361125)
                ·
                  refine ⟨205047202798987791630211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1093585081594601555361125 205047202798987791630211)
                  ·
                    refine ⟨307570804198481687445317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 205047202798987791630211 307570804198481687445317)
                    ·
                      refine ⟨57669525787215316395997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 307570804198481687445317 57669525787215316395997)
                      ·
                        rfl

theorem cell23_112311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_112311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112311 prefixEnd_112311 := by exact prefixLift 112311
  have htrace : WordTrace (prefixWord ++ tailWord_112311) baseStart_112311 baseEnd_112311 := by
    simpa [prefixWord, tailWord_112311, baseEnd_112311] using wordTrace_append hprefix tailTrace_112311
  have hstable : (prefixWord ++ tailWord_112311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112311).length < 2 ^ (prefixWord ++ tailWord_112311).sum := by decide
  have hdescent : baseEnd_112311 < baseStart_112311 := by decide
  rcases family_descends (prefixWord ++ tailWord_112311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112342 : List Nat := [5, 2, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_112342 : Nat := 118140960795 + 112342 * 2 ^ 59
def prefixEnd_112342 : Nat := 4983230072969 + 3 ^ 40 * 112342 * 2
def baseEnd_112342 : Nat := 19228481229168231702785

theorem tailTrace_112342 : CollatzResearch.WordTrace tailWord_112342 prefixEnd_112342 19228481229168231702785 := by
  unfold tailWord_112342
  simp only [CollatzResearch.WordTrace]
  refine ⟨256090584938224708199705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2731632906007730220796853 256090584938224708199705)
  ·
    refine ⟨192067938703668531149779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256090584938224708199705 192067938703668531149779)
    ·
      refine ⟨288101908055502796724669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192067938703668531149779 288101908055502796724669)
      ·
        refine ⟨108038215520813548771751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288101908055502796724669 108038215520813548771751)
        ·
          refine ⟨162057323281220323157627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108038215520813548771751 162057323281220323157627)
          ·
            refine ⟨243085984921830484736441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162057323281220323157627 243085984921830484736441)
            ·
              refine ⟨182314488691372863552331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243085984921830484736441 182314488691372863552331)
              ·
                refine ⟨273471733037059295328497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182314488691372863552331 273471733037059295328497)
                ·
                  refine ⟨205103799777794471496373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273471733037059295328497 205103799777794471496373)
                  ·
                    refine ⟨19228481229168231702785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 205103799777794471496373 19228481229168231702785)
                    ·
                      rfl

theorem cell23_112342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_112342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112342 prefixEnd_112342 := by exact prefixLift 112342
  have htrace : WordTrace (prefixWord ++ tailWord_112342) baseStart_112342 baseEnd_112342 := by
    simpa [prefixWord, tailWord_112342, baseEnd_112342] using wordTrace_append hprefix tailTrace_112342
  have hstable : (prefixWord ++ tailWord_112342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112342).length < 2 ^ (prefixWord ++ tailWord_112342).sum := by decide
  have hdescent : baseEnd_112342 < baseStart_112342 := by decide
  rcases family_descends (prefixWord ++ tailWord_112342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112378 : List Nat := [3, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3]
def baseStart_112378 : Nat := 118140960795 + 112378 * 2 ^ 59
def prefixEnd_112378 : Nat := 4983230072969 + 3 ^ 40 * 112378 * 2
def baseEnd_112378 : Nat := 57703928991066554258189

theorem tailTrace_112378 : CollatzResearch.WordTrace tailWord_112378 prefixEnd_112378 57703928991066554258189 := by
  unfold tailWord_112378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1024690596720293369876447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2732508257920782319670525 1024690596720293369876447)
  ·
    refine ⟨1537035895080440054814671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1024690596720293369876447 1537035895080440054814671)
    ·
      refine ⟨2305553842620660082222007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1537035895080440054814671 2305553842620660082222007)
      ·
        refine ⟨3458330763930990123333011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2305553842620660082222007 3458330763930990123333011)
        ·
          refine ⟨5187496145896485184999517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3458330763930990123333011 5187496145896485184999517)
          ·
            refine ⟨1945311054711181944374819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5187496145896485184999517 1945311054711181944374819)
            ·
              refine ⟨2917966582066772916562229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1945311054711181944374819 2917966582066772916562229)
              ·
                refine ⟨273559367068759960927709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2917966582066772916562229 273559367068759960927709)
                ·
                  refine ⟨102584762650784985347891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273559367068759960927709 102584762650784985347891)
                  ·
                    refine ⟨153877143976177478021837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102584762650784985347891 153877143976177478021837)
                    ·
                      refine ⟨57703928991066554258189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 153877143976177478021837 57703928991066554258189)
                      ·
                        rfl

theorem cell23_112378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3].length) (baseStart_112378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112378 prefixEnd_112378 := by exact prefixLift 112378
  have htrace : WordTrace (prefixWord ++ tailWord_112378) baseStart_112378 baseEnd_112378 := by
    simpa [prefixWord, tailWord_112378, baseEnd_112378] using wordTrace_append hprefix tailTrace_112378
  have hstable : (prefixWord ++ tailWord_112378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112378).length < 2 ^ (prefixWord ++ tailWord_112378).sum := by decide
  have hdescent : baseEnd_112378 < baseStart_112378 := by decide
  rcases family_descends (prefixWord ++ tailWord_112378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112405 : List Nat := [1, 3, 2, 1, 2, 3, 3, 1, 2, 3, 2]
def baseStart_112405 : Nat := 118140960795 + 112405 * 2 ^ 59
def prefixEnd_112405 : Nat := 4983230072969 + 3 ^ 40 * 112405 * 2
def baseEnd_112405 : Nat := 57717792968737948620565

theorem tailTrace_112405 : CollatzResearch.WordTrace tailWord_112405 prefixEnd_112405 57717792968737948620565 := by
  unfold tailWord_112405
  simp only [CollatzResearch.WordTrace]
  refine ⟨4099747157783357090738669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2733164771855571393825779 4099747157783357090738669)
  ·
    refine ⟨1537405184168758909027001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4099747157783357090738669 1537405184168758909027001)
    ·
      refine ⟨1153053888126569181770251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1537405184168758909027001 1153053888126569181770251)
      ·
        refine ⟨1729580832189853772655377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1153053888126569181770251 1729580832189853772655377)
        ·
          refine ⟨1297185624142390329491533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1729580832189853772655377 1297185624142390329491533)
          ·
            refine ⟨486444609053396373559325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1297185624142390329491533 486444609053396373559325)
            ·
              refine ⟨182416728395023640084747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 486444609053396373559325 182416728395023640084747)
              ·
                refine ⟨273625092592535460127121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182416728395023640084747 273625092592535460127121)
                ·
                  refine ⟨205218819444401595095341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273625092592535460127121 205218819444401595095341)
                  ·
                    refine ⟨76957057291650598160753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 205218819444401595095341 76957057291650598160753)
                    ·
                      refine ⟨57717792968737948620565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 76957057291650598160753 57717792968737948620565)
                      ·
                        rfl

theorem cell23_112405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_112405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112405 prefixEnd_112405 := by exact prefixLift 112405
  have htrace : WordTrace (prefixWord ++ tailWord_112405) baseStart_112405 baseEnd_112405 := by
    simpa [prefixWord, tailWord_112405, baseEnd_112405] using wordTrace_append hprefix tailTrace_112405
  have hstable : (prefixWord ++ tailWord_112405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112405).length < 2 ^ (prefixWord ++ tailWord_112405).sum := by decide
  have hdescent : baseEnd_112405 < baseStart_112405 := by decide
  rcases family_descends (prefixWord ++ tailWord_112405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112411 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 6, 4]
def baseStart_112411 : Nat := 118140960795 + 112411 * 2 ^ 59
def prefixEnd_112411 : Nat := 4983230072969 + 3 ^ 40 * 112411 * 2
def baseEnd_112411 : Nat := 19240291284221641715179

theorem tailTrace_112411 : CollatzResearch.WordTrace tailWord_112411 prefixEnd_112411 19240291284221641715179 := by
  unfold tailWord_112411
  simp only [CollatzResearch.WordTrace]
  refine ⟨4099965995761620115457087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2733310663841080076971391 4099965995761620115457087)
  ·
    refine ⟨6149948993642430173185631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4099965995761620115457087 6149948993642430173185631)
    ·
      refine ⟨9224923490463645259778447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6149948993642430173185631 9224923490463645259778447)
      ·
        refine ⟨13837385235695467889667671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9224923490463645259778447 13837385235695467889667671)
        ·
          refine ⟨20756077853543201834501507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13837385235695467889667671 20756077853543201834501507)
          ·
            refine ⟨31134116780314802751752261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20756077853543201834501507 31134116780314802751752261)
            ·
              refine ⟨5837646896309025515953549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31134116780314802751752261 5837646896309025515953549)
              ·
                refine ⟨2189117586115884568482581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5837646896309025515953549 2189117586115884568482581)
                ·
                  refine ⟨102614886849182089147621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2189117586115884568482581 102614886849182089147621)
                  ·
                    refine ⟨19240291284221641715179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102614886849182089147621 19240291284221641715179)
                    ·
                      rfl

theorem cell23_112411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 4].length) (baseStart_112411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112411 prefixEnd_112411 := by exact prefixLift 112411
  have htrace : WordTrace (prefixWord ++ tailWord_112411) baseStart_112411 baseEnd_112411 := by
    simpa [prefixWord, tailWord_112411, baseEnd_112411] using wordTrace_append hprefix tailTrace_112411
  have hstable : (prefixWord ++ tailWord_112411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112411).length < 2 ^ (prefixWord ++ tailWord_112411).sum := by decide
  have hdescent : baseEnd_112411 < baseStart_112411 := by decide
  rcases family_descends (prefixWord ++ tailWord_112411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112412 : List Nat := [2, 2, 3, 1, 1, 2, 4, 3, 1, 1, 3]
def baseStart_112412 : Nat := 118140960795 + 112412 * 2 ^ 59
def prefixEnd_112412 : Nat := 4983230072969 + 3 ^ 40 * 112412 * 2
def baseEnd_112412 : Nat := 57721387333319421233033

theorem tailTrace_112412 : CollatzResearch.WordTrace tailWord_112412 prefixEnd_112412 57721387333319421233033 := by
  unfold tailWord_112412
  simp only [CollatzResearch.WordTrace]
  refine ⟨2050001234378998643121745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2733334979171998190828993 2050001234378998643121745)
  ·
    refine ⟨1537500925784248982341309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2050001234378998643121745 1537500925784248982341309)
    ·
      refine ⟨576562847169093368377991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1537500925784248982341309 576562847169093368377991)
      ·
        refine ⟨864844270753640052566987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576562847169093368377991 864844270753640052566987)
        ·
          refine ⟨1297266406130460078850481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864844270753640052566987 1297266406130460078850481)
          ·
            refine ⟨972949804597845059137861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1297266406130460078850481 972949804597845059137861)
            ·
              refine ⟨182428088362095948588349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 972949804597845059137861 182428088362095948588349)
              ·
                refine ⟨68410533135785980720631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182428088362095948588349 68410533135785980720631)
                ·
                  refine ⟨102615799703678971080947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68410533135785980720631 102615799703678971080947)
                  ·
                    refine ⟨153923699555518456621421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102615799703678971080947 153923699555518456621421)
                    ·
                      refine ⟨57721387333319421233033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 153923699555518456621421 57721387333319421233033)
                      ·
                        rfl

theorem cell23_112412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_112412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112412 prefixEnd_112412 := by exact prefixLift 112412
  have htrace : WordTrace (prefixWord ++ tailWord_112412) baseStart_112412 baseEnd_112412 := by
    simpa [prefixWord, tailWord_112412, baseEnd_112412] using wordTrace_append hprefix tailTrace_112412
  have hstable : (prefixWord ++ tailWord_112412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112412).length < 2 ^ (prefixWord ++ tailWord_112412).sum := by decide
  have hdescent : baseEnd_112412 < baseStart_112412 := by decide
  rcases family_descends (prefixWord ++ tailWord_112412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112428 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 4, 4]
def baseStart_112428 : Nat := 118140960795 + 112428 * 2 ^ 59
def prefixEnd_112428 : Nat := 4983230072969 + 3 ^ 40 * 112428 * 2
def baseEnd_112428 : Nat := 19243201007930452877653

theorem tailTrace_112428 : CollatzResearch.WordTrace tailWord_112428 prefixEnd_112428 19243201007930452877653 := by
  unfold tailWord_112428
  simp only [CollatzResearch.WordTrace]
  refine ⟨2050293018350016009412969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2733724024466688012550625 2050293018350016009412969)
  ·
    refine ⟨1537719763762512007059727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2050293018350016009412969 1537719763762512007059727)
    ·
      refine ⟨2306579645643768010589591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1537719763762512007059727 2306579645643768010589591)
      ·
        refine ⟨3459869468465652015884387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2306579645643768010589591 3459869468465652015884387)
        ·
          refine ⟨5189804202698478023826581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3459869468465652015884387 5189804202698478023826581)
          ·
            refine ⟨243272072001491157366871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5189804202698478023826581 243272072001491157366871)
            ·
              refine ⟨364908108002236736050307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243272072001491157366871 364908108002236736050307)
              ·
                refine ⟨547362162003355104075461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364908108002236736050307 547362162003355104075461)
                ·
                  refine ⟨102630405375629082014149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 547362162003355104075461 102630405375629082014149)
                  ·
                    refine ⟨19243201007930452877653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102630405375629082014149 19243201007930452877653)
                    ·
                      rfl

theorem cell23_112428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 4].length) (baseStart_112428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112428 prefixEnd_112428 := by exact prefixLift 112428
  have htrace : WordTrace (prefixWord ++ tailWord_112428) baseStart_112428 baseEnd_112428 := by
    simpa [prefixWord, tailWord_112428, baseEnd_112428] using wordTrace_append hprefix tailTrace_112428
  have hstable : (prefixWord ++ tailWord_112428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112428).length < 2 ^ (prefixWord ++ tailWord_112428).sum := by decide
  have hdescent : baseEnd_112428 < baseStart_112428 := by decide
  rcases family_descends (prefixWord ++ tailWord_112428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112445 : List Nat := [1, 4, 1, 4, 1, 3, 1, 1, 1, 6]
def baseStart_112445 : Nat := 118140960795 + 112445 * 2 ^ 59
def prefixEnd_112445 : Nat := 4983230072969 + 3 ^ 40 * 112445 * 2
def baseEnd_112445 : Nat := 19246110731639264040127

theorem tailTrace_112445 : CollatzResearch.WordTrace tailWord_112445 prefixEnd_112445 19246110731639264040127 := by
  unfold tailWord_112445
  simp only [CollatzResearch.WordTrace]
  refine ⟨4101206077638443922194789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2734137385092295948129859 4101206077638443922194789)
  ·
    refine ⟨768976139557208235411523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4101206077638443922194789 768976139557208235411523)
    ·
      refine ⟨1153464209335812353117285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 768976139557208235411523 1153464209335812353117285)
      ·
        refine ⟨216274539250464816209491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1153464209335812353117285 216274539250464816209491)
        ·
          refine ⟨324411808875697224314237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216274539250464816209491 324411808875697224314237)
          ·
            refine ⟨121654428328386459117839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324411808875697224314237 121654428328386459117839)
            ·
              refine ⟨182481642492579688676759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121654428328386459117839 182481642492579688676759)
              ·
                refine ⟨273722463738869533015139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182481642492579688676759 273722463738869533015139)
                ·
                  refine ⟨410583695608304299522709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273722463738869533015139 410583695608304299522709)
                  ·
                    refine ⟨19246110731639264040127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 410583695608304299522709 19246110731639264040127)
                    ·
                      rfl

theorem cell23_112445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_112445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112445 prefixEnd_112445 := by exact prefixLift 112445
  have htrace : WordTrace (prefixWord ++ tailWord_112445) baseStart_112445 baseEnd_112445 := by
    simpa [prefixWord, tailWord_112445, baseEnd_112445] using wordTrace_append hprefix tailTrace_112445
  have hstable : (prefixWord ++ tailWord_112445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112445).length < 2 ^ (prefixWord ++ tailWord_112445).sum := by decide
  have hdescent : baseEnd_112445 < baseStart_112445 := by decide
  rcases family_descends (prefixWord ++ tailWord_112445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112469 : List Nat := [1, 3, 2, 2, 2, 2, 3, 3, 1, 2, 2]
def baseStart_112469 : Nat := 118140960795 + 112469 * 2 ^ 59
def prefixEnd_112469 : Nat := 4983230072969 + 3 ^ 40 * 112469 * 2
def baseEnd_112469 : Nat := 57750655730625698220271

theorem tailTrace_112469 : CollatzResearch.WordTrace tailWord_112469 prefixEnd_112469 57750655730625698220271 := by
  unfold tailWord_112469
  simp only [CollatzResearch.WordTrace]
  refine ⟨4102081429551496021068461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2734720953034330680712307 4102081429551496021068461)
  ·
    refine ⟨1538280536081811007900673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4102081429551496021068461 1538280536081811007900673)
    ·
      refine ⟨1153710402061358255925505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1538280536081811007900673 1153710402061358255925505)
      ·
        refine ⟨865282801546018691944129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1153710402061358255925505 865282801546018691944129)
        ·
          refine ⟨648962101159514018958097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 865282801546018691944129 648962101159514018958097)
          ·
            refine ⟨486721575869635514218573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 648962101159514018958097 486721575869635514218573)
            ·
              refine ⟨182520590951113317831965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 486721575869635514218573 182520590951113317831965)
              ·
                refine ⟨68445221606667494186987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182520590951113317831965 68445221606667494186987)
                ·
                  refine ⟨102667832410001241280481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68445221606667494186987 102667832410001241280481)
                  ·
                    refine ⟨77000874307500930960361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102667832410001241280481 77000874307500930960361)
                    ·
                      refine ⟨57750655730625698220271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 77000874307500930960361 57750655730625698220271)
                      ·
                        rfl

theorem cell23_112469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_112469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112469 prefixEnd_112469 := by exact prefixLift 112469
  have htrace : WordTrace (prefixWord ++ tailWord_112469) baseStart_112469 baseEnd_112469 := by
    simpa [prefixWord, tailWord_112469, baseEnd_112469] using wordTrace_append hprefix tailTrace_112469
  have hstable : (prefixWord ++ tailWord_112469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112469).length < 2 ^ (prefixWord ++ tailWord_112469).sum := by decide
  have hdescent : baseEnd_112469 < baseStart_112469 := by decide
  rcases family_descends (prefixWord ++ tailWord_112469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112481 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_112481 : Nat := 118140960795 + 112481 * 2 ^ 59
def prefixEnd_112481 : Nat := 4983230072969 + 3 ^ 40 * 112481 * 2
def baseEnd_112481 : Nat := 57756817498479651270215

theorem tailTrace_112481 : CollatzResearch.WordTrace tailWord_112481 prefixEnd_112481 57756817498479651270215 := by
  unfold tailWord_112481
  simp only [CollatzResearch.WordTrace]
  refine ⟨4102519105508022070505297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2735012737005348047003531 4102519105508022070505297)
  ·
    refine ⟨3076889329131016552878973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4102519105508022070505297 3076889329131016552878973)
    ·
      refine ⟨1153833498424131207329615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3076889329131016552878973 1153833498424131207329615)
      ·
        refine ⟨1730750247636196810994423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1153833498424131207329615 1730750247636196810994423)
        ·
          refine ⟨2596125371454295216491635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1730750247636196810994423 2596125371454295216491635)
          ·
            refine ⟨3894188057181442824737453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2596125371454295216491635 3894188057181442824737453)
            ·
              refine ⟨1460320521443041059276545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3894188057181442824737453 1460320521443041059276545)
              ·
                refine ⟨1095240391082280794457409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1460320521443041059276545 1095240391082280794457409)
                ·
                  refine ⟨821430293311710595843057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1095240391082280794457409 821430293311710595843057)
                  ·
                    refine ⟨616072719983782946882293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 821430293311710595843057 616072719983782946882293)
                    ·
                      refine ⟨57756817498479651270215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 616072719983782946882293 57756817498479651270215)
                      ·
                        rfl

theorem cell23_112481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_112481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112481 prefixEnd_112481 := by exact prefixLift 112481
  have htrace : WordTrace (prefixWord ++ tailWord_112481) baseStart_112481 baseEnd_112481 := by
    simpa [prefixWord, tailWord_112481, baseEnd_112481] using wordTrace_append hprefix tailTrace_112481
  have hstable : (prefixWord ++ tailWord_112481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112481).length < 2 ^ (prefixWord ++ tailWord_112481).sum := by decide
  have hdescent : baseEnd_112481 < baseStart_112481 := by decide
  rcases family_descends (prefixWord ++ tailWord_112481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112485 : List Nat := [1, 3, 1, 3, 1, 1, 1, 6, 2, 1, 3]
def baseStart_112485 : Nat := 118140960795 + 112485 * 2 ^ 59
def prefixEnd_112485 : Nat := 4983230072969 + 3 ^ 40 * 112485 * 2
def baseEnd_112485 : Nat := 57758871421097635620197

theorem tailTrace_112485 : CollatzResearch.WordTrace tailWord_112485 prefixEnd_112485 57758871421097635620197 := by
  unfold tailWord_112485
  simp only [CollatzResearch.WordTrace]
  refine ⟨4102664997493530753650909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2735109998329020502433939 4102664997493530753650909)
  ·
    refine ⟨1538499374060074032619091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4102664997493530753650909 1538499374060074032619091)
    ·
      refine ⟨2307749061090111048928637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1538499374060074032619091 2307749061090111048928637)
      ·
        refine ⟨865405897908791643348239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2307749061090111048928637 865405897908791643348239)
        ·
          refine ⟨1298108846863187465022359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 865405897908791643348239 1298108846863187465022359)
          ·
            refine ⟨1947163270294781197533539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298108846863187465022359 1947163270294781197533539)
            ·
              refine ⟨2920744905442171796300309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1947163270294781197533539 2920744905442171796300309)
              ·
                refine ⟨136909917442601802951577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2920744905442171796300309 136909917442601802951577)
                ·
                  refine ⟨102682438081951352213683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136909917442601802951577 102682438081951352213683)
                  ·
                    refine ⟨154023657122927028320525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102682438081951352213683 154023657122927028320525)
                    ·
                      refine ⟨57758871421097635620197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 154023657122927028320525 57758871421097635620197)
                      ·
                        rfl

theorem cell23_112485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_112485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112485 prefixEnd_112485 := by exact prefixLift 112485
  have htrace : WordTrace (prefixWord ++ tailWord_112485) baseStart_112485 baseEnd_112485 := by
    simpa [prefixWord, tailWord_112485, baseEnd_112485] using wordTrace_append hprefix tailTrace_112485
  have hstable : (prefixWord ++ tailWord_112485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112485).length < 2 ^ (prefixWord ++ tailWord_112485).sum := by decide
  have hdescent : baseEnd_112485 < baseStart_112485 := by decide
  rcases family_descends (prefixWord ++ tailWord_112485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112491 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 4]
def baseStart_112491 : Nat := 118140960795 + 112491 * 2 ^ 59
def prefixEnd_112491 : Nat := 4983230072969 + 3 ^ 40 * 112491 * 2
def baseEnd_112491 : Nat := 57761952305024612145169

theorem tailTrace_112491 : CollatzResearch.WordTrace tailWord_112491 prefixEnd_112491 57761952305024612145169 := by
  unfold tailWord_112491
  simp only [CollatzResearch.WordTrace]
  refine ⟨4102883835471793778369327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2735255890314529185579551 4102883835471793778369327)
  ·
    refine ⟨6154325753207690667553991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4102883835471793778369327 6154325753207690667553991)
    ·
      refine ⟨9231488629811536001330987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6154325753207690667553991 9231488629811536001330987)
      ·
        refine ⟨13847232944717304001996481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9231488629811536001330987 13847232944717304001996481)
        ·
          refine ⟨10385424708537978001497361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13847232944717304001996481 10385424708537978001497361)
          ·
            refine ⟨7789068531403483501123021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10385424708537978001497361 7789068531403483501123021)
            ·
              refine ⟨2920900699276306312921133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7789068531403483501123021 2920900699276306312921133)
              ·
                refine ⟨1095337762228614867345425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2920900699276306312921133 1095337762228614867345425)
                ·
                  refine ⟨821503321671461150509069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1095337762228614867345425 821503321671461150509069)
                  ·
                    refine ⟨308063745626797931440901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 821503321671461150509069 308063745626797931440901)
                    ·
                      refine ⟨57761952305024612145169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 308063745626797931440901 57761952305024612145169)
                      ·
                        rfl

theorem cell23_112491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 4].length) (baseStart_112491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112491 prefixEnd_112491 := by exact prefixLift 112491
  have htrace : WordTrace (prefixWord ++ tailWord_112491) baseStart_112491 baseEnd_112491 := by
    simpa [prefixWord, tailWord_112491, baseEnd_112491] using wordTrace_append hprefix tailTrace_112491
  have hstable : (prefixWord ++ tailWord_112491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112491).length < 2 ^ (prefixWord ++ tailWord_112491).sum := by decide
  have hdescent : baseEnd_112491 < baseStart_112491 := by decide
  rcases family_descends (prefixWord ++ tailWord_112491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112552 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 2, 6]
def baseStart_112552 : Nat := 118140960795 + 112552 * 2 ^ 59
def prefixEnd_112552 : Nat := 4983230072969 + 3 ^ 40 * 112552 * 2
def baseEnd_112552 : Nat := 19264424874982957827463

theorem tailTrace_112552 : CollatzResearch.WordTrace tailWord_112552 prefixEnd_112552 19264424874982957827463 := by
  unfold tailWord_112552
  simp only [CollatzResearch.WordTrace]
  refine ⟨2052554344125400598169955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2736739125500534130893273 2052554344125400598169955)
  ·
    refine ⟨3078831516188100897254933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2052554344125400598169955 3078831516188100897254933)
    ·
      refine ⟨144320227321317229558825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3078831516188100897254933 144320227321317229558825)
      ·
        refine ⟨108240170490987922169119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144320227321317229558825 108240170490987922169119)
        ·
          refine ⟨162360255736481883253679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108240170490987922169119 162360255736481883253679)
          ·
            refine ⟨243540383604722824880519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162360255736481883253679 243540383604722824880519)
            ·
              refine ⟨365310575407084237320779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243540383604722824880519 365310575407084237320779)
              ·
                refine ⟨547965863110626355981169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365310575407084237320779 547965863110626355981169)
                ·
                  refine ⟨410974397332969766985877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547965863110626355981169 410974397332969766985877)
                  ·
                    refine ⟨19264424874982957827463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 410974397332969766985877 19264424874982957827463)
                    ·
                      rfl

theorem cell23_112552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_112552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112552 prefixEnd_112552 := by exact prefixLift 112552
  have htrace : WordTrace (prefixWord ++ tailWord_112552) baseStart_112552 baseEnd_112552 := by
    simpa [prefixWord, tailWord_112552, baseEnd_112552] using wordTrace_append hprefix tailTrace_112552
  have hstable : (prefixWord ++ tailWord_112552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112552).length < 2 ^ (prefixWord ++ tailWord_112552).sum := by decide
  have hdescent : baseEnd_112552 < baseStart_112552 := by decide
  rcases family_descends (prefixWord ++ tailWord_112552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112571 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 7]
def baseStart_112571 : Nat := 118140960795 + 112571 * 2 ^ 59
def prefixEnd_112571 : Nat := 4983230072969 + 3 ^ 40 * 112571 * 2
def baseEnd_112571 : Nat := 57803030757384299144801

theorem tailTrace_112571 : CollatzResearch.WordTrace tailWord_112571 prefixEnd_112571 57803030757384299144801 := by
  unfold tailWord_112571
  simp only [CollatzResearch.WordTrace]
  refine ⟨4105801675181967441281567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2737201116787978294187711 4105801675181967441281567)
  ·
    refine ⟨6158702512772951161922351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4105801675181967441281567 6158702512772951161922351)
    ·
      refine ⟨9238053769159426742883527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6158702512772951161922351 9238053769159426742883527)
      ·
        refine ⟨13857080653739140114325291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9238053769159426742883527 13857080653739140114325291)
        ·
          refine ⟨20785620980608710171487937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13857080653739140114325291 20785620980608710171487937)
          ·
            refine ⟨15589215735456532628615953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20785620980608710171487937 15589215735456532628615953)
            ·
              refine ⟨11691911801592399471461965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15589215735456532628615953 11691911801592399471461965)
              ·
                refine ⟨4384466925597149801798237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11691911801592399471461965 4384466925597149801798237)
                ·
                  refine ⟨1644175097098931175674339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4384466925597149801798237 1644175097098931175674339)
                  ·
                    refine ⟨2466262645648396763511509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1644175097098931175674339 2466262645648396763511509)
                    ·
                      refine ⟨57803030757384299144801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2466262645648396763511509 57803030757384299144801)
                      ·
                        rfl

theorem cell23_112571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 7].length) (baseStart_112571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112571 prefixEnd_112571 := by exact prefixLift 112571
  have htrace : WordTrace (prefixWord ++ tailWord_112571) baseStart_112571 baseEnd_112571 := by
    simpa [prefixWord, tailWord_112571, baseEnd_112571] using wordTrace_append hprefix tailTrace_112571
  have hstable : (prefixWord ++ tailWord_112571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112571).length < 2 ^ (prefixWord ++ tailWord_112571).sum := by decide
  have hdescent : baseEnd_112571 < baseStart_112571 := by decide
  rcases family_descends (prefixWord ++ tailWord_112571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112716 : List Nat := [2, 2, 1, 3, 1, 1, 6, 2, 1, 1, 3]
def baseStart_112716 : Nat := 118140960795 + 112716 * 2 ^ 59
def prefixEnd_112716 : Nat := 4983230072969 + 3 ^ 40 * 112716 * 2
def baseEnd_112716 : Nat := 57877485452286231831635

theorem tailTrace_112716 : CollatzResearch.WordTrace tailWord_112716 prefixEnd_112716 57877485452286231831635 := by
  unfold tailWord_112716
  simp only [CollatzResearch.WordTrace]
  refine ⟨2055545129828328602655001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2740726839771104803540001 2055545129828328602655001)
  ·
    refine ⟨1541658847371246451991251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2055545129828328602655001 1541658847371246451991251)
    ·
      refine ⟨2312488271056869677986877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1541658847371246451991251 2312488271056869677986877)
      ·
        refine ⟨867183101646326129245079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2312488271056869677986877 867183101646326129245079)
        ·
          refine ⟨1300774652469489193867619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867183101646326129245079 1300774652469489193867619)
          ·
            refine ⟨1951161978704233790801429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300774652469489193867619 1951161978704233790801429)
            ·
              refine ⟨91460717751760958943817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1951161978704233790801429 91460717751760958943817)
              ·
                refine ⟨68595538313820719207863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91460717751760958943817 68595538313820719207863)
                ·
                  refine ⟨102893307470731078811795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68595538313820719207863 102893307470731078811795)
                  ·
                    refine ⟨154339961206096618217693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102893307470731078811795 154339961206096618217693)
                    ·
                      refine ⟨57877485452286231831635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 154339961206096618217693 57877485452286231831635)
                      ·
                        rfl

theorem cell23_112716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_112716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112716 prefixEnd_112716 := by exact prefixLift 112716
  have htrace : WordTrace (prefixWord ++ tailWord_112716) baseStart_112716 baseEnd_112716 := by
    simpa [prefixWord, tailWord_112716, baseEnd_112716] using wordTrace_append hprefix tailTrace_112716
  have hstable : (prefixWord ++ tailWord_112716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112716).length < 2 ^ (prefixWord ++ tailWord_112716).sum := by decide
  have hdescent : baseEnd_112716 < baseStart_112716 := by decide
  rcases family_descends (prefixWord ++ tailWord_112716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112732 : List Nat := [2, 2, 4, 1, 1, 3, 2, 1, 1, 6]
def baseStart_112732 : Nat := 118140960795 + 112732 * 2 ^ 59
def prefixEnd_112732 : Nat := 4983230072969 + 3 ^ 40 * 112732 * 2
def baseEnd_112732 : Nat := 19295233714252723077187

theorem tailTrace_112732 : CollatzResearch.WordTrace tailWord_112732 prefixEnd_112732 19295233714252723077187 := by
  unfold tailWord_112732
  simp only [CollatzResearch.WordTrace]
  refine ⟨2055836913799345968946225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2741115885065794625261633 2055836913799345968946225)
  ·
    refine ⟨1541877685349509476709669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2055836913799345968946225 1541877685349509476709669)
    ·
      refine ⟨289102066003033026883063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1541877685349509476709669 289102066003033026883063)
      ·
        refine ⟨433653099004549540324595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289102066003033026883063 433653099004549540324595)
        ·
          refine ⟨650479648506824310486893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433653099004549540324595 650479648506824310486893)
          ·
            refine ⟨243929868190059116432585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 650479648506824310486893 243929868190059116432585)
            ·
              refine ⟨182947401142544337324439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243929868190059116432585 182947401142544337324439)
              ·
                refine ⟨274421101713816505986659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182947401142544337324439 274421101713816505986659)
                ·
                  refine ⟨411631652570724758979989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274421101713816505986659 411631652570724758979989)
                  ·
                    refine ⟨19295233714252723077187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 411631652570724758979989 19295233714252723077187)
                    ·
                      rfl

theorem cell23_112732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_112732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112732 prefixEnd_112732 := by exact prefixLift 112732
  have htrace : WordTrace (prefixWord ++ tailWord_112732) baseStart_112732 baseEnd_112732 := by
    simpa [prefixWord, tailWord_112732, baseEnd_112732] using wordTrace_append hprefix tailTrace_112732
  have hstable : (prefixWord ++ tailWord_112732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112732).length < 2 ^ (prefixWord ++ tailWord_112732).sum := by decide
  have hdescent : baseEnd_112732 < baseStart_112732 := by decide
  rcases family_descends (prefixWord ++ tailWord_112732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112745 : List Nat := [1, 2, 1, 1, 1, 5, 5, 7]
def baseStart_112745 : Nat := 118140960795 + 112745 * 2 ^ 59
def prefixEnd_112745 : Nat := 4983230072969 + 3 ^ 40 * 112745 * 2
def baseEnd_112745 : Nat := 2144162088565430309963

theorem tailTrace_112745 : CollatzResearch.WordTrace tailWord_112745 prefixEnd_112745 2144162088565430309963 := by
  unfold tailWord_112745
  simp only [CollatzResearch.WordTrace]
  refine ⟨4112147976551595158115689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2741431984367730105410459 4112147976551595158115689)
  ·
    refine ⟨3084110982413696368586767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4112147976551595158115689 3084110982413696368586767)
    ·
      refine ⟨4626166473620544552880151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3084110982413696368586767 4626166473620544552880151)
      ·
        refine ⟨6939249710430816829320227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4626166473620544552880151 6939249710430816829320227)
        ·
          refine ⟨10408874565646225243980341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6939249710430816829320227 10408874565646225243980341)
          ·
            refine ⟨975831990529333616623157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10408874565646225243980341 975831990529333616623157)
            ·
              refine ⟨91484249112125026558421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 975831990529333616623157 91484249112125026558421)
              ·
                refine ⟨2144162088565430309963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 91484249112125026558421 2144162088565430309963)
                ·
                  rfl

theorem cell23_112745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 7].length) (baseStart_112745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112745 prefixEnd_112745 := by exact prefixLift 112745
  have htrace : WordTrace (prefixWord ++ tailWord_112745) baseStart_112745 baseEnd_112745 := by
    simpa [prefixWord, tailWord_112745, baseEnd_112745] using wordTrace_append hprefix tailTrace_112745
  have hstable : (prefixWord ++ tailWord_112745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112745).length < 2 ^ (prefixWord ++ tailWord_112745).sum := by decide
  have hdescent : baseEnd_112745 < baseStart_112745 := by decide
  rcases family_descends (prefixWord ++ tailWord_112745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112759 : List Nat := [1, 1, 3, 1, 1, 5, 4, 1, 1, 2, 3]
def baseStart_112759 : Nat := 118140960795 + 112759 * 2 ^ 59
def prefixEnd_112759 : Nat := 4983230072969 + 3 ^ 40 * 112759 * 2
def baseEnd_112759 : Nat := 57899565120429563593937

theorem tailTrace_112759 : CollatzResearch.WordTrace tailWord_112759 prefixEnd_112759 57899565120429563593937 := by
  unfold tailWord_112759
  simp only [CollatzResearch.WordTrace]
  refine ⟨4112658598500875549125331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2741772399000583699416887 4112658598500875549125331)
  ·
    refine ⟨6168987897751313323687997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4112658598500875549125331 6168987897751313323687997)
    ·
      refine ⟨2313370461656742496382999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6168987897751313323687997 2313370461656742496382999)
      ·
        refine ⟨3470055692485113744574499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2313370461656742496382999 3470055692485113744574499)
        ·
          refine ⟨5205083538727670616861749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3470055692485113744574499 5205083538727670616861749)
          ·
            refine ⟨487976581755719120330789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5205083538727670616861749 487976581755719120330789)
            ·
              refine ⟨91495609079197335062023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 487976581755719120330789 91495609079197335062023)
              ·
                refine ⟨137243413618796002593035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91495609079197335062023 137243413618796002593035)
                ·
                  refine ⟨205865120428194003889553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137243413618796002593035 205865120428194003889553)
                  ·
                    refine ⟨154398840321145502917165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 205865120428194003889553 154398840321145502917165)
                    ·
                      refine ⟨57899565120429563593937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 154398840321145502917165 57899565120429563593937)
                      ·
                        rfl

theorem cell23_112759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 1, 2, 3].length) (baseStart_112759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112759 prefixEnd_112759 := by exact prefixLift 112759
  have htrace : WordTrace (prefixWord ++ tailWord_112759) baseStart_112759 baseEnd_112759 := by
    simpa [prefixWord, tailWord_112759, baseEnd_112759] using wordTrace_append hprefix tailTrace_112759
  have hstable : (prefixWord ++ tailWord_112759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112759).length < 2 ^ (prefixWord ++ tailWord_112759).sum := by decide
  have hdescent : baseEnd_112759 < baseStart_112759 := by decide
  rcases family_descends (prefixWord ++ tailWord_112759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112802 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_112802 : Nat := 118140960795 + 112802 * 2 ^ 59
def prefixEnd_112802 : Nat := 4983230072969 + 3 ^ 40 * 112802 * 2
def baseEnd_112802 : Nat := 57921644788572895356239

theorem tailTrace_112802 : CollatzResearch.WordTrace tailWord_112802 prefixEnd_112802 57921644788572895356239 := by
  unfold tailWord_112802
  simp only [CollatzResearch.WordTrace]
  refine ⟨1028556734336273473235165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2742817958230062595293773 1028556734336273473235165)
  ·
    refine ⟨385708775376102552463187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1028556734336273473235165 385708775376102552463187)
    ·
      refine ⟨578563163064153828694781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385708775376102552463187 578563163064153828694781)
      ·
        refine ⟨216961186149057685760543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 578563163064153828694781 216961186149057685760543)
        ·
          refine ⟨325441779223586528640815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216961186149057685760543 325441779223586528640815)
          ·
            refine ⟨488162668835379792961223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325441779223586528640815 488162668835379792961223)
            ·
              refine ⟨732244003253069689441835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488162668835379792961223 732244003253069689441835)
              ·
                refine ⟨1098366004879604534162753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732244003253069689441835 1098366004879604534162753)
                ·
                  refine ⟨823774503659703400622065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1098366004879604534162753 823774503659703400622065)
                  ·
                    refine ⟨617830877744777550466549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 823774503659703400622065 617830877744777550466549)
                    ·
                      refine ⟨57921644788572895356239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 617830877744777550466549 57921644788572895356239)
                      ·
                        rfl

theorem cell23_112802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_112802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112802 prefixEnd_112802 := by exact prefixLift 112802
  have htrace : WordTrace (prefixWord ++ tailWord_112802) baseStart_112802 baseEnd_112802 := by
    simpa [prefixWord, tailWord_112802, baseEnd_112802] using wordTrace_append hprefix tailTrace_112802
  have hstable : (prefixWord ++ tailWord_112802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112802).length < 2 ^ (prefixWord ++ tailWord_112802).sum := by decide
  have hdescent : baseEnd_112802 < baseStart_112802 := by decide
  rcases family_descends (prefixWord ++ tailWord_112802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112807 : List Nat := [1, 1, 6, 2, 3, 1, 1, 3, 1, 2, 2]
def baseStart_112807 : Nat := 118140960795 + 112807 * 2 ^ 59
def prefixEnd_112807 : Nat := 4983230072969 + 3 ^ 40 * 112807 * 2
def baseEnd_112807 : Nat := 57924212191845375793717

theorem tailTrace_112807 : CollatzResearch.WordTrace tailWord_112807 prefixEnd_112807 57924212191845375793717 := by
  unfold tailWord_112807
  simp only [CollatzResearch.WordTrace]
  refine ⟨4114409302326979746872675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2742939534884653164581783 4114409302326979746872675)
  ·
    refine ⟨6171613953490469620309013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4114409302326979746872675 6171613953490469620309013)
    ·
      refine ⟨289294404069865763451985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6171613953490469620309013 289294404069865763451985)
      ·
        refine ⟨216970803052399322588989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289294404069865763451985 216970803052399322588989)
        ·
          refine ⟨81364051144649745970871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216970803052399322588989 81364051144649745970871)
          ·
            refine ⟨122046076716974618956307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81364051144649745970871 122046076716974618956307)
            ·
              refine ⟨183069115075461928434461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122046076716974618956307 183069115075461928434461)
              ·
                refine ⟨68650918153298223162923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183069115075461928434461 68650918153298223162923)
                ·
                  refine ⟨102976377229947334744385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68650918153298223162923 102976377229947334744385)
                  ·
                    refine ⟨77232282922460501058289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102976377229947334744385 77232282922460501058289)
                    ·
                      refine ⟨57924212191845375793717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 77232282922460501058289 57924212191845375793717)
                      ·
                        rfl

theorem cell23_112807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_112807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112807 prefixEnd_112807 := by exact prefixLift 112807
  have htrace : WordTrace (prefixWord ++ tailWord_112807) baseStart_112807 baseEnd_112807 := by
    simpa [prefixWord, tailWord_112807, baseEnd_112807] using wordTrace_append hprefix tailTrace_112807
  have hstable : (prefixWord ++ tailWord_112807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112807).length < 2 ^ (prefixWord ++ tailWord_112807).sum := by decide
  have hdescent : baseEnd_112807 < baseStart_112807 := by decide
  rcases family_descends (prefixWord ++ tailWord_112807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112815 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 3]
def baseStart_112815 : Nat := 118140960795 + 112815 * 2 ^ 59
def prefixEnd_112815 : Nat := 4983230072969 + 3 ^ 40 * 112815 * 2
def baseEnd_112815 : Nat := 57928320037081344493679

theorem tailTrace_112815 : CollatzResearch.WordTrace tailWord_112815 prefixEnd_112815 57928320037081344493679 := by
  unfold tailWord_112815
  simp only [CollatzResearch.WordTrace]
  refine ⟨4114701086297997113163899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2743134057531998075442599 4114701086297997113163899)
  ·
    refine ⟨6172051629446995669745849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4114701086297997113163899 6172051629446995669745849)
    ·
      refine ⟨4629038722085246752309387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6172051629446995669745849 4629038722085246752309387)
      ·
        refine ⟨6943558083127870128464081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4629038722085246752309387 6943558083127870128464081)
        ·
          refine ⟨5207668562345902596348061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6943558083127870128464081 5207668562345902596348061)
          ·
            refine ⟨1952875710879713473630523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5207668562345902596348061 1952875710879713473630523)
            ·
              refine ⟨2929313566319570210445785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1952875710879713473630523 2929313566319570210445785)
              ·
                refine ⟨2196985174739677657834339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2929313566319570210445785 2196985174739677657834339)
                ·
                  refine ⟨3295477762109516486751509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2196985174739677657834339 3295477762109516486751509)
                  ·
                    refine ⟨154475520098883585316477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3295477762109516486751509 154475520098883585316477)
                    ·
                      refine ⟨57928320037081344493679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 154475520098883585316477 57928320037081344493679)
                      ·
                        rfl

theorem cell23_112815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 3].length) (baseStart_112815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112815 prefixEnd_112815 := by exact prefixLift 112815
  have htrace : WordTrace (prefixWord ++ tailWord_112815) baseStart_112815 baseEnd_112815 := by
    simpa [prefixWord, tailWord_112815, baseEnd_112815] using wordTrace_append hprefix tailTrace_112815
  have hstable : (prefixWord ++ tailWord_112815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112815).length < 2 ^ (prefixWord ++ tailWord_112815).sum := by decide
  have hdescent : baseEnd_112815 < baseStart_112815 := by decide
  rcases family_descends (prefixWord ++ tailWord_112815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112875 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 5]
def baseStart_112875 : Nat := 118140960795 + 112875 * 2 ^ 59
def prefixEnd_112875 : Nat := 4983230072969 + 3 ^ 40 * 112875 * 2
def baseEnd_112875 : Nat := 57959128876351109743403

theorem tailTrace_112875 : CollatzResearch.WordTrace tailWord_112875 prefixEnd_112875 57959128876351109743403 := by
  unfold tailWord_112875
  simp only [CollatzResearch.WordTrace]
  refine ⟨4116889466080627360348079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2744592977387084906898719 4116889466080627360348079)
  ·
    refine ⟨6175334199120941040522119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4116889466080627360348079 6175334199120941040522119)
    ·
      refine ⟨9263001298681411560783179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6175334199120941040522119 9263001298681411560783179)
      ·
        refine ⟨13894501948022117341174769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9263001298681411560783179 13894501948022117341174769)
        ·
          refine ⟨10420876461016588005881077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13894501948022117341174769 10420876461016588005881077)
          ·
            refine ⟨976957168220305125551351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10420876461016588005881077 976957168220305125551351)
            ·
              refine ⟨1465435752330457688327027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976957168220305125551351 1465435752330457688327027)
              ·
                refine ⟨2198153628495686532490541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1465435752330457688327027 2198153628495686532490541)
                ·
                  refine ⟨824307610685882449683953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2198153628495686532490541 824307610685882449683953)
                  ·
                    refine ⟨618230708014411837262965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 824307610685882449683953 618230708014411837262965)
                    ·
                      refine ⟨57959128876351109743403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 618230708014411837262965 57959128876351109743403)
                      ·
                        rfl

theorem cell23_112875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 5].length) (baseStart_112875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112875 prefixEnd_112875 := by exact prefixLift 112875
  have htrace : WordTrace (prefixWord ++ tailWord_112875) baseStart_112875 baseEnd_112875 := by
    simpa [prefixWord, tailWord_112875, baseEnd_112875] using wordTrace_append hprefix tailTrace_112875
  have hstable : (prefixWord ++ tailWord_112875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112875).length < 2 ^ (prefixWord ++ tailWord_112875).sum := by decide
  have hdescent : baseEnd_112875 < baseStart_112875 := by decide
  rcases family_descends (prefixWord ++ tailWord_112875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112886 : List Nat := [5, 1, 1, 1, 1, 1, 6, 2, 5]
def baseStart_112886 : Nat := 118140960795 + 112886 * 2 ^ 59
def prefixEnd_112886 : Nat := 4983230072969 + 3 ^ 40 * 112886 * 2
def baseEnd_112886 : Nat := 6440530795950062967317

theorem tailTrace_112886 : CollatzResearch.WordTrace tailWord_112886 prefixEnd_112886 6440530795950062967317 := by
  unfold tailWord_112886
  simp only [CollatzResearch.WordTrace]
  refine ⟨257330666815048514937407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2744860446027184159332341 257330666815048514937407)
  ·
    refine ⟨385996000222572772406111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 257330666815048514937407 385996000222572772406111)
    ·
      refine ⟨578994000333859158609167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385996000222572772406111 578994000333859158609167)
      ·
        refine ⟨868491000500788737913751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578994000333859158609167 868491000500788737913751)
        ·
          refine ⟨1302736500751183106870627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 868491000500788737913751 1302736500751183106870627)
          ·
            refine ⟨1954104751126774660305941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1302736500751183106870627 1954104751126774660305941)
            ·
              refine ⟨91598660209067562201841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1954104751126774660305941 91598660209067562201841)
              ·
                refine ⟨68698995156800671651381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91598660209067562201841 68698995156800671651381)
                ·
                  refine ⟨6440530795950062967317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68698995156800671651381 6440530795950062967317)
                  ·
                    rfl

theorem cell23_112886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_112886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112886 prefixEnd_112886 := by exact prefixLift 112886
  have htrace : WordTrace (prefixWord ++ tailWord_112886) baseStart_112886 baseEnd_112886 := by
    simpa [prefixWord, tailWord_112886, baseEnd_112886] using wordTrace_append hprefix tailTrace_112886
  have hstable : (prefixWord ++ tailWord_112886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112886).length < 2 ^ (prefixWord ++ tailWord_112886).sum := by decide
  have hdescent : baseEnd_112886 < baseStart_112886 := by decide
  rcases family_descends (prefixWord ++ tailWord_112886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112892 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_112892 : Nat := 118140960795 + 112892 * 2 ^ 59
def prefixEnd_112892 : Nat := 4983230072969 + 3 ^ 40 * 112892 * 2
def baseEnd_112892 : Nat := 57967858047477543230825

theorem tailTrace_112892 : CollatzResearch.WordTrace tailWord_112892 prefixEnd_112892 57967858047477543230825 := by
  unfold tailWord_112892
  simp only [CollatzResearch.WordTrace]
  refine ⟨2058754753509519631858465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2745006338012692842477953 2058754753509519631858465)
  ·
    refine ⟨1544066065132139723893849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2058754753509519631858465 1544066065132139723893849)
    ·
      refine ⟨1158049548849104792920387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1544066065132139723893849 1158049548849104792920387)
      ·
        refine ⟨1737074323273657189380581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1158049548849104792920387 1737074323273657189380581)
        ·
          refine ⟨325701435613810723008859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1737074323273657189380581 325701435613810723008859)
          ·
            refine ⟨488552153420716084513289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325701435613810723008859 488552153420716084513289)
            ·
              refine ⟨366414115065537063384967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488552153420716084513289 366414115065537063384967)
              ·
                refine ⟨549621172598305595077451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366414115065537063384967 549621172598305595077451)
                ·
                  refine ⟨824431758897458392616177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 549621172598305595077451 824431758897458392616177)
                  ·
                    refine ⟨618323819173093794462133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 824431758897458392616177 618323819173093794462133)
                    ·
                      refine ⟨57967858047477543230825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 618323819173093794462133 57967858047477543230825)
                      ·
                        rfl

theorem cell23_112892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_112892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112892 prefixEnd_112892 := by exact prefixLift 112892
  have htrace : WordTrace (prefixWord ++ tailWord_112892) baseStart_112892 baseEnd_112892 := by
    simpa [prefixWord, tailWord_112892, baseEnd_112892] using wordTrace_append hprefix tailTrace_112892
  have hstable : (prefixWord ++ tailWord_112892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112892).length < 2 ^ (prefixWord ++ tailWord_112892).sum := by decide
  have hdescent : baseEnd_112892 < baseStart_112892 := by decide
  rcases family_descends (prefixWord ++ tailWord_112892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112915 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 6]
def baseStart_112915 : Nat := 118140960795 + 112915 * 2 ^ 59
def prefixEnd_112915 : Nat := 4983230072969 + 3 ^ 40 * 112915 * 2
def baseEnd_112915 : Nat := 57979668102530953243219

theorem tailTrace_112915 : CollatzResearch.WordTrace tailWord_112915 prefixEnd_112915 57979668102530953243219 := by
  unfold tailWord_112915
  simp only [CollatzResearch.WordTrace]
  refine ⟨4118348385935714191804199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2745565590623809461202799 4118348385935714191804199)
  ·
    refine ⟨6177522578903571287706299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4118348385935714191804199 6177522578903571287706299)
    ·
      refine ⟨9266283868355356931559449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6177522578903571287706299 9266283868355356931559449)
      ·
        refine ⟨6949712901266517698669587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9266283868355356931559449 6949712901266517698669587)
        ·
          refine ⟨10424569351899776548004381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6949712901266517698669587 10424569351899776548004381)
          ·
            refine ⟨3909213506962416205501643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10424569351899776548004381 3909213506962416205501643)
            ·
              refine ⟨5863820260443624308252465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3909213506962416205501643 5863820260443624308252465)
              ·
                refine ⟨4397865195332718231189349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5863820260443624308252465 4397865195332718231189349)
                ·
                  refine ⟨824599724124884668348003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4397865195332718231189349 824599724124884668348003)
                  ·
                    refine ⟨1236899586187327002522005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 824599724124884668348003 1236899586187327002522005)
                    ·
                      refine ⟨57979668102530953243219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1236899586187327002522005 57979668102530953243219)
                      ·
                        rfl

theorem cell23_112915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_112915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112915 prefixEnd_112915 := by exact prefixLift 112915
  have htrace : WordTrace (prefixWord ++ tailWord_112915) baseStart_112915 baseEnd_112915 := by
    simpa [prefixWord, tailWord_112915, baseEnd_112915] using wordTrace_append hprefix tailTrace_112915
  have hstable : (prefixWord ++ tailWord_112915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112915).length < 2 ^ (prefixWord ++ tailWord_112915).sum := by decide
  have hdescent : baseEnd_112915 < baseStart_112915 := by decide
  rcases family_descends (prefixWord ++ tailWord_112915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112919 : List Nat := [1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 4]
def baseStart_112919 : Nat := 118140960795 + 112919 * 2 ^ 59
def prefixEnd_112919 : Nat := 4983230072969 + 3 ^ 40 * 112919 * 2
def baseEnd_112919 : Nat := 57981722025148937593201

theorem tailTrace_112919 : CollatzResearch.WordTrace tailWord_112919 prefixEnd_112919 57981722025148937593201 := by
  unfold tailWord_112919
  simp only [CollatzResearch.WordTrace]
  refine ⟨4118494277921222874949811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2745662851947481916633207 4118494277921222874949811)
  ·
    refine ⟨6177741416881834312424717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4118494277921222874949811 6177741416881834312424717)
    ·
      refine ⟨2316653031330687867159269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6177741416881834312424717 2316653031330687867159269)
      ·
        refine ⟨434372443374503975092363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2316653031330687867159269 434372443374503975092363)
        ·
          refine ⟨651558665061755962638545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434372443374503975092363 651558665061755962638545)
          ·
            refine ⟨488668998796316971978909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 651558665061755962638545 488668998796316971978909)
            ·
              refine ⟨183250874548618864492091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 488668998796316971978909 183250874548618864492091)
              ·
                refine ⟨274876311822928296738137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183250874548618864492091 274876311822928296738137)
                ·
                  refine ⟨206157233867196222553603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274876311822928296738137 206157233867196222553603)
                  ·
                    refine ⟨309235850800794333830405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 206157233867196222553603 309235850800794333830405)
                    ·
                      refine ⟨57981722025148937593201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 309235850800794333830405 57981722025148937593201)
                      ·
                        rfl

theorem cell23_112919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_112919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112919 prefixEnd_112919 := by exact prefixLift 112919
  have htrace : WordTrace (prefixWord ++ tailWord_112919) baseStart_112919 baseEnd_112919 := by
    simpa [prefixWord, tailWord_112919, baseEnd_112919] using wordTrace_append hprefix tailTrace_112919
  have hstable : (prefixWord ++ tailWord_112919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112919).length < 2 ^ (prefixWord ++ tailWord_112919).sum := by decide
  have hdescent : baseEnd_112919 < baseStart_112919 := by decide
  rcases family_descends (prefixWord ++ tailWord_112919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112932 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_112932 : Nat := 118140960795 + 112932 * 2 ^ 59
def prefixEnd_112932 : Nat := 4983230072969 + 3 ^ 40 * 112932 * 2
def baseEnd_112932 : Nat := 57988397273657386730641

theorem tailTrace_112932 : CollatzResearch.WordTrace tailWord_112932 prefixEnd_112932 57988397273657386730641 := by
  unfold tailWord_112932
  simp only [CollatzResearch.WordTrace]
  refine ⟨2059484213437063047586525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2745978951249417396782033 2059484213437063047586525)
  ·
    refine ⟨772306580038898642844947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2059484213437063047586525 772306580038898642844947)
    ·
      refine ⟨1158459870058347964267421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 772306580038898642844947 1158459870058347964267421)
      ·
        refine ⟨434422451271880486600283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1158459870058347964267421 434422451271880486600283)
        ·
          refine ⟨651633676907820729900425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434422451271880486600283 651633676907820729900425)
          ·
            refine ⟨488725257680865547425319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 651633676907820729900425 488725257680865547425319)
            ·
              refine ⟨733087886521298321137979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488725257680865547425319 733087886521298321137979)
              ·
                refine ⟨1099631829781947481706969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733087886521298321137979 1099631829781947481706969)
                ·
                  refine ⟨824723872336460611280227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1099631829781947481706969 824723872336460611280227)
                  ·
                    refine ⟨1237085808504690916920341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 824723872336460611280227 1237085808504690916920341)
                    ·
                      refine ⟨57988397273657386730641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1237085808504690916920341 57988397273657386730641)
                      ·
                        rfl

theorem cell23_112932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_112932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112932 prefixEnd_112932 := by exact prefixLift 112932
  have htrace : WordTrace (prefixWord ++ tailWord_112932) baseStart_112932 baseEnd_112932 := by
    simpa [prefixWord, tailWord_112932, baseEnd_112932] using wordTrace_append hprefix tailTrace_112932
  have hstable : (prefixWord ++ tailWord_112932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112932).length < 2 ^ (prefixWord ++ tailWord_112932).sum := by decide
  have hdescent : baseEnd_112932 < baseStart_112932 := by decide
  rcases family_descends (prefixWord ++ tailWord_112932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112946 : List Nat := [3, 2, 1, 1, 5, 1, 2, 1, 3, 4]
def baseStart_112946 : Nat := 118140960795 + 112946 * 2 ^ 59
def prefixEnd_112946 : Nat := 4983230072969 + 3 ^ 40 * 112946 * 2
def baseEnd_112946 : Nat := 19331862000940110651859

theorem tailTrace_112946 : CollatzResearch.WordTrace tailWord_112946 prefixEnd_112946 19331862000940110651859 := by
  unfold tailWord_112946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1029869762205851621545673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2746319365882270990788461 1029869762205851621545673)
  ·
    refine ⟨772402321654388716159255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1029869762205851621545673 772402321654388716159255)
    ·
      refine ⟨1158603482481583074238883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 772402321654388716159255 1158603482481583074238883)
      ·
        refine ⟨1737905223722374611358325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1158603482481583074238883 1737905223722374611358325)
        ·
          refine ⟨162928614723972619814843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1737905223722374611358325 162928614723972619814843)
          ·
            refine ⟨244392922085958929722265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162928614723972619814843 244392922085958929722265)
            ·
              refine ⟨183294691564469197291699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244392922085958929722265 183294691564469197291699)
              ·
                refine ⟨274942037346703795937549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183294691564469197291699 274942037346703795937549)
                ·
                  refine ⟨103103264005013923476581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274942037346703795937549 103103264005013923476581)
                  ·
                    refine ⟨19331862000940110651859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103103264005013923476581 19331862000940110651859)
                    ·
                      rfl

theorem cell23_112946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_112946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112946 prefixEnd_112946 := by exact prefixLift 112946
  have htrace : WordTrace (prefixWord ++ tailWord_112946) baseStart_112946 baseEnd_112946 := by
    simpa [prefixWord, tailWord_112946, baseEnd_112946] using wordTrace_append hprefix tailTrace_112946
  have hstable : (prefixWord ++ tailWord_112946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112946).length < 2 ^ (prefixWord ++ tailWord_112946).sum := by decide
  have hdescent : baseEnd_112946 < baseStart_112946 := by decide
  rcases family_descends (prefixWord ++ tailWord_112946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112959 : List Nat := [1, 1, 2, 2, 4, 1, 5, 1, 6]
def baseStart_112959 : Nat := 118140960795 + 112959 * 2 ^ 59
def prefixEnd_112959 : Nat := 4983230072969 + 3 ^ 40 * 112959 * 2
def baseEnd_112959 : Nat := 6444695694592086788113

theorem tailTrace_112959 : CollatzResearch.WordTrace tailWord_112959 prefixEnd_112959 6444695694592086788113 := by
  unfold tailWord_112959
  simp only [CollatzResearch.WordTrace]
  refine ⟨4119953197776309706405931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2746635465184206470937287 4119953197776309706405931)
  ·
    refine ⟨6179929796664464559608897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4119953197776309706405931 6179929796664464559608897)
    ·
      refine ⟨4634947347498348419706673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6179929796664464559608897 4634947347498348419706673)
      ·
        refine ⟨3476210510623761314780005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4634947347498348419706673 3476210510623761314780005)
        ·
          refine ⟨651789470741955246521251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3476210510623761314780005 651789470741955246521251)
          ·
            refine ⟨977684206112932869781877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651789470741955246521251 977684206112932869781877)
            ·
              refine ⟨91657894323087456542051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 977684206112932869781877 91657894323087456542051)
              ·
                refine ⟨137486841484631184813077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91657894323087456542051 137486841484631184813077)
                ·
                  refine ⟨6444695694592086788113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137486841484631184813077 6444695694592086788113)
                  ·
                    rfl

theorem cell23_112959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 6].length) (baseStart_112959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112959 prefixEnd_112959 := by exact prefixLift 112959
  have htrace : WordTrace (prefixWord ++ tailWord_112959) baseStart_112959 baseEnd_112959 := by
    simpa [prefixWord, tailWord_112959, baseEnd_112959] using wordTrace_append hprefix tailTrace_112959
  have hstable : (prefixWord ++ tailWord_112959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112959).length < 2 ^ (prefixWord ++ tailWord_112959).sum := by decide
  have hdescent : baseEnd_112959 < baseStart_112959 := by decide
  rcases family_descends (prefixWord ++ tailWord_112959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112996 : List Nat := [2, 3, 1, 1, 3, 1, 3, 2, 2, 3, 2]
def baseStart_112996 : Nat := 118140960795 + 112996 * 2 ^ 59
def prefixEnd_112996 : Nat := 4983230072969 + 3 ^ 40 * 112996 * 2
def baseEnd_112996 : Nat := 58021260035545136330347

theorem tailTrace_112996 : CollatzResearch.WordTrace tailWord_112996 prefixEnd_112996 58021260035545136330347 := by
  unfold tailWord_112996
  simp only [CollatzResearch.WordTrace]
  refine ⟨2060651349321132512751421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2747535132428176683668561 2060651349321132512751421)
  ·
    refine ⟨772744255995424692281783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2060651349321132512751421 772744255995424692281783)
    ·
      refine ⟨1159116383993137038422675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 772744255995424692281783 1159116383993137038422675)
      ·
        refine ⟨1738674575989705557634013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1159116383993137038422675 1738674575989705557634013)
        ·
          refine ⟨652002965996139584112755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1738674575989705557634013 652002965996139584112755)
          ·
            refine ⟨978004448994209376169133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652002965996139584112755 978004448994209376169133)
            ·
              refine ⟨366751668372828516063425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 978004448994209376169133 366751668372828516063425)
              ·
                refine ⟨275063751279621387047569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366751668372828516063425 275063751279621387047569)
                ·
                  refine ⟨206297813459716040285677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275063751279621387047569 206297813459716040285677)
                  ·
                    refine ⟨77361680047393515107129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 206297813459716040285677 77361680047393515107129)
                    ·
                      refine ⟨58021260035545136330347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 77361680047393515107129 58021260035545136330347)
                      ·
                        rfl

theorem cell23_112996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_112996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_112996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_112996 prefixEnd_112996 := by exact prefixLift 112996
  have htrace : WordTrace (prefixWord ++ tailWord_112996) baseStart_112996 baseEnd_112996 := by
    simpa [prefixWord, tailWord_112996, baseEnd_112996] using wordTrace_append hprefix tailTrace_112996
  have hstable : (prefixWord ++ tailWord_112996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112996).length < 2 ^ (prefixWord ++ tailWord_112996).sum := by decide
  have hdescent : baseEnd_112996 < baseStart_112996 := by decide
  rcases family_descends (prefixWord ++ tailWord_112996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113032 : List Nat := [2, 1, 3, 3, 1, 1, 1, 11]
def baseStart_113032 : Nat := 118140960795 + 113032 * 2 ^ 59
def prefixEnd_113032 : Nat := 4983230072969 + 3 ^ 40 * 113032 * 2
def baseEnd_113032 : Nat := 2149620197744703536303

theorem tailTrace_113032 : CollatzResearch.WordTrace tailWord_113032 prefixEnd_113032 2149620197744703536303 := by
  unfold tailWord_113032
  simp only [CollatzResearch.WordTrace]
  refine ⟨2061307863255921586906675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2748410484341228782542233 2061307863255921586906675)
  ·
    refine ⟨3091961794883882380360013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2061307863255921586906675 3091961794883882380360013)
    ·
      refine ⟨1159485673081455892635005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3091961794883882380360013 1159485673081455892635005)
      ·
        refine ⟨434807127405545959738127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1159485673081455892635005 434807127405545959738127)
        ·
          refine ⟨652210691108318939607191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434807127405545959738127 652210691108318939607191)
          ·
            refine ⟨978316036662478409410787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652210691108318939607191 978316036662478409410787)
            ·
              refine ⟨1467474054993717614116181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978316036662478409410787 1467474054993717614116181)
              ·
                refine ⟨2149620197744703536303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 1467474054993717614116181 2149620197744703536303)
                ·
                  rfl

theorem cell23_113032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 11].length) (baseStart_113032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113032 prefixEnd_113032 := by exact prefixLift 113032
  have htrace : WordTrace (prefixWord ++ tailWord_113032) baseStart_113032 baseEnd_113032 := by
    simpa [prefixWord, tailWord_113032, baseEnd_113032] using wordTrace_append hprefix tailTrace_113032
  have hstable : (prefixWord ++ tailWord_113032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113032).length < 2 ^ (prefixWord ++ tailWord_113032).sum := by decide
  have hdescent : baseEnd_113032 < baseStart_113032 := by decide
  rcases family_descends (prefixWord ++ tailWord_113032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113053 : List Nat := [1, 4, 2, 1, 4, 1, 2, 2, 2, 4]
def baseStart_113053 : Nat := 118140960795 + 113053 * 2 ^ 59
def prefixEnd_113053 : Nat := 4983230072969 + 3 ^ 40 * 113053 * 2
def baseEnd_113053 : Nat := 19350176144283804439195

theorem tailTrace_113053 : CollatzResearch.WordTrace tailWord_113053 prefixEnd_113053 19350176144283804439195 := by
  unfold tailWord_113053
  simp only [CollatzResearch.WordTrace]
  refine ⟨4123381659435763760327813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2748921106290509173551875 4123381659435763760327813)
  ·
    refine ⟨773134061144205705061465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4123381659435763760327813 773134061144205705061465)
    ·
      refine ⟨579850545858154278796099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 773134061144205705061465 579850545858154278796099)
      ·
        refine ⟨869775818787231418194149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579850545858154278796099 869775818787231418194149)
        ·
          refine ⟨163082966022605890911403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 869775818787231418194149 163082966022605890911403)
          ·
            refine ⟨244624449033908836367105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163082966022605890911403 244624449033908836367105)
            ·
              refine ⟨183468336775431627275329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244624449033908836367105 183468336775431627275329)
              ·
                refine ⟨137601252581573720456497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183468336775431627275329 137601252581573720456497)
                ·
                  refine ⟨103200939436180290342373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137601252581573720456497 103200939436180290342373)
                  ·
                    refine ⟨19350176144283804439195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103200939436180290342373 19350176144283804439195)
                    ·
                      rfl

theorem cell23_113053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_113053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113053 prefixEnd_113053 := by exact prefixLift 113053
  have htrace : WordTrace (prefixWord ++ tailWord_113053) baseStart_113053 baseEnd_113053 := by
    simpa [prefixWord, tailWord_113053, baseEnd_113053] using wordTrace_append hprefix tailTrace_113053
  have hstable : (prefixWord ++ tailWord_113053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113053).length < 2 ^ (prefixWord ++ tailWord_113053).sum := by decide
  have hdescent : baseEnd_113053 < baseStart_113053 := by decide
  rcases family_descends (prefixWord ++ tailWord_113053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113054 : List Nat := [4, 3, 1, 2, 1, 3, 2, 2, 1, 1, 3]
def baseStart_113054 : Nat := 118140960795 + 113054 * 2 ^ 59
def prefixEnd_113054 : Nat := 4983230072969 + 3 ^ 40 * 113054 * 2
def baseEnd_113054 : Nat := 58051041913505909405081

theorem tailTrace_113054 : CollatzResearch.WordTrace tailWord_113054 prefixEnd_113054 58051041913505909405081 := by
  unfold tailWord_113054
  simp only [CollatzResearch.WordTrace]
  refine ⟨515427266554017616389277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2748945421621427287409477 515427266554017616389277)
  ·
    refine ⟨193285224957756606145979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 515427266554017616389277 193285224957756606145979)
    ·
      refine ⟨289927837436634909218969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193285224957756606145979 289927837436634909218969)
      ·
        refine ⟨217445878077476181914227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289927837436634909218969 217445878077476181914227)
        ·
          refine ⟨326168817116214272871341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217445878077476181914227 326168817116214272871341)
          ·
            refine ⟨122313306418580352326753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326168817116214272871341 122313306418580352326753)
            ·
              refine ⟨91734979813935264245065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122313306418580352326753 91734979813935264245065)
              ·
                refine ⟨68801234860451448183799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91734979813935264245065 68801234860451448183799)
                ·
                  refine ⟨103201852290677172275699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68801234860451448183799 103201852290677172275699)
                  ·
                    refine ⟨154802778436015758413549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103201852290677172275699 154802778436015758413549)
                    ·
                      refine ⟨58051041913505909405081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 154802778436015758413549 58051041913505909405081)
                      ·
                        rfl

theorem cell23_113054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_113054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113054 prefixEnd_113054 := by exact prefixLift 113054
  have htrace : WordTrace (prefixWord ++ tailWord_113054) baseStart_113054 baseEnd_113054 := by
    simpa [prefixWord, tailWord_113054, baseEnd_113054] using wordTrace_append hprefix tailTrace_113054
  have hstable : (prefixWord ++ tailWord_113054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113054).length < 2 ^ (prefixWord ++ tailWord_113054).sum := by decide
  have hdescent : baseEnd_113054 < baseStart_113054 := by decide
  rcases family_descends (prefixWord ++ tailWord_113054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113109 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 2, 6]
def baseStart_113109 : Nat := 118140960795 + 113109 * 2 ^ 59
def prefixEnd_113109 : Nat := 4983230072969 + 3 ^ 40 * 113109 * 2
def baseEnd_113109 : Nat := 19359761116501064739109

theorem tailTrace_113109 : CollatzResearch.WordTrace tailWord_113109 prefixEnd_113109 19359761116501064739109 := by
  unfold tailWord_113109
  simp only [CollatzResearch.WordTrace]
  refine ⟨4125424147232885324366381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2750282764821923549577587 4125424147232885324366381)
  ·
    refine ⟨1547034055212331996637393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4125424147232885324366381 1547034055212331996637393)
    ·
      refine ⟨1160275541409248997478045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1547034055212331996637393 1160275541409248997478045)
      ·
        refine ⟨435103328028468374054267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1160275541409248997478045 435103328028468374054267)
        ·
          refine ⟨652654992042702561081401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435103328028468374054267 652654992042702561081401)
          ·
            refine ⟨489491244032026920811051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 652654992042702561081401 489491244032026920811051)
            ·
              refine ⟨734236866048040381216577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489491244032026920811051 734236866048040381216577)
              ·
                refine ⟨550677649536030285912433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 734236866048040381216577 550677649536030285912433)
                ·
                  refine ⟨413008237152022714434325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 550677649536030285912433 413008237152022714434325)
                  ·
                    refine ⟨19359761116501064739109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 413008237152022714434325 19359761116501064739109)
                    ·
                      rfl

theorem cell23_113109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_113109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113109 prefixEnd_113109 := by exact prefixLift 113109
  have htrace : WordTrace (prefixWord ++ tailWord_113109) baseStart_113109 baseEnd_113109 := by
    simpa [prefixWord, tailWord_113109, baseEnd_113109] using wordTrace_append hprefix tailTrace_113109
  have hstable : (prefixWord ++ tailWord_113109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113109).length < 2 ^ (prefixWord ++ tailWord_113109).sum := by decide
  have hdescent : baseEnd_113109 < baseStart_113109 := by decide
  rcases family_descends (prefixWord ++ tailWord_113109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113173 : List Nat := [1, 3, 2, 1, 3, 1, 5, 2, 5]
def baseStart_113173 : Nat := 118140960795 + 113173 * 2 ^ 59
def prefixEnd_113173 : Nat := 4983230072969 + 3 ^ 40 * 113173 * 2
def baseEnd_113173 : Nat := 6456905123487882646337

theorem tailTrace_113173 : CollatzResearch.WordTrace tailWord_113173 prefixEnd_113173 6456905123487882646337 := by
  unfold tailWord_113173
  simp only [CollatzResearch.WordTrace]
  refine ⟨4127758419001024254696173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2751838946000682836464115 4127758419001024254696173)
  ·
    refine ⟨1547909407125384095511065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4127758419001024254696173 1547909407125384095511065)
    ·
      refine ⟨1160932055344038071633299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1547909407125384095511065 1160932055344038071633299)
      ·
        refine ⟨1741398083016057107449949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160932055344038071633299 1741398083016057107449949)
        ·
          refine ⟨653024281131021415293731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1741398083016057107449949 653024281131021415293731)
          ·
            refine ⟨979536421696532122940597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653024281131021415293731 979536421696532122940597)
            ·
              refine ⟨91831539534049886525681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 979536421696532122940597 91831539534049886525681)
              ·
                refine ⟨68873654650537414894261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91831539534049886525681 68873654650537414894261)
                ·
                  refine ⟨6456905123487882646337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68873654650537414894261 6456905123487882646337)
                  ·
                    rfl

theorem cell23_113173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 5].length) (baseStart_113173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113173 prefixEnd_113173 := by exact prefixLift 113173
  have htrace : WordTrace (prefixWord ++ tailWord_113173) baseStart_113173 baseEnd_113173 := by
    simpa [prefixWord, tailWord_113173, baseEnd_113173] using wordTrace_append hprefix tailTrace_113173
  have hstable : (prefixWord ++ tailWord_113173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113173).length < 2 ^ (prefixWord ++ tailWord_113173).sum := by decide
  have hdescent : baseEnd_113173 < baseStart_113173 := by decide
  rcases family_descends (prefixWord ++ tailWord_113173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113184 : List Nat := [2, 1, 1, 6, 2, 2, 2, 1, 2, 2, 2]
def baseStart_113184 : Nat := 118140960795 + 113184 * 2 ^ 59
def prefixEnd_113184 : Nat := 4983230072969 + 3 ^ 40 * 113184 * 2
def baseEnd_113184 : Nat := 58117794398590400779483

theorem tailTrace_113184 : CollatzResearch.WordTrace tailWord_113184 prefixEnd_113184 58117794398590400779483 := by
  unfold tailWord_113184
  simp only [CollatzResearch.WordTrace]
  refine ⟨2064079810980586566673303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2752106414640782088897737 2064079810980586566673303)
  ·
    refine ⟨3096119716470879850009955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2064079810980586566673303 3096119716470879850009955)
    ·
      refine ⟨4644179574706319775014933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3096119716470879850009955 4644179574706319775014933)
      ·
        refine ⟨217695917564358739453825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4644179574706319775014933 217695917564358739453825)
        ·
          refine ⟨163271938173269054590369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217695917564358739453825 163271938173269054590369)
          ·
            refine ⟨122453953629951790942777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163271938173269054590369 122453953629951790942777)
            ·
              refine ⟨91840465222463843207083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122453953629951790942777 91840465222463843207083)
              ·
                refine ⟨137760697833695764810625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91840465222463843207083 137760697833695764810625)
                ·
                  refine ⟨103320523375271823607969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137760697833695764810625 103320523375271823607969)
                  ·
                    refine ⟨77490392531453867705977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103320523375271823607969 77490392531453867705977)
                    ·
                      refine ⟨58117794398590400779483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 77490392531453867705977 58117794398590400779483)
                      ·
                        rfl

theorem cell23_113184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_113184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113184 prefixEnd_113184 := by exact prefixLift 113184
  have htrace : WordTrace (prefixWord ++ tailWord_113184) baseStart_113184 baseEnd_113184 := by
    simpa [prefixWord, tailWord_113184, baseEnd_113184] using wordTrace_append hprefix tailTrace_113184
  have hstable : (prefixWord ++ tailWord_113184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113184).length < 2 ^ (prefixWord ++ tailWord_113184).sum := by decide
  have hdescent : baseEnd_113184 < baseStart_113184 := by decide
  rcases family_descends (prefixWord ++ tailWord_113184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113189 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 3, 3, 4]
def baseStart_113189 : Nat := 118140960795 + 113189 * 2 ^ 59
def prefixEnd_113189 : Nat := 4983230072969 + 3 ^ 40 * 113189 * 2
def baseEnd_113189 : Nat := 58120361801862881216959

theorem tailTrace_113189 : CollatzResearch.WordTrace tailWord_113189 prefixEnd_113189 58120361801862881216959 := by
  unfold tailWord_113189
  simp only [CollatzResearch.WordTrace]
  refine ⟨4128341986943058987278621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2752227991295372658185747 4128341986943058987278621)
  ·
    refine ⟨1548128245103647120229483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4128341986943058987278621 1548128245103647120229483)
    ·
      refine ⟨2322192367655470680344225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1548128245103647120229483 2322192367655470680344225)
      ·
        refine ⟨1741644275741603010258169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2322192367655470680344225 1741644275741603010258169)
        ·
          refine ⟨1306233206806202257693627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1741644275741603010258169 1306233206806202257693627)
          ·
            refine ⟨1959349810209303386540441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306233206806202257693627 1959349810209303386540441)
            ·
              refine ⟨1469512357656977539905331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1959349810209303386540441 1469512357656977539905331)
              ·
                refine ⟨2204268536485466309857997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1469512357656977539905331 2204268536485466309857997)
                ·
                  refine ⟨826600701182049866196749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2204268536485466309857997 826600701182049866196749)
                  ·
                    refine ⟨309975262943268699823781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 826600701182049866196749 309975262943268699823781)
                    ·
                      refine ⟨58120361801862881216959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 309975262943268699823781 58120361801862881216959)
                      ·
                        rfl

theorem cell23_113189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_113189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113189 prefixEnd_113189 := by exact prefixLift 113189
  have htrace : WordTrace (prefixWord ++ tailWord_113189) baseStart_113189 baseEnd_113189 := by
    simpa [prefixWord, tailWord_113189, baseEnd_113189] using wordTrace_append hprefix tailTrace_113189
  have hstable : (prefixWord ++ tailWord_113189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113189).length < 2 ^ (prefixWord ++ tailWord_113189).sum := by decide
  have hdescent : baseEnd_113189 < baseStart_113189 := by decide
  rcases family_descends (prefixWord ++ tailWord_113189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113283 : List Nat := [1, 1, 1, 3, 3, 1, 2, 4, 2, 3, 2]
def baseStart_113283 : Nat := 118140960795 + 113283 * 2 ^ 59
def prefixEnd_113283 : Nat := 4983230072969 + 3 ^ 40 * 113283 * 2
def baseEnd_113283 : Nat := 58168628983385513441527

theorem tailTrace_113283 : CollatzResearch.WordTrace tailWord_113283 prefixEnd_113283 58168628983385513441527 := by
  unfold tailWord_113283
  simp only [CollatzResearch.WordTrace]
  refine ⟨4131770448602513041200503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2754513632401675360800335 4131770448602513041200503)
  ·
    refine ⟨6197655672903769561800755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4131770448602513041200503 6197655672903769561800755)
    ·
      refine ⟨9296483509355654342701133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6197655672903769561800755 9296483509355654342701133)
      ·
        refine ⟨3486181316008370378512925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9296483509355654342701133 3486181316008370378512925)
        ·
          refine ⟨1307317993503138891942347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3486181316008370378512925 1307317993503138891942347)
          ·
            refine ⟨1960976990254708337913521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307317993503138891942347 1960976990254708337913521)
            ·
              refine ⟨1470732742691031253435141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1960976990254708337913521 1470732742691031253435141)
              ·
                refine ⟨275762389254568360019089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1470732742691031253435141 275762389254568360019089)
                ·
                  refine ⟨206821791940926270014317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275762389254568360019089 206821791940926270014317)
                  ·
                    refine ⟨77558171977847351255369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 206821791940926270014317 77558171977847351255369)
                    ·
                      refine ⟨58168628983385513441527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 77558171977847351255369 58168628983385513441527)
                      ·
                        rfl

theorem cell23_113283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 3, 2].length) (baseStart_113283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113283 prefixEnd_113283 := by exact prefixLift 113283
  have htrace : WordTrace (prefixWord ++ tailWord_113283) baseStart_113283 baseEnd_113283 := by
    simpa [prefixWord, tailWord_113283, baseEnd_113283] using wordTrace_append hprefix tailTrace_113283
  have hstable : (prefixWord ++ tailWord_113283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113283).length < 2 ^ (prefixWord ++ tailWord_113283).sum := by decide
  have hdescent : baseEnd_113283 < baseStart_113283 := by decide
  rcases family_descends (prefixWord ++ tailWord_113283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113300 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_113300 : Nat := 118140960795 + 113300 * 2 ^ 59
def prefixEnd_113300 : Nat := 4983230072969 + 3 ^ 40 * 113300 * 2
def baseEnd_113300 : Nat := 58177358154511946928949

theorem tailTrace_113300 : CollatzResearch.WordTrace tailWord_113300 prefixEnd_113300 58177358154511946928949 := by
  unfold tailWord_113300
  simp only [CollatzResearch.WordTrace]
  refine ⟨2066195244770462472284677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2754926993027283296379569 2066195244770462472284677)
  ·
    refine ⟨387411608394461713553377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2066195244770462472284677 387411608394461713553377)
    ·
      refine ⟨290558706295846285165033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387411608394461713553377 290558706295846285165033)
      ·
        refine ⟨217919029721884713873775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290558706295846285165033 217919029721884713873775)
        ·
          refine ⟨326878544582827070810663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217919029721884713873775 326878544582827070810663)
          ·
            refine ⟨490317816874240606215995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326878544582827070810663 490317816874240606215995)
            ·
              refine ⟨735476725311360909323993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490317816874240606215995 735476725311360909323993)
              ·
                refine ⟨551607543983520681992995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735476725311360909323993 551607543983520681992995)
                ·
                  refine ⟨827411315975281022989493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 551607543983520681992995 827411315975281022989493)
                  ·
                    refine ⟨77569810872682595905265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 827411315975281022989493 77569810872682595905265)
                    ·
                      refine ⟨58177358154511946928949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 77569810872682595905265 58177358154511946928949)
                      ·
                        rfl

theorem cell23_113300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_113300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113300 prefixEnd_113300 := by exact prefixLift 113300
  have htrace : WordTrace (prefixWord ++ tailWord_113300) baseStart_113300 baseEnd_113300 := by
    simpa [prefixWord, tailWord_113300, baseEnd_113300] using wordTrace_append hprefix tailTrace_113300
  have hstable : (prefixWord ++ tailWord_113300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113300).length < 2 ^ (prefixWord ++ tailWord_113300).sum := by decide
  have hdescent : baseEnd_113300 < baseStart_113300 := by decide
  rcases family_descends (prefixWord ++ tailWord_113300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113310 : List Nat := [4, 3, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_113310 : Nat := 118140960795 + 113310 * 2 ^ 59
def prefixEnd_113310 : Nat := 4983230072969 + 3 ^ 40 * 113310 * 2
def baseEnd_113310 : Nat := 19394164320352302601301

theorem tailTrace_113310 : CollatzResearch.WordTrace tailWord_113310 prefixEnd_113310 19394164320352302601301 := by
  unfold tailWord_113310
  simp only [CollatzResearch.WordTrace]
  refine ⟨516594402438087081554173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2755170146336464434955589 516594402438087081554173)
  ·
    refine ⟨193722900914282655582815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 516594402438087081554173 193722900914282655582815)
    ·
      refine ⟨290584351371423983374223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193722900914282655582815 290584351371423983374223)
      ·
        refine ⟨435876527057135975061335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290584351371423983374223 435876527057135975061335)
        ·
          refine ⟨653814790585703962592003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435876527057135975061335 653814790585703962592003)
          ·
            refine ⟨980722185878555943888005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653814790585703962592003 980722185878555943888005)
            ·
              refine ⟨183885409852229239479001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 980722185878555943888005 183885409852229239479001)
              ·
                refine ⟨137914057389171929609251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183885409852229239479001 137914057389171929609251)
                ·
                  refine ⟨206871086083757894413877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137914057389171929609251 206871086083757894413877)
                  ·
                    refine ⟨19394164320352302601301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 206871086083757894413877 19394164320352302601301)
                    ·
                      rfl

theorem cell23_113310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_113310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113310 prefixEnd_113310 := by exact prefixLift 113310
  have htrace : WordTrace (prefixWord ++ tailWord_113310) baseStart_113310 baseEnd_113310 := by
    simpa [prefixWord, tailWord_113310, baseEnd_113310] using wordTrace_append hprefix tailTrace_113310
  have hstable : (prefixWord ++ tailWord_113310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113310).length < 2 ^ (prefixWord ++ tailWord_113310).sum := by decide
  have hdescent : baseEnd_113310 < baseStart_113310 := by decide
  rcases family_descends (prefixWord ++ tailWord_113310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113316 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_113316 : Nat := 118140960795 + 113316 * 2 ^ 59
def prefixEnd_113316 : Nat := 4983230072969 + 3 ^ 40 * 113316 * 2
def baseEnd_113316 : Nat := 58185573844983884328875

theorem tailTrace_113316 : CollatzResearch.WordTrace tailWord_113316 prefixEnd_113316 58185573844983884328875 := by
  unfold tailWord_113316
  simp only [CollatzResearch.WordTrace]
  refine ⟨2066487028741479838575901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2755316038321973118101201 2066487028741479838575901)
  ·
    refine ⟨774932635778054939465963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2066487028741479838575901 774932635778054939465963)
    ·
      refine ⟨1162398953667082409198945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 774932635778054939465963 1162398953667082409198945)
      ·
        refine ⟨871799215250311806899209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1162398953667082409198945 871799215250311806899209)
        ·
          refine ⟨653849411437733855174407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 871799215250311806899209 653849411437733855174407)
          ·
            refine ⟨980774117156600782761611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653849411437733855174407 980774117156600782761611)
            ·
              refine ⟨1471161175734901174142417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980774117156600782761611 1471161175734901174142417)
              ·
                refine ⟨1103370881801175880606813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1471161175734901174142417 1103370881801175880606813)
                ·
                  refine ⟨413764080675440955227555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1103370881801175880606813 413764080675440955227555)
                  ·
                    refine ⟨620646121013161432841333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 413764080675440955227555 620646121013161432841333)
                    ·
                      refine ⟨58185573844983884328875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 620646121013161432841333 58185573844983884328875)
                      ·
                        rfl

theorem cell23_113316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_113316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113316 prefixEnd_113316 := by exact prefixLift 113316
  have htrace : WordTrace (prefixWord ++ tailWord_113316) baseStart_113316 baseEnd_113316 := by
    simpa [prefixWord, tailWord_113316, baseEnd_113316] using wordTrace_append hprefix tailTrace_113316
  have hstable : (prefixWord ++ tailWord_113316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113316).length < 2 ^ (prefixWord ++ tailWord_113316).sum := by decide
  have hdescent : baseEnd_113316 < baseStart_113316 := by decide
  rcases family_descends (prefixWord ++ tailWord_113316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113333 : List Nat := [1, 3, 3, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_113333 : Nat := 118140960795 + 113333 * 2 ^ 59
def prefixEnd_113333 : Nat := 4983230072969 + 3 ^ 40 * 113333 * 2
def baseEnd_113333 : Nat := 58194303016110317816297

theorem tailTrace_113333 : CollatzResearch.WordTrace tailWord_113333 prefixEnd_113333 58194303016110317816297 := by
  unfold tailWord_113333
  simp only [CollatzResearch.WordTrace]
  refine ⟨4133594098421371580520653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2755729398947581053680435 4133594098421371580520653)
  ·
    refine ⟨1550097786908014342695245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4133594098421371580520653 1550097786908014342695245)
    ·
      refine ⟨581286670090505378510717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1550097786908014342695245 581286670090505378510717)
      ·
        refine ⟨217982501283939516941519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 581286670090505378510717 217982501283939516941519)
        ·
          refine ⟨326973751925909275412279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217982501283939516941519 326973751925909275412279)
          ·
            refine ⟨490460627888863913118419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326973751925909275412279 490460627888863913118419)
            ·
              refine ⟨735690941833295869677629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490460627888863913118419 735690941833295869677629)
              ·
                refine ⟨275884103187485951129111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 735690941833295869677629 275884103187485951129111)
                ·
                  refine ⟨413826154781228926693667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 275884103187485951129111 413826154781228926693667)
                  ·
                    refine ⟨620739232171843390040501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 413826154781228926693667 620739232171843390040501)
                    ·
                      refine ⟨58194303016110317816297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 620739232171843390040501 58194303016110317816297)
                      ·
                        rfl

theorem cell23_113333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_113333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113333 prefixEnd_113333 := by exact prefixLift 113333
  have htrace : WordTrace (prefixWord ++ tailWord_113333) baseStart_113333 baseEnd_113333 := by
    simpa [prefixWord, tailWord_113333, baseEnd_113333] using wordTrace_append hprefix tailTrace_113333
  have hstable : (prefixWord ++ tailWord_113333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113333).length < 2 ^ (prefixWord ++ tailWord_113333).sum := by decide
  have hdescent : baseEnd_113333 < baseStart_113333 := by decide
  rcases family_descends (prefixWord ++ tailWord_113333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113334 : List Nat := [5, 1, 3, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_113334 : Nat := 118140960795 + 113334 * 2 ^ 59
def prefixEnd_113334 : Nat := 4983230072969 + 3 ^ 40 * 113334 * 2
def baseEnd_113334 : Nat := 58194816496764813903793

theorem tailTrace_113334 : CollatzResearch.WordTrace tailWord_113334 prefixEnd_113334 58194816496764813903793 := by
  unfold tailWord_113334
  simp only [CollatzResearch.WordTrace]
  refine ⟨258351910713609296956691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2755753714278499167538037 258351910713609296956691)
  ·
    refine ⟨387527866070413945435037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258351910713609296956691 387527866070413945435037)
    ·
      refine ⟨145322949776405229538139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387527866070413945435037 145322949776405229538139)
      ·
        refine ⟨217984424664607844307209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145322949776405229538139 217984424664607844307209)
        ·
          refine ⟨163488318498455883230407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217984424664607844307209 163488318498455883230407)
          ·
            refine ⟨245232477747683824845611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163488318498455883230407 245232477747683824845611)
            ·
              refine ⟨367848716621525737268417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245232477747683824845611 367848716621525737268417)
              ·
                refine ⟨275886537466144302951313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367848716621525737268417 275886537466144302951313)
                ·
                  refine ⟨206914903099608227213485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 275886537466144302951313 206914903099608227213485)
                  ·
                    refine ⟨77593088662353085205057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 206914903099608227213485 77593088662353085205057)
                    ·
                      refine ⟨58194816496764813903793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 77593088662353085205057 58194816496764813903793)
                      ·
                        rfl

theorem cell23_113334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_113334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113334 prefixEnd_113334 := by exact prefixLift 113334
  have htrace : WordTrace (prefixWord ++ tailWord_113334) baseStart_113334 baseEnd_113334 := by
    simpa [prefixWord, tailWord_113334, baseEnd_113334] using wordTrace_append hprefix tailTrace_113334
  have hstable : (prefixWord ++ tailWord_113334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113334).length < 2 ^ (prefixWord ++ tailWord_113334).sum := by decide
  have hdescent : baseEnd_113334 < baseStart_113334 := by decide
  rcases family_descends (prefixWord ++ tailWord_113334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113364 : List Nat := [2, 4, 1, 3, 3, 1, 1, 2, 1, 1, 4]
def baseStart_113364 : Nat := 118140960795 + 113364 * 2 ^ 59
def prefixEnd_113364 : Nat := 4983230072969 + 3 ^ 40 * 113364 * 2
def baseEnd_113364 : Nat := 58210220916399696528655

theorem tailTrace_113364 : CollatzResearch.WordTrace tailWord_113364 prefixEnd_113364 58210220916399696528655 := by
  unfold tailWord_113364
  simp only [CollatzResearch.WordTrace]
  refine ⟨2067362380654531937449573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2756483174206042583266097 2067362380654531937449573)
  ·
    refine ⟨387630446372724738271795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2067362380654531937449573 387630446372724738271795)
    ·
      refine ⟨581445669559087107407693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387630446372724738271795 581445669559087107407693)
      ·
        refine ⟨218042126084657665277885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 581445669559087107407693 218042126084657665277885)
        ·
          refine ⟨81765797281746624479207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218042126084657665277885 81765797281746624479207)
          ·
            refine ⟨122648695922619936718811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81765797281746624479207 122648695922619936718811)
            ·
              refine ⟨183973043883929905078217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122648695922619936718811 183973043883929905078217)
              ·
                refine ⟨137979782912947428808663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183973043883929905078217 137979782912947428808663)
                ·
                  refine ⟨206969674369421143212995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137979782912947428808663 206969674369421143212995)
                  ·
                    refine ⟨310454511554131714819493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 206969674369421143212995 310454511554131714819493)
                    ·
                      refine ⟨58210220916399696528655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 310454511554131714819493 58210220916399696528655)
                      ·
                        rfl

theorem cell23_113364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_113364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113364 prefixEnd_113364 := by exact prefixLift 113364
  have htrace : WordTrace (prefixWord ++ tailWord_113364) baseStart_113364 baseEnd_113364 := by
    simpa [prefixWord, tailWord_113364, baseEnd_113364] using wordTrace_append hprefix tailTrace_113364
  have hstable : (prefixWord ++ tailWord_113364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113364).length < 2 ^ (prefixWord ++ tailWord_113364).sum := by decide
  have hdescent : baseEnd_113364 < baseStart_113364 := by decide
  rcases family_descends (prefixWord ++ tailWord_113364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113420 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 6, 2, 2]
def baseStart_113420 : Nat := 118140960795 + 113420 * 2 ^ 59
def prefixEnd_113420 : Nat := 4983230072969 + 3 ^ 40 * 113420 * 2
def baseEnd_113420 : Nat := 58238975833051477428397

theorem tailTrace_113420 : CollatzResearch.WordTrace tailWord_113420 prefixEnd_113420 58238975833051477428397 := by
  unfold tailWord_113420
  simp only [CollatzResearch.WordTrace]
  refine ⟨2068383624553092719468857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2757844832737456959291809 2068383624553092719468857)
  ·
    refine ⟨1551287718414819539601643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2068383624553092719468857 1551287718414819539601643)
    ·
      refine ⟨2326931577622229309402465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1551287718414819539601643 2326931577622229309402465)
      ·
        refine ⟨1745198683216671982051849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2326931577622229309402465 1745198683216671982051849)
        ·
          refine ⟨1308899012412503986538887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1745198683216671982051849 1308899012412503986538887)
          ·
            refine ⟨1963348518618755979808331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1308899012412503986538887 1963348518618755979808331)
            ·
              refine ⟨2945022777928133969712497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1963348518618755979808331 2945022777928133969712497)
              ·
                refine ⟨2208767083446100477284373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2945022777928133969712497 2208767083446100477284373)
                ·
                  refine ⟨103535957036535959872705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2208767083446100477284373 103535957036535959872705)
                  ·
                    refine ⟨77651967777401969904529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103535957036535959872705 77651967777401969904529)
                    ·
                      refine ⟨58238975833051477428397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 77651967777401969904529 58238975833051477428397)
                      ·
                        rfl

theorem cell23_113420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_113420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113420 prefixEnd_113420 := by exact prefixLift 113420
  have htrace : WordTrace (prefixWord ++ tailWord_113420) baseStart_113420 baseEnd_113420 := by
    simpa [prefixWord, tailWord_113420, baseEnd_113420] using wordTrace_append hprefix tailTrace_113420
  have hstable : (prefixWord ++ tailWord_113420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113420).length < 2 ^ (prefixWord ++ tailWord_113420).sum := by decide
  have hdescent : baseEnd_113420 < baseStart_113420 := by decide
  rcases family_descends (prefixWord ++ tailWord_113420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113454 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_113454 : Nat := 118140960795 + 113454 * 2 ^ 59
def prefixEnd_113454 : Nat := 4983230072969 + 3 ^ 40 * 113454 * 2
def baseEnd_113454 : Nat := 58256434175304344403241

theorem tailTrace_113454 : CollatzResearch.WordTrace tailWord_113454 prefixEnd_113454 58256434175304344403241 := by
  unfold tailWord_113454
  simp only [CollatzResearch.WordTrace]
  refine ⟨517250916372876155709427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2758671553988672830450277 517250916372876155709427)
  ·
    refine ⟨775876374559314233564141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 517250916372876155709427 775876374559314233564141)
    ·
      refine ⟨290953640459742837586553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 775876374559314233564141 290953640459742837586553)
      ·
        refine ⟨218215230344807128189915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290953640459742837586553 218215230344807128189915)
        ·
          refine ⟨327322845517210692284873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218215230344807128189915 327322845517210692284873)
          ·
            refine ⟨245492134137908019213655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327322845517210692284873 245492134137908019213655)
            ·
              refine ⟨368238201206862028820483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245492134137908019213655 368238201206862028820483)
              ·
                refine ⟨552357301810293043230725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368238201206862028820483 552357301810293043230725)
                ·
                  refine ⟨103566994089429945605761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 552357301810293043230725 103566994089429945605761)
                  ·
                    refine ⟨77675245567072459204321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103566994089429945605761 77675245567072459204321)
                    ·
                      refine ⟨58256434175304344403241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 77675245567072459204321 58256434175304344403241)
                      ·
                        rfl

theorem cell23_113454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_113454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113454 prefixEnd_113454 := by exact prefixLift 113454
  have htrace : WordTrace (prefixWord ++ tailWord_113454) baseStart_113454 baseEnd_113454 := by
    simpa [prefixWord, tailWord_113454, baseEnd_113454] using wordTrace_append hprefix tailTrace_113454
  have hstable : (prefixWord ++ tailWord_113454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113454).length < 2 ^ (prefixWord ++ tailWord_113454).sum := by decide
  have hdescent : baseEnd_113454 < baseStart_113454 := by decide
  rcases family_descends (prefixWord ++ tailWord_113454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113493 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_113493 : Nat := 118140960795 + 113493 * 2 ^ 59
def prefixEnd_113493 : Nat := 4983230072969 + 3 ^ 40 * 113493 * 2
def baseEnd_113493 : Nat := 58276459920829691815561

theorem tailTrace_113493 : CollatzResearch.WordTrace tailWord_113493 prefixEnd_113493 58276459920829691815561 := by
  unfold tailWord_113493
  simp only [CollatzResearch.WordTrace]
  refine ⟨4139429777841718906345133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2759619851894479270896755 4139429777841718906345133)
  ·
    refine ⟨1552286166690644589879425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4139429777841718906345133 1552286166690644589879425)
    ·
      refine ⟨1164214625017983442409569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1552286166690644589879425 1164214625017983442409569)
      ·
        refine ⟨873160968763487581807177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1164214625017983442409569 873160968763487581807177)
        ·
          refine ⟨654870726572615686355383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 873160968763487581807177 654870726572615686355383)
          ·
            refine ⟨982306089858923529533075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654870726572615686355383 982306089858923529533075)
            ·
              refine ⟨1473459134788385294299613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982306089858923529533075 1473459134788385294299613)
              ·
                refine ⟨552547175545644485362355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1473459134788385294299613 552547175545644485362355)
                ·
                  refine ⟨828820763318466728043533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552547175545644485362355 828820763318466728043533)
                  ·
                    refine ⟨310807786244425023016325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 828820763318466728043533 310807786244425023016325)
                    ·
                      refine ⟨58276459920829691815561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 310807786244425023016325 58276459920829691815561)
                      ·
                        rfl

theorem cell23_113493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_113493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113493 prefixEnd_113493 := by exact prefixLift 113493
  have htrace : WordTrace (prefixWord ++ tailWord_113493) baseStart_113493 baseEnd_113493 := by
    simpa [prefixWord, tailWord_113493, baseEnd_113493] using wordTrace_append hprefix tailTrace_113493
  have hstable : (prefixWord ++ tailWord_113493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113493).length < 2 ^ (prefixWord ++ tailWord_113493).sum := by decide
  have hdescent : baseEnd_113493 < baseStart_113493 := by decide
  rcases family_descends (prefixWord ++ tailWord_113493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113520 : List Nat := [2, 1, 1, 1, 4, 1, 5, 1, 3, 4]
def baseStart_113520 : Nat := 118140960795 + 113520 * 2 ^ 59
def prefixEnd_113520 : Nat := 4983230072969 + 3 ^ 40 * 113520 * 2
def baseEnd_113520 : Nat := 19430107966167028725979

theorem tailTrace_113520 : CollatzResearch.WordTrace tailWord_113520 prefixEnd_113520 19430107966167028725979 := by
  unfold tailWord_113520
  simp only [CollatzResearch.WordTrace]
  refine ⟨2070207274371951258789007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2760276365829268345052009 2070207274371951258789007)
  ·
    refine ⟨3105310911557926888183511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2070207274371951258789007 3105310911557926888183511)
    ·
      refine ⟨4657966367336890332275267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3105310911557926888183511 4657966367336890332275267)
      ·
        refine ⟨6986949551005335498412901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4657966367336890332275267 6986949551005335498412901)
        ·
          refine ⟨1310053040813500405952419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6986949551005335498412901 1310053040813500405952419)
          ·
            refine ⟨1965079561220250608928629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310053040813500405952419 1965079561220250608928629)
            ·
              refine ⟨184226208864398494587059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1965079561220250608928629 184226208864398494587059)
              ·
                refine ⟨276339313296597741880589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184226208864398494587059 276339313296597741880589)
                ·
                  refine ⟨103627242486224153205221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276339313296597741880589 103627242486224153205221)
                  ·
                    refine ⟨19430107966167028725979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103627242486224153205221 19430107966167028725979)
                    ·
                      rfl

theorem cell23_113520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 3, 4].length) (baseStart_113520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113520 prefixEnd_113520 := by exact prefixLift 113520
  have htrace : WordTrace (prefixWord ++ tailWord_113520) baseStart_113520 baseEnd_113520 := by
    simpa [prefixWord, tailWord_113520, baseEnd_113520] using wordTrace_append hprefix tailTrace_113520
  have hstable : (prefixWord ++ tailWord_113520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113520).length < 2 ^ (prefixWord ++ tailWord_113520).sum := by decide
  have hdescent : baseEnd_113520 < baseStart_113520 := by decide
  rcases family_descends (prefixWord ++ tailWord_113520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113600 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 4]
def baseStart_113600 : Nat := 118140960795 + 113600 * 2 ^ 59
def prefixEnd_113600 : Nat := 4983230072969 + 3 ^ 40 * 113600 * 2
def baseEnd_113600 : Nat := 58331402350860773177569

theorem tailTrace_113600 : CollatzResearch.WordTrace tailWord_113600 prefixEnd_113600 58331402350860773177569 := by
  unfold tailWord_113600
  simp only [CollatzResearch.WordTrace]
  refine ⟨2071666194227038090245127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2762221592302717453660169 2071666194227038090245127)
  ·
    refine ⟨3107499291340557135367691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2071666194227038090245127 3107499291340557135367691)
    ·
      refine ⟨4661248937010835703051537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3107499291340557135367691 4661248937010835703051537)
      ·
        refine ⟨3495936702758126777288653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4661248937010835703051537 3495936702758126777288653)
        ·
          refine ⟨1310976263534297541483245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3495936702758126777288653 1310976263534297541483245)
          ·
            refine ⟨491616098825361578056217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1310976263534297541483245 491616098825361578056217)
            ·
              refine ⟨368712074119021183542163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491616098825361578056217 368712074119021183542163)
              ·
                refine ⟨553068111178531775313245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368712074119021183542163 553068111178531775313245)
                ·
                  refine ⟨207400541691949415742467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 553068111178531775313245 207400541691949415742467)
                  ·
                    refine ⟨311100812537924123613701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 207400541691949415742467 311100812537924123613701)
                    ·
                      refine ⟨58331402350860773177569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 311100812537924123613701 58331402350860773177569)
                      ·
                        rfl

theorem cell23_113600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_113600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113600 prefixEnd_113600 := by exact prefixLift 113600
  have htrace : WordTrace (prefixWord ++ tailWord_113600) baseStart_113600 baseEnd_113600 := by
    simpa [prefixWord, tailWord_113600, baseEnd_113600] using wordTrace_append hprefix tailTrace_113600
  have hstable : (prefixWord ++ tailWord_113600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113600).length < 2 ^ (prefixWord ++ tailWord_113600).sum := by decide
  have hdescent : baseEnd_113600 < baseStart_113600 := by decide
  rcases family_descends (prefixWord ++ tailWord_113600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113603 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 5]
def baseStart_113603 : Nat := 118140960795 + 113603 * 2 ^ 59
def prefixEnd_113603 : Nat := 4983230072969 + 3 ^ 40 * 113603 * 2
def baseEnd_113603 : Nat := 58332942792824261440055

theorem tailTrace_113603 : CollatzResearch.WordTrace tailWord_113603 prefixEnd_113603 58332942792824261440055 := by
  unfold tailWord_113603
  simp only [CollatzResearch.WordTrace]
  refine ⟨4143441807443207692849463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2762294538295471795232975 4143441807443207692849463)
  ·
    refine ⟨6215162711164811539274195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4143441807443207692849463 6215162711164811539274195)
    ·
      refine ⟨9322744066747217308911293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6215162711164811539274195 9322744066747217308911293)
      ·
        refine ⟨3496029025030206490841735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9322744066747217308911293 3496029025030206490841735)
        ·
          refine ⟨5244043537545309736262603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3496029025030206490841735 5244043537545309736262603)
          ·
            refine ⟨7866065306317964604393905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5244043537545309736262603 7866065306317964604393905)
            ·
              refine ⟨5899548979738473453295429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7866065306317964604393905 5899548979738473453295429)
              ·
                refine ⟨1106165433700963772492893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5899548979738473453295429 1106165433700963772492893)
                ·
                  refine ⟨414812037637861414684835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106165433700963772492893 414812037637861414684835)
                  ·
                    refine ⟨622218056456792122027253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 414812037637861414684835 622218056456792122027253)
                    ·
                      refine ⟨58332942792824261440055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 622218056456792122027253 58332942792824261440055)
                      ·
                        rfl

theorem cell23_113603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_113603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113603 prefixEnd_113603 := by exact prefixLift 113603
  have htrace : WordTrace (prefixWord ++ tailWord_113603) baseStart_113603 baseEnd_113603 := by
    simpa [prefixWord, tailWord_113603, baseEnd_113603] using wordTrace_append hprefix tailTrace_113603
  have hstable : (prefixWord ++ tailWord_113603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113603).length < 2 ^ (prefixWord ++ tailWord_113603).sum := by decide
  have hdescent : baseEnd_113603 < baseStart_113603 := by decide
  rcases family_descends (prefixWord ++ tailWord_113603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113610 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 4, 4]
def baseStart_113610 : Nat := 118140960795 + 113610 * 2 ^ 59
def prefixEnd_113610 : Nat := 4983230072969 + 3 ^ 40 * 113610 * 2
def baseEnd_113610 : Nat := 19445512385801911350841

theorem tailTrace_113610 : CollatzResearch.WordTrace tailWord_113610 prefixEnd_113610 19445512385801911350841 := by
  unfold tailWord_113610
  simp only [CollatzResearch.WordTrace]
  refine ⟨1035924279604461972088571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2762464745611898592236189 1035924279604461972088571)
  ·
    refine ⟨1553886419406692958132857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1035924279604461972088571 1553886419406692958132857)
    ·
      refine ⟨1165414814555019718599643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1553886419406692958132857 1165414814555019718599643)
      ·
        refine ⟨1748122221832529577899465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1165414814555019718599643 1748122221832529577899465)
        ·
          refine ⟨1311091666374397183424599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1748122221832529577899465 1311091666374397183424599)
          ·
            refine ⟨1966637499561595775136899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311091666374397183424599 1966637499561595775136899)
            ·
              refine ⟨2949956249342393662705349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1966637499561595775136899 2949956249342393662705349)
              ·
                refine ⟨553116796751698811757253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2949956249342393662705349 553116796751698811757253)
                ·
                  refine ⟨103709399390943527204485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 553116796751698811757253 103709399390943527204485)
                  ·
                    refine ⟨19445512385801911350841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103709399390943527204485 19445512385801911350841)
                    ·
                      rfl

theorem cell23_113610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_113610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113610 prefixEnd_113610 := by exact prefixLift 113610
  have htrace : WordTrace (prefixWord ++ tailWord_113610) baseStart_113610 baseEnd_113610 := by
    simpa [prefixWord, tailWord_113610, baseEnd_113610] using wordTrace_append hprefix tailTrace_113610
  have hstable : (prefixWord ++ tailWord_113610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113610).length < 2 ^ (prefixWord ++ tailWord_113610).sum := by decide
  have hdescent : baseEnd_113610 < baseStart_113610 := by decide
  rcases family_descends (prefixWord ++ tailWord_113610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113614 : List Nat := [4, 1, 1, 1, 2, 5, 2, 1, 1, 5]
def baseStart_113614 : Nat := 118140960795 + 113614 * 2 ^ 59
def prefixEnd_113614 : Nat := 4983230072969 + 3 ^ 40 * 113614 * 2
def baseEnd_113614 : Nat := 19446197026674572800835

theorem tailTrace_113614 : CollatzResearch.WordTrace tailWord_113614 prefixEnd_113614 19446197026674572800835 := by
  unfold tailWord_113614
  simp only [CollatzResearch.WordTrace]
  refine ⟨517980376300419571437487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2762562006935571047666597 517980376300419571437487)
  ·
    refine ⟨776970564450629357156231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 517980376300419571437487 776970564450629357156231)
    ·
      refine ⟨1165455846675944035734347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 776970564450629357156231 1165455846675944035734347)
      ·
        refine ⟨1748183770013916053601521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1165455846675944035734347 1748183770013916053601521)
        ·
          refine ⟨1311137827510437040201141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1748183770013916053601521 1311137827510437040201141)
          ·
            refine ⟨122919171329103472518857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1311137827510437040201141 122919171329103472518857)
            ·
              refine ⟨92189378496827604389143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122919171329103472518857 92189378496827604389143)
              ·
                refine ⟨138284067745241406583715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92189378496827604389143 138284067745241406583715)
                ·
                  refine ⟨207426101617862109875573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138284067745241406583715 207426101617862109875573)
                  ·
                    refine ⟨19446197026674572800835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 207426101617862109875573 19446197026674572800835)
                    ·
                      rfl

theorem cell23_113614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_113614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113614 prefixEnd_113614 := by exact prefixLift 113614
  have htrace : WordTrace (prefixWord ++ tailWord_113614) baseStart_113614 baseEnd_113614 := by
    simpa [prefixWord, tailWord_113614, baseEnd_113614] using wordTrace_append hprefix tailTrace_113614
  have hstable : (prefixWord ++ tailWord_113614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113614).length < 2 ^ (prefixWord ++ tailWord_113614).sum := by decide
  have hdescent : baseEnd_113614 < baseStart_113614 := by decide
  rcases family_descends (prefixWord ++ tailWord_113614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113617 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 5, 2, 2]
def baseStart_113617 : Nat := 118140960795 + 113617 * 2 ^ 59
def prefixEnd_113617 : Nat := 4983230072969 + 3 ^ 40 * 113617 * 2
def baseEnd_113617 : Nat := 58340131521987206664991

theorem tailTrace_113617 : CollatzResearch.WordTrace tailWord_113617 prefixEnd_113617 58340131521987206664991 := by
  unfold tailWord_113617
  simp only [CollatzResearch.WordTrace]
  refine ⟨4143952429392488083859105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2762634952928325389239403 4143952429392488083859105)
  ·
    refine ⟨3107964322044366062894329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4143952429392488083859105 3107964322044366062894329)
    ·
      refine ⟨2330973241533274547170747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3107964322044366062894329 2330973241533274547170747)
      ·
        refine ⟨3496459862299911820756121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2330973241533274547170747 3496459862299911820756121)
        ·
          refine ⟨2622344896724933865567091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3496459862299911820756121 2622344896724933865567091)
          ·
            refine ⟨3933517345087400798350637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2622344896724933865567091 3933517345087400798350637)
            ·
              refine ⟨1475069004407775299381489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3933517345087400798350637 1475069004407775299381489)
              ·
                refine ⟨1106301753305831474536117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1475069004407775299381489 1106301753305831474536117)
                ·
                  refine ⟨103715789372421700737761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1106301753305831474536117 103715789372421700737761)
                  ·
                    refine ⟨77786842029316275553321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103715789372421700737761 77786842029316275553321)
                    ·
                      refine ⟨58340131521987206664991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 77786842029316275553321 58340131521987206664991)
                      ·
                        rfl

theorem cell23_113617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 2, 2].length) (baseStart_113617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113617 prefixEnd_113617 := by exact prefixLift 113617
  have htrace : WordTrace (prefixWord ++ tailWord_113617) baseStart_113617 baseEnd_113617 := by
    simpa [prefixWord, tailWord_113617, baseEnd_113617] using wordTrace_append hprefix tailTrace_113617
  have hstable : (prefixWord ++ tailWord_113617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113617).length < 2 ^ (prefixWord ++ tailWord_113617).sum := by decide
  have hdescent : baseEnd_113617 < baseStart_113617 := by decide
  rcases family_descends (prefixWord ++ tailWord_113617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113633 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_113633 : Nat := 118140960795 + 113633 * 2 ^ 59
def prefixEnd_113633 : Nat := 4983230072969 + 3 ^ 40 * 113633 * 2
def baseEnd_113633 : Nat := 58348347212459144064917

theorem tailTrace_113633 : CollatzResearch.WordTrace tailWord_113633 prefixEnd_113633 58348347212459144064917 := by
  unfold tailWord_113633
  simp only [CollatzResearch.WordTrace]
  refine ⟨4144535997334522816441553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2763023998223015210961035 4144535997334522816441553)
  ·
    refine ⟨3108401998000892112331165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4144535997334522816441553 3108401998000892112331165)
    ·
      refine ⟨1165650749250334542124187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3108401998000892112331165 1165650749250334542124187)
      ·
        refine ⟨1748476123875501813186281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1165650749250334542124187 1748476123875501813186281)
        ·
          refine ⟨1311357092906626359889711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1748476123875501813186281 1311357092906626359889711)
          ·
            refine ⟨1967035639359939539834567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311357092906626359889711 1967035639359939539834567)
            ·
              refine ⟨2950553459039909309751851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1967035639359939539834567 2950553459039909309751851)
              ·
                refine ⟨4425830188559863964627777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2950553459039909309751851 4425830188559863964627777)
                ·
                  refine ⟨3319372641419897973470833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4425830188559863964627777 3319372641419897973470833)
                  ·
                    refine ⟨2489529481064923480103125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3319372641419897973470833 2489529481064923480103125)
                    ·
                      refine ⟨58348347212459144064917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2489529481064923480103125 58348347212459144064917)
                      ·
                        rfl

theorem cell23_113633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_113633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113633 prefixEnd_113633 := by exact prefixLift 113633
  have htrace : WordTrace (prefixWord ++ tailWord_113633) baseStart_113633 baseEnd_113633 := by
    simpa [prefixWord, tailWord_113633, baseEnd_113633] using wordTrace_append hprefix tailTrace_113633
  have hstable : (prefixWord ++ tailWord_113633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113633).length < 2 ^ (prefixWord ++ tailWord_113633).sum := by decide
  have hdescent : baseEnd_113633 < baseStart_113633 := by decide
  rcases family_descends (prefixWord ++ tailWord_113633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113647 : List Nat := [1, 1, 2, 1, 4, 5, 1, 1, 1, 2, 4]
def baseStart_113647 : Nat := 118140960795 + 113647 * 2 ^ 59
def prefixEnd_113647 : Nat := 4983230072969 + 3 ^ 40 * 113647 * 2
def baseEnd_113647 : Nat := 58355535941622089289853

theorem tailTrace_113647 : CollatzResearch.WordTrace tailWord_113647 prefixEnd_113647 58355535941622089289853 := by
  unfold tailWord_113647
  simp only [CollatzResearch.WordTrace]
  refine ⟨4145046619283803207451195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2763364412855868804967463 4145046619283803207451195)
  ·
    refine ⟨6217569928925704811176793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4145046619283803207451195 6217569928925704811176793)
    ·
      refine ⟨4663177446694278608382595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6217569928925704811176793 4663177446694278608382595)
      ·
        refine ⟨6994766170041417912573893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4663177446694278608382595 6994766170041417912573893)
        ·
          refine ⟨1311518656882765858607605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6994766170041417912573893 1311518656882765858607605)
          ·
            refine ⟨122954874082759299244463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1311518656882765858607605 122954874082759299244463)
            ·
              refine ⟨184432311124138948866695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122954874082759299244463 184432311124138948866695)
              ·
                refine ⟨276648466686208423300043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184432311124138948866695 276648466686208423300043)
                ·
                  refine ⟨414972700029312634950065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276648466686208423300043 414972700029312634950065)
                  ·
                    refine ⟨311229525021984476212549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 414972700029312634950065 311229525021984476212549)
                    ·
                      refine ⟨58355535941622089289853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 311229525021984476212549 58355535941622089289853)
                      ·
                        rfl

theorem cell23_113647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 2, 4].length) (baseStart_113647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113647 prefixEnd_113647 := by exact prefixLift 113647
  have htrace : WordTrace (prefixWord ++ tailWord_113647) baseStart_113647 baseEnd_113647 := by
    simpa [prefixWord, tailWord_113647, baseEnd_113647] using wordTrace_append hprefix tailTrace_113647
  have hstable : (prefixWord ++ tailWord_113647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113647).length < 2 ^ (prefixWord ++ tailWord_113647).sum := by decide
  have hdescent : baseEnd_113647 < baseStart_113647 := by decide
  rcases family_descends (prefixWord ++ tailWord_113647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113654 : List Nat := [5, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3]
def baseStart_113654 : Nat := 118140960795 + 113654 * 2 ^ 59
def prefixEnd_113654 : Nat := 4983230072969 + 3 ^ 40 * 113654 * 2
def baseEnd_113654 : Nat := 58359130306203561902321

theorem tailTrace_113654 : CollatzResearch.WordTrace tailWord_113654 prefixEnd_113654 58359130306203561902321 := by
  unfold tailWord_113654
  simp only [CollatzResearch.WordTrace]
  refine ⟨259081370641152712684751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2763534620172295601970677 259081370641152712684751)
  ·
    refine ⟨388622055961729069027127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259081370641152712684751 388622055961729069027127)
    ·
      refine ⟨582933083942593603540691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388622055961729069027127 582933083942593603540691)
      ·
        refine ⟨874399625913890405311037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582933083942593603540691 874399625913890405311037)
        ·
          refine ⟨327899859717708901991639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 874399625913890405311037 327899859717708901991639)
          ·
            refine ⟨491849789576563352987459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327899859717708901991639 491849789576563352987459)
            ·
              refine ⟨737774684364845029481189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491849789576563352987459 737774684364845029481189)
              ·
                refine ⟨138332753318408443027723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 737774684364845029481189 138332753318408443027723)
                ·
                  refine ⟨207499129977612664541585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138332753318408443027723 207499129977612664541585)
                  ·
                    refine ⟨155624347483209498406189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 207499129977612664541585 155624347483209498406189)
                    ·
                      refine ⟨58359130306203561902321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 155624347483209498406189 58359130306203561902321)
                      ·
                        rfl

theorem cell23_113654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_113654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113654 prefixEnd_113654 := by exact prefixLift 113654
  have htrace : WordTrace (prefixWord ++ tailWord_113654) baseStart_113654 baseEnd_113654 := by
    simpa [prefixWord, tailWord_113654, baseEnd_113654] using wordTrace_append hprefix tailTrace_113654
  have hstable : (prefixWord ++ tailWord_113654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113654).length < 2 ^ (prefixWord ++ tailWord_113654).sum := by decide
  have hdescent : baseEnd_113654 < baseStart_113654 := by decide
  rcases family_descends (prefixWord ++ tailWord_113654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113673 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 8]
def baseStart_113673 : Nat := 118140960795 + 113673 * 2 ^ 59
def prefixEnd_113673 : Nat := 4983230072969 + 3 ^ 40 * 113673 * 2
def baseEnd_113673 : Nat := 58368886438638987564733

theorem tailTrace_113673 : CollatzResearch.WordTrace tailWord_113673 prefixEnd_113673 58368886438638987564733 := by
  unfold tailWord_113673
  simp only [CollatzResearch.WordTrace]
  refine ⟨4145994917189609647897673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2763996611459739765265115 4145994917189609647897673)
  ·
    refine ⟨3109496187892207235923255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4145994917189609647897673 3109496187892207235923255)
    ·
      refine ⟨4664244281838310853884883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3109496187892207235923255 4664244281838310853884883)
      ·
        refine ⟨6996366422757466280827325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4664244281838310853884883 6996366422757466280827325)
        ·
          refine ⟨2623637408534049855310247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6996366422757466280827325 2623637408534049855310247)
          ·
            refine ⟨3935456112801074782965371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623637408534049855310247 3935456112801074782965371)
            ·
              refine ⟨5903184169201612174448057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3935456112801074782965371 5903184169201612174448057)
              ·
                refine ⟨4427388126901209130836043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5903184169201612174448057 4427388126901209130836043)
                ·
                  refine ⟨6641082190351813696254065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4427388126901209130836043 6641082190351813696254065)
                  ·
                    refine ⟨4980811642763860272190549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6641082190351813696254065 4980811642763860272190549)
                    ·
                      refine ⟨58368886438638987564733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 4980811642763860272190549 58368886438638987564733)
                      ·
                        rfl

theorem cell23_113673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_113673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113673 prefixEnd_113673 := by exact prefixLift 113673
  have htrace : WordTrace (prefixWord ++ tailWord_113673) baseStart_113673 baseEnd_113673 := by
    simpa [prefixWord, tailWord_113673, baseEnd_113673] using wordTrace_append hprefix tailTrace_113673
  have hstable : (prefixWord ++ tailWord_113673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113673).length < 2 ^ (prefixWord ++ tailWord_113673).sum := by decide
  have hdescent : baseEnd_113673 < baseStart_113673 := by decide
  rcases family_descends (prefixWord ++ tailWord_113673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113690 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4]
def baseStart_113690 : Nat := 118140960795 + 113690 * 2 ^ 59
def prefixEnd_113690 : Nat := 4983230072969 + 3 ^ 40 * 113690 * 2
def baseEnd_113690 : Nat := 58377615609765421052155

theorem tailTrace_113690 : CollatzResearch.WordTrace tailWord_113690 prefixEnd_113690 58377615609765421052155 := by
  unfold tailWord_113690
  simp only [CollatzResearch.WordTrace]
  refine ⟨1036653739532005387816631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2764409972085347700844349 1036653739532005387816631)
  ·
    refine ⟨1554980609298008081724947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1036653739532005387816631 1554980609298008081724947)
    ·
      refine ⟨2332470913947012122587421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1554980609298008081724947 2332470913947012122587421)
      ·
        refine ⟨874676592730129545970283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2332470913947012122587421 874676592730129545970283)
        ·
          refine ⟨1312014889095194318955425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874676592730129545970283 1312014889095194318955425)
          ·
            refine ⟨984011166821395739216569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1312014889095194318955425 984011166821395739216569)
            ·
              refine ⟨738008375116046804412427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 984011166821395739216569 738008375116046804412427)
              ·
                refine ⟨1107012562674070206618641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738008375116046804412427 1107012562674070206618641)
                ·
                  refine ⟨830259422005552654963981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1107012562674070206618641 830259422005552654963981)
                  ·
                    refine ⟨311347283252082245611493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 830259422005552654963981 311347283252082245611493)
                    ·
                      refine ⟨58377615609765421052155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 311347283252082245611493 58377615609765421052155)
                      ·
                        rfl

theorem cell23_113690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_113690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113690 prefixEnd_113690 := by exact prefixLift 113690
  have htrace : WordTrace (prefixWord ++ tailWord_113690) baseStart_113690 baseEnd_113690 := by
    simpa [prefixWord, tailWord_113690, baseEnd_113690] using wordTrace_append hprefix tailTrace_113690
  have hstable : (prefixWord ++ tailWord_113690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113690).length < 2 ^ (prefixWord ++ tailWord_113690).sum := by decide
  have hdescent : baseEnd_113690 < baseStart_113690 := by decide
  rcases family_descends (prefixWord ++ tailWord_113690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113707 : List Nat := [1, 1, 1, 1, 2, 1, 6, 3, 1, 4, 2]
def baseStart_113707 : Nat := 118140960795 + 113707 * 2 ^ 59
def prefixEnd_113707 : Nat := 4983230072969 + 3 ^ 40 * 113707 * 2
def baseEnd_113707 : Nat := 58386344780891854539577

theorem tailTrace_113707 : CollatzResearch.WordTrace tailWord_113707 prefixEnd_113707 58386344780891854539577 := by
  unfold tailWord_113707
  simp only [CollatzResearch.WordTrace]
  refine ⟨4147234999066433454635375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2764823332710955636423583 4147234999066433454635375)
  ·
    refine ⟨6220852498599650181953063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4147234999066433454635375 6220852498599650181953063)
    ·
      refine ⟨9331278747899475272929595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6220852498599650181953063 9331278747899475272929595)
      ·
        refine ⟨13996918121849212909394393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9331278747899475272929595 13996918121849212909394393)
        ·
          refine ⟨10497688591386909682045795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13996918121849212909394393 10497688591386909682045795)
          ·
            refine ⟨15746532887080364523068693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10497688591386909682045795 15746532887080364523068693)
            ·
              refine ⟨738118729081892087018845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15746532887080364523068693 738118729081892087018845)
              ·
                refine ⟨276794523405709532632067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 738118729081892087018845 276794523405709532632067)
                ·
                  refine ⟨415191785108564298948101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276794523405709532632067 415191785108564298948101)
                  ·
                    refine ⟨77848459707855806052769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 415191785108564298948101 77848459707855806052769)
                    ·
                      refine ⟨58386344780891854539577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 77848459707855806052769 58386344780891854539577)
                      ·
                        rfl

theorem cell23_113707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 4, 2].length) (baseStart_113707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113707 prefixEnd_113707 := by exact prefixLift 113707
  have htrace : WordTrace (prefixWord ++ tailWord_113707) baseStart_113707 baseEnd_113707 := by
    simpa [prefixWord, tailWord_113707, baseEnd_113707] using wordTrace_append hprefix tailTrace_113707
  have hstable : (prefixWord ++ tailWord_113707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113707).length < 2 ^ (prefixWord ++ tailWord_113707).sum := by decide
  have hdescent : baseEnd_113707 < baseStart_113707 := by decide
  rcases family_descends (prefixWord ++ tailWord_113707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113724 : List Nat := [2, 2, 2, 2, 2, 3, 1, 2, 1, 4, 2]
def baseStart_113724 : Nat := 118140960795 + 113724 * 2 ^ 59
def prefixEnd_113724 : Nat := 4983230072969 + 3 ^ 40 * 113724 * 2
def baseEnd_113724 : Nat := 58395073952018288026999

theorem tailTrace_113724 : CollatzResearch.WordTrace tailWord_113724 prefixEnd_113724 58395073952018288026999 := by
  unfold tailWord_113724
  simp only [CollatzResearch.WordTrace]
  refine ⟨2073927520002422679002113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2765236693336563572002817 2073927520002422679002113)
  ·
    refine ⟨1555445640001817009251585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2073927520002422679002113 1555445640001817009251585)
    ·
      refine ⟨1166584230001362756938689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1555445640001817009251585 1166584230001362756938689)
      ·
        refine ⟨874938172501022067704017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1166584230001362756938689 874938172501022067704017)
        ·
          refine ⟨656203629375766550778013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 874938172501022067704017 656203629375766550778013)
          ·
            refine ⟨246076361015912456541755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 656203629375766550778013 246076361015912456541755)
            ·
              refine ⟨369114541523868684812633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246076361015912456541755 369114541523868684812633)
              ·
                refine ⟨276835906142901513609475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369114541523868684812633 276835906142901513609475)
                ·
                  refine ⟨415253859214352270414213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276835906142901513609475 415253859214352270414213)
                  ·
                    refine ⟨77860098602691050702665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 415253859214352270414213 77860098602691050702665)
                    ·
                      refine ⟨58395073952018288026999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 77860098602691050702665 58395073952018288026999)
                      ·
                        rfl

theorem cell23_113724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_113724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113724 prefixEnd_113724 := by exact prefixLift 113724
  have htrace : WordTrace (prefixWord ++ tailWord_113724) baseStart_113724 baseEnd_113724 := by
    simpa [prefixWord, tailWord_113724, baseEnd_113724] using wordTrace_append hprefix tailTrace_113724
  have hstable : (prefixWord ++ tailWord_113724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113724).length < 2 ^ (prefixWord ++ tailWord_113724).sum := by decide
  have hdescent : baseEnd_113724 < baseStart_113724 := by decide
  rcases family_descends (prefixWord ++ tailWord_113724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113758 : List Nat := [4, 4, 1, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_113758 : Nat := 118140960795 + 113758 * 2 ^ 59
def prefixEnd_113758 : Nat := 4983230072969 + 3 ^ 40 * 113758 * 2
def baseEnd_113758 : Nat := 58412532294271155001843

theorem tailTrace_113758 : CollatzResearch.WordTrace tailWord_113758 prefixEnd_113758 58412532294271155001843 := by
  unfold tailWord_113758
  simp only [CollatzResearch.WordTrace]
  refine ⟨518636890235208645592741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2766063414587779443161285 518636890235208645592741)
  ·
    refine ⟨97244416919101621048639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 518636890235208645592741 97244416919101621048639)
    ·
      refine ⟨145866625378652431572959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97244416919101621048639 145866625378652431572959)
      ·
        refine ⟨218799938067978647359439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145866625378652431572959 218799938067978647359439)
        ·
          refine ⟨328199907101967971039159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218799938067978647359439 328199907101967971039159)
          ·
            refine ⟨492299860652951956558739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328199907101967971039159 492299860652951956558739)
            ·
              refine ⟨738449790979427934838109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492299860652951956558739 738449790979427934838109)
              ·
                refine ⟨276918671617285475564291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 738449790979427934838109 276918671617285475564291)
                ·
                  refine ⟨415378007425928213346437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276918671617285475564291 415378007425928213346437)
                  ·
                    refine ⟨77883376392361540002457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 415378007425928213346437 77883376392361540002457)
                    ·
                      refine ⟨58412532294271155001843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 77883376392361540002457 58412532294271155001843)
                      ·
                        rfl

theorem cell23_113758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_113758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113758 prefixEnd_113758 := by exact prefixLift 113758
  have htrace : WordTrace (prefixWord ++ tailWord_113758) baseStart_113758 baseEnd_113758 := by
    simpa [prefixWord, tailWord_113758, baseEnd_113758] using wordTrace_append hprefix tailTrace_113758
  have hstable : (prefixWord ++ tailWord_113758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113758).length < 2 ^ (prefixWord ++ tailWord_113758).sum := by decide
  have hdescent : baseEnd_113758 < baseStart_113758 := by decide
  rcases family_descends (prefixWord ++ tailWord_113758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113760 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 1, 7]
def baseStart_113760 : Nat := 118140960795 + 113760 * 2 ^ 59
def prefixEnd_113760 : Nat := 4983230072969 + 3 ^ 40 * 113760 * 2
def baseEnd_113760 : Nat := 19471186418526715725611

theorem tailTrace_113760 : CollatzResearch.WordTrace tailWord_113760 prefixEnd_113760 19471186418526715725611 := by
  unfold tailWord_113760
  simp only [CollatzResearch.WordTrace]
  refine ⟨2074584033937211753157367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2766112045249615670876489 2074584033937211753157367)
  ·
    refine ⟨3111876050905817629736051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2074584033937211753157367 3111876050905817629736051)
    ·
      refine ⟨4667814076358726444604077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3111876050905817629736051 4667814076358726444604077)
      ·
        refine ⟨1750430278634522416726529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4667814076358726444604077 1750430278634522416726529)
        ·
          refine ⟨1312822708975891812544897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1750430278634522416726529 1312822708975891812544897)
          ·
            refine ⟨984617031731918859408673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1312822708975891812544897 984617031731918859408673)
            ·
              refine ⟨738462773798939144556505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 984617031731918859408673 738462773798939144556505)
              ·
                refine ⟨553847080349204358417379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 738462773798939144556505 553847080349204358417379)
                ·
                  refine ⟨830770620523806537626069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 553847080349204358417379 830770620523806537626069)
                  ·
                    refine ⟨19471186418526715725611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 830770620523806537626069 19471186418526715725611)
                    ·
                      rfl

theorem cell23_113760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 1, 7].length) (baseStart_113760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113760 prefixEnd_113760 := by exact prefixLift 113760
  have htrace : WordTrace (prefixWord ++ tailWord_113760) baseStart_113760 baseEnd_113760 := by
    simpa [prefixWord, tailWord_113760, baseEnd_113760] using wordTrace_append hprefix tailTrace_113760
  have hstable : (prefixWord ++ tailWord_113760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113760).length < 2 ^ (prefixWord ++ tailWord_113760).sum := by decide
  have hdescent : baseEnd_113760 < baseStart_113760 := by decide
  rcases family_descends (prefixWord ++ tailWord_113760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113840 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 6]
def baseStart_113840 : Nat := 118140960795 + 113840 * 2 ^ 59
def prefixEnd_113840 : Nat := 4983230072969 + 3 ^ 40 * 113840 * 2
def baseEnd_113840 : Nat := 58454637707939834176465

theorem tailTrace_113840 : CollatzResearch.WordTrace tailWord_113840 prefixEnd_113840 58454637707939834176465 := by
  unfold tailWord_113840
  simp only [CollatzResearch.WordTrace]
  refine ⟨2076042953792298584613487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2768057271723064779484649 2076042953792298584613487)
  ·
    refine ⟨3114064430688447876920231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2076042953792298584613487 3114064430688447876920231)
    ·
      refine ⟨4671096646032671815380347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3114064430688447876920231 4671096646032671815380347)
      ·
        refine ⟨7006644969049007723070521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4671096646032671815380347 7006644969049007723070521)
        ·
          refine ⟨5254983726786755792302891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7006644969049007723070521 5254983726786755792302891)
          ·
            refine ⟨7882475590180133688454337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5254983726786755792302891 7882475590180133688454337)
            ·
              refine ⟨5911856692635100266340753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7882475590180133688454337 5911856692635100266340753)
              ·
                refine ⟨4433892519476325199755565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5911856692635100266340753 4433892519476325199755565)
                ·
                  refine ⟨1662709694803621949908337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4433892519476325199755565 1662709694803621949908337)
                  ·
                    refine ⟨1247032271102716462431253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1662709694803621949908337 1247032271102716462431253)
                    ·
                      refine ⟨58454637707939834176465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1247032271102716462431253 58454637707939834176465)
                      ·
                        rfl

theorem cell23_113840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_113840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113840 prefixEnd_113840 := by exact prefixLift 113840
  have htrace : WordTrace (prefixWord ++ tailWord_113840) baseStart_113840 baseEnd_113840 := by
    simpa [prefixWord, tailWord_113840, baseEnd_113840] using wordTrace_append hprefix tailTrace_113840
  have hstable : (prefixWord ++ tailWord_113840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113840).length < 2 ^ (prefixWord ++ tailWord_113840).sum := by decide
  have hdescent : baseEnd_113840 < baseStart_113840 := by decide
  rcases family_descends (prefixWord ++ tailWord_113840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113934 : List Nat := [4, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4]
def baseStart_113934 : Nat := 118140960795 + 113934 * 2 ^ 59
def prefixEnd_113934 : Nat := 4983230072969 + 3 ^ 40 * 113934 * 2
def baseEnd_113934 : Nat := 58502904889462466401033

theorem tailTrace_113934 : CollatzResearch.WordTrace tailWord_113934 prefixEnd_113934 58502904889462466401033 := by
  unfold tailWord_113934
  simp only [CollatzResearch.WordTrace]
  refine ⟨519439296155506402893607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2770342912829367482099237 519439296155506402893607)
  ·
    refine ⟨779158944233259604340411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 519439296155506402893607 779158944233259604340411)
    ·
      refine ⟨1168738416349889406510617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 779158944233259604340411 1168738416349889406510617)
      ·
        refine ⟨876553812262417054882963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1168738416349889406510617 876553812262417054882963)
        ·
          refine ⟨1314830718393625582324445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876553812262417054882963 1314830718393625582324445)
          ·
            refine ⟨493061519397609593371667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1314830718393625582324445 493061519397609593371667)
            ·
              refine ⟨739592279096414390057501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493061519397609593371667 739592279096414390057501)
              ·
                refine ⟨277347104661155396271563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 739592279096414390057501 277347104661155396271563)
                ·
                  refine ⟨416020656991733094407345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277347104661155396271563 416020656991733094407345)
                  ·
                    refine ⟨312015492743799820805509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 416020656991733094407345 312015492743799820805509)
                    ·
                      refine ⟨58502904889462466401033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 312015492743799820805509 58502904889462466401033)
                      ·
                        rfl

theorem cell23_113934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_113934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113934 prefixEnd_113934 := by exact prefixLift 113934
  have htrace : WordTrace (prefixWord ++ tailWord_113934) baseStart_113934 baseEnd_113934 := by
    simpa [prefixWord, tailWord_113934, baseEnd_113934] using wordTrace_append hprefix tailTrace_113934
  have hstable : (prefixWord ++ tailWord_113934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113934).length < 2 ^ (prefixWord ++ tailWord_113934).sum := by decide
  have hdescent : baseEnd_113934 < baseStart_113934 := by decide
  rcases family_descends (prefixWord ++ tailWord_113934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113944 : List Nat := [2, 1, 2, 3, 1, 4, 3, 7]
def baseStart_113944 : Nat := 118140960795 + 113944 * 2 ^ 59
def prefixEnd_113944 : Nat := 4983230072969 + 3 ^ 40 * 113944 * 2
def baseEnd_113944 : Nat := 2166964433185460269481

theorem tailTrace_113944 : CollatzResearch.WordTrace tailWord_113944 prefixEnd_113944 2166964433185460269481 := by
  unfold tailWord_113944
  simp only [CollatzResearch.WordTrace]
  refine ⟨2077939549603911465506443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2770586066138548620675257 2077939549603911465506443)
  ·
    refine ⟨3116909324405867198259665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2077939549603911465506443 3116909324405867198259665)
    ·
      refine ⟨2337681993304400398694749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3116909324405867198259665 2337681993304400398694749)
      ·
        refine ⟨876630747489150149510531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2337681993304400398694749 876630747489150149510531)
        ·
          refine ⟨1314946121233725224265797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876630747489150149510531 1314946121233725224265797)
          ·
            refine ⟨246552397731323479549837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1314946121233725224265797 246552397731323479549837)
            ·
              refine ⟨92457149149246304831189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246552397731323479549837 92457149149246304831189)
              ·
                refine ⟨2166964433185460269481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 92457149149246304831189 2166964433185460269481)
                ·
                  rfl

theorem cell23_113944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 7].length) (baseStart_113944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113944 prefixEnd_113944 := by exact prefixLift 113944
  have htrace : WordTrace (prefixWord ++ tailWord_113944) baseStart_113944 baseEnd_113944 := by
    simpa [prefixWord, tailWord_113944, baseEnd_113944] using wordTrace_append hprefix tailTrace_113944
  have hstable : (prefixWord ++ tailWord_113944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113944).length < 2 ^ (prefixWord ++ tailWord_113944).sum := by decide
  have hdescent : baseEnd_113944 < baseStart_113944 := by decide
  rcases family_descends (prefixWord ++ tailWord_113944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113955 : List Nat := [1, 1, 1, 4, 2, 4, 2, 3, 1, 2, 2]
def baseStart_113955 : Nat := 118140960795 + 113955 * 2 ^ 59
def prefixEnd_113955 : Nat := 4983230072969 + 3 ^ 40 * 113955 * 2
def baseEnd_113955 : Nat := 58513687983206884238437

theorem tailTrace_113955 : CollatzResearch.WordTrace tailWord_113955 prefixEnd_113955 58513687983206884238437 := by
  unfold tailWord_113955
  simp only [CollatzResearch.WordTrace]
  refine ⟨4156280302167971809663319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2770853534778647873108879 4156280302167971809663319)
  ·
    refine ⟨6234420453251957714494979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4156280302167971809663319 6234420453251957714494979)
    ·
      refine ⟨9351630679877936571742469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6234420453251957714494979 9351630679877936571742469)
      ·
        refine ⟨1753430752477113107201713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9351630679877936571742469 1753430752477113107201713)
        ·
          refine ⟨1315073064357834830401285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1753430752477113107201713 1315073064357834830401285)
          ·
            refine ⟨246576199567094030700241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1315073064357834830401285 246576199567094030700241)
            ·
              refine ⟨184932149675320523025181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246576199567094030700241 184932149675320523025181)
              ·
                refine ⟨69349556128245196134443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184932149675320523025181 69349556128245196134443)
                ·
                  refine ⟨104024334192367794201665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69349556128245196134443 104024334192367794201665)
                  ·
                    refine ⟨78018250644275845651249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104024334192367794201665 78018250644275845651249)
                    ·
                      refine ⟨58513687983206884238437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 78018250644275845651249 58513687983206884238437)
                      ·
                        rfl

theorem cell23_113955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 1, 2, 2].length) (baseStart_113955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113955 prefixEnd_113955 := by exact prefixLift 113955
  have htrace : WordTrace (prefixWord ++ tailWord_113955) baseStart_113955 baseEnd_113955 := by
    simpa [prefixWord, tailWord_113955, baseEnd_113955] using wordTrace_append hprefix tailTrace_113955
  have hstable : (prefixWord ++ tailWord_113955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113955).length < 2 ^ (prefixWord ++ tailWord_113955).sum := by decide
  have hdescent : baseEnd_113955 < baseStart_113955 := by decide
  rcases family_descends (prefixWord ++ tailWord_113955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113965 : List Nat := [1, 5, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_113965 : Nat := 118140960795 + 113965 * 2 ^ 59
def prefixEnd_113965 : Nat := 4983230072969 + 3 ^ 40 * 113965 * 2
def baseEnd_113965 : Nat := 19506274263250615037797

theorem tailTrace_113965 : CollatzResearch.WordTrace tailWord_113965 prefixEnd_113965 19506274263250615037797 := by
  unfold tailWord_113965
  simp only [CollatzResearch.WordTrace]
  refine ⟨4156645032131743517527349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2771096688087829011684899 4156645032131743517527349)
  ·
    refine ⟨389685471762350954768189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4156645032131743517527349 389685471762350954768189)
    ·
      refine ⟨146132051910881608038071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389685471762350954768189 146132051910881608038071)
      ·
        refine ⟨219198077866322412057107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146132051910881608038071 219198077866322412057107)
        ·
          refine ⟨328797116799483618085661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219198077866322412057107 328797116799483618085661)
          ·
            refine ⟨123298918799806356782123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328797116799483618085661 123298918799806356782123)
            ·
              refine ⟨184948378199709535173185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123298918799806356782123 184948378199709535173185)
              ·
                refine ⟨138711283649782151379889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184948378199709535173185 138711283649782151379889)
                ·
                  refine ⟨104033462737336613534917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138711283649782151379889 104033462737336613534917)
                  ·
                    refine ⟨19506274263250615037797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104033462737336613534917 19506274263250615037797)
                    ·
                      rfl

theorem cell23_113965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_113965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113965 prefixEnd_113965 := by exact prefixLift 113965
  have htrace : WordTrace (prefixWord ++ tailWord_113965) baseStart_113965 baseEnd_113965 := by
    simpa [prefixWord, tailWord_113965, baseEnd_113965] using wordTrace_append hprefix tailTrace_113965
  have hstable : (prefixWord ++ tailWord_113965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113965).length < 2 ^ (prefixWord ++ tailWord_113965).sum := by decide
  have hdescent : baseEnd_113965 < baseStart_113965 := by decide
  rcases family_descends (prefixWord ++ tailWord_113965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113971 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 4, 1, 3]
def baseStart_113971 : Nat := 118140960795 + 113971 * 2 ^ 59
def prefixEnd_113971 : Nat := 4983230072969 + 3 ^ 40 * 113971 * 2
def baseEnd_113971 : Nat := 58521903673678821638363

theorem tailTrace_113971 : CollatzResearch.WordTrace tailWord_113971 prefixEnd_113971 58521903673678821638363 := by
  unfold tailWord_113971
  simp only [CollatzResearch.WordTrace]
  refine ⟨4156863870110006542245767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2771242580073337694830511 4156863870110006542245767)
  ·
    refine ⟨6235295805165009813368651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4156863870110006542245767 6235295805165009813368651)
    ·
      refine ⟨9352943707747514720052977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6235295805165009813368651 9352943707747514720052977)
      ·
        refine ⟨7014707780810636040039733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9352943707747514720052977 7014707780810636040039733)
        ·
          refine ⟨657628854450997128753725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7014707780810636040039733 657628854450997128753725)
          ·
            refine ⟨246610820419123923282647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 657628854450997128753725 246610820419123923282647)
            ·
              refine ⟨369916230628685884923971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246610820419123923282647 369916230628685884923971)
              ·
                refine ⟨554874345943028827385957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369916230628685884923971 554874345943028827385957)
                ·
                  refine ⟨104038939864317905134867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 554874345943028827385957 104038939864317905134867)
                  ·
                    refine ⟨156058409796476857702301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104038939864317905134867 156058409796476857702301)
                    ·
                      refine ⟨58521903673678821638363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 156058409796476857702301 58521903673678821638363)
                      ·
                        rfl

theorem cell23_113971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 1, 3].length) (baseStart_113971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113971 prefixEnd_113971 := by exact prefixLift 113971
  have htrace : WordTrace (prefixWord ++ tailWord_113971) baseStart_113971 baseEnd_113971 := by
    simpa [prefixWord, tailWord_113971, baseEnd_113971] using wordTrace_append hprefix tailTrace_113971
  have hstable : (prefixWord ++ tailWord_113971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113971).length < 2 ^ (prefixWord ++ tailWord_113971).sum := by decide
  have hdescent : baseEnd_113971 < baseStart_113971 := by decide
  rcases family_descends (prefixWord ++ tailWord_113971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113988 : List Nat := [2, 3, 4, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_113988 : Nat := 118140960795 + 113988 * 2 ^ 59
def prefixEnd_113988 : Nat := 4983230072969 + 3 ^ 40 * 113988 * 2
def baseEnd_113988 : Nat := 58530632844805255125785

theorem tailTrace_113988 : CollatzResearch.WordTrace tailWord_113988 prefixEnd_113988 58530632844805255125785 := by
  unfold tailWord_113988
  simp only [CollatzResearch.WordTrace]
  refine ⟨2078741955524209222807309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2771655940698945630409745 2078741955524209222807309)
  ·
    refine ⟨779528233321578458552741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2078741955524209222807309 779528233321578458552741)
    ·
      refine ⟨146161543747795960978639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 779528233321578458552741 146161543747795960978639)
      ·
        refine ⟨219242315621693941467959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146161543747795960978639 219242315621693941467959)
        ·
          refine ⟨328863473432540912201939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219242315621693941467959 328863473432540912201939)
          ·
            refine ⟨493295210148811368302909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328863473432540912201939 493295210148811368302909)
            ·
              refine ⟨184985703805804263113591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 493295210148811368302909 184985703805804263113591)
              ·
                refine ⟨277478555708706394670387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184985703805804263113591 277478555708706394670387)
                ·
                  refine ⟨416217833563059592005581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277478555708706394670387 416217833563059592005581)
                  ·
                    refine ⟨156081687586147347002093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 416217833563059592005581 156081687586147347002093)
                    ·
                      refine ⟨58530632844805255125785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 156081687586147347002093 58530632844805255125785)
                      ·
                        rfl

theorem cell23_113988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_113988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113988 prefixEnd_113988 := by exact prefixLift 113988
  have htrace : WordTrace (prefixWord ++ tailWord_113988) baseStart_113988 baseEnd_113988 := by
    simpa [prefixWord, tailWord_113988, baseEnd_113988] using wordTrace_append hprefix tailTrace_113988
  have hstable : (prefixWord ++ tailWord_113988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113988).length < 2 ^ (prefixWord ++ tailWord_113988).sum := by decide
  have hdescent : baseEnd_113988 < baseStart_113988 := by decide
  rcases family_descends (prefixWord ++ tailWord_113988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113998 : List Nat := [4, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2]
def baseStart_113998 : Nat := 118140960795 + 113998 * 2 ^ 59
def prefixEnd_113998 : Nat := 4983230072969 + 3 ^ 40 * 113998 * 2
def baseEnd_113998 : Nat := 58535767651350216000739

theorem tailTrace_113998 : CollatzResearch.WordTrace tailWord_113998 prefixEnd_113998 58535767651350216000739 := by
  unfold tailWord_113998
  simp only [CollatzResearch.WordTrace]
  refine ⟨519731080126523769184831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2771899094008126768985765 519731080126523769184831)
  ·
    refine ⟨779596620189785653777247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 519731080126523769184831 779596620189785653777247)
    ·
      refine ⟨1169394930284678480665871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 779596620189785653777247 1169394930284678480665871)
      ·
        refine ⟨1754092395427017720998807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1169394930284678480665871 1754092395427017720998807)
        ·
          refine ⟨2631138593140526581498211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754092395427017720998807 2631138593140526581498211)
          ·
            refine ⟨3946707889710789872247317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2631138593140526581498211 3946707889710789872247317)
            ·
              refine ⟨185001932330193275261593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3946707889710789872247317 185001932330193275261593)
              ·
                refine ⟨138751449247644956446195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185001932330193275261593 138751449247644956446195)
                ·
                  refine ⟨208127173871467434669293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138751449247644956446195 208127173871467434669293)
                  ·
                    refine ⟨78047690201800288000985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 208127173871467434669293 78047690201800288000985)
                    ·
                      refine ⟨58535767651350216000739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 78047690201800288000985 58535767651350216000739)
                      ·
                        rfl

theorem cell23_113998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_113998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_113998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_113998 prefixEnd_113998 := by exact prefixLift 113998
  have htrace : WordTrace (prefixWord ++ tailWord_113998) baseStart_113998 baseEnd_113998 := by
    simpa [prefixWord, tailWord_113998, baseEnd_113998] using wordTrace_append hprefix tailTrace_113998
  have hstable : (prefixWord ++ tailWord_113998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113998).length < 2 ^ (prefixWord ++ tailWord_113998).sum := by decide
  have hdescent : baseEnd_113998 < baseStart_113998 := by decide
  rcases family_descends (prefixWord ++ tailWord_113998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114017 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 9]
def baseStart_114017 : Nat := 118140960795 + 114017 * 2 ^ 59
def prefixEnd_114017 : Nat := 4983230072969 + 3 ^ 40 * 114017 * 2
def baseEnd_114017 : Nat := 6505058198198404629239

theorem tailTrace_114017 : CollatzResearch.WordTrace tailWord_114017 prefixEnd_114017 6505058198198404629239 := by
  unfold tailWord_114017
  simp only [CollatzResearch.WordTrace]
  refine ⟨4158541627943356398420305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2772361085295570932280203 4158541627943356398420305)
  ·
    refine ⟨3118906220957517298815229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4158541627943356398420305 3118906220957517298815229)
    ·
      refine ⟨1169589832859068987055711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3118906220957517298815229 1169589832859068987055711)
      ·
        refine ⟨1754384749288603480583567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1169589832859068987055711 1754384749288603480583567)
        ·
          refine ⟨2631577123932905220875351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754384749288603480583567 2631577123932905220875351)
          ·
            refine ⟨3947365685899357831313027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2631577123932905220875351 3947365685899357831313027)
            ·
              refine ⟨5921048528849036746969541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3947365685899357831313027 5921048528849036746969541)
              ·
                refine ⟨1110196599159194390056789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5921048528849036746969541 1110196599159194390056789)
                ·
                  refine ⟨6505058198198404629239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1110196599159194390056789 6505058198198404629239)
                  ·
                    rfl

theorem cell23_114017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 9].length) (baseStart_114017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114017 prefixEnd_114017 := by exact prefixLift 114017
  have htrace : WordTrace (prefixWord ++ tailWord_114017) baseStart_114017 baseEnd_114017 := by
    simpa [prefixWord, tailWord_114017, baseEnd_114017] using wordTrace_append hprefix tailTrace_114017
  have hstable : (prefixWord ++ tailWord_114017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114017).length < 2 ^ (prefixWord ++ tailWord_114017).sum := by decide
  have hdescent : baseEnd_114017 < baseStart_114017 := by decide
  rcases family_descends (prefixWord ++ tailWord_114017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114028 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 4, 2, 2]
def baseStart_114028 : Nat := 118140960795 + 114028 * 2 ^ 59
def prefixEnd_114028 : Nat := 4983230072969 + 3 ^ 40 * 114028 * 2
def baseEnd_114028 : Nat := 58551172070985098625601

theorem tailTrace_114028 : CollatzResearch.WordTrace tailWord_114028 prefixEnd_114028 58551172070985098625601 := by
  unfold tailWord_114028
  simp only [CollatzResearch.WordTrace]
  refine ⟨2079471415451752638535369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2772628553935670184713825 2079471415451752638535369)
  ·
    refine ⟨1559603561588814478901527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2079471415451752638535369 1559603561588814478901527)
    ·
      refine ⟨2339405342383221718352291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1559603561588814478901527 2339405342383221718352291)
      ·
        refine ⟨3509108013574832577528437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2339405342383221718352291 3509108013574832577528437)
        ·
          refine ⟨328978876272640554143291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3509108013574832577528437 328978876272640554143291)
          ·
            refine ⟨493468314408960831214937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328978876272640554143291 493468314408960831214937)
            ·
              refine ⟨370101235806720623411203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493468314408960831214937 370101235806720623411203)
              ·
                refine ⟨555151853710080935116805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370101235806720623411203 555151853710080935116805)
                ·
                  refine ⟨104090972570640175334401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 555151853710080935116805 104090972570640175334401)
                  ·
                    refine ⟨78068229427980131500801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104090972570640175334401 78068229427980131500801)
                    ·
                      refine ⟨58551172070985098625601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 78068229427980131500801 58551172070985098625601)
                      ·
                        rfl

theorem cell23_114028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 2, 2].length) (baseStart_114028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114028 prefixEnd_114028 := by exact prefixLift 114028
  have htrace : WordTrace (prefixWord ++ tailWord_114028) baseStart_114028 baseEnd_114028 := by
    simpa [prefixWord, tailWord_114028, baseEnd_114028] using wordTrace_append hprefix tailTrace_114028
  have hstable : (prefixWord ++ tailWord_114028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114028).length < 2 ^ (prefixWord ++ tailWord_114028).sum := by decide
  have hdescent : baseEnd_114028 < baseStart_114028 := by decide
  rcases family_descends (prefixWord ++ tailWord_114028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114044 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 1, 5, 3]
def baseStart_114044 : Nat := 118140960795 + 114044 * 2 ^ 59
def prefixEnd_114044 : Nat := 4983230072969 + 3 ^ 40 * 114044 * 2
def baseEnd_114044 : Nat := 58559387761457036025527

theorem tailTrace_114044 : CollatzResearch.WordTrace tailWord_114044 prefixEnd_114044 58559387761457036025527 := by
  unfold tailWord_114044
  simp only [CollatzResearch.WordTrace]
  refine ⟨2079763199422770004826593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2773017599230360006435457 2079763199422770004826593)
  ·
    refine ⟨1559822399567077503619945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2079763199422770004826593 1559822399567077503619945)
    ·
      refine ⟨1169866799675308127714959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1559822399567077503619945 1169866799675308127714959)
      ·
        refine ⟨1754800199512962191572439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1169866799675308127714959 1754800199512962191572439)
        ·
          refine ⟨2632200299269443287358659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754800199512962191572439 2632200299269443287358659)
          ·
            refine ⟨3948300448904164931037989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632200299269443287358659 3948300448904164931037989)
            ·
              refine ⟨740306334169530924569623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3948300448904164931037989 740306334169530924569623)
              ·
                refine ⟨1110459501254296386854435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740306334169530924569623 1110459501254296386854435)
                ·
                  refine ⟨1665689251881444580281653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1110459501254296386854435 1665689251881444580281653)
                  ·
                    refine ⟨156158367363885429401405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1665689251881444580281653 156158367363885429401405)
                    ·
                      refine ⟨58559387761457036025527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 156158367363885429401405 58559387761457036025527)
                      ·
                        rfl

theorem cell23_114044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_114044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114044 prefixEnd_114044 := by exact prefixLift 114044
  have htrace : WordTrace (prefixWord ++ tailWord_114044) baseStart_114044 baseEnd_114044 := by
    simpa [prefixWord, tailWord_114044, baseEnd_114044] using wordTrace_append hprefix tailTrace_114044
  have hstable : (prefixWord ++ tailWord_114044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114044).length < 2 ^ (prefixWord ++ tailWord_114044).sum := by decide
  have hdescent : baseEnd_114044 < baseStart_114044 := by decide
  rcases family_descends (prefixWord ++ tailWord_114044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114074 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5]
def baseStart_114074 : Nat := 118140960795 + 114074 * 2 ^ 59
def prefixEnd_114074 : Nat := 4983230072969 + 3 ^ 40 * 114074 * 2
def baseEnd_114074 : Nat := 58574792181091918650389

theorem tailTrace_114074 : CollatzResearch.WordTrace tailWord_114074 prefixEnd_114074 58574792181091918650389 := by
  unfold tailWord_114074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1040155147184213783311319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2773747059157903422163517 1040155147184213783311319)
  ·
    refine ⟨1560232720776320674966979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1040155147184213783311319 1560232720776320674966979)
    ·
      refine ⟨2340349081164481012450469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1560232720776320674966979 2340349081164481012450469)
      ·
        refine ⟨438815452718340189834463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2340349081164481012450469 438815452718340189834463)
        ·
          refine ⟨658223179077510284751695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438815452718340189834463 658223179077510284751695)
          ·
            refine ⟨987334768616265427127543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658223179077510284751695 987334768616265427127543)
            ·
              refine ⟨1481002152924398140691315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987334768616265427127543 1481002152924398140691315)
              ·
                refine ⟨2221503229386597211036973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1481002152924398140691315 2221503229386597211036973)
                ·
                  refine ⟨833063711019973954138865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2221503229386597211036973 833063711019973954138865)
                  ·
                    refine ⟨624797783264980465604149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 833063711019973954138865 624797783264980465604149)
                    ·
                      refine ⟨58574792181091918650389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 624797783264980465604149 58574792181091918650389)
                      ·
                        rfl

theorem cell23_114074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_114074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114074 prefixEnd_114074 := by exact prefixLift 114074
  have htrace : WordTrace (prefixWord ++ tailWord_114074) baseStart_114074 baseEnd_114074 := by
    simpa [prefixWord, tailWord_114074, baseEnd_114074] using wordTrace_append hprefix tailTrace_114074
  have hstable : (prefixWord ++ tailWord_114074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114074).length < 2 ^ (prefixWord ++ tailWord_114074).sum := by decide
  have hdescent : baseEnd_114074 < baseStart_114074 := by decide
  rcases family_descends (prefixWord ++ tailWord_114074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114084 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_114084 : Nat := 118140960795 + 114084 * 2 ^ 59
def prefixEnd_114084 : Nat := 4983230072969 + 3 ^ 40 * 114084 * 2
def baseEnd_114084 : Nat := 58579926987636879525343

theorem tailTrace_114084 : CollatzResearch.WordTrace tailWord_114084 prefixEnd_114084 58579926987636879525343 := by
  unfold tailWord_114084
  simp only [CollatzResearch.WordTrace]
  refine ⟨2080492659350313420554653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2773990212467084560739537 2080492659350313420554653)
  ·
    refine ⟨780184747256367532707995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2080492659350313420554653 780184747256367532707995)
    ·
      refine ⟨1170277120884551299061993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 780184747256367532707995 1170277120884551299061993)
      ·
        refine ⟨877707840663413474296495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1170277120884551299061993 877707840663413474296495)
        ·
          refine ⟨1316561760995120211444743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 877707840663413474296495 1316561760995120211444743)
          ·
            refine ⟨1974842641492680317167115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1316561760995120211444743 1974842641492680317167115)
            ·
              refine ⟨2962263962239020475750673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1974842641492680317167115 2962263962239020475750673)
              ·
                refine ⟨2221697971679265356813005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2962263962239020475750673 2221697971679265356813005)
                ·
                  refine ⟨833136739379724508804877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2221697971679265356813005 833136739379724508804877)
                  ·
                    refine ⟨312426277267396690801829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 833136739379724508804877 312426277267396690801829)
                    ·
                      refine ⟨58579926987636879525343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 312426277267396690801829 58579926987636879525343)
                      ·
                        rfl

theorem cell23_114084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_114084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114084 prefixEnd_114084 := by exact prefixLift 114084
  have htrace : WordTrace (prefixWord ++ tailWord_114084) baseStart_114084 baseEnd_114084 := by
    simpa [prefixWord, tailWord_114084, baseEnd_114084] using wordTrace_append hprefix tailTrace_114084
  have hstable : (prefixWord ++ tailWord_114084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114084).length < 2 ^ (prefixWord ++ tailWord_114084).sum := by decide
  have hdescent : baseEnd_114084 < baseStart_114084 := by decide
  rcases family_descends (prefixWord ++ tailWord_114084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114141 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 8]
def baseStart_114141 : Nat := 118140960795 + 114141 * 2 ^ 59
def prefixEnd_114141 : Nat := 4983230072969 + 3 ^ 40 * 114141 * 2
def baseEnd_114141 : Nat := 6512132820549239612509

theorem tailTrace_114141 : CollatzResearch.WordTrace tailWord_114141 prefixEnd_114141 6512132820549239612509 := by
  unfold tailWord_114141
  simp only [CollatzResearch.WordTrace]
  refine ⟨4163064279494125575934277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2775376186329417050622851 4163064279494125575934277)
  ·
    refine ⟨780574552405148545487677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4163064279494125575934277 780574552405148545487677)
    ·
      refine ⟨292715457151930704557879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 780574552405148545487677 292715457151930704557879)
      ·
        refine ⟨439073185727896056836819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292715457151930704557879 439073185727896056836819)
        ·
          refine ⟨658609778591844085255229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439073185727896056836819 658609778591844085255229)
          ·
            refine ⟨246978666971941531970711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 658609778591844085255229 246978666971941531970711)
            ·
              refine ⟨370468000457912297956067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246978666971941531970711 370468000457912297956067)
              ·
                refine ⟨555702000686868446934101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370468000457912297956067 555702000686868446934101)
                ·
                  refine ⟨6512132820549239612509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 555702000686868446934101 6512132820549239612509)
                  ·
                    rfl

theorem cell23_114141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_114141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114141 prefixEnd_114141 := by exact prefixLift 114141
  have htrace : WordTrace (prefixWord ++ tailWord_114141) baseStart_114141 baseEnd_114141 := by
    simpa [prefixWord, tailWord_114141, baseEnd_114141] using wordTrace_append hprefix tailTrace_114141
  have hstable : (prefixWord ++ tailWord_114141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114141).length < 2 ^ (prefixWord ++ tailWord_114141).sum := by decide
  have hdescent : baseEnd_114141 < baseStart_114141 := by decide
  rcases family_descends (prefixWord ++ tailWord_114141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114158 : List Nat := [4, 1, 2, 1, 2, 1, 5, 1, 6]
def baseStart_114158 : Nat := 118140960795 + 114158 * 2 ^ 59
def prefixEnd_114158 : Nat := 4983230072969 + 3 ^ 40 * 114158 * 2
def baseEnd_114158 : Nat := 6513102728452176666667

theorem tailTrace_114158 : CollatzResearch.WordTrace tailWord_114158 prefixEnd_114158 6513102728452176666667 := by
  unfold tailWord_114158
  simp only [CollatzResearch.WordTrace]
  refine ⟨520460540054067184912891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2775789546955024986202085 520460540054067184912891)
  ·
    refine ⟨780690810081100777369337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 520460540054067184912891 780690810081100777369337)
    ·
      refine ⟨585518107560825583027003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 780690810081100777369337 585518107560825583027003)
      ·
        refine ⟨878277161341238374540505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585518107560825583027003 878277161341238374540505)
        ·
          refine ⟨658707871005928780905379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 878277161341238374540505 658707871005928780905379)
          ·
            refine ⟨988061806508893171358069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658707871005928780905379 988061806508893171358069)
            ·
              refine ⟨92630794360208734814819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 988061806508893171358069 92630794360208734814819)
              ·
                refine ⟨138946191540313102222229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92630794360208734814819 138946191540313102222229)
                ·
                  refine ⟨6513102728452176666667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138946191540313102222229 6513102728452176666667)
                  ·
                    rfl

theorem cell23_114158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_114158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114158 prefixEnd_114158 := by exact prefixLift 114158
  have htrace : WordTrace (prefixWord ++ tailWord_114158) baseStart_114158 baseEnd_114158 := by
    simpa [prefixWord, tailWord_114158, baseEnd_114158] using wordTrace_append hprefix tailTrace_114158
  have hstable : (prefixWord ++ tailWord_114158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114158).length < 2 ^ (prefixWord ++ tailWord_114158).sum := by decide
  have hdescent : baseEnd_114158 < baseStart_114158 := by decide
  rcases family_descends (prefixWord ++ tailWord_114158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114168 : List Nat := [2, 1, 2, 1, 1, 5, 2, 2, 3, 1, 3]
def baseStart_114168 : Nat := 118140960795 + 114168 * 2 ^ 59
def prefixEnd_114168 : Nat := 4983230072969 + 3 ^ 40 * 114168 * 2
def baseEnd_114168 : Nat := 58623059362614550874957

theorem tailTrace_114168 : CollatzResearch.WordTrace tailWord_114168 prefixEnd_114168 58623059362614550874957 := by
  unfold tailWord_114168
  simp only [CollatzResearch.WordTrace]
  refine ⟨2082024525198154593583579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2776032700264206124778105 2082024525198154593583579)
  ·
    refine ⟨3123036787797231890375369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2082024525198154593583579 3123036787797231890375369)
    ·
      refine ⟨2342277590847923917781527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3123036787797231890375369 2342277590847923917781527)
      ·
        refine ⟨3513416386271885876672291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2342277590847923917781527 3513416386271885876672291)
        ·
          refine ⟨5270124579407828815008437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3513416386271885876672291 5270124579407828815008437)
          ·
            refine ⟨494074179319483951407041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5270124579407828815008437 494074179319483951407041)
            ·
              refine ⟨370555634489612963555281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494074179319483951407041 370555634489612963555281)
              ·
                refine ⟨277916725867209722666461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370555634489612963555281 277916725867209722666461)
                ·
                  refine ⟨104218772200203645999923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277916725867209722666461 104218772200203645999923)
                  ·
                    refine ⟨156328158300305468999885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104218772200203645999923 156328158300305468999885)
                    ·
                      refine ⟨58623059362614550874957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 156328158300305468999885 58623059362614550874957)
                      ·
                        rfl

theorem cell23_114168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 3, 1, 3].length) (baseStart_114168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114168 prefixEnd_114168 := by exact prefixLift 114168
  have htrace : WordTrace (prefixWord ++ tailWord_114168) baseStart_114168 baseEnd_114168 := by
    simpa [prefixWord, tailWord_114168, baseEnd_114168] using wordTrace_append hprefix tailTrace_114168
  have hstable : (prefixWord ++ tailWord_114168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114168).length < 2 ^ (prefixWord ++ tailWord_114168).sum := by decide
  have hdescent : baseEnd_114168 < baseStart_114168 := by decide
  rcases family_descends (prefixWord ++ tailWord_114168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114191 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 4, 6, 2]
def baseStart_114191 : Nat := 118140960795 + 114191 * 2 ^ 59
def prefixEnd_114191 : Nat := 4983230072969 + 3 ^ 40 * 114191 * 2
def baseEnd_114191 : Nat := 58634869417667960887351

theorem tailTrace_114191 : CollatzResearch.WordTrace tailWord_114191 prefixEnd_114191 58634869417667960887351 := by
  unfold tailWord_114191
  simp only [CollatzResearch.WordTrace]
  refine ⟨4164887929312984115254427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2776591952875322743502951 4164887929312984115254427)
  ·
    refine ⟨6247331893969476172881641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4164887929312984115254427 6247331893969476172881641)
    ·
      refine ⟨4685498920477107129661231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6247331893969476172881641 4685498920477107129661231)
      ·
        refine ⟨7028248380715660694491847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4685498920477107129661231 7028248380715660694491847)
        ·
          refine ⟨10542372571073491041737771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7028248380715660694491847 10542372571073491041737771)
          ·
            refine ⟨15813558856610236562606657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10542372571073491041737771 15813558856610236562606657)
            ·
              refine ⟨11860169142457677421954993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15813558856610236562606657 11860169142457677421954993)
              ·
                refine ⟨8895126856843258066466245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11860169142457677421954993 8895126856843258066466245)
                ·
                  refine ⟨1667836285658110887462421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8895126856843258066466245 1667836285658110887462421)
                  ·
                    refine ⟨78179825890223947849801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1667836285658110887462421 78179825890223947849801)
                    ·
                      refine ⟨58634869417667960887351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 78179825890223947849801 58634869417667960887351)
                      ·
                        rfl

theorem cell23_114191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 6, 2].length) (baseStart_114191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114191 prefixEnd_114191 := by exact prefixLift 114191
  have htrace : WordTrace (prefixWord ++ tailWord_114191) baseStart_114191 baseEnd_114191 := by
    simpa [prefixWord, tailWord_114191, baseEnd_114191] using wordTrace_append hprefix tailTrace_114191
  have hstable : (prefixWord ++ tailWord_114191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114191).length < 2 ^ (prefixWord ++ tailWord_114191).sum := by decide
  have hdescent : baseEnd_114191 < baseStart_114191 := by decide
  rcases family_descends (prefixWord ++ tailWord_114191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114245 : List Nat := [1, 3, 1, 1, 1, 4, 5, 1, 1, 2, 3]
def baseStart_114245 : Nat := 118140960795 + 114245 * 2 ^ 59
def prefixEnd_114245 : Nat := 4983230072969 + 3 ^ 40 * 114245 * 2
def baseEnd_114245 : Nat := 58662597373010749612103

theorem tailTrace_114245 : CollatzResearch.WordTrace tailWord_114245 prefixEnd_114245 58662597373010749612103 := by
  unfold tailWord_114245
  simp only [CollatzResearch.WordTrace]
  refine ⟨4166857471117351337720189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2777904980744900891813459 4166857471117351337720189)
  ·
    refine ⟨1562571551669006751645071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4166857471117351337720189 1562571551669006751645071)
    ·
      refine ⟨2343857327503510127467607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1562571551669006751645071 2343857327503510127467607)
      ·
        refine ⟨3515785991255265191201411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2343857327503510127467607 3515785991255265191201411)
        ·
          refine ⟨5273678986882897786802117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3515785991255265191201411 5273678986882897786802117)
          ·
            refine ⟨988814810040543335025397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5273678986882897786802117 988814810040543335025397)
            ·
              refine ⟨92701388441300937658631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 988814810040543335025397 92701388441300937658631)
              ·
                refine ⟨139052082661951406487947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92701388441300937658631 139052082661951406487947)
                ·
                  refine ⟨208578123992927109731921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139052082661951406487947 208578123992927109731921)
                  ·
                    refine ⟨156433592994695332298941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 208578123992927109731921 156433592994695332298941)
                    ·
                      refine ⟨58662597373010749612103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 156433592994695332298941 58662597373010749612103)
                      ·
                        rfl

theorem cell23_114245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 1, 2, 3].length) (baseStart_114245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114245 prefixEnd_114245 := by exact prefixLift 114245
  have htrace : WordTrace (prefixWord ++ tailWord_114245) baseStart_114245 baseEnd_114245 := by
    simpa [prefixWord, tailWord_114245, baseEnd_114245] using wordTrace_append hprefix tailTrace_114245
  have hstable : (prefixWord ++ tailWord_114245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114245).length < 2 ^ (prefixWord ++ tailWord_114245).sum := by decide
  have hdescent : baseEnd_114245 < baseStart_114245 := by decide
  rcases family_descends (prefixWord ++ tailWord_114245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114253 : List Nat := [1, 6, 1, 1, 4, 1, 2, 2, 1, 1, 3]
def baseStart_114253 : Nat := 118140960795 + 114253 * 2 ^ 59
def prefixEnd_114253 : Nat := 4983230072969 + 3 ^ 40 * 114253 * 2
def baseEnd_114253 : Nat := 58666705218246718312067

theorem tailTrace_114253 : CollatzResearch.WordTrace tailWord_114253 prefixEnd_114253 58666705218246718312067 := by
  unfold tailWord_114253
  simp only [CollatzResearch.WordTrace]
  refine ⟨4167149255088368704011413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2778099503392245802674275 4167149255088368704011413)
  ·
    refine ⟨195335121332267283000535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4167149255088368704011413 195335121332267283000535)
    ·
      refine ⟨293002681998400924500803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195335121332267283000535 293002681998400924500803)
      ·
        refine ⟨439504022997601386751205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293002681998400924500803 439504022997601386751205)
        ·
          refine ⟨82407004312050260015851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 439504022997601386751205 82407004312050260015851)
          ·
            refine ⟨123610506468075390023777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82407004312050260015851 123610506468075390023777)
            ·
              refine ⟨92707879851056542517833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123610506468075390023777 92707879851056542517833)
              ·
                refine ⟨69530909888292406888375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92707879851056542517833 69530909888292406888375)
                ·
                  refine ⟨104296364832438610332563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69530909888292406888375 104296364832438610332563)
                  ·
                    refine ⟨156444547248657915498845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104296364832438610332563 156444547248657915498845)
                    ·
                      refine ⟨58666705218246718312067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 156444547248657915498845 58666705218246718312067)
                      ·
                        rfl

theorem cell23_114253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_114253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114253 prefixEnd_114253 := by exact prefixLift 114253
  have htrace : WordTrace (prefixWord ++ tailWord_114253) baseStart_114253 baseEnd_114253 := by
    simpa [prefixWord, tailWord_114253, baseEnd_114253] using wordTrace_append hprefix tailTrace_114253
  have hstable : (prefixWord ++ tailWord_114253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114253).length < 2 ^ (prefixWord ++ tailWord_114253).sum := by decide
  have hdescent : baseEnd_114253 < baseStart_114253 := by decide
  rcases family_descends (prefixWord ++ tailWord_114253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114275 : List Nat := [1, 1, 1, 5, 1, 3, 2, 3, 2, 1, 3]
def baseStart_114275 : Nat := 118140960795 + 114275 * 2 ^ 59
def prefixEnd_114275 : Nat := 4983230072969 + 3 ^ 40 * 114275 * 2
def baseEnd_114275 : Nat := 58678001792645632236965

theorem tailTrace_114275 : CollatzResearch.WordTrace tailWord_114275 prefixEnd_114275 58678001792645632236965 := by
  unfold tailWord_114275
  simp only [CollatzResearch.WordTrace]
  refine ⟨4167951661008666461312279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2778634440672444307541519 4167951661008666461312279)
  ·
    refine ⟨6251927491512999691968419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4167951661008666461312279 6251927491512999691968419)
    ·
      refine ⟨9377891237269499537952629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6251927491512999691968419 9377891237269499537952629)
      ·
        refine ⟨879177303494015581683059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9377891237269499537952629 879177303494015581683059)
        ·
          refine ⟨1318765955241023372524589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879177303494015581683059 1318765955241023372524589)
          ·
            refine ⟨494537233215383764696721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1318765955241023372524589 494537233215383764696721)
            ·
              refine ⟨370902924911537823522541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494537233215383764696721 370902924911537823522541)
              ·
                refine ⟨139088596841826683820953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370902924911537823522541 139088596841826683820953)
                ·
                  refine ⟨104316447631370012865715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139088596841826683820953 104316447631370012865715)
                  ·
                    refine ⟨156474671447055019298573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104316447631370012865715 156474671447055019298573)
                    ·
                      refine ⟨58678001792645632236965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 156474671447055019298573 58678001792645632236965)
                      ·
                        rfl

theorem cell23_114275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_114275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114275 prefixEnd_114275 := by exact prefixLift 114275
  have htrace : WordTrace (prefixWord ++ tailWord_114275) baseStart_114275 baseEnd_114275 := by
    simpa [prefixWord, tailWord_114275, baseEnd_114275] using wordTrace_append hprefix tailTrace_114275
  have hstable : (prefixWord ++ tailWord_114275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114275).length < 2 ^ (prefixWord ++ tailWord_114275).sum := by decide
  have hdescent : baseEnd_114275 < baseStart_114275 := by decide
  rcases family_descends (prefixWord ++ tailWord_114275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114298 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2]
def baseStart_114298 : Nat := 118140960795 + 114298 * 2 ^ 59
def prefixEnd_114298 : Nat := 4983230072969 + 3 ^ 40 * 114298 * 2
def baseEnd_114298 : Nat := 58689811847699042249359

theorem tailTrace_114298 : CollatzResearch.WordTrace tailWord_114298 prefixEnd_114298 58689811847699042249359 := by
  unfold tailWord_114298
  simp only [CollatzResearch.WordTrace]
  refine ⟨1042197634981335347349887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2779193693283560926266365 1042197634981335347349887)
  ·
    refine ⟨1563296452472003021024831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1042197634981335347349887 1563296452472003021024831)
    ·
      refine ⟨2344944678708004531537247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1563296452472003021024831 2344944678708004531537247)
      ·
        refine ⟨3517417018062006797305871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2344944678708004531537247 3517417018062006797305871)
        ·
          refine ⟨5276125527093010195958807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3517417018062006797305871 5276125527093010195958807)
          ·
            refine ⟨7914188290639515293938211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5276125527093010195958807 7914188290639515293938211)
            ·
              refine ⟨11871282435959272940907317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7914188290639515293938211 11871282435959272940907317)
              ·
                refine ⟨1112932728371181838210061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11871282435959272940907317 1112932728371181838210061)
                ·
                  refine ⟨417349773139193189328773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112932728371181838210061 417349773139193189328773)
                  ·
                    refine ⟨78253082463598722999145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 417349773139193189328773 78253082463598722999145)
                    ·
                      refine ⟨58689811847699042249359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 78253082463598722999145 58689811847699042249359)
                      ·
                        rfl

theorem cell23_114298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2].length) (baseStart_114298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114298 prefixEnd_114298 := by exact prefixLift 114298
  have htrace : WordTrace (prefixWord ++ tailWord_114298) baseStart_114298 baseEnd_114298 := by
    simpa [prefixWord, tailWord_114298, baseEnd_114298] using wordTrace_append hprefix tailTrace_114298
  have hstable : (prefixWord ++ tailWord_114298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114298).length < 2 ^ (prefixWord ++ tailWord_114298).sum := by decide
  have hdescent : baseEnd_114298 < baseStart_114298 := by decide
  rcases family_descends (prefixWord ++ tailWord_114298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114315 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 4, 2, 2]
def baseStart_114315 : Nat := 118140960795 + 114315 * 2 ^ 59
def prefixEnd_114315 : Nat := 4983230072969 + 3 ^ 40 * 114315 * 2
def baseEnd_114315 : Nat := 58698541018825475736781

theorem tailTrace_114315 : CollatzResearch.WordTrace tailWord_114315 prefixEnd_114315 58698541018825475736781 := by
  unfold tailWord_114315
  simp only [CollatzResearch.WordTrace]
  refine ⟨4169410580863753292768399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2779607053909168861845599 4169410580863753292768399)
  ·
    refine ⟨6254115871295629939152599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4169410580863753292768399 6254115871295629939152599)
    ·
      refine ⟨9381173806943444908728899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6254115871295629939152599 9381173806943444908728899)
      ·
        refine ⟨14071760710415167363093349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9381173806943444908728899 14071760710415167363093349)
        ·
          refine ⟨2638455133202843880580003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14071760710415167363093349 2638455133202843880580003)
          ·
            refine ⟨3957682699804265820870005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2638455133202843880580003 3957682699804265820870005)
            ·
              refine ⟨371032753106649920706563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3957682699804265820870005 371032753106649920706563)
              ·
                refine ⟨556549129659974881059845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371032753106649920706563 556549129659974881059845)
                ·
                  refine ⟨104352961811245290198721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 556549129659974881059845 104352961811245290198721)
                  ·
                    refine ⟨78264721358433967649041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104352961811245290198721 78264721358433967649041)
                    ·
                      refine ⟨58698541018825475736781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 78264721358433967649041 58698541018825475736781)
                      ·
                        rfl

theorem cell23_114315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 2, 2].length) (baseStart_114315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114315 prefixEnd_114315 := by exact prefixLift 114315
  have htrace : WordTrace (prefixWord ++ tailWord_114315) baseStart_114315 baseEnd_114315 := by
    simpa [prefixWord, tailWord_114315, baseEnd_114315] using wordTrace_append hprefix tailTrace_114315
  have hstable : (prefixWord ++ tailWord_114315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114315).length < 2 ^ (prefixWord ++ tailWord_114315).sum := by decide
  have hdescent : baseEnd_114315 < baseStart_114315 := by decide
  rcases family_descends (prefixWord ++ tailWord_114315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114328 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 2, 2, 4]
def baseStart_114328 : Nat := 118140960795 + 114328 * 2 ^ 59
def prefixEnd_114328 : Nat := 4983230072969 + 3 ^ 40 * 114328 * 2
def baseEnd_114328 : Nat := 58705216267333924874221

theorem tailTrace_114328 : CollatzResearch.WordTrace tailWord_114328 prefixEnd_114328 58705216267333924874221 := by
  unfold tailWord_114328
  simp only [CollatzResearch.WordTrace]
  refine ⟨2084942364908328256495819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2779923153211104341994425 2084942364908328256495819)
  ·
    refine ⟨3127413547362492384743729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2084942364908328256495819 3127413547362492384743729)
    ·
      refine ⟨2345560160521869288557797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3127413547362492384743729 2345560160521869288557797)
      ·
        refine ⟨439792530097850491604587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2345560160521869288557797 439792530097850491604587)
        ·
          refine ⟨659688795146775737406881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439792530097850491604587 659688795146775737406881)
          ·
            refine ⟨494766596360081803055161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 659688795146775737406881 494766596360081803055161)
            ·
              refine ⟨371074947270061352291371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494766596360081803055161 371074947270061352291371)
              ·
                refine ⟨556612420905092028437057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371074947270061352291371 556612420905092028437057)
                ·
                  refine ⟨417459315678819021327793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 556612420905092028437057 417459315678819021327793)
                  ·
                    refine ⟨313094486759114265995845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 417459315678819021327793 313094486759114265995845)
                    ·
                      refine ⟨58705216267333924874221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 313094486759114265995845 58705216267333924874221)
                      ·
                        rfl

theorem cell23_114328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_114328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114328 prefixEnd_114328 := by exact prefixLift 114328
  have htrace : WordTrace (prefixWord ++ tailWord_114328) baseStart_114328 baseEnd_114328 := by
    simpa [prefixWord, tailWord_114328, baseEnd_114328] using wordTrace_append hprefix tailTrace_114328
  have hstable : (prefixWord ++ tailWord_114328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114328).length < 2 ^ (prefixWord ++ tailWord_114328).sum := by decide
  have hdescent : baseEnd_114328 < baseStart_114328 := by decide
  rcases family_descends (prefixWord ++ tailWord_114328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114351 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 1, 7]
def baseStart_114351 : Nat := 118140960795 + 114351 * 2 ^ 59
def prefixEnd_114351 : Nat := 4983230072969 + 3 ^ 40 * 114351 * 2
def baseEnd_114351 : Nat := 19572342107462444962205

theorem tailTrace_114351 : CollatzResearch.WordTrace tailWord_114351 prefixEnd_114351 19572342107462444962205 := by
  unfold tailWord_114351
  simp only [CollatzResearch.WordTrace]
  refine ⟨4170723608733331441078907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2780482405822220960719271 4170723608733331441078907)
  ·
    refine ⟨6256085413099997161618361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4170723608733331441078907 6256085413099997161618361)
    ·
      refine ⟨4692064059824997871213771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6256085413099997161618361 4692064059824997871213771)
      ·
        refine ⟨7038096089737496806820657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4692064059824997871213771 7038096089737496806820657)
        ·
          refine ⟨5278572067303122605115493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7038096089737496806820657 5278572067303122605115493)
          ·
            refine ⟨989732262619335488459155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5278572067303122605115493 989732262619335488459155)
            ·
              refine ⟨1484598393929003232688733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989732262619335488459155 1484598393929003232688733)
              ·
                refine ⟨556724397723376212258275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1484598393929003232688733 556724397723376212258275)
                ·
                  refine ⟨835086596585064318387413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 556724397723376212258275 835086596585064318387413)
                  ·
                    refine ⟨19572342107462444962205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 835086596585064318387413 19572342107462444962205)
                    ·
                      rfl

theorem cell23_114351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 7].length) (baseStart_114351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114351 prefixEnd_114351 := by exact prefixLift 114351
  have htrace : WordTrace (prefixWord ++ tailWord_114351) baseStart_114351 baseEnd_114351 := by
    simpa [prefixWord, tailWord_114351, baseEnd_114351] using wordTrace_append hprefix tailTrace_114351
  have hstable : (prefixWord ++ tailWord_114351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114351).length < 2 ^ (prefixWord ++ tailWord_114351).sum := by decide
  have hdescent : baseEnd_114351 < baseStart_114351 := by decide
  rcases family_descends (prefixWord ++ tailWord_114351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114368 : List Nat := [2, 1, 1, 2, 4, 1, 3, 2, 2, 5]
def baseStart_114368 : Nat := 118140960795 + 114368 * 2 ^ 59
def prefixEnd_114368 : Nat := 4983230072969 + 3 ^ 40 * 114368 * 2
def baseEnd_114368 : Nat := 19575251831171256124679

theorem tailTrace_114368 : CollatzResearch.WordTrace tailWord_114368 prefixEnd_114368 19575251831171256124679 := by
  unfold tailWord_114368
  simp only [CollatzResearch.WordTrace]
  refine ⟨2085671824835871672223879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2780895766447828896298505 2085671824835871672223879)
  ·
    refine ⟨3128507737253807508335819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2085671824835871672223879 3128507737253807508335819)
    ·
      refine ⟨4692761605880711262503729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3128507737253807508335819 4692761605880711262503729)
      ·
        refine ⟨3519571204410533446877797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4692761605880711262503729 3519571204410533446877797)
        ·
          refine ⟨659919600826975021289587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3519571204410533446877797 659919600826975021289587)
          ·
            refine ⟨989879401240462531934381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659919600826975021289587 989879401240462531934381)
            ·
              refine ⟨371204775465173449475393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 989879401240462531934381 371204775465173449475393)
              ·
                refine ⟨278403581598880087106545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 371204775465173449475393 278403581598880087106545)
                ·
                  refine ⟨208802686199160065329909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278403581598880087106545 208802686199160065329909)
                  ·
                    refine ⟨19575251831171256124679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 208802686199160065329909 19575251831171256124679)
                    ·
                      rfl

theorem cell23_114368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 2, 5].length) (baseStart_114368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114368 prefixEnd_114368 := by exact prefixLift 114368
  have htrace : WordTrace (prefixWord ++ tailWord_114368) baseStart_114368 baseEnd_114368 := by
    simpa [prefixWord, tailWord_114368, baseEnd_114368] using wordTrace_append hprefix tailTrace_114368
  have hstable : (prefixWord ++ tailWord_114368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114368).length < 2 ^ (prefixWord ++ tailWord_114368).sum := by decide
  have hdescent : baseEnd_114368 < baseStart_114368 := by decide
  rcases family_descends (prefixWord ++ tailWord_114368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114371 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 4]
def baseStart_114371 : Nat := 118140960795 + 114371 * 2 ^ 59
def prefixEnd_114371 : Nat := 4983230072969 + 3 ^ 40 * 114371 * 2
def baseEnd_114371 : Nat := 58727295935477256636523

theorem tailTrace_114371 : CollatzResearch.WordTrace tailWord_114371 prefixEnd_114371 58727295935477256636523 := by
  unfold tailWord_114371
  simp only [CollatzResearch.WordTrace]
  refine ⟨4171453068660874856806967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2780968712440583237871311 4171453068660874856806967)
  ·
    refine ⟨6257179602991312285210451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4171453068660874856806967 6257179602991312285210451)
    ·
      refine ⟨9385769404486968427815677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6257179602991312285210451 9385769404486968427815677)
      ·
        refine ⟨3519663526682613160430879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9385769404486968427815677 3519663526682613160430879)
        ·
          refine ⟨5279495290023919740646319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519663526682613160430879 5279495290023919740646319)
          ·
            refine ⟨7919242935035879610969479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5279495290023919740646319 7919242935035879610969479)
            ·
              refine ⟨11878864402553819416454219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7919242935035879610969479 11878864402553819416454219)
              ·
                refine ⟨17818296603830729124681329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11878864402553819416454219 17818296603830729124681329)
                ·
                  refine ⟨13363722452873046843510997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17818296603830729124681329 13363722452873046843510997)
                  ·
                    refine ⟨313212244989212035394789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13363722452873046843510997 313212244989212035394789)
                    ·
                      refine ⟨58727295935477256636523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 313212244989212035394789 58727295935477256636523)
                      ·
                        rfl

theorem cell23_114371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_114371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114371 prefixEnd_114371 := by exact prefixLift 114371
  have htrace : WordTrace (prefixWord ++ tailWord_114371) baseStart_114371 baseEnd_114371 := by
    simpa [prefixWord, tailWord_114371, baseEnd_114371] using wordTrace_append hprefix tailTrace_114371
  have hstable : (prefixWord ++ tailWord_114371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114371).length < 2 ^ (prefixWord ++ tailWord_114371).sum := by decide
  have hdescent : baseEnd_114371 < baseStart_114371 := by decide
  rcases family_descends (prefixWord ++ tailWord_114371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114372 : List Nat := [2, 3, 3, 1, 1, 1, 5, 2, 5]
def baseStart_114372 : Nat := 118140960795 + 114372 * 2 ^ 59
def prefixEnd_114372 : Nat := 4983230072969 + 3 ^ 40 * 114372 * 2
def baseEnd_114372 : Nat := 6525312157347972524891

theorem tailTrace_114372 : CollatzResearch.WordTrace tailWord_114372 prefixEnd_114372 6525312157347972524891 := by
  unfold tailWord_114372
  simp only [CollatzResearch.WordTrace]
  refine ⟨2085744770828626013796685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2780993027771501351728913 2085744770828626013796685)
  ·
    refine ⟨782154289060734755173757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2085744770828626013796685 782154289060734755173757)
    ·
      refine ⟨293307858397775533190159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 782154289060734755173757 293307858397775533190159)
      ·
        refine ⟨439961787596663299785239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293307858397775533190159 439961787596663299785239)
        ·
          refine ⟨659942681394994949677859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439961787596663299785239 659942681394994949677859)
          ·
            refine ⟨989914022092492424516789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659942681394994949677859 989914022092492424516789)
            ·
              refine ⟨92804439571171164798449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 989914022092492424516789 92804439571171164798449)
              ·
                refine ⟨69603329678378373598837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92804439571171164798449 69603329678378373598837)
                ·
                  refine ⟨6525312157347972524891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69603329678378373598837 6525312157347972524891)
                  ·
                    rfl

theorem cell23_114372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_114372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114372 prefixEnd_114372 := by exact prefixLift 114372
  have htrace : WordTrace (prefixWord ++ tailWord_114372) baseStart_114372 baseEnd_114372 := by
    simpa [prefixWord, tailWord_114372, baseEnd_114372] using wordTrace_append hprefix tailTrace_114372
  have hstable : (prefixWord ++ tailWord_114372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114372).length < 2 ^ (prefixWord ++ tailWord_114372).sum := by decide
  have hdescent : baseEnd_114372 < baseStart_114372 := by decide
  rcases family_descends (prefixWord ++ tailWord_114372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114405 : List Nat := [1, 3, 1, 4, 1, 1, 4, 1, 2, 1, 4]
def baseStart_114405 : Nat := 118140960795 + 114405 * 2 ^ 59
def prefixEnd_114405 : Nat := 4983230072969 + 3 ^ 40 * 114405 * 2
def baseEnd_114405 : Nat := 58744754277730123611367

theorem tailTrace_114405 : CollatzResearch.WordTrace tailWord_114405 prefixEnd_114405 58744754277730123611367 := by
  unfold tailWord_114405
  simp only [CollatzResearch.WordTrace]
  refine ⟨4172693150537698663544669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2781795433691799109029779 4172693150537698663544669)
  ·
    refine ⟨1564759931451636998829251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4172693150537698663544669 1564759931451636998829251)
    ·
      refine ⟨2347139897177455498243877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1564759931451636998829251 2347139897177455498243877)
      ·
        refine ⟨440088730720772905920727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2347139897177455498243877 440088730720772905920727)
        ·
          refine ⟨660133096081159358881091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440088730720772905920727 660133096081159358881091)
          ·
            refine ⟨990199644121739038321637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660133096081159358881091 990199644121739038321637)
            ·
              refine ⟨185662433272826069685307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 990199644121739038321637 185662433272826069685307)
              ·
                refine ⟨278493649909239104527961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185662433272826069685307 278493649909239104527961)
                ·
                  refine ⟨208870237431929328395971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 278493649909239104527961 208870237431929328395971)
                  ·
                    refine ⟨313305356147893992593957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 208870237431929328395971 313305356147893992593957)
                    ·
                      refine ⟨58744754277730123611367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 313305356147893992593957 58744754277730123611367)
                      ·
                        rfl

theorem cell23_114405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_114405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114405 prefixEnd_114405 := by exact prefixLift 114405
  have htrace : WordTrace (prefixWord ++ tailWord_114405) baseStart_114405 baseEnd_114405 := by
    simpa [prefixWord, tailWord_114405, baseEnd_114405] using wordTrace_append hprefix tailTrace_114405
  have hstable : (prefixWord ++ tailWord_114405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114405).length < 2 ^ (prefixWord ++ tailWord_114405).sum := by decide
  have hdescent : baseEnd_114405 < baseStart_114405 := by decide
  rcases family_descends (prefixWord ++ tailWord_114405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114411 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 10]
def baseStart_114411 : Nat := 118140960795 + 114411 * 2 ^ 59
def prefixEnd_114411 : Nat := 4983230072969 + 3 ^ 40 * 114411 * 2
def baseEnd_114411 : Nat := 6527537240184122237371

theorem tailTrace_114411 : CollatzResearch.WordTrace tailWord_114411 prefixEnd_114411 6527537240184122237371 := by
  unfold tailWord_114411
  simp only [CollatzResearch.WordTrace]
  refine ⟨4172911988515961688263087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2781941325677307792175391 4172911988515961688263087)
  ·
    refine ⟨6259367982773942532394631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4172911988515961688263087 6259367982773942532394631)
    ·
      refine ⟨9389051974160913798591947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6259367982773942532394631 9389051974160913798591947)
      ·
        refine ⟨14083577961241370697887921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9389051974160913798591947 14083577961241370697887921)
        ·
          refine ⟨10562683470931028023415941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14083577961241370697887921 10562683470931028023415941)
          ·
            refine ⟨1980503150799567754390489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10562683470931028023415941 1980503150799567754390489)
            ·
              refine ⟨1485377363099675815792867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1980503150799567754390489 1485377363099675815792867)
              ·
                refine ⟨2228066044649513723689301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485377363099675815792867 2228066044649513723689301)
                ·
                  refine ⟨6527537240184122237371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 2228066044649513723689301 6527537240184122237371)
                  ·
                    rfl

theorem cell23_114411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 10].length) (baseStart_114411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114411 prefixEnd_114411 := by exact prefixLift 114411
  have htrace : WordTrace (prefixWord ++ tailWord_114411) baseStart_114411 baseEnd_114411 := by
    simpa [prefixWord, tailWord_114411, baseEnd_114411] using wordTrace_append hprefix tailTrace_114411
  have hstable : (prefixWord ++ tailWord_114411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114411).length < 2 ^ (prefixWord ++ tailWord_114411).sum := by decide
  have hdescent : baseEnd_114411 < baseStart_114411 := by decide
  rcases family_descends (prefixWord ++ tailWord_114411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114418 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_114418 : Nat := 118140960795 + 114418 * 2 ^ 59
def prefixEnd_114418 : Nat := 4983230072969 + 3 ^ 40 * 114418 * 2
def baseEnd_114418 : Nat := 58751429526238572748807

theorem tailTrace_114418 : CollatzResearch.WordTrace tailWord_114418 prefixEnd_114418 58751429526238572748807 := by
  unfold tailWord_114418
  simp only [CollatzResearch.WordTrace]
  refine ⟨1043291824872650470941977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2782111532993734589178605 1043291824872650470941977)
  ·
    refine ⟨782468868654487853206483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1043291824872650470941977 782468868654487853206483)
    ·
      refine ⟨1173703302981731779809725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 782468868654487853206483 1173703302981731779809725)
      ·
        refine ⟨440138738618149417428647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1173703302981731779809725 440138738618149417428647)
        ·
          refine ⟨660208107927224126142971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440138738618149417428647 660208107927224126142971)
          ·
            refine ⟨990312161890836189214457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660208107927224126142971 990312161890836189214457)
            ·
              refine ⟨742734121418127141910843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 990312161890836189214457 742734121418127141910843)
              ·
                refine ⟨1114101182127190712866265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742734121418127141910843 1114101182127190712866265)
                ·
                  refine ⟨835575886595393034649699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1114101182127190712866265 835575886595393034649699)
                  ·
                    refine ⟨1253363829893089551974549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 835575886595393034649699 1253363829893089551974549)
                    ·
                      refine ⟨58751429526238572748807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1253363829893089551974549 58751429526238572748807)
                      ·
                        rfl

theorem cell23_114418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_114418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114418 prefixEnd_114418 := by exact prefixLift 114418
  have htrace : WordTrace (prefixWord ++ tailWord_114418) baseStart_114418 baseEnd_114418 := by
    simpa [prefixWord, tailWord_114418, baseEnd_114418] using wordTrace_append hprefix tailTrace_114418
  have hstable : (prefixWord ++ tailWord_114418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114418).length < 2 ^ (prefixWord ++ tailWord_114418).sum := by decide
  have hdescent : baseEnd_114418 < baseStart_114418 := by decide
  rcases family_descends (prefixWord ++ tailWord_114418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114509 : List Nat := [1, 6, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_114509 : Nat := 118140960795 + 114509 * 2 ^ 59
def prefixEnd_114509 : Nat := 4983230072969 + 3 ^ 40 * 114509 * 2
def baseEnd_114509 : Nat := 19599385421932572236963

theorem tailTrace_114509 : CollatzResearch.WordTrace tailWord_114509 prefixEnd_114509 19599385421932572236963 := by
  unfold tailWord_114509
  simp only [CollatzResearch.WordTrace]
  refine ⟨4176486342160924425330581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2784324228107282950220387 4176486342160924425330581)
  ·
    refine ⟨195772797288793332437371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4176486342160924425330581 195772797288793332437371)
    ·
      refine ⟨293659195933189998656057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195772797288793332437371 293659195933189998656057)
      ·
        refine ⟨220244396949892498992043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293659195933189998656057 220244396949892498992043)
        ·
          refine ⟨330366595424838748488065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220244396949892498992043 330366595424838748488065)
          ·
            refine ⟨247774946568629061366049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330366595424838748488065 247774946568629061366049)
            ·
              refine ⟨185831209926471796024537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247774946568629061366049 185831209926471796024537)
              ·
                refine ⟨139373407444853847018403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185831209926471796024537 139373407444853847018403)
                ·
                  refine ⟨209060111167280770527605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139373407444853847018403 209060111167280770527605)
                  ·
                    refine ⟨19599385421932572236963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 209060111167280770527605 19599385421932572236963)
                    ·
                      rfl

theorem cell23_114509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_114509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114509 prefixEnd_114509 := by exact prefixLift 114509
  have htrace : WordTrace (prefixWord ++ tailWord_114509) baseStart_114509 baseEnd_114509 := by
    simpa [prefixWord, tailWord_114509, baseEnd_114509] using wordTrace_append hprefix tailTrace_114509
  have hstable : (prefixWord ++ tailWord_114509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114509).length < 2 ^ (prefixWord ++ tailWord_114509).sum := by decide
  have hdescent : baseEnd_114509 < baseStart_114509 := by decide
  rcases family_descends (prefixWord ++ tailWord_114509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114532 : List Nat := [2, 3, 1, 1, 5, 1, 2, 1, 1, 1, 5]
def baseStart_114532 : Nat := 118140960795 + 114532 * 2 ^ 59
def prefixEnd_114532 : Nat := 4983230072969 + 3 ^ 40 * 114532 * 2
def baseEnd_114532 : Nat := 58809966320851126723283

theorem tailTrace_114532 : CollatzResearch.WordTrace tailWord_114532 prefixEnd_114532 58809966320851126723283 := by
  unfold tailWord_114532
  simp only [CollatzResearch.WordTrace]
  refine ⟨2088662610538799676708925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2784883480718399568945233 2088662610538799676708925)
  ·
    refine ⟨783248478952049878765847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2088662610538799676708925 783248478952049878765847)
    ·
      refine ⟨1174872718428074818148771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 783248478952049878765847 1174872718428074818148771)
      ·
        refine ⟨1762309077642112227223157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1174872718428074818148771 1762309077642112227223157)
        ·
          refine ⟨165216476028948021302171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1762309077642112227223157 165216476028948021302171)
          ·
            refine ⟨247824714043422031953257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165216476028948021302171 247824714043422031953257)
            ·
              refine ⟨185868535532566523964943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247824714043422031953257 185868535532566523964943)
              ·
                refine ⟨278802803298849785947415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185868535532566523964943 278802803298849785947415)
                ·
                  refine ⟨418204204948274678921123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 278802803298849785947415 418204204948274678921123)
                  ·
                    refine ⟨627306307422412018381685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 418204204948274678921123 627306307422412018381685)
                    ·
                      refine ⟨58809966320851126723283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 627306307422412018381685 58809966320851126723283)
                      ·
                        rfl

theorem cell23_114532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_114532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114532 prefixEnd_114532 := by exact prefixLift 114532
  have htrace : WordTrace (prefixWord ++ tailWord_114532) baseStart_114532 baseEnd_114532 := by
    simpa [prefixWord, tailWord_114532, baseEnd_114532] using wordTrace_append hprefix tailTrace_114532
  have hstable : (prefixWord ++ tailWord_114532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114532).length < 2 ^ (prefixWord ++ tailWord_114532).sum := by decide
  have hdescent : baseEnd_114532 < baseStart_114532 := by decide
  rcases family_descends (prefixWord ++ tailWord_114532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114555 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 2, 7, 2]
def baseStart_114555 : Nat := 118140960795 + 114555 * 2 ^ 59
def prefixEnd_114555 : Nat := 4983230072969 + 3 ^ 40 * 114555 * 2
def baseEnd_114555 : Nat := 58821776375904536735677

theorem tailTrace_114555 : CollatzResearch.WordTrace tailWord_114555 prefixEnd_114555 58821776375904536735677 := by
  unfold tailWord_114555
  simp only [CollatzResearch.WordTrace]
  refine ⟨4178164099994274281505119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2785442733329516187670079 4178164099994274281505119)
  ·
    refine ⟨6267246149991411422257679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4178164099994274281505119 6267246149991411422257679)
    ·
      refine ⟨9400869224987117133386519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6267246149991411422257679 9400869224987117133386519)
      ·
        refine ⟨14101303837480675700079779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9400869224987117133386519 14101303837480675700079779)
        ·
          refine ⟨21151955756221013550119669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14101303837480675700079779 21151955756221013550119669)
          ·
            refine ⟨1982995852145720020323719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21151955756221013550119669 1982995852145720020323719)
            ·
              refine ⟨2974493778218580030485579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1982995852145720020323719 2974493778218580030485579)
              ·
                refine ⟨4461740667327870045728369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2974493778218580030485579 4461740667327870045728369)
                ·
                  refine ⟨3346305500495902534296277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4461740667327870045728369 3346305500495902534296277)
                  ·
                    refine ⟨78429035167872715647569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3346305500495902534296277 78429035167872715647569)
                    ·
                      refine ⟨58821776375904536735677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 78429035167872715647569 58821776375904536735677)
                      ·
                        rfl

theorem cell23_114555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 7, 2].length) (baseStart_114555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114555 prefixEnd_114555 := by exact prefixLift 114555
  have htrace : WordTrace (prefixWord ++ tailWord_114555) baseStart_114555 baseEnd_114555 := by
    simpa [prefixWord, tailWord_114555, baseEnd_114555] using wordTrace_append hprefix tailTrace_114555
  have hstable : (prefixWord ++ tailWord_114555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114555).length < 2 ^ (prefixWord ++ tailWord_114555).sum := by decide
  have hdescent : baseEnd_114555 < baseStart_114555 := by decide
  rcases family_descends (prefixWord ++ tailWord_114555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114608 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 13]
def baseStart_114608 : Nat := 118140960795 + 114608 * 2 ^ 59
def prefixEnd_114608 : Nat := 4983230072969 + 3 ^ 40 * 114608 * 2
def baseEnd_114608 : Nat := 6538776761176981041437

theorem tailTrace_114608 : CollatzResearch.WordTrace tailWord_114608 prefixEnd_114608 6538776761176981041437 := by
  unfold tailWord_114608
  simp only [CollatzResearch.WordTrace]
  refine ⟨2090048584401132166592239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2786731445868176222122985 2090048584401132166592239)
  ·
    refine ⟨3135072876601698249888359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2090048584401132166592239 3135072876601698249888359)
    ·
      refine ⟨4702609314902547374832539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3135072876601698249888359 4702609314902547374832539)
      ·
        refine ⟨7053913972353821062248809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4702609314902547374832539 7053913972353821062248809)
        ·
          refine ⟨5290435479265365796686607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7053913972353821062248809 5290435479265365796686607)
          ·
            refine ⟨7935653218898048695029911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5290435479265365796686607 7935653218898048695029911)
            ·
              refine ⟨11903479828347073042544867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7935653218898048695029911 11903479828347073042544867)
              ·
                refine ⟨17855219742520609563817301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11903479828347073042544867 17855219742520609563817301)
                ·
                  refine ⟨6538776761176981041437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 17855219742520609563817301 6538776761176981041437)
                  ·
                    rfl

theorem cell23_114608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 13].length) (baseStart_114608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114608 prefixEnd_114608 := by exact prefixLift 114608
  have htrace : WordTrace (prefixWord ++ tailWord_114608) baseStart_114608 baseEnd_114608 := by
    simpa [prefixWord, tailWord_114608, baseEnd_114608] using wordTrace_append hprefix tailTrace_114608
  have hstable : (prefixWord ++ tailWord_114608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114608).length < 2 ^ (prefixWord ++ tailWord_114608).sum := by decide
  have hdescent : baseEnd_114608 < baseStart_114608 := by decide
  rcases family_descends (prefixWord ++ tailWord_114608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114635 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 3]
def baseStart_114635 : Nat := 118140960795 + 114635 * 2 ^ 59
def prefixEnd_114635 : Nat := 4983230072969 + 3 ^ 40 * 114635 * 2
def baseEnd_114635 : Nat := 58862854828264223735309

theorem tailTrace_114635 : CollatzResearch.WordTrace tailWord_114635 prefixEnd_114635 58862854828264223735309 := by
  unfold tailWord_114635
  simp only [CollatzResearch.WordTrace]
  refine ⟨4181081939704447944417359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2787387959802965296278239 4181081939704447944417359)
  ·
    refine ⟨6271622909556671916626039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4181081939704447944417359 6271622909556671916626039)
    ·
      refine ⟨9407434364335007874939059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6271622909556671916626039 9407434364335007874939059)
      ·
        refine ⟨14111151546502511812408589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9407434364335007874939059 14111151546502511812408589)
        ·
          refine ⟨5291681829938441929653221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14111151546502511812408589 5291681829938441929653221)
          ·
            refine ⟨992190343113457861809979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5291681829938441929653221 992190343113457861809979)
            ·
              refine ⟨1488285514670186792714969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 992190343113457861809979 1488285514670186792714969)
              ·
                refine ⟨1116214136002640094536227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1488285514670186792714969 1116214136002640094536227)
                ·
                  refine ⟨1674321204003960141804341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1116214136002640094536227 1674321204003960141804341)
                  ·
                    refine ⟨156967612875371263294157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1674321204003960141804341 156967612875371263294157)
                    ·
                      refine ⟨58862854828264223735309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 156967612875371263294157 58862854828264223735309)
                      ·
                        rfl

theorem cell23_114635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 3].length) (baseStart_114635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114635 prefixEnd_114635 := by exact prefixLift 114635
  have htrace : WordTrace (prefixWord ++ tailWord_114635) baseStart_114635 baseEnd_114635 := by
    simpa [prefixWord, tailWord_114635, baseEnd_114635] using wordTrace_append hprefix tailTrace_114635
  have hstable : (prefixWord ++ tailWord_114635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114635).length < 2 ^ (prefixWord ++ tailWord_114635).sum := by decide
  have hdescent : baseEnd_114635 < baseStart_114635 := by decide
  rcases family_descends (prefixWord ++ tailWord_114635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114709 : List Nat := [1, 3, 2, 1, 5, 1, 1, 2, 2, 1, 4]
def baseStart_114709 : Nat := 118140960795 + 114709 * 2 ^ 59
def prefixEnd_114709 : Nat := 4983230072969 + 3 ^ 40 * 114709 * 2
def baseEnd_114709 : Nat := 58900852396696934209969

theorem tailTrace_114709 : CollatzResearch.WordTrace tailWord_114709 prefixEnd_114709 58900852396696934209969 := by
  unfold tailWord_114709
  simp only [CollatzResearch.WordTrace]
  refine ⟨4183780941436358582611181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2789187294290905721740787 4183780941436358582611181)
  ·
    refine ⟨1568917853038634468479193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4183780941436358582611181 1568917853038634468479193)
    ·
      refine ⟨1176688389778975851359395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1568917853038634468479193 1176688389778975851359395)
      ·
        refine ⟨1765032584668463777039093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1176688389778975851359395 1765032584668463777039093)
        ·
          refine ⟨165471804812668479097415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1765032584668463777039093 165471804812668479097415)
          ·
            refine ⟨248207707219002718646123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165471804812668479097415 248207707219002718646123)
            ·
              refine ⟨372311560828504077969185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248207707219002718646123 372311560828504077969185)
              ·
                refine ⟨279233670621378058476889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372311560828504077969185 279233670621378058476889)
                ·
                  refine ⟨209425252966033543857667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279233670621378058476889 209425252966033543857667)
                  ·
                    refine ⟨314137879449050315786501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 209425252966033543857667 314137879449050315786501)
                    ·
                      refine ⟨58900852396696934209969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 314137879449050315786501 58900852396696934209969)
                      ·
                        rfl

theorem cell23_114709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_114709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114709 prefixEnd_114709 := by exact prefixLift 114709
  have htrace : WordTrace (prefixWord ++ tailWord_114709) baseStart_114709 baseEnd_114709 := by
    simpa [prefixWord, tailWord_114709, baseEnd_114709] using wordTrace_append hprefix tailTrace_114709
  have hstable : (prefixWord ++ tailWord_114709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114709).length < 2 ^ (prefixWord ++ tailWord_114709).sum := by decide
  have hdescent : baseEnd_114709 < baseStart_114709 := by decide
  rcases family_descends (prefixWord ++ tailWord_114709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114755 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 5]
def baseStart_114755 : Nat := 118140960795 + 114755 * 2 ^ 59
def prefixEnd_114755 : Nat := 4983230072969 + 3 ^ 40 * 114755 * 2
def baseEnd_114755 : Nat := 58924472506803754234757

theorem tailTrace_114755 : CollatzResearch.WordTrace tailWord_114755 prefixEnd_114755 58924472506803754234757 := by
  unfold tailWord_114755
  simp only [CollatzResearch.WordTrace]
  refine ⟨4185458699269708438785719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2790305799513138959190479 4185458699269708438785719)
  ·
    refine ⟨6278188048904562658178579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4185458699269708438785719 6278188048904562658178579)
    ·
      refine ⟨9417282073356843987267869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6278188048904562658178579 9417282073356843987267869)
      ·
        refine ⟨3531480777508816495225451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9417282073356843987267869 3531480777508816495225451)
        ·
          refine ⟨5297221166263224742838177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3531480777508816495225451 5297221166263224742838177)
          ·
            refine ⟨3972915874697418557128633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5297221166263224742838177 3972915874697418557128633)
            ·
              refine ⟨2979686906023063917846475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3972915874697418557128633 2979686906023063917846475)
              ·
                refine ⟨4469530359034595876769713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2979686906023063917846475 4469530359034595876769713)
                ·
                  refine ⟨3352147769275946907577285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4469530359034595876769713 3352147769275946907577285)
                  ·
                    refine ⟨628527706739240045170741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3352147769275946907577285 628527706739240045170741)
                    ·
                      refine ⟨58924472506803754234757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 628527706739240045170741 58924472506803754234757)
                      ·
                        rfl

theorem cell23_114755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_114755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114755 prefixEnd_114755 := by exact prefixLift 114755
  have htrace : WordTrace (prefixWord ++ tailWord_114755) baseStart_114755 baseEnd_114755 := by
    simpa [prefixWord, tailWord_114755, baseEnd_114755] using wordTrace_append hprefix tailTrace_114755
  have hstable : (prefixWord ++ tailWord_114755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114755).length < 2 ^ (prefixWord ++ tailWord_114755).sum := by decide
  have hdescent : baseEnd_114755 < baseStart_114755 := by decide
  rcases family_descends (prefixWord ++ tailWord_114755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114770 : List Nat := [3, 2, 2, 1, 4, 2, 2, 2, 1, 4]
def baseStart_114770 : Nat := 118140960795 + 114770 * 2 ^ 59
def prefixEnd_114770 : Nat := 4983230072969 + 3 ^ 40 * 114770 * 2
def baseEnd_114770 : Nat := 19644058238873731849063

theorem tailTrace_114770 : CollatzResearch.WordTrace tailWord_114770 prefixEnd_114770 19644058238873731849063 := by
  unfold tailWord_114770
  simp only [CollatzResearch.WordTrace]
  refine ⟨1046501448553841500145441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2790670529476910667054509 1046501448553841500145441)
  ·
    refine ⟨784876086415381125109081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1046501448553841500145441 784876086415381125109081)
    ·
      refine ⟨588657064811535843831811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 784876086415381125109081 588657064811535843831811)
      ·
        refine ⟨882985597217303765747717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588657064811535843831811 882985597217303765747717)
        ·
          refine ⟨165559799478244456077697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 882985597217303765747717 165559799478244456077697)
          ·
            refine ⟨124169849608683342058273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165559799478244456077697 124169849608683342058273)
            ·
              refine ⟨93127387206512506543705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124169849608683342058273 93127387206512506543705)
              ·
                refine ⟨69845540404884379907779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93127387206512506543705 69845540404884379907779)
                ·
                  refine ⟨104768310607326569861669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69845540404884379907779 104768310607326569861669)
                  ·
                    refine ⟨19644058238873731849063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104768310607326569861669 19644058238873731849063)
                    ·
                      rfl

theorem cell23_114770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_114770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114770 prefixEnd_114770 := by exact prefixLift 114770
  have htrace : WordTrace (prefixWord ++ tailWord_114770) baseStart_114770 baseEnd_114770 := by
    simpa [prefixWord, tailWord_114770, baseEnd_114770] using wordTrace_append hprefix tailTrace_114770
  have hstable : (prefixWord ++ tailWord_114770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114770).length < 2 ^ (prefixWord ++ tailWord_114770).sum := by decide
  have hdescent : baseEnd_114770 < baseStart_114770 := by decide
  rcases family_descends (prefixWord ++ tailWord_114770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114826 : List Nat := [3, 1, 2, 3, 1, 2, 3, 2, 2, 4]
def baseStart_114826 : Nat := 118140960795 + 114826 * 2 ^ 59
def prefixEnd_114826 : Nat := 4983230072969 + 3 ^ 40 * 114826 * 2
def baseEnd_114826 : Nat := 19653643211090992148977

theorem tailTrace_114826 : CollatzResearch.WordTrace tailWord_114826 prefixEnd_114826 19653643211090992148977 := by
  unfold tailWord_114826
  simp only [CollatzResearch.WordTrace]
  refine ⟨1047012070503121891155083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2792032188008325043080221 1047012070503121891155083)
  ·
    refine ⟨1570518105754682836732625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1047012070503121891155083 1570518105754682836732625)
    ·
      refine ⟨1177888579316012127549469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1570518105754682836732625 1177888579316012127549469)
      ·
        refine ⟨441708217243504547831051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1177888579316012127549469 441708217243504547831051)
        ·
          refine ⟨662562325865256821746577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441708217243504547831051 662562325865256821746577)
          ·
            refine ⟨496921744398942616309933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 662562325865256821746577 496921744398942616309933)
            ·
              refine ⟨186345654149603481116225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 496921744398942616309933 186345654149603481116225)
              ·
                refine ⟨139759240612202610837169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186345654149603481116225 139759240612202610837169)
                ·
                  refine ⟨104819430459151958127877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139759240612202610837169 104819430459151958127877)
                  ·
                    refine ⟨19653643211090992148977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104819430459151958127877 19653643211090992148977)
                    ·
                      rfl

theorem cell23_114826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_114826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114826 prefixEnd_114826 := by exact prefixLift 114826
  have htrace : WordTrace (prefixWord ++ tailWord_114826) baseStart_114826 baseEnd_114826 := by
    simpa [prefixWord, tailWord_114826, baseEnd_114826] using wordTrace_append hprefix tailTrace_114826
  have hstable : (prefixWord ++ tailWord_114826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114826).length < 2 ^ (prefixWord ++ tailWord_114826).sum := by decide
  have hdescent : baseEnd_114826 < baseStart_114826 := by decide
  rcases family_descends (prefixWord ++ tailWord_114826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114846 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_114846 : Nat := 118140960795 + 114846 * 2 ^ 59
def prefixEnd_114846 : Nat := 4983230072969 + 3 ^ 40 * 114846 * 2
def baseEnd_114846 : Nat := 58971199246362898196839

theorem tailTrace_114846 : CollatzResearch.WordTrace tailWord_114846 prefixEnd_114846 58971199246362898196839 := by
  unfold tailWord_114846
  simp only [CollatzResearch.WordTrace]
  refine ⟨523597217742503872543549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2792518494626687320232261 523597217742503872543549)
  ·
    refine ⟨196348956653438952203831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 523597217742503872543549 196348956653438952203831)
    ·
      refine ⟨294523434980158428305747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196348956653438952203831 294523434980158428305747)
      ·
        refine ⟨441785152470237642458621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294523434980158428305747 441785152470237642458621)
        ·
          refine ⟨165669432176339115921983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 441785152470237642458621 165669432176339115921983)
          ·
            refine ⟨248504148264508673882975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165669432176339115921983 248504148264508673882975)
            ·
              refine ⟨372756222396763010824463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248504148264508673882975 372756222396763010824463)
              ·
                refine ⟨559134333595144516236695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372756222396763010824463 559134333595144516236695)
                ·
                  refine ⟨838701500392716774355043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 559134333595144516236695 838701500392716774355043)
                  ·
                    refine ⟨1258052250589075161532565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 838701500392716774355043 1258052250589075161532565)
                    ·
                      refine ⟨58971199246362898196839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1258052250589075161532565 58971199246362898196839)
                      ·
                        rfl

theorem cell23_114846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_114846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114846 prefixEnd_114846 := by exact prefixLift 114846
  have htrace : WordTrace (prefixWord ++ tailWord_114846) baseStart_114846 baseEnd_114846 := by
    simpa [prefixWord, tailWord_114846, baseEnd_114846] using wordTrace_append hprefix tailTrace_114846
  have hstable : (prefixWord ++ tailWord_114846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114846).length < 2 ^ (prefixWord ++ tailWord_114846).sum := by decide
  have hdescent : baseEnd_114846 < baseStart_114846 := by decide
  rcases family_descends (prefixWord ++ tailWord_114846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114859 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 9, 3, 2]
def baseStart_114859 : Nat := 118140960795 + 114859 * 2 ^ 59
def prefixEnd_114859 : Nat := 4983230072969 + 3 ^ 40 * 114859 * 2
def baseEnd_114859 : Nat := 58977874494871347334279

theorem tailTrace_114859 : CollatzResearch.WordTrace tailWord_114859 prefixEnd_114859 58977874494871347334279 := by
  unfold tailWord_114859
  simp only [CollatzResearch.WordTrace]
  refine ⟨4189251890892934200571631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2792834593928622800381087 4189251890892934200571631)
  ·
    refine ⟨6283877836339401300857447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4189251890892934200571631 6283877836339401300857447)
    ·
      refine ⟨9425816754509101951286171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6283877836339401300857447 9425816754509101951286171)
      ·
        refine ⟨14138725131763652926929257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9425816754509101951286171 14138725131763652926929257)
        ·
          refine ⟨10604043848822739695196943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14138725131763652926929257 10604043848822739695196943)
          ·
            refine ⟨15906065773234109542795415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10604043848822739695196943 15906065773234109542795415)
            ·
              refine ⟨23859098659851164314193123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15906065773234109542795415 23859098659851164314193123)
              ·
                refine ⟨35788647989776746471289685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23859098659851164314193123 35788647989776746471289685)
                ·
                  refine ⟨209699109315098123855213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35788647989776746471289685 209699109315098123855213)
                  ·
                    refine ⟨78637165993161796445705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 209699109315098123855213 78637165993161796445705)
                    ·
                      refine ⟨58977874494871347334279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 78637165993161796445705 58977874494871347334279)
                      ·
                        rfl

theorem cell23_114859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 3, 2].length) (baseStart_114859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114859 prefixEnd_114859 := by exact prefixLift 114859
  have htrace : WordTrace (prefixWord ++ tailWord_114859) baseStart_114859 baseEnd_114859 := by
    simpa [prefixWord, tailWord_114859, baseEnd_114859] using wordTrace_append hprefix tailTrace_114859
  have hstable : (prefixWord ++ tailWord_114859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114859).length < 2 ^ (prefixWord ++ tailWord_114859).sum := by decide
  have hdescent : baseEnd_114859 < baseStart_114859 := by decide
  rcases family_descends (prefixWord ++ tailWord_114859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114889 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 5, 4, 2]
def baseStart_114889 : Nat := 118140960795 + 114889 * 2 ^ 59
def prefixEnd_114889 : Nat := 4983230072969 + 3 ^ 40 * 114889 * 2
def baseEnd_114889 : Nat := 58993278914506229959141

theorem tailTrace_114889 : CollatzResearch.WordTrace tailWord_114889 prefixEnd_114889 58993278914506229959141 := by
  unfold tailWord_114889
  simp only [CollatzResearch.WordTrace]
  refine ⟨4190346080784249324163721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2793564053856166216109147 4190346080784249324163721)
  ·
    refine ⟨3142759560588186993122791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4190346080784249324163721 3142759560588186993122791)
    ·
      refine ⟨4714139340882280489684187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3142759560588186993122791 4714139340882280489684187)
      ·
        refine ⟨7071209011323420734526281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4714139340882280489684187 7071209011323420734526281)
        ·
          refine ⟨5303406758492565550894711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7071209011323420734526281 5303406758492565550894711)
          ·
            refine ⟨7955110137738848326342067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5303406758492565550894711 7955110137738848326342067)
            ·
              refine ⟨11932665206608272489513101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7955110137738848326342067 11932665206608272489513101)
              ·
                refine ⟨4474749452478102183567413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11932665206608272489513101 4474749452478102183567413)
                ·
                  refine ⟨419507761169822079709445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4474749452478102183567413 419507761169822079709445)
                  ·
                    refine ⟨78657705219341639945521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 419507761169822079709445 78657705219341639945521)
                    ·
                      refine ⟨58993278914506229959141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 78657705219341639945521 58993278914506229959141)
                      ·
                        rfl

theorem cell23_114889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 4, 2].length) (baseStart_114889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114889 prefixEnd_114889 := by exact prefixLift 114889
  have htrace : WordTrace (prefixWord ++ tailWord_114889) baseStart_114889 baseEnd_114889 := by
    simpa [prefixWord, tailWord_114889, baseEnd_114889] using wordTrace_append hprefix tailTrace_114889
  have hstable : (prefixWord ++ tailWord_114889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114889).length < 2 ^ (prefixWord ++ tailWord_114889).sum := by decide
  have hdescent : baseEnd_114889 < baseStart_114889 := by decide
  rcases family_descends (prefixWord ++ tailWord_114889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114912 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 9]
def baseStart_114912 : Nat := 118140960795 + 114912 * 2 ^ 59
def prefixEnd_114912 : Nat := 4983230072969 + 3 ^ 40 * 114912 * 2
def baseEnd_114912 : Nat := 6556120996617737774615

theorem tailTrace_114912 : CollatzResearch.WordTrace tailWord_114912 prefixEnd_114912 6556120996617737774615 := by
  unfold tailWord_114912
  simp only [CollatzResearch.WordTrace]
  refine ⟨2095592479850462126125495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2794123306467282834833993 2095592479850462126125495)
  ·
    refine ⟨3143388719775693189188243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2095592479850462126125495 3143388719775693189188243)
    ·
      refine ⟨4715083079663539783782365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3143388719775693189188243 4715083079663539783782365)
      ·
        refine ⟨1768156154873827418918387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4715083079663539783782365 1768156154873827418918387)
        ·
          refine ⟨2652234232310741128377581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1768156154873827418918387 2652234232310741128377581)
          ·
            refine ⟨994587837116527923141593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2652234232310741128377581 994587837116527923141593)
            ·
              refine ⟨745940877837395942356195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 994587837116527923141593 745940877837395942356195)
              ·
                refine ⟨1118911316756093913534293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745940877837395942356195 1118911316756093913534293)
                ·
                  refine ⟨6556120996617737774615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1118911316756093913534293 6556120996617737774615)
                  ·
                    rfl

theorem cell23_114912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 9].length) (baseStart_114912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114912 prefixEnd_114912 := by exact prefixLift 114912
  have htrace : WordTrace (prefixWord ++ tailWord_114912) baseStart_114912 baseEnd_114912 := by
    simpa [prefixWord, tailWord_114912, baseEnd_114912] using wordTrace_append hprefix tailTrace_114912
  have hstable : (prefixWord ++ tailWord_114912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114912).length < 2 ^ (prefixWord ++ tailWord_114912).sum := by decide
  have hdescent : baseEnd_114912 < baseStart_114912 := by decide
  rcases family_descends (prefixWord ++ tailWord_114912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114940 : List Nat := [2, 2, 2, 1, 4, 2, 2, 2, 2, 2, 2]
def baseStart_114940 : Nat := 118140960795 + 114940 * 2 ^ 59
def prefixEnd_114940 : Nat := 4983230072969 + 3 ^ 40 * 114940 * 2
def baseEnd_114940 : Nat := 59019466427885530421407

theorem tailTrace_114940 : CollatzResearch.WordTrace tailWord_114940 prefixEnd_114940 59019466427885530421407 := by
  unfold tailWord_114940
  simp only [CollatzResearch.WordTrace]
  refine ⟨2096103101799742517135137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2794804135732990022846849 2096103101799742517135137)
  ·
    refine ⟨1572077326349806887851353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2096103101799742517135137 1572077326349806887851353)
    ·
      refine ⟨1179057994762355165888515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1572077326349806887851353 1179057994762355165888515)
      ·
        refine ⟨1768586992143532748832773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1179057994762355165888515 1768586992143532748832773)
        ·
          refine ⟨331610061026912390406145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1768586992143532748832773 331610061026912390406145)
          ·
            refine ⟨248707545770184292804609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331610061026912390406145 248707545770184292804609)
            ·
              refine ⟨186530659327638219603457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248707545770184292804609 186530659327638219603457)
              ·
                refine ⟨139897994495728664702593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186530659327638219603457 139897994495728664702593)
                ·
                  refine ⟨104923495871796498526945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139897994495728664702593 104923495871796498526945)
                  ·
                    refine ⟨78692621903847373895209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104923495871796498526945 78692621903847373895209)
                    ·
                      refine ⟨59019466427885530421407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 78692621903847373895209 59019466427885530421407)
                      ·
                        rfl

theorem cell23_114940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_114940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114940 prefixEnd_114940 := by exact prefixLift 114940
  have htrace : WordTrace (prefixWord ++ tailWord_114940) baseStart_114940 baseEnd_114940 := by
    simpa [prefixWord, tailWord_114940, baseEnd_114940] using wordTrace_append hprefix tailTrace_114940
  have hstable : (prefixWord ++ tailWord_114940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114940).length < 2 ^ (prefixWord ++ tailWord_114940).sum := by decide
  have hdescent : baseEnd_114940 < baseStart_114940 := by decide
  rcases family_descends (prefixWord ++ tailWord_114940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114976 : List Nat := [2, 1, 1, 5, 2, 1, 3, 1, 2, 5]
def baseStart_114976 : Nat := 118140960795 + 114976 * 2 ^ 59
def prefixEnd_114976 : Nat := 4983230072969 + 3 ^ 40 * 114976 * 2
def baseEnd_114976 : Nat := 19679317243815796523747

theorem tailTrace_114976 : CollatzResearch.WordTrace tailWord_114976 prefixEnd_114976 19679317243815796523747 := by
  unfold tailWord_114976
  simp only [CollatzResearch.WordTrace]
  refine ⟨2096759615734531591290391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2795679487646042121720521 2096759615734531591290391)
  ·
    refine ⟨3145139423601797386935587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2096759615734531591290391 3145139423601797386935587)
    ·
      refine ⟨4717709135402696080403381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3145139423601797386935587 4717709135402696080403381)
      ·
        refine ⟨442285231444002757537817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4717709135402696080403381 442285231444002757537817)
        ·
          refine ⟨331713923583002068153363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442285231444002757537817 331713923583002068153363)
          ·
            refine ⟨497570885374503102230045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331713923583002068153363 497570885374503102230045)
            ·
              refine ⟨186589082015438663336267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 497570885374503102230045 186589082015438663336267)
              ·
                refine ⟨279883623023157995004401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186589082015438663336267 279883623023157995004401)
                ·
                  refine ⟨209912717267368496253301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279883623023157995004401 209912717267368496253301)
                  ·
                    refine ⟨19679317243815796523747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 209912717267368496253301 19679317243815796523747)
                    ·
                      rfl

theorem cell23_114976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 2, 5].length) (baseStart_114976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114976 prefixEnd_114976 := by exact prefixLift 114976
  have htrace : WordTrace (prefixWord ++ tailWord_114976) baseStart_114976 baseEnd_114976 := by
    simpa [prefixWord, tailWord_114976, baseEnd_114976] using wordTrace_append hprefix tailTrace_114976
  have hstable : (prefixWord ++ tailWord_114976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114976).length < 2 ^ (prefixWord ++ tailWord_114976).sum := by decide
  have hdescent : baseEnd_114976 < baseStart_114976 := by decide
  rcases family_descends (prefixWord ++ tailWord_114976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114979 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 4]
def baseStart_114979 : Nat := 118140960795 + 114979 * 2 ^ 59
def prefixEnd_114979 : Nat := 4983230072969 + 3 ^ 40 * 114979 * 2
def baseEnd_114979 : Nat := 59039492173410877833727

theorem tailTrace_114979 : CollatzResearch.WordTrace tailWord_114979 prefixEnd_114979 59039492173410877833727 := by
  unfold tailWord_114979
  simp only [CollatzResearch.WordTrace]
  refine ⟨4193628650458194694939991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2795752433638796463293327 4193628650458194694939991)
  ·
    refine ⟨6290442975687292042409987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4193628650458194694939991 6290442975687292042409987)
    ·
      refine ⟨9435664463530938063614981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6290442975687292042409987 9435664463530938063614981)
      ·
        refine ⟨1769187086912050886927809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9435664463530938063614981 1769187086912050886927809)
        ·
          refine ⟨1326890315184038165195857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1769187086912050886927809 1326890315184038165195857)
          ·
            refine ⟨995167736388028623896893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1326890315184038165195857 995167736388028623896893)
            ·
              refine ⟨373187901145510733961335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 995167736388028623896893 373187901145510733961335)
              ·
                refine ⟨559781851718266100942003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373187901145510733961335 559781851718266100942003)
                ·
                  refine ⟨839672777577399151413005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 559781851718266100942003 839672777577399151413005)
                  ·
                    refine ⟨314877291591524681779877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 839672777577399151413005 314877291591524681779877)
                    ·
                      refine ⟨59039492173410877833727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 314877291591524681779877 59039492173410877833727)
                      ·
                        rfl

theorem cell23_114979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_114979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_114979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_114979 prefixEnd_114979 := by exact prefixLift 114979
  have htrace : WordTrace (prefixWord ++ tailWord_114979) baseStart_114979 baseEnd_114979 := by
    simpa [prefixWord, tailWord_114979, baseEnd_114979] using wordTrace_append hprefix tailTrace_114979
  have hstable : (prefixWord ++ tailWord_114979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114979).length < 2 ^ (prefixWord ++ tailWord_114979).sum := by decide
  have hdescent : baseEnd_114979 < baseStart_114979 := by decide
  rcases family_descends (prefixWord ++ tailWord_114979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115083 : List Nat := [1, 1, 1, 1, 4, 6, 1, 2, 1, 5]
def baseStart_115083 : Nat := 118140960795 + 115083 * 2 ^ 59
def prefixEnd_115083 : Nat := 4983230072969 + 3 ^ 40 * 115083 * 2
def baseEnd_115083 : Nat := 19697631387159490311083

theorem tailTrace_115083 : CollatzResearch.WordTrace tailWord_115083 prefixEnd_115083 19697631387159490311083 := by
  unfold tailWord_115083
  simp only [CollatzResearch.WordTrace]
  refine ⟨4197421842081420456725903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2798281228054280304483935 4197421842081420456725903)
  ·
    refine ⟨6296132763122130685088855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4197421842081420456725903 6296132763122130685088855)
    ·
      refine ⟨9444199144683196027633283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6296132763122130685088855 9444199144683196027633283)
      ·
        refine ⟨14166298717024794041449925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9444199144683196027633283 14166298717024794041449925)
        ·
          refine ⟨2656181009442148882771861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14166298717024794041449925 2656181009442148882771861)
          ·
            refine ⟨124508484817600728879931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2656181009442148882771861 124508484817600728879931)
            ·
              refine ⟨186762727226401093319897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124508484817600728879931 186762727226401093319897)
              ·
                refine ⟨140072045419800819989923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186762727226401093319897 140072045419800819989923)
                ·
                  refine ⟨210108068129701229984885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140072045419800819989923 210108068129701229984885)
                  ·
                    refine ⟨19697631387159490311083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 210108068129701229984885 19697631387159490311083)
                    ·
                      rfl

theorem cell23_115083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 5].length) (baseStart_115083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115083 prefixEnd_115083 := by exact prefixLift 115083
  have htrace : WordTrace (prefixWord ++ tailWord_115083) baseStart_115083 baseEnd_115083 := by
    simpa [prefixWord, tailWord_115083, baseEnd_115083] using wordTrace_append hprefix tailTrace_115083
  have hstable : (prefixWord ++ tailWord_115083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115083).length < 2 ^ (prefixWord ++ tailWord_115083).sum := by decide
  have hdescent : baseEnd_115083 < baseStart_115083 := by decide
  rcases family_descends (prefixWord ++ tailWord_115083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115096 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 3, 6]
def baseStart_115096 : Nat := 118140960795 + 115096 * 2 ^ 59
def prefixEnd_115096 : Nat := 4983230072969 + 3 ^ 40 * 115096 * 2
def baseEnd_115096 : Nat := 19699856469995640023563

theorem tailTrace_115096 : CollatzResearch.WordTrace tailWord_115096 prefixEnd_115096 19699856469995640023563 := by
  unfold tailWord_115096
  simp only [CollatzResearch.WordTrace]
  refine ⟨2098947995517161838474571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2798597327356215784632761 2098947995517161838474571)
  ·
    refine ⟨3148421993275742757711857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2098947995517161838474571 3148421993275742757711857)
    ·
      refine ⟨2361316494956807068283893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3148421993275742757711857 2361316494956807068283893)
      ·
        refine ⟨221373421402200662651615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2361316494956807068283893 221373421402200662651615)
        ·
          refine ⟨332060132103300993977423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221373421402200662651615 332060132103300993977423)
          ·
            refine ⟨498090198154951490966135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332060132103300993977423 498090198154951490966135)
            ·
              refine ⟨747135297232427236449203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498090198154951490966135 747135297232427236449203)
              ·
                refine ⟨1120702945848640854673805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747135297232427236449203 1120702945848640854673805)
                ·
                  refine ⟨420263604693240320502677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1120702945848640854673805 420263604693240320502677)
                  ·
                    refine ⟨19699856469995640023563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 420263604693240320502677 19699856469995640023563)
                    ·
                      rfl

theorem cell23_115096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_115096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115096 prefixEnd_115096 := by exact prefixLift 115096
  have htrace : WordTrace (prefixWord ++ tailWord_115096) baseStart_115096 baseEnd_115096 := by
    simpa [prefixWord, tailWord_115096, baseEnd_115096] using wordTrace_append hprefix tailTrace_115096
  have hstable : (prefixWord ++ tailWord_115096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115096).length < 2 ^ (prefixWord ++ tailWord_115096).sum := by decide
  have hdescent : baseEnd_115096 < baseStart_115096 := by decide
  rcases family_descends (prefixWord ++ tailWord_115096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115133 : List Nat := [1, 4, 1, 2, 2, 3, 2, 1, 1, 2, 4]
def baseStart_115133 : Nat := 118140960795 + 115133 * 2 ^ 59
def prefixEnd_115133 : Nat := 4983230072969 + 3 ^ 40 * 115133 * 2
def baseEnd_115133 : Nat := 59118568194203275308019

theorem tailTrace_115133 : CollatzResearch.WordTrace tailWord_115133 prefixEnd_115133 59118568194203275308019 := by
  unfold tailWord_115133
  simp only [CollatzResearch.WordTrace]
  refine ⟨4199245491900278996046053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2799496994600185997364035 4199245491900278996046053)
  ·
    refine ⟨787358529731302311758635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4199245491900278996046053 787358529731302311758635)
    ·
      refine ⟨1181037794596953467637953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 787358529731302311758635 1181037794596953467637953)
      ·
        refine ⟨885778345947715100728465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1181037794596953467637953 885778345947715100728465)
        ·
          refine ⟨664333759460786325546349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 885778345947715100728465 664333759460786325546349)
          ·
            refine ⟨249125159797794872079881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 664333759460786325546349 249125159797794872079881)
            ·
              refine ⟨186843869848346154059911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249125159797794872079881 186843869848346154059911)
              ·
                refine ⟨280265804772519231089867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186843869848346154059911 280265804772519231089867)
                ·
                  refine ⟨420398707158778846634801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280265804772519231089867 420398707158778846634801)
                  ·
                    refine ⟨315299030369084134976101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 420398707158778846634801 315299030369084134976101)
                    ·
                      refine ⟨59118568194203275308019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 315299030369084134976101 59118568194203275308019)
                      ·
                        rfl

theorem cell23_115133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_115133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115133 prefixEnd_115133 := by exact prefixLift 115133
  have htrace : WordTrace (prefixWord ++ tailWord_115133) baseStart_115133 baseEnd_115133 := by
    simpa [prefixWord, tailWord_115133, baseEnd_115133] using wordTrace_append hprefix tailTrace_115133
  have hstable : (prefixWord ++ tailWord_115133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115133).length < 2 ^ (prefixWord ++ tailWord_115133).sum := by decide
  have hdescent : baseEnd_115133 < baseStart_115133 := by decide
  rcases family_descends (prefixWord ++ tailWord_115133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115139 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 4, 7]
def baseStart_115139 : Nat := 118140960795 + 115139 * 2 ^ 59
def prefixEnd_115139 : Nat := 4983230072969 + 3 ^ 40 * 115139 * 2
def baseEnd_115139 : Nat := 19707216359376750610997

theorem tailTrace_115139 : CollatzResearch.WordTrace tailWord_115139 prefixEnd_115139 19707216359376750610997 := by
  unfold tailWord_115139
  simp only [CollatzResearch.WordTrace]
  refine ⟨4199464329878542020764471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2799642886585694680509647 4199464329878542020764471)
  ·
    refine ⟨6299196494817813031146707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4199464329878542020764471 6299196494817813031146707)
    ·
      refine ⟨9448794742226719546720061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6299196494817813031146707 9448794742226719546720061)
      ·
        refine ⟨3543298028335019830020023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9448794742226719546720061 3543298028335019830020023)
        ·
          refine ⟨5314947042502529745030035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3543298028335019830020023 5314947042502529745030035)
          ·
            refine ⟨7972420563753794617545053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5314947042502529745030035 7972420563753794617545053)
            ·
              refine ⟨2989657711407672981579395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7972420563753794617545053 2989657711407672981579395)
              ·
                refine ⟨4484486567111509472369093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2989657711407672981579395 4484486567111509472369093)
                ·
                  refine ⟨840841231333408026069205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4484486567111509472369093 840841231333408026069205)
                  ·
                    refine ⟨19707216359376750610997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 840841231333408026069205 19707216359376750610997)
                    ·
                      rfl

theorem cell23_115139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 7].length) (baseStart_115139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115139 prefixEnd_115139 := by exact prefixLift 115139
  have htrace : WordTrace (prefixWord ++ tailWord_115139) baseStart_115139 baseEnd_115139 := by
    simpa [prefixWord, tailWord_115139, baseEnd_115139] using wordTrace_append hprefix tailTrace_115139
  have hstable : (prefixWord ++ tailWord_115139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115139).length < 2 ^ (prefixWord ++ tailWord_115139).sum := by decide
  have hdescent : baseEnd_115139 < baseStart_115139 := by decide
  rcases family_descends (prefixWord ++ tailWord_115139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115154 : List Nat := [3, 2, 2, 4, 1, 2, 2, 1, 1, 1, 4]
def baseStart_115154 : Nat := 118140960795 + 115154 * 2 ^ 59
def prefixEnd_115154 : Nat := 4983230072969 + 3 ^ 40 * 115154 * 2
def baseEnd_115154 : Nat := 59129351287947693145423

theorem tailTrace_115154 : CollatzResearch.WordTrace tailWord_115154 prefixEnd_115154 59129351287947693145423 := by
  unfold tailWord_115154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1050002856206049895640129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2800007616549466388373677 1050002856206049895640129)
  ·
    refine ⟨787502142154537421730097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1050002856206049895640129 787502142154537421730097)
    ·
      refine ⟨590626606615903066297573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 787502142154537421730097 590626606615903066297573)
      ·
        refine ⟨110742488740481824930795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 590626606615903066297573 110742488740481824930795)
        ·
          refine ⟨166113733110722737396193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110742488740481824930795 166113733110722737396193)
          ·
            refine ⟨124585299833042053047145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166113733110722737396193 124585299833042053047145)
            ·
              refine ⟨93438974874781539785359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124585299833042053047145 93438974874781539785359)
              ·
                refine ⟨140158462312172309678039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93438974874781539785359 140158462312172309678039)
                ·
                  refine ⟨210237693468258464517059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140158462312172309678039 210237693468258464517059)
                  ·
                    refine ⟨315356540202387696775589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 210237693468258464517059 315356540202387696775589)
                    ·
                      refine ⟨59129351287947693145423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 315356540202387696775589 59129351287947693145423)
                      ·
                        rfl

theorem cell23_115154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_115154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115154 prefixEnd_115154 := by exact prefixLift 115154
  have htrace : WordTrace (prefixWord ++ tailWord_115154) baseStart_115154 baseEnd_115154 := by
    simpa [prefixWord, tailWord_115154, baseEnd_115154] using wordTrace_append hprefix tailTrace_115154
  have hstable : (prefixWord ++ tailWord_115154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115154).length < 2 ^ (prefixWord ++ tailWord_115154).sum := by decide
  have hdescent : baseEnd_115154 < baseStart_115154 := by decide
  rcases family_descends (prefixWord ++ tailWord_115154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115157 : List Nat := [1, 3, 2, 3, 1, 4, 2, 1, 1, 2, 3]
def baseStart_115157 : Nat := 118140960795 + 115157 * 2 ^ 59
def prefixEnd_115157 : Nat := 4983230072969 + 3 ^ 40 * 115157 * 2
def baseEnd_115157 : Nat := 59130891729911181407909

theorem tailTrace_115157 : CollatzResearch.WordTrace tailWord_115157 prefixEnd_115157 59130891729911181407909 := by
  unfold tailWord_115157
  simp only [CollatzResearch.WordTrace]
  refine ⟨4200120843813331094919725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2800080562542220729946483 4200120843813331094919725)
  ·
    refine ⟨1575045316429999160594897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4200120843813331094919725 1575045316429999160594897)
    ·
      refine ⟨1181283987322499370446173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1575045316429999160594897 1181283987322499370446173)
      ·
        refine ⟨442981495245937263917315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1181283987322499370446173 442981495245937263917315)
        ·
          refine ⟨664472242868905895875973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442981495245937263917315 664472242868905895875973)
          ·
            refine ⟨124588545537919855476745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 664472242868905895875973 124588545537919855476745)
            ·
              refine ⟨93441409153439891607559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124588545537919855476745 93441409153439891607559)
              ·
                refine ⟨140162113730159837411339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93441409153439891607559 140162113730159837411339)
                ·
                  refine ⟨210243170595239756117009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140162113730159837411339 210243170595239756117009)
                  ·
                    refine ⟨157682377946429817087757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 210243170595239756117009 157682377946429817087757)
                    ·
                      refine ⟨59130891729911181407909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 157682377946429817087757 59130891729911181407909)
                      ·
                        rfl

theorem cell23_115157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_115157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115157 prefixEnd_115157 := by exact prefixLift 115157
  have htrace : WordTrace (prefixWord ++ tailWord_115157) baseStart_115157 baseEnd_115157 := by
    simpa [prefixWord, tailWord_115157, baseEnd_115157] using wordTrace_append hprefix tailTrace_115157
  have hstable : (prefixWord ++ tailWord_115157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115157).length < 2 ^ (prefixWord ++ tailWord_115157).sum := by decide
  have hdescent : baseEnd_115157 < baseStart_115157 := by decide
  rcases family_descends (prefixWord ++ tailWord_115157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115196 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_115196 : Nat := 118140960795 + 115196 * 2 ^ 59
def prefixEnd_115196 : Nat := 4983230072969 + 3 ^ 40 * 115196 * 2
def baseEnd_115196 : Nat := 59150917475436528820229

theorem tailTrace_115196 : CollatzResearch.WordTrace tailWord_115196 prefixEnd_115196 59150917475436528820229 := by
  unfold tailWord_115196
  simp only [CollatzResearch.WordTrace]
  refine ⟨2100771645336020377794721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2801028860448027170392961 2100771645336020377794721)
  ·
    refine ⟨1575578734002015283346041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2100771645336020377794721 1575578734002015283346041)
    ·
      refine ⟨1181684050501511462509531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1575578734002015283346041 1181684050501511462509531)
      ·
        refine ⟨1772526075752267193764297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1181684050501511462509531 1772526075752267193764297)
        ·
          refine ⟨1329394556814200395323223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1772526075752267193764297 1329394556814200395323223)
          ·
            refine ⟨1994091835221300592984835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329394556814200395323223 1994091835221300592984835)
            ·
              refine ⟨2991137752831950889477253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1994091835221300592984835 2991137752831950889477253)
              ·
                refine ⟨560838328655990791776985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2991137752831950889477253 560838328655990791776985)
                ·
                  refine ⟨420628746491993093832739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 560838328655990791776985 420628746491993093832739)
                  ·
                    refine ⟨630943119737989640749109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 420628746491993093832739 630943119737989640749109)
                    ·
                      refine ⟨59150917475436528820229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 630943119737989640749109 59150917475436528820229)
                      ·
                        rfl

theorem cell23_115196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_115196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115196 prefixEnd_115196 := by exact prefixLift 115196
  have htrace : WordTrace (prefixWord ++ tailWord_115196) baseStart_115196 baseEnd_115196 := by
    simpa [prefixWord, tailWord_115196, baseEnd_115196] using wordTrace_append hprefix tailTrace_115196
  have hstable : (prefixWord ++ tailWord_115196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115196).length < 2 ^ (prefixWord ++ tailWord_115196).sum := by decide
  have hdescent : baseEnd_115196 < baseStart_115196 := by decide
  rcases family_descends (prefixWord ++ tailWord_115196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115210 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 6, 2, 2]
def baseStart_115210 : Nat := 118140960795 + 115210 * 2 ^ 59
def prefixEnd_115210 : Nat := 4983230072969 + 3 ^ 40 * 115210 * 2
def baseEnd_115210 : Nat := 59158106204599474045165

theorem tailTrace_115210 : CollatzResearch.WordTrace tailWord_115210 prefixEnd_115210 59158106204599474045165 := by
  unfold tailWord_115210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1050513478155330286649771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2801369275080880764399389 1050513478155330286649771)
  ·
    refine ⟨1575770217232995429974657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1050513478155330286649771 1575770217232995429974657)
    ·
      refine ⟨1181827662924746572480993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1575770217232995429974657 1181827662924746572480993)
      ·
        refine ⟨886370747193559929360745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1181827662924746572480993 886370747193559929360745)
        ·
          refine ⟨664778060395169947020559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 886370747193559929360745 664778060395169947020559)
          ·
            refine ⟨997167090592754920530839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664778060395169947020559 997167090592754920530839)
            ·
              refine ⟨1495750635889132380796259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997167090592754920530839 1495750635889132380796259)
              ·
                refine ⟨2243625953833698571194389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495750635889132380796259 2243625953833698571194389)
                ·
                  refine ⟨105169966585954620524737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2243625953833698571194389 105169966585954620524737)
                  ·
                    refine ⟨78877474939465965393553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105169966585954620524737 78877474939465965393553)
                    ·
                      refine ⟨59158106204599474045165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 78877474939465965393553 59158106204599474045165)
                      ·
                        rfl

theorem cell23_115210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_115210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115210 prefixEnd_115210 := by exact prefixLift 115210
  have htrace : WordTrace (prefixWord ++ tailWord_115210) baseStart_115210 baseEnd_115210 := by
    simpa [prefixWord, tailWord_115210, baseEnd_115210] using wordTrace_append hprefix tailTrace_115210
  have hstable : (prefixWord ++ tailWord_115210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115210).length < 2 ^ (prefixWord ++ tailWord_115210).sum := by decide
  have hdescent : baseEnd_115210 < baseStart_115210 := by decide
  rcases family_descends (prefixWord ++ tailWord_115210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115256 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 1, 1, 7]
def baseStart_115256 : Nat := 118140960795 + 115256 * 2 ^ 59
def prefixEnd_115256 : Nat := 4983230072969 + 3 ^ 40 * 115256 * 2
def baseEnd_115256 : Nat := 59181726314706294069953

theorem tailTrace_115256 : CollatzResearch.WordTrace tailWord_115256 prefixEnd_115256 59181726314706294069953 := by
  unfold tailWord_115256
  simp only [CollatzResearch.WordTrace]
  refine ⟨2101865835227335501386811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2802487780303114001849081 2101865835227335501386811)
  ·
    refine ⟨3152798752841003252080217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2101865835227335501386811 3152798752841003252080217)
    ·
      refine ⟨2364599064630752439060163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3152798752841003252080217 2364599064630752439060163)
      ·
        refine ⟨3546898596946128658590245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2364599064630752439060163 3546898596946128658590245)
        ·
          refine ⟨665043486927399123485671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3546898596946128658590245 665043486927399123485671)
          ·
            refine ⟨997565230391098685228507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665043486927399123485671 997565230391098685228507)
            ·
              refine ⟨1496347845586648027842761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997565230391098685228507 1496347845586648027842761)
              ·
                refine ⟨1122260884189986020882071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1496347845586648027842761 1122260884189986020882071)
                ·
                  refine ⟨1683391326284979031323107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1122260884189986020882071 1683391326284979031323107)
                  ·
                    refine ⟨2525086989427468546984661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1683391326284979031323107 2525086989427468546984661)
                    ·
                      refine ⟨59181726314706294069953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2525086989427468546984661 59181726314706294069953)
                      ·
                        rfl

theorem cell23_115256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_115256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115256 prefixEnd_115256 := by exact prefixLift 115256
  have htrace : WordTrace (prefixWord ++ tailWord_115256) baseStart_115256 baseEnd_115256 := by
    simpa [prefixWord, tailWord_115256, baseEnd_115256] using wordTrace_append hprefix tailTrace_115256
  have hstable : (prefixWord ++ tailWord_115256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115256).length < 2 ^ (prefixWord ++ tailWord_115256).sum := by decide
  have hdescent : baseEnd_115256 < baseStart_115256 := by decide
  rcases family_descends (prefixWord ++ tailWord_115256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115263 : List Nat := [1, 1, 2, 2, 3, 2, 4, 1, 2, 5]
def baseStart_115263 : Nat := 118140960795 + 115263 * 2 ^ 59
def prefixEnd_115263 : Nat := 4983230072969 + 3 ^ 40 * 115263 * 2
def baseEnd_115263 : Nat := 19728440226429255560807

theorem tailTrace_115263 : CollatzResearch.WordTrace tailWord_115263 prefixEnd_115263 19728440226429255560807 := by
  unfold tailWord_115263
  simp only [CollatzResearch.WordTrace]
  refine ⟨4203986981429311198278443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2802657987619540798852295 4203986981429311198278443)
  ·
    refine ⟨6305980472143966797417665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4203986981429311198278443 6305980472143966797417665)
    ·
      refine ⟨4729485354107975098063249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6305980472143966797417665 4729485354107975098063249)
      ·
        refine ⟨3547114015580981323547437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4729485354107975098063249 3547114015580981323547437)
        ·
          refine ⟨1330167755842867996330289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3547114015580981323547437 1330167755842867996330289)
          ·
            refine ⟨997625816882150997247717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1330167755842867996330289 997625816882150997247717)
            ·
              refine ⟨187054840665403311983947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 997625816882150997247717 187054840665403311983947)
              ·
                refine ⟨280582260998104967975921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187054840665403311983947 280582260998104967975921)
                ·
                  refine ⟨210436695748578725981941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280582260998104967975921 210436695748578725981941)
                  ·
                    refine ⟨19728440226429255560807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 210436695748578725981941 19728440226429255560807)
                    ·
                      rfl

theorem cell23_115263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 5].length) (baseStart_115263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115263 prefixEnd_115263 := by exact prefixLift 115263
  have htrace : WordTrace (prefixWord ++ tailWord_115263) baseStart_115263 baseEnd_115263 := by
    simpa [prefixWord, tailWord_115263, baseEnd_115263] using wordTrace_append hprefix tailTrace_115263
  have hstable : (prefixWord ++ tailWord_115263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115263).length < 2 ^ (prefixWord ++ tailWord_115263).sum := by decide
  have hdescent : baseEnd_115263 < baseStart_115263 := by decide
  rcases family_descends (prefixWord ++ tailWord_115263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115300 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 2, 4, 2]
def baseStart_115300 : Nat := 118140960795 + 115300 * 2 ^ 59
def prefixEnd_115300 : Nat := 4983230072969 + 3 ^ 40 * 115300 * 2
def baseEnd_115300 : Nat := 59204319463504121919751

theorem tailTrace_115300 : CollatzResearch.WordTrace tailWord_115300 prefixEnd_115300 59204319463504121919751 := by
  unfold tailWord_115300
  simp only [CollatzResearch.WordTrace]
  refine ⟨2102668241147633258687677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2803557654863511011583569 2102668241147633258687677)
  ·
    refine ⟨788500590430362472007879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2102668241147633258687677 788500590430362472007879)
    ·
      refine ⟨1182750885645543708011819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 788500590430362472007879 1182750885645543708011819)
      ·
        refine ⟨1774126328468315562017729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1182750885645543708011819 1774126328468315562017729)
        ·
          refine ⟨1330594746351236671513297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1774126328468315562017729 1330594746351236671513297)
          ·
            refine ⟨997946059763427503634973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1330594746351236671513297 997946059763427503634973)
            ·
              refine ⟨374229772411285313863115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 997946059763427503634973 374229772411285313863115)
              ·
                refine ⟨561344658616927970794673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374229772411285313863115 561344658616927970794673)
                ·
                  refine ⟨421008493962695978096005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561344658616927970794673 421008493962695978096005)
                  ·
                    refine ⟨78939092618005495893001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 421008493962695978096005 78939092618005495893001)
                    ·
                      refine ⟨59204319463504121919751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 78939092618005495893001 59204319463504121919751)
                      ·
                        rfl

theorem cell23_115300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_115300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115300 prefixEnd_115300 := by exact prefixLift 115300
  have htrace : WordTrace (prefixWord ++ tailWord_115300) baseStart_115300 baseEnd_115300 := by
    simpa [prefixWord, tailWord_115300, baseEnd_115300] using wordTrace_append hprefix tailTrace_115300
  have hstable : (prefixWord ++ tailWord_115300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115300).length < 2 ^ (prefixWord ++ tailWord_115300).sum := by decide
  have hdescent : baseEnd_115300 < baseStart_115300 := by decide
  rcases family_descends (prefixWord ++ tailWord_115300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115303 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_115303 : Nat := 118140960795 + 115303 * 2 ^ 59
def prefixEnd_115303 : Nat := 4983230072969 + 3 ^ 40 * 115303 * 2
def baseEnd_115303 : Nat := 59205859905467610182237

theorem tailTrace_115303 : CollatzResearch.WordTrace tailWord_115303 prefixEnd_115303 59205859905467610182237 := by
  unfold tailWord_115303
  simp only [CollatzResearch.WordTrace]
  refine ⟨4205445901284398029734563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2803630600856265353156375 4205445901284398029734563)
  ·
    refine ⟨6308168851926597044601845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4205445901284398029734563 6308168851926597044601845)
    ·
      refine ⟨591390829868118472931423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6308168851926597044601845 591390829868118472931423)
      ·
        refine ⟨887086244802177709397135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591390829868118472931423 887086244802177709397135)
        ·
          refine ⟨1330629367203266564095703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 887086244802177709397135 1330629367203266564095703)
          ·
            refine ⟨1995944050804899846143555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330629367203266564095703 1995944050804899846143555)
            ·
              refine ⟨2993916076207349769215333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1995944050804899846143555 2993916076207349769215333)
              ·
                refine ⟨561359264288878081727875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2993916076207349769215333 561359264288878081727875)
                ·
                  refine ⟨842038896433317122591813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561359264288878081727875 842038896433317122591813)
                  ·
                    refine ⟨157882293081246960485965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 842038896433317122591813 157882293081246960485965)
                    ·
                      refine ⟨59205859905467610182237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 157882293081246960485965 59205859905467610182237)
                      ·
                        rfl

theorem cell23_115303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_115303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115303 prefixEnd_115303 := by exact prefixLift 115303
  have htrace : WordTrace (prefixWord ++ tailWord_115303) baseStart_115303 baseEnd_115303 := by
    simpa [prefixWord, tailWord_115303, baseEnd_115303] using wordTrace_append hprefix tailTrace_115303
  have hstable : (prefixWord ++ tailWord_115303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115303).length < 2 ^ (prefixWord ++ tailWord_115303).sum := by decide
  have hdescent : baseEnd_115303 < baseStart_115303 := by decide
  rcases family_descends (prefixWord ++ tailWord_115303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115310 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 5, 4]
def baseStart_115310 : Nat := 118140960795 + 115310 * 2 ^ 59
def prefixEnd_115310 : Nat := 4983230072969 + 3 ^ 40 * 115310 * 2
def baseEnd_115310 : Nat := 19736484756683027598235

theorem tailTrace_115310 : CollatzResearch.WordTrace tailWord_115310 prefixEnd_115310 19736484756683027598235 := by
  unfold tailWord_115310
  simp only [CollatzResearch.WordTrace]
  refine ⟨525712651532379778154923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2803800808172692150159589 525712651532379778154923)
  ·
    refine ⟨788568977298569667232385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 525712651532379778154923 788568977298569667232385)
    ·
      refine ⟨591426732973927250424289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 788568977298569667232385 591426732973927250424289)
      ·
        refine ⟨443570049730445437818217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591426732973927250424289 443570049730445437818217)
        ·
          refine ⟨332677537297834078363663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443570049730445437818217 332677537297834078363663)
          ·
            refine ⟨499016305946751117545495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332677537297834078363663 499016305946751117545495)
            ·
              refine ⟨748524458920126676318243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499016305946751117545495 748524458920126676318243)
              ·
                refine ⟨1122786688380190014477365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748524458920126676318243 1122786688380190014477365)
                ·
                  refine ⟨105261252035642813857253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1122786688380190014477365 105261252035642813857253)
                  ·
                    refine ⟨19736484756683027598235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105261252035642813857253 19736484756683027598235)
                    ·
                      rfl

theorem cell23_115310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_115310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115310 prefixEnd_115310 := by exact prefixLift 115310
  have htrace : WordTrace (prefixWord ++ tailWord_115310) baseStart_115310 baseEnd_115310 := by
    simpa [prefixWord, tailWord_115310, baseEnd_115310] using wordTrace_append hprefix tailTrace_115310
  have hstable : (prefixWord ++ tailWord_115310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115310).length < 2 ^ (prefixWord ++ tailWord_115310).sum := by decide
  have hdescent : baseEnd_115310 < baseStart_115310 := by decide
  rcases family_descends (prefixWord ++ tailWord_115310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115400 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 4, 4]
def baseStart_115400 : Nat := 118140960795 + 115400 * 2 ^ 59
def prefixEnd_115400 : Nat := 4983230072969 + 3 ^ 40 * 115400 * 2
def baseEnd_115400 : Nat := 19751889176317910223097

theorem tailTrace_115400 : CollatzResearch.WordTrace tailWord_115400 prefixEnd_115400 19751889176317910223097 := by
  unfold tailWord_115400
  simp only [CollatzResearch.WordTrace]
  refine ⟨2104491890966491798007827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2805989187955322397343769 2104491890966491798007827)
  ·
    refine ⟨3156737836449737697011741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2104491890966491798007827 3156737836449737697011741)
    ·
      refine ⟨1183776688668651636379403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3156737836449737697011741 1183776688668651636379403)
      ·
        refine ⟨1775665033002977454569105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1183776688668651636379403 1775665033002977454569105)
        ·
          refine ⟨1331748774752233090926829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1775665033002977454569105 1331748774752233090926829)
          ·
            refine ⟨499405790532087409097561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1331748774752233090926829 499405790532087409097561)
            ·
              refine ⟨374554342899065556823171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499405790532087409097561 374554342899065556823171)
              ·
                refine ⟨561831514348598335234757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374554342899065556823171 561831514348598335234757)
                ·
                  refine ⟨105343408940362187856517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 561831514348598335234757 105343408940362187856517)
                  ·
                    refine ⟨19751889176317910223097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105343408940362187856517 19751889176317910223097)
                    ·
                      rfl

theorem cell23_115400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_115400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115400 prefixEnd_115400 := by exact prefixLift 115400
  have htrace : WordTrace (prefixWord ++ tailWord_115400) baseStart_115400 baseEnd_115400 := by
    simpa [prefixWord, tailWord_115400, baseEnd_115400] using wordTrace_append hprefix tailTrace_115400
  have hstable : (prefixWord ++ tailWord_115400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115400).length < 2 ^ (prefixWord ++ tailWord_115400).sum := by decide
  have hdescent : baseEnd_115400 < baseStart_115400 := by decide
  rcases family_descends (prefixWord ++ tailWord_115400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115427 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 3]
def baseStart_115427 : Nat := 118140960795 + 115427 * 2 ^ 59
def prefixEnd_115427 : Nat := 4983230072969 + 3 ^ 40 * 115427 * 2
def baseEnd_115427 : Nat := 59269531506625125031667

theorem tailTrace_115427 : CollatzResearch.WordTrace tailWord_115427 prefixEnd_115427 59269531506625125031667 := by
  unfold tailWord_115427
  simp only [CollatzResearch.WordTrace]
  refine ⟨4209968552835167207248535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2806645701890111471499023 4209968552835167207248535)
  ·
    refine ⟨6314952829252750810872803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4209968552835167207248535 6314952829252750810872803)
    ·
      refine ⟨9472429243879126216309205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6314952829252750810872803 9472429243879126216309205)
      ·
        refine ⟨222010060403417020694747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 9472429243879126216309205 222010060403417020694747)
        ·
          refine ⟨333015090605125531042121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222010060403417020694747 333015090605125531042121)
          ·
            refine ⟨249761317953844148281591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333015090605125531042121 249761317953844148281591)
            ·
              refine ⟨374641976930766222422387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249761317953844148281591 374641976930766222422387)
              ·
                refine ⟨561962965396149333633581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374641976930766222422387 561962965396149333633581)
                ·
                  refine ⟨210736112023556000112593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 561962965396149333633581 210736112023556000112593)
                  ·
                    refine ⟨158052084017667000084445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 210736112023556000112593 158052084017667000084445)
                    ·
                      refine ⟨59269531506625125031667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 158052084017667000084445 59269531506625125031667)
                      ·
                        rfl

theorem cell23_115427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_115427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115427 prefixEnd_115427 := by exact prefixLift 115427
  have htrace : WordTrace (prefixWord ++ tailWord_115427) baseStart_115427 baseEnd_115427 := by
    simpa [prefixWord, tailWord_115427, baseEnd_115427] using wordTrace_append hprefix tailTrace_115427
  have hstable : (prefixWord ++ tailWord_115427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115427).length < 2 ^ (prefixWord ++ tailWord_115427).sum := by decide
  have hdescent : baseEnd_115427 < baseStart_115427 := by decide
  rcases family_descends (prefixWord ++ tailWord_115427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115440 : List Nat := [2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 3]
def baseStart_115440 : Nat := 118140960795 + 115440 * 2 ^ 59
def prefixEnd_115440 : Nat := 4983230072969 + 3 ^ 40 * 115440 * 2
def baseEnd_115440 : Nat := 59276206755133574169107

theorem tailTrace_115440 : CollatzResearch.WordTrace tailWord_115440 prefixEnd_115440 59276206755133574169107 := by
  unfold tailWord_115440
  simp only [CollatzResearch.WordTrace]
  refine ⟨2105221350894035213735887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2806961801192046951647849 2105221350894035213735887)
  ·
    refine ⟨3157832026341052820603831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2105221350894035213735887 3157832026341052820603831)
    ·
      refine ⟨4736748039511579230905747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3157832026341052820603831 4736748039511579230905747)
      ·
        refine ⟨7105122059267368846358621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4736748039511579230905747 7105122059267368846358621)
        ·
          refine ⟨2664420772225263317384483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7105122059267368846358621 2664420772225263317384483)
          ·
            refine ⟨3996631158337894976076725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2664420772225263317384483 3996631158337894976076725)
            ·
              refine ⟨374684171094177654007193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3996631158337894976076725 374684171094177654007193)
              ·
                refine ⟨281013128320633240505395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374684171094177654007193 281013128320633240505395)
                ·
                  refine ⟨421519692480949860758093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281013128320633240505395 421519692480949860758093)
                  ·
                    refine ⟨158069884680356197784285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 421519692480949860758093 158069884680356197784285)
                    ·
                      refine ⟨59276206755133574169107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 158069884680356197784285 59276206755133574169107)
                      ·
                        rfl

theorem cell23_115440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 3].length) (baseStart_115440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115440 prefixEnd_115440 := by exact prefixLift 115440
  have htrace : WordTrace (prefixWord ++ tailWord_115440) baseStart_115440 baseEnd_115440 := by
    simpa [prefixWord, tailWord_115440, baseEnd_115440] using wordTrace_append hprefix tailTrace_115440
  have hstable : (prefixWord ++ tailWord_115440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115440).length < 2 ^ (prefixWord ++ tailWord_115440).sum := by decide
  have hdescent : baseEnd_115440 < baseStart_115440 := by decide
  rcases family_descends (prefixWord ++ tailWord_115440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115458 : List Nat := [3, 4, 1, 1, 1, 3, 1, 4, 1, 2, 2]
def baseStart_115458 : Nat := 118140960795 + 115458 * 2 ^ 59
def prefixEnd_115458 : Nat := 4983230072969 + 3 ^ 40 * 115458 * 2
def baseEnd_115458 : Nat := 59285449406914503744025

theorem tailTrace_115458 : CollatzResearch.WordTrace tailWord_115458 prefixEnd_115458 59285449406914503744025 := by
  unfold tailWord_115458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1052774803930714875406757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2807399477148573001084685 1052774803930714875406757)
  ·
    refine ⟨197395275737009039138767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1052774803930714875406757 197395275737009039138767)
    ·
      refine ⟨296092913605513558708151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197395275737009039138767 296092913605513558708151)
      ·
        refine ⟨444139370408270338062227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296092913605513558708151 444139370408270338062227)
        ·
          refine ⟨666209055612405507093341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444139370408270338062227 666209055612405507093341)
          ·
            refine ⟨249828395854652065160003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 666209055612405507093341 249828395854652065160003)
            ·
              refine ⟨374742593781978097740005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249828395854652065160003 374742593781978097740005)
              ·
                refine ⟨70264236334120893326251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 374742593781978097740005 70264236334120893326251)
                ·
                  refine ⟨105396354501181339989377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70264236334120893326251 105396354501181339989377)
                  ·
                    refine ⟨79047265875886004992033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105396354501181339989377 79047265875886004992033)
                    ·
                      refine ⟨59285449406914503744025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 79047265875886004992033 59285449406914503744025)
                      ·
                        rfl

theorem cell23_115458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_115458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115458 prefixEnd_115458 := by exact prefixLift 115458
  have htrace : WordTrace (prefixWord ++ tailWord_115458) baseStart_115458 baseEnd_115458 := by
    simpa [prefixWord, tailWord_115458, baseEnd_115458] using wordTrace_append hprefix tailTrace_115458
  have hstable : (prefixWord ++ tailWord_115458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115458).length < 2 ^ (prefixWord ++ tailWord_115458).sum := by decide
  have hdescent : baseEnd_115458 < baseStart_115458 := by decide
  rcases family_descends (prefixWord ++ tailWord_115458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115473 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 1, 8]
def baseStart_115473 : Nat := 118140960795 + 115473 * 2 ^ 59
def prefixEnd_115473 : Nat := 4983230072969 + 3 ^ 40 * 115473 * 2
def baseEnd_115473 : Nat := 19764383872243981685485

theorem tailTrace_115473 : CollatzResearch.WordTrace tailWord_115473 prefixEnd_115473 19764383872243981685485 := by
  unfold tailWord_115473
  simp only [CollatzResearch.WordTrace]
  refine ⟨4211646310668517063423073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2807764207112344708948715 4211646310668517063423073)
  ·
    refine ⟨3158734733001387797567305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4211646310668517063423073 3158734733001387797567305)
    ·
      refine ⟨2369051049751040848175479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3158734733001387797567305 2369051049751040848175479)
      ·
        refine ⟨3553576574626561272263219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2369051049751040848175479 3553576574626561272263219)
        ·
          refine ⟨5330364861939841908394829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3553576574626561272263219 5330364861939841908394829)
          ·
            refine ⟨1998886823227440715648061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5330364861939841908394829 1998886823227440715648061)
            ·
              refine ⟨749582558710290268368023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1998886823227440715648061 749582558710290268368023)
              ·
                refine ⟨1124373838065435402552035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 749582558710290268368023 1124373838065435402552035)
                ·
                  refine ⟨1686560757098153103828053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1124373838065435402552035 1686560757098153103828053)
                  ·
                    refine ⟨19764383872243981685485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1686560757098153103828053 19764383872243981685485)
                    ·
                      rfl

theorem cell23_115473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_115473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115473 prefixEnd_115473 := by exact prefixLift 115473
  have htrace : WordTrace (prefixWord ++ tailWord_115473) baseStart_115473 baseEnd_115473 := by
    simpa [prefixWord, tailWord_115473, baseEnd_115473] using wordTrace_append hprefix tailTrace_115473
  have hstable : (prefixWord ++ tailWord_115473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115473).length < 2 ^ (prefixWord ++ tailWord_115473).sum := by decide
  have hdescent : baseEnd_115473 < baseStart_115473 := by decide
  rcases family_descends (prefixWord ++ tailWord_115473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115497 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 6, 2, 2]
def baseStart_115497 : Nat := 118140960795 + 115497 * 2 ^ 59
def prefixEnd_115497 : Nat := 4983230072969 + 3 ^ 40 * 115497 * 2
def baseEnd_115497 : Nat := 59305475152439851156345

theorem tailTrace_115497 : CollatzResearch.WordTrace tailWord_115497 prefixEnd_115497 59305475152439851156345 := by
  unfold tailWord_115497
  simp only [CollatzResearch.WordTrace]
  refine ⟨4212521662581569162296745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2808347775054379441531163 4212521662581569162296745)
  ·
    refine ⟨3159391246936176871722559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4212521662581569162296745 3159391246936176871722559)
    ·
      refine ⟨4739086870404265307583839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3159391246936176871722559 4739086870404265307583839)
      ·
        refine ⟨7108630305606397961375759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4739086870404265307583839 7108630305606397961375759)
        ·
          refine ⟨10662945458409596942063639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7108630305606397961375759 10662945458409596942063639)
          ·
            refine ⟨15994418187614395413095459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10662945458409596942063639 15994418187614395413095459)
            ·
              refine ⟨23991627281421593119643189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15994418187614395413095459 23991627281421593119643189)
              ·
                refine ⟨2249215057633274354966549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23991627281421593119643189 2249215057633274354966549)
                ·
                  refine ⟨105431955826559735389057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2249215057633274354966549 105431955826559735389057)
                  ·
                    refine ⟨79073966869919801541793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105431955826559735389057 79073966869919801541793)
                    ·
                      refine ⟨59305475152439851156345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 79073966869919801541793 59305475152439851156345)
                      ·
                        rfl

theorem cell23_115497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 2, 2].length) (baseStart_115497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115497 prefixEnd_115497 := by exact prefixLift 115497
  have htrace : WordTrace (prefixWord ++ tailWord_115497) baseStart_115497 baseEnd_115497 := by
    simpa [prefixWord, tailWord_115497, baseEnd_115497] using wordTrace_append hprefix tailTrace_115497
  have hstable : (prefixWord ++ tailWord_115497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115497).length < 2 ^ (prefixWord ++ tailWord_115497).sum := by decide
  have hdescent : baseEnd_115497 < baseStart_115497 := by decide
  rcases family_descends (prefixWord ++ tailWord_115497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115508 : List Nat := [2, 5, 1, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_115508 : Nat := 118140960795 + 115508 * 2 ^ 59
def prefixEnd_115508 : Nat := 4983230072969 + 3 ^ 40 * 115508 * 2
def baseEnd_115508 : Nat := 59311123439639308118795

theorem tailTrace_115508 : CollatzResearch.WordTrace tailWord_115508 prefixEnd_115508 59311123439639308118795 := by
  unfold tailWord_115508
  simp only [CollatzResearch.WordTrace]
  refine ⟨2106461432770859020473589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2808615243694478693964785 2106461432770859020473589)
  ·
    refine ⟨197480759322268033169399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2106461432770859020473589 197480759322268033169399)
    ·
      refine ⟨296221138983402049754099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197480759322268033169399 296221138983402049754099)
      ·
        refine ⟨444331708475103074631149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296221138983402049754099 444331708475103074631149)
        ·
          refine ⟨166624390678163652986681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 444331708475103074631149 166624390678163652986681)
          ·
            refine ⟨124968293008622739740011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166624390678163652986681 124968293008622739740011)
            ·
              refine ⟨187452439512934109610017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124968293008622739740011 187452439512934109610017)
              ·
                refine ⟨140589329634700582207513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187452439512934109610017 140589329634700582207513)
                ·
                  refine ⟨105441997226025436655635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140589329634700582207513 105441997226025436655635)
                  ·
                    refine ⟨158162995839038154983453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105441997226025436655635 158162995839038154983453)
                    ·
                      refine ⟨59311123439639308118795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 158162995839038154983453 59311123439639308118795)
                      ·
                        rfl

theorem cell23_115508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_115508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115508 prefixEnd_115508 := by exact prefixLift 115508
  have htrace : WordTrace (prefixWord ++ tailWord_115508) baseStart_115508 baseEnd_115508 := by
    simpa [prefixWord, tailWord_115508, baseEnd_115508] using wordTrace_append hprefix tailTrace_115508
  have hstable : (prefixWord ++ tailWord_115508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115508).length < 2 ^ (prefixWord ++ tailWord_115508).sum := by decide
  have hdescent : baseEnd_115508 < baseStart_115508 := by decide
  rcases family_descends (prefixWord ++ tailWord_115508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115530 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 1, 5, 3]
def baseStart_115530 : Nat := 118140960795 + 115530 * 2 ^ 59
def prefixEnd_115530 : Nat := 4983230072969 + 3 ^ 40 * 115530 * 2
def baseEnd_115530 : Nat := 59322420014038222043693

theorem tailTrace_115530 : CollatzResearch.WordTrace tailWord_115530 prefixEnd_115530 59322420014038222043693 := by
  unfold tailWord_115530
  simp only [CollatzResearch.WordTrace]
  refine ⟨1053431317865503949562011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2809150180974677198832029 1053431317865503949562011)
  ·
    refine ⟨1580146976798255924343017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1053431317865503949562011 1580146976798255924343017)
    ·
      refine ⟨1185110232598691943257263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1580146976798255924343017 1185110232598691943257263)
      ·
        refine ⟨1777665348898037914885895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1185110232598691943257263 1777665348898037914885895)
        ·
          refine ⟨2666498023347056872328843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1777665348898037914885895 2666498023347056872328843)
          ·
            refine ⟨3999747035020585308493265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2666498023347056872328843 3999747035020585308493265)
            ·
              refine ⟨2999810276265438981369949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3999747035020585308493265 2999810276265438981369949)
              ·
                refine ⟨1124928853599539618013731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2999810276265438981369949 1124928853599539618013731)
                ·
                  refine ⟨1687393280399309427020597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1124928853599539618013731 1687393280399309427020597)
                  ·
                    refine ⟨158193120037435258783181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1687393280399309427020597 158193120037435258783181)
                    ·
                      refine ⟨59322420014038222043693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 158193120037435258783181 59322420014038222043693)
                      ·
                        rfl

theorem cell23_115530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_115530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115530 prefixEnd_115530 := by exact prefixLift 115530
  have htrace : WordTrace (prefixWord ++ tailWord_115530) baseStart_115530 baseEnd_115530 := by
    simpa [prefixWord, tailWord_115530, baseEnd_115530] using wordTrace_append hprefix tailTrace_115530
  have hstable : (prefixWord ++ tailWord_115530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115530).length < 2 ^ (prefixWord ++ tailWord_115530).sum := by decide
  have hdescent : baseEnd_115530 < baseStart_115530 := by decide
  rcases family_descends (prefixWord ++ tailWord_115530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115582 : List Nat := [4, 2, 3, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_115582 : Nat := 118140960795 + 115582 * 2 ^ 59
def prefixEnd_115582 : Nat := 4983230072969 + 3 ^ 40 * 115582 * 2
def baseEnd_115582 : Nat := 59349121008072018593455

theorem tailTrace_115582 : CollatzResearch.WordTrace tailWord_115582 prefixEnd_115582 59349121008072018593455 := by
  unfold tailWord_115582
  simp only [CollatzResearch.WordTrace]
  refine ⟨526952733409203584892625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2810414578182419119427333 526952733409203584892625)
  ·
    refine ⟨395214550056902688669469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 526952733409203584892625 395214550056902688669469)
    ·
      refine ⟨148205456271338508251051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395214550056902688669469 148205456271338508251051)
      ·
        refine ⟨222308184407007762376577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148205456271338508251051 222308184407007762376577)
        ·
          refine ⟨166731138305255821782433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222308184407007762376577 166731138305255821782433)
          ·
            refine ⟨125048353728941866336825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166731138305255821782433 125048353728941866336825)
            ·
              refine ⟨93786265296706399752619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125048353728941866336825 93786265296706399752619)
              ·
                refine ⟨140679397945059599628929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93786265296706399752619 140679397945059599628929)
                ·
                  refine ⟨105509548458794699721697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140679397945059599628929 105509548458794699721697)
                  ·
                    refine ⟨79132161344096024791273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105509548458794699721697 79132161344096024791273)
                    ·
                      refine ⟨59349121008072018593455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 79132161344096024791273 59349121008072018593455)
                      ·
                        rfl

theorem cell23_115582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_115582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115582 prefixEnd_115582 := by exact prefixLift 115582
  have htrace : WordTrace (prefixWord ++ tailWord_115582) baseStart_115582 baseEnd_115582 := by
    simpa [prefixWord, tailWord_115582, baseEnd_115582] using wordTrace_append hprefix tailTrace_115582
  have hstable : (prefixWord ++ tailWord_115582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115582).length < 2 ^ (prefixWord ++ tailWord_115582).sum := by decide
  have hdescent : baseEnd_115582 < baseStart_115582 := by decide
  rcases family_descends (prefixWord ++ tailWord_115582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115587 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 1, 6, 2]
def baseStart_115587 : Nat := 118140960795 + 115587 * 2 ^ 59
def prefixEnd_115587 : Nat := 4983230072969 + 3 ^ 40 * 115587 * 2
def baseEnd_115587 : Nat := 59351688411344499030931

theorem tailTrace_115587 : CollatzResearch.WordTrace tailWord_115587 prefixEnd_115587 59351688411344499030931 := by
  unfold tailWord_115587
  simp only [CollatzResearch.WordTrace]
  refine ⟨4215804232255514533073015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2810536154837009688715343 4215804232255514533073015)
  ·
    refine ⟨6323706348383271799609523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4215804232255514533073015 6323706348383271799609523)
    ·
      refine ⟨9485559522574907699414285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6323706348383271799609523 9485559522574907699414285)
      ·
        refine ⟨3557084820965590387280357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9485559522574907699414285 3557084820965590387280357)
        ·
          refine ⟨666953403931048197615067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3557084820965590387280357 666953403931048197615067)
          ·
            refine ⟨1000430105896572296422601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666953403931048197615067 1000430105896572296422601)
            ·
              refine ⟨750322579422429222316951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1000430105896572296422601 750322579422429222316951)
              ·
                refine ⟨1125483869133643833475427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750322579422429222316951 1125483869133643833475427)
                ·
                  refine ⟨1688225803700465750213141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1125483869133643833475427 1688225803700465750213141)
                  ·
                    refine ⟨79135584548459332041241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1688225803700465750213141 79135584548459332041241)
                    ·
                      refine ⟨59351688411344499030931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 79135584548459332041241 59351688411344499030931)
                      ·
                        rfl

theorem cell23_115587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 6, 2].length) (baseStart_115587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115587 prefixEnd_115587 := by exact prefixLift 115587
  have htrace : WordTrace (prefixWord ++ tailWord_115587) baseStart_115587 baseEnd_115587 := by
    simpa [prefixWord, tailWord_115587, baseEnd_115587] using wordTrace_append hprefix tailTrace_115587
  have hstable : (prefixWord ++ tailWord_115587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115587).length < 2 ^ (prefixWord ++ tailWord_115587).sum := by decide
  have hdescent : baseEnd_115587 < baseStart_115587 := by decide
  rcases family_descends (prefixWord ++ tailWord_115587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115604 : List Nat := [2, 4, 2, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_115604 : Nat := 118140960795 + 115604 * 2 ^ 59
def prefixEnd_115604 : Nat := 4983230072969 + 3 ^ 40 * 115604 * 2
def baseEnd_115604 : Nat := 59360417582470932518353

theorem tailTrace_115604 : CollatzResearch.WordTrace tailWord_115604 prefixEnd_115604 59360417582470932518353 := by
  unfold tailWord_115604
  simp only [CollatzResearch.WordTrace]
  refine ⟨2108212136596963218220933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2810949515462617624294577 2108212136596963218220933)
  ·
    refine ⟨395289775611930603416425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2108212136596963218220933 395289775611930603416425)
    ·
      refine ⟨296467331708947952562319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395289775611930603416425 296467331708947952562319)
      ·
        refine ⟨444700997563421928843479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296467331708947952562319 444700997563421928843479)
        ·
          refine ⟨667051496345132893265219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444700997563421928843479 667051496345132893265219)
          ·
            refine ⟨1000577244517699339897829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667051496345132893265219 1000577244517699339897829)
            ·
              refine ⟨187608233347068626230843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1000577244517699339897829 187608233347068626230843)
              ·
                refine ⟨281412350020602939346265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187608233347068626230843 281412350020602939346265)
                ·
                  refine ⟨211059262515452204509699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281412350020602939346265 211059262515452204509699)
                  ·
                    refine ⟨316588893773178306764549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 211059262515452204509699 316588893773178306764549)
                    ·
                      refine ⟨59360417582470932518353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 316588893773178306764549 59360417582470932518353)
                      ·
                        rfl

theorem cell23_115604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_115604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115604 prefixEnd_115604 := by exact prefixLift 115604
  have htrace : WordTrace (prefixWord ++ tailWord_115604) baseStart_115604 baseEnd_115604 := by
    simpa [prefixWord, tailWord_115604, baseEnd_115604] using wordTrace_append hprefix tailTrace_115604
  have hstable : (prefixWord ++ tailWord_115604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115604).length < 2 ^ (prefixWord ++ tailWord_115604).sum := by decide
  have hdescent : baseEnd_115604 < baseStart_115604 := by decide
  rcases family_descends (prefixWord ++ tailWord_115604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115674 : List Nat := [3, 1, 1, 2, 4, 2, 1, 3, 1, 5]
def baseStart_115674 : Nat := 118140960795 + 115674 * 2 ^ 59
def prefixEnd_115674 : Nat := 4983230072969 + 3 ^ 40 * 115674 * 2
def baseEnd_115674 : Nat := 19798787076095219547677

theorem tailTrace_115674 : CollatzResearch.WordTrace tailWord_115674 prefixEnd_115674 19798787076095219547677 := by
  unfold tailWord_115674
  simp only [CollatzResearch.WordTrace]
  refine ⟨1054744345735082097872519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2812651588626885594326717 1054744345735082097872519)
  ·
    refine ⟨1582116518602623146808779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1054744345735082097872519 1582116518602623146808779)
    ·
      refine ⟨2373174777903934720213169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1582116518602623146808779 2373174777903934720213169)
      ·
        refine ⟨1779881083427951040159877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2373174777903934720213169 1779881083427951040159877)
        ·
          refine ⟨333727703142740820029977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1779881083427951040159877 333727703142740820029977)
          ·
            refine ⟨250295777357055615022483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333727703142740820029977 250295777357055615022483)
            ·
              refine ⟨375443666035583422533725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250295777357055615022483 375443666035583422533725)
              ·
                refine ⟨140791374763343783450147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375443666035583422533725 140791374763343783450147)
                ·
                  refine ⟨211187062145015675175221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140791374763343783450147 211187062145015675175221)
                  ·
                    refine ⟨19798787076095219547677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 211187062145015675175221 19798787076095219547677)
                    ·
                      rfl

theorem cell23_115674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 1, 5].length) (baseStart_115674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115674 prefixEnd_115674 := by exact prefixLift 115674
  have htrace : WordTrace (prefixWord ++ tailWord_115674) baseStart_115674 baseEnd_115674 := by
    simpa [prefixWord, tailWord_115674, baseEnd_115674] using wordTrace_append hprefix tailTrace_115674
  have hstable : (prefixWord ++ tailWord_115674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115674).length < 2 ^ (prefixWord ++ tailWord_115674).sum := by decide
  have hdescent : baseEnd_115674 < baseStart_115674 := by decide
  rcases family_descends (prefixWord ++ tailWord_115674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115697 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 3, 1, 5]
def baseStart_115697 : Nat := 118140960795 + 115697 * 2 ^ 59
def prefixEnd_115697 : Nat := 4983230072969 + 3 ^ 40 * 115697 * 2
def baseEnd_115697 : Nat := 59408171283339068655425

theorem tailTrace_115697 : CollatzResearch.WordTrace tailWord_115697 prefixEnd_115697 59408171283339068655425 := by
  unfold tailWord_115697
  simp only [CollatzResearch.WordTrace]
  refine ⟨4219816261857003319577345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2813210841238002213051563 4219816261857003319577345)
  ·
    refine ⟨3164862196392752489683009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4219816261857003319577345 3164862196392752489683009)
    ·
      refine ⟨2373646647294564367262257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3164862196392752489683009 2373646647294564367262257)
      ·
        refine ⟨1780234985470923275446693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2373646647294564367262257 1780234985470923275446693)
        ·
          refine ⟨333794059775798114146255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1780234985470923275446693 333794059775798114146255)
          ·
            refine ⟨500691089663697171219383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333794059775798114146255 500691089663697171219383)
            ·
              refine ⟨751036634495545756829075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500691089663697171219383 751036634495545756829075)
              ·
                refine ⟨1126554951743318635243613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751036634495545756829075 1126554951743318635243613)
                ·
                  refine ⟨422458106903744488216355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1126554951743318635243613 422458106903744488216355)
                  ·
                    refine ⟨633687160355616732324533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 422458106903744488216355 633687160355616732324533)
                    ·
                      refine ⟨59408171283339068655425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 633687160355616732324533 59408171283339068655425)
                      ·
                        rfl

theorem cell23_115697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_115697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115697 prefixEnd_115697 := by exact prefixLift 115697
  have htrace : WordTrace (prefixWord ++ tailWord_115697) baseStart_115697 baseEnd_115697 := by
    simpa [prefixWord, tailWord_115697, baseEnd_115697] using wordTrace_append hprefix tailTrace_115697
  have hstable : (prefixWord ++ tailWord_115697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115697).length < 2 ^ (prefixWord ++ tailWord_115697).sum := by decide
  have hdescent : baseEnd_115697 < baseStart_115697 := by decide
  rcases family_descends (prefixWord ++ tailWord_115697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115761 : List Nat := [1, 2, 2, 3, 1, 2, 3, 3, 2, 1, 3]
def baseStart_115761 : Nat := 118140960795 + 115761 * 2 ^ 59
def prefixEnd_115761 : Nat := 4983230072969 + 3 ^ 40 * 115761 * 2
def baseEnd_115761 : Nat := 59441034045226818255131

theorem tailTrace_115761 : CollatzResearch.WordTrace tailWord_115761 prefixEnd_115761 59441034045226818255131 := by
  unfold tailWord_115761
  simp only [CollatzResearch.WordTrace]
  refine ⟨4222150533625142249907137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2814767022416761499938091 4222150533625142249907137)
  ·
    refine ⟨3166612900218856687430353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4222150533625142249907137 3166612900218856687430353)
    ·
      refine ⟨2374959675164142515572765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3166612900218856687430353 2374959675164142515572765)
      ·
        refine ⟨890609878186553443339787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2374959675164142515572765 890609878186553443339787)
        ·
          refine ⟨1335914817279830165009681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890609878186553443339787 1335914817279830165009681)
          ·
            refine ⟨1001936112959872623757261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1335914817279830165009681 1001936112959872623757261)
            ·
              refine ⟨375726042359952233908973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1001936112959872623757261 375726042359952233908973)
              ·
                refine ⟨140897265884982087715865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375726042359952233908973 140897265884982087715865)
                ·
                  refine ⟨105672949413736565786899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140897265884982087715865 105672949413736565786899)
                  ·
                    refine ⟨158509424120604848680349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105672949413736565786899 158509424120604848680349)
                    ·
                      refine ⟨59441034045226818255131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 158509424120604848680349 59441034045226818255131)
                      ·
                        rfl

theorem cell23_115761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_115761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115761 prefixEnd_115761 := by exact prefixLift 115761
  have htrace : WordTrace (prefixWord ++ tailWord_115761) baseStart_115761 baseEnd_115761 := by
    simpa [prefixWord, tailWord_115761, baseEnd_115761] using wordTrace_append hprefix tailTrace_115761
  have hstable : (prefixWord ++ tailWord_115761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115761).length < 2 ^ (prefixWord ++ tailWord_115761).sum := by decide
  have hdescent : baseEnd_115761 < baseStart_115761 := by decide
  rcases family_descends (prefixWord ++ tailWord_115761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115787 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 3]
def baseStart_115787 : Nat := 118140960795 + 115787 * 2 ^ 59
def prefixEnd_115787 : Nat := 4983230072969 + 3 ^ 40 * 115787 * 2
def baseEnd_115787 : Nat := 59454384542243716530011

theorem tailTrace_115787 : CollatzResearch.WordTrace tailWord_115787 prefixEnd_115787 59454384542243716530011 := by
  unfold tailWord_115787
  simp only [CollatzResearch.WordTrace]
  refine ⟨4223098831530948690353615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2815399221020632460235743 4223098831530948690353615)
  ·
    refine ⟨6334648247296423035530423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4223098831530948690353615 6334648247296423035530423)
    ·
      refine ⟨9501972370944634553295635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6334648247296423035530423 9501972370944634553295635)
      ·
        refine ⟨14252958556416951829943453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9501972370944634553295635 14252958556416951829943453)
        ·
          refine ⟨5344859458656356936228795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14252958556416951829943453 5344859458656356936228795)
          ·
            refine ⟨8017289187984535404343193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5344859458656356936228795 8017289187984535404343193)
            ·
              refine ⟨6012966890988401553257395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8017289187984535404343193 6012966890988401553257395)
              ·
                refine ⟨9019450336482602329886093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6012966890988401553257395 9019450336482602329886093)
                ·
                  refine ⟨3382293876180975873707285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9019450336482602329886093 3382293876180975873707285)
                  ·
                    refine ⟨158545025445983244080029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3382293876180975873707285 158545025445983244080029)
                    ·
                      refine ⟨59454384542243716530011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 158545025445983244080029 59454384542243716530011)
                      ·
                        rfl

theorem cell23_115787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 3].length) (baseStart_115787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115787 prefixEnd_115787 := by exact prefixLift 115787
  have htrace : WordTrace (prefixWord ++ tailWord_115787) baseStart_115787 baseEnd_115787 := by
    simpa [prefixWord, tailWord_115787, baseEnd_115787] using wordTrace_append hprefix tailTrace_115787
  have hstable : (prefixWord ++ tailWord_115787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115787).length < 2 ^ (prefixWord ++ tailWord_115787).sum := by decide
  have hdescent : baseEnd_115787 < baseStart_115787 := by decide
  rcases family_descends (prefixWord ++ tailWord_115787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115804 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_115804 : Nat := 118140960795 + 115804 * 2 ^ 59
def prefixEnd_115804 : Nat := 4983230072969 + 3 ^ 40 * 115804 * 2
def baseEnd_115804 : Nat := 59463113713370150017433

theorem tailTrace_115804 : CollatzResearch.WordTrace tailWord_115804 prefixEnd_115804 59463113713370150017433 := by
  unfold tailWord_115804
  simp only [CollatzResearch.WordTrace]
  refine ⟨2111859436234680296861233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2815812581646240395814977 2111859436234680296861233)
  ·
    refine ⟨1583894577176010222645925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2111859436234680296861233 1583894577176010222645925)
    ·
      refine ⟨296980233220501916746111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1583894577176010222645925 296980233220501916746111)
      ·
        refine ⟨445470349830752875119167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296980233220501916746111 445470349830752875119167)
        ·
          refine ⟨668205524746129312678751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445470349830752875119167 668205524746129312678751)
          ·
            refine ⟨1002308287119193969018127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668205524746129312678751 1002308287119193969018127)
            ·
              refine ⟨1503462430678790953527191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1002308287119193969018127 1503462430678790953527191)
              ·
                refine ⟨2255193646018186430290787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1503462430678790953527191 2255193646018186430290787)
                ·
                  refine ⟨3382790469027279645436181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2255193646018186430290787 3382790469027279645436181)
                  ·
                    refine ⟨158568303235653733379821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3382790469027279645436181 158568303235653733379821)
                    ·
                      refine ⟨59463113713370150017433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 158568303235653733379821 59463113713370150017433)
                      ·
                        rfl

theorem cell23_115804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_115804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115804 prefixEnd_115804 := by exact prefixLift 115804
  have htrace : WordTrace (prefixWord ++ tailWord_115804) baseStart_115804 baseEnd_115804 := by
    simpa [prefixWord, tailWord_115804, baseEnd_115804] using wordTrace_append hprefix tailTrace_115804
  have hstable : (prefixWord ++ tailWord_115804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115804).length < 2 ^ (prefixWord ++ tailWord_115804).sum := by decide
  have hdescent : baseEnd_115804 < baseStart_115804 := by decide
  rcases family_descends (prefixWord ++ tailWord_115804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115807 : List Nat := [1, 1, 2, 3, 1, 1, 4, 3, 7]
def baseStart_115807 : Nat := 118140960795 + 115807 * 2 ^ 59
def prefixEnd_115807 : Nat := 4983230072969 + 3 ^ 40 * 115807 * 2
def baseEnd_115807 : Nat := 6607183795037070919991

theorem tailTrace_115807 : CollatzResearch.WordTrace tailWord_115807 prefixEnd_115807 6607183795037070919991 := by
  unfold tailWord_115807
  simp only [CollatzResearch.WordTrace]
  refine ⟨4223828291458492106081675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2815885527638994737387783 4223828291458492106081675)
  ·
    refine ⟨6335742437187738159122513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4223828291458492106081675 6335742437187738159122513)
    ·
      refine ⟨4751806827890803619341885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6335742437187738159122513 4751806827890803619341885)
      ·
        refine ⟨1781927560459051357253207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4751806827890803619341885 1781927560459051357253207)
        ·
          refine ⟨2672891340688577035879811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1781927560459051357253207 2672891340688577035879811)
          ·
            refine ⟨4009337011032865553819717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2672891340688577035879811 4009337011032865553819717)
            ·
              refine ⟨751750689568662291341197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4009337011032865553819717 751750689568662291341197)
              ·
                refine ⟨281906508588248359252949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 751750689568662291341197 281906508588248359252949)
                ·
                  refine ⟨6607183795037070919991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 281906508588248359252949 6607183795037070919991)
                  ·
                    rfl

theorem cell23_115807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 7].length) (baseStart_115807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115807 prefixEnd_115807 := by exact prefixLift 115807
  have htrace : WordTrace (prefixWord ++ tailWord_115807) baseStart_115807 baseEnd_115807 := by
    simpa [prefixWord, tailWord_115807, baseEnd_115807] using wordTrace_append hprefix tailTrace_115807
  have hstable : (prefixWord ++ tailWord_115807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115807).length < 2 ^ (prefixWord ++ tailWord_115807).sum := by decide
  have hdescent : baseEnd_115807 < baseStart_115807 := by decide
  rcases family_descends (prefixWord ++ tailWord_115807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115818 : List Nat := [3, 1, 3, 2, 2, 2, 2, 1, 1, 4, 2]
def baseStart_115818 : Nat := 118140960795 + 115818 * 2 ^ 59
def prefixEnd_115818 : Nat := 4983230072969 + 3 ^ 40 * 115818 * 2
def baseEnd_115818 : Nat := 59470302442533095242369

theorem tailTrace_115818 : CollatzResearch.WordTrace tailWord_115818 prefixEnd_115818 59470302442533095242369 := by
  unfold tailWord_115818
  simp only [CollatzResearch.WordTrace]
  refine ⟨1056057373604660246183027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2816152996279093989821405 1056057373604660246183027)
  ·
    refine ⟨1584086060406990369274541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1056057373604660246183027 1584086060406990369274541)
    ·
      refine ⟨594032272652621388477953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1584086060406990369274541 594032272652621388477953)
      ·
        refine ⟨445524204489466041358465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 594032272652621388477953 445524204489466041358465)
        ·
          refine ⟨334143153367099531018849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445524204489466041358465 334143153367099531018849)
          ·
            refine ⟨250607365025324648264137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334143153367099531018849 250607365025324648264137)
            ·
              refine ⟨187955523768993486198103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250607365025324648264137 187955523768993486198103)
              ·
                refine ⟨281933285653490229297155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187955523768993486198103 281933285653490229297155)
                ·
                  refine ⟨422899928480235343945733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281933285653490229297155 422899928480235343945733)
                  ·
                    refine ⟨79293736590044126989825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 422899928480235343945733 79293736590044126989825)
                    ·
                      refine ⟨59470302442533095242369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 79293736590044126989825 59470302442533095242369)
                      ·
                        rfl

theorem cell23_115818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_115818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115818 prefixEnd_115818 := by exact prefixLift 115818
  have htrace : WordTrace (prefixWord ++ tailWord_115818) baseStart_115818 baseEnd_115818 := by
    simpa [prefixWord, tailWord_115818, baseEnd_115818] using wordTrace_append hprefix tailTrace_115818
  have hstable : (prefixWord ++ tailWord_115818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115818).length < 2 ^ (prefixWord ++ tailWord_115818).sum := by decide
  have hdescent : baseEnd_115818 < baseStart_115818 := by decide
  rcases family_descends (prefixWord ++ tailWord_115818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115841 : List Nat := [1, 2, 4, 2, 2, 1, 1, 5, 5]
def baseStart_115841 : Nat := 118140960795 + 115841 * 2 ^ 59
def prefixEnd_115841 : Nat := 4983230072969 + 3 ^ 40 * 115841 * 2
def baseEnd_115841 : Nat := 6609123610842945028307

theorem tailTrace_115841 : CollatzResearch.WordTrace tailWord_115841 prefixEnd_115841 6609123610842945028307 := by
  unfold tailWord_115841
  simp only [CollatzResearch.WordTrace]
  refine ⟨4225068373335315912819377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2816712248890210608546251 4225068373335315912819377)
  ·
    refine ⟨3168801280001486934614533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4225068373335315912819377 3168801280001486934614533)
    ·
      refine ⟨594150240000278800240225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3168801280001486934614533 594150240000278800240225)
      ·
        refine ⟨445612680000209100180169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 594150240000278800240225 445612680000209100180169)
        ·
          refine ⟨334209510000156825135127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445612680000209100180169 334209510000156825135127)
          ·
            refine ⟨501314265000235237702691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334209510000156825135127 501314265000235237702691)
            ·
              refine ⟨751971397500352856554037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501314265000235237702691 751971397500352856554037)
              ·
                refine ⟨70497318515658080301941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 751971397500352856554037 70497318515658080301941)
                ·
                  refine ⟨6609123610842945028307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70497318515658080301941 6609123610842945028307)
                  ·
                    rfl

theorem cell23_115841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 5].length) (baseStart_115841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115841 prefixEnd_115841 := by exact prefixLift 115841
  have htrace : WordTrace (prefixWord ++ tailWord_115841) baseStart_115841 baseEnd_115841 := by
    simpa [prefixWord, tailWord_115841, baseEnd_115841] using wordTrace_append hprefix tailTrace_115841
  have hstable : (prefixWord ++ tailWord_115841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115841).length < 2 ^ (prefixWord ++ tailWord_115841).sum := by decide
  have hdescent : baseEnd_115841 < baseStart_115841 := by decide
  rcases family_descends (prefixWord ++ tailWord_115841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115884 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 5, 4]
def baseStart_115884 : Nat := 118140960795 + 115884 * 2 ^ 59
def prefixEnd_115884 : Nat := 4983230072969 + 3 ^ 40 * 115884 * 2
def baseEnd_115884 : Nat := 19834730721909945672355

theorem tailTrace_115884 : CollatzResearch.WordTrace tailWord_115884 prefixEnd_115884 19834730721909945672355 := by
  unfold tailWord_115884
  simp only [CollatzResearch.WordTrace]
  refine ⟨2113318356089767128317353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2817757808119689504423137 2113318356089767128317353)
  ·
    refine ⟨1584988767067325346238015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2113318356089767128317353 1584988767067325346238015)
    ·
      refine ⟨2377483150600988019357023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1584988767067325346238015 2377483150600988019357023)
      ·
        refine ⟨3566224725901482029035535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2377483150600988019357023 3566224725901482029035535)
        ·
          refine ⟨5349337088852223043553303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3566224725901482029035535 5349337088852223043553303)
          ·
            refine ⟨8024005633278334565329955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5349337088852223043553303 8024005633278334565329955)
            ·
              refine ⟨12036008449917501847994933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8024005633278334565329955 12036008449917501847994933)
              ·
                refine ⟨1128375792179765798249525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12036008449917501847994933 1128375792179765798249525)
                ·
                  refine ⟨105785230516853043585893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1128375792179765798249525 105785230516853043585893)
                  ·
                    refine ⟨19834730721909945672355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105785230516853043585893 19834730721909945672355)
                    ·
                      rfl

theorem cell23_115884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 4].length) (baseStart_115884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115884 prefixEnd_115884 := by exact prefixLift 115884
  have htrace : WordTrace (prefixWord ++ tailWord_115884) baseStart_115884 baseEnd_115884 := by
    simpa [prefixWord, tailWord_115884, baseEnd_115884] using wordTrace_append hprefix tailTrace_115884
  have hstable : (prefixWord ++ tailWord_115884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115884).length < 2 ^ (prefixWord ++ tailWord_115884).sum := by decide
  have hdescent : baseEnd_115884 < baseStart_115884 := by decide
  rcases family_descends (prefixWord ++ tailWord_115884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115908 : List Nat := [2, 3, 3, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_115908 : Nat := 118140960795 + 115908 * 2 ^ 59
def prefixEnd_115908 : Nat := 4983230072969 + 3 ^ 40 * 115908 * 2
def baseEnd_115908 : Nat := 59516515701437743116955

theorem tailTrace_115908 : CollatzResearch.WordTrace tailWord_115908 prefixEnd_115908 59516515701437743116955 := by
  unfold tailWord_115908
  simp only [CollatzResearch.WordTrace]
  refine ⟨2113756032046293177754189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2818341376061724237005585 2113756032046293177754189)
  ·
    refine ⟨792658512017359941657821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2113756032046293177754189 792658512017359941657821)
    ·
      refine ⟨297246942006509978121683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 792658512017359941657821 297246942006509978121683)
      ·
        refine ⟨445870413009764967182525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297246942006509978121683 445870413009764967182525)
        ·
          refine ⟨167201404878661862693447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445870413009764967182525 167201404878661862693447)
          ·
            refine ⟨250802107317992794040171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167201404878661862693447 250802107317992794040171)
            ·
              refine ⟨376203160976989191060257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250802107317992794040171 376203160976989191060257)
              ·
                refine ⟨282152370732741893295193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376203160976989191060257 282152370732741893295193)
                ·
                  refine ⟨211614278049556419971395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282152370732741893295193 211614278049556419971395)
                  ·
                    refine ⟨317421417074334629957093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 211614278049556419971395 317421417074334629957093)
                    ·
                      refine ⟨59516515701437743116955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 317421417074334629957093 59516515701437743116955)
                      ·
                        rfl

theorem cell23_115908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_115908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115908 prefixEnd_115908 := by exact prefixLift 115908
  have htrace : WordTrace (prefixWord ++ tailWord_115908) baseStart_115908 baseEnd_115908 := by
    simpa [prefixWord, tailWord_115908, baseEnd_115908] using wordTrace_append hprefix tailTrace_115908
  have hstable : (prefixWord ++ tailWord_115908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115908).length < 2 ^ (prefixWord ++ tailWord_115908).sum := by decide
  have hdescent : baseEnd_115908 < baseStart_115908 := by decide
  rcases family_descends (prefixWord ++ tailWord_115908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115914 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 8]
def baseStart_115914 : Nat := 118140960795 + 115914 * 2 ^ 59
def prefixEnd_115914 : Nat := 4983230072969 + 3 ^ 40 * 115914 * 2
def baseEnd_115914 : Nat := 6613288509484968849103

theorem tailTrace_115914 : CollatzResearch.WordTrace tailWord_115914 prefixEnd_115914 6613288509484968849103 := by
  unfold tailWord_115914
  simp only [CollatzResearch.WordTrace]
  refine ⟨1056932725517712345056699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2818487268047232920151197 1056932725517712345056699)
  ·
    refine ⟨1585399088276568517585049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1056932725517712345056699 1585399088276568517585049)
    ·
      refine ⟨1189049316207426388188787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1585399088276568517585049 1189049316207426388188787)
      ·
        refine ⟨1783573974311139582283181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1189049316207426388188787 1783573974311139582283181)
        ·
          refine ⟨668840240366677343356193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1783573974311139582283181 668840240366677343356193)
          ·
            refine ⟨501630180275008007517145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 668840240366677343356193 501630180275008007517145)
            ·
              refine ⟨376222635206256005637859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501630180275008007517145 376222635206256005637859)
              ·
                refine ⟨564333952809384008456789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376222635206256005637859 564333952809384008456789)
                ·
                  refine ⟨6613288509484968849103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 564333952809384008456789 6613288509484968849103)
                  ·
                    rfl

theorem cell23_115914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 8].length) (baseStart_115914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115914 prefixEnd_115914 := by exact prefixLift 115914
  have htrace : WordTrace (prefixWord ++ tailWord_115914) baseStart_115914 baseEnd_115914 := by
    simpa [prefixWord, tailWord_115914, baseEnd_115914] using wordTrace_append hprefix tailTrace_115914
  have hstable : (prefixWord ++ tailWord_115914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115914).length < 2 ^ (prefixWord ++ tailWord_115914).sum := by decide
  have hdescent : baseEnd_115914 < baseStart_115914 := by decide
  rcases family_descends (prefixWord ++ tailWord_115914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115991 : List Nat := [1, 1, 3, 4, 1, 1, 4, 1, 1, 6]
def baseStart_115991 : Nat := 118140960795 + 115991 * 2 ^ 59
def prefixEnd_115991 : Nat := 4983230072969 + 3 ^ 40 * 115991 * 2
def baseEnd_115991 : Nat := 19853044865253639459691

theorem tailTrace_115991 : CollatzResearch.WordTrace tailWord_115991 prefixEnd_115991 19853044865253639459691 := by
  unfold tailWord_115991
  simp only [CollatzResearch.WordTrace]
  refine ⟨4230539322791891530779827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2820359548527927687186551 4230539322791891530779827)
  ·
    refine ⟨6345808984187837296169741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4230539322791891530779827 6345808984187837296169741)
    ·
      refine ⟨2379678369070438986063653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6345808984187837296169741 2379678369070438986063653)
      ·
        refine ⟨446189694200707309886935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2379678369070438986063653 446189694200707309886935)
        ·
          refine ⟨669284541301060964830403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446189694200707309886935 669284541301060964830403)
          ·
            refine ⟨1003926811951591447245605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669284541301060964830403 1003926811951591447245605)
            ·
              refine ⟨188236277240923396358551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1003926811951591447245605 188236277240923396358551)
              ·
                refine ⟨282354415861385094537827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188236277240923396358551 282354415861385094537827)
                ·
                  refine ⟨423531623792077641806741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282354415861385094537827 423531623792077641806741)
                  ·
                    refine ⟨19853044865253639459691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 423531623792077641806741 19853044865253639459691)
                    ·
                      rfl

theorem cell23_115991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_115991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_115991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_115991 prefixEnd_115991 := by exact prefixLift 115991
  have htrace : WordTrace (prefixWord ++ tailWord_115991) baseStart_115991 baseEnd_115991 := by
    simpa [prefixWord, tailWord_115991, baseEnd_115991] using wordTrace_append hprefix tailTrace_115991
  have hstable : (prefixWord ++ tailWord_115991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115991).length < 2 ^ (prefixWord ++ tailWord_115991).sum := by decide
  have hdescent : baseEnd_115991 < baseStart_115991 := by decide
  rcases family_descends (prefixWord ++ tailWord_115991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116002 : List Nat := [3, 3, 1, 1, 4, 2, 1, 1, 2, 3, 2]
def baseStart_116002 : Nat := 118140960795 + 116002 * 2 ^ 59
def prefixEnd_116002 : Nat := 4983230072969 + 3 ^ 40 * 116002 * 2
def baseEnd_116002 : Nat := 59564782882960375341523

theorem tailTrace_116002 : CollatzResearch.WordTrace tailWord_116002 prefixEnd_116002 59564782882960375341523 := by
  unfold tailWord_116002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1057735131438010102357565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2820627017168026939620173 1057735131438010102357565)
  ·
    refine ⟨396650674289253788384087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1057735131438010102357565 396650674289253788384087)
    ·
      refine ⟨594976011433880682576131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396650674289253788384087 594976011433880682576131)
      ·
        refine ⟨892464017150821023864197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594976011433880682576131 892464017150821023864197)
        ·
          refine ⟨167337003215778941974537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 892464017150821023864197 167337003215778941974537)
          ·
            refine ⟨125502752411834206480903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167337003215778941974537 125502752411834206480903)
            ·
              refine ⟨188254128617751309721355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125502752411834206480903 188254128617751309721355)
              ·
                refine ⟨282381192926626964582033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188254128617751309721355 282381192926626964582033)
                ·
                  refine ⟨211785894694970223436525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282381192926626964582033 211785894694970223436525)
                  ·
                    refine ⟨79419710510613833788697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 211785894694970223436525 79419710510613833788697)
                    ·
                      refine ⟨59564782882960375341523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 79419710510613833788697 59564782882960375341523)
                      ·
                        rfl

theorem cell23_116002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_116002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116002 prefixEnd_116002 := by exact prefixLift 116002
  have htrace : WordTrace (prefixWord ++ tailWord_116002) baseStart_116002 baseEnd_116002 := by
    simpa [prefixWord, tailWord_116002, baseEnd_116002] using wordTrace_append hprefix tailTrace_116002
  have hstable : (prefixWord ++ tailWord_116002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116002).length < 2 ^ (prefixWord ++ tailWord_116002).sum := by decide
  have hdescent : baseEnd_116002 < baseStart_116002 := by decide
  rcases family_descends (prefixWord ++ tailWord_116002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116024 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 2, 2, 6]
def baseStart_116024 : Nat := 118140960795 + 116024 * 2 ^ 59
def prefixEnd_116024 : Nat := 4983230072969 + 3 ^ 40 * 116024 * 2
def baseEnd_116024 : Nat := 59576079457359289266421

theorem tailTrace_116024 : CollatzResearch.WordTrace tailWord_116024 prefixEnd_116024 59576079457359289266421 := by
  unfold tailWord_116024
  simp only [CollatzResearch.WordTrace]
  refine ⟨2115871465836169083365563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2821161954448225444487417 2115871465836169083365563)
  ·
    refine ⟨3173807198754253625048345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2115871465836169083365563 3173807198754253625048345)
    ·
      refine ⟨2380355399065690218786259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3173807198754253625048345 2380355399065690218786259)
      ·
        refine ⟨3570533098598535328179389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2380355399065690218786259 3570533098598535328179389)
        ·
          refine ⟨1338949911974450748067271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3570533098598535328179389 1338949911974450748067271)
          ·
            refine ⟨2008424867961676122100907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338949911974450748067271 2008424867961676122100907)
            ·
              refine ⟨3012637301942514183151361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008424867961676122100907 3012637301942514183151361)
              ·
                refine ⟨2259477976456885637363521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3012637301942514183151361 2259477976456885637363521)
                ·
                  refine ⟨1694608482342664228022641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2259477976456885637363521 1694608482342664228022641)
                  ·
                    refine ⟨1270956361756998171016981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1694608482342664228022641 1270956361756998171016981)
                    ·
                      refine ⟨59576079457359289266421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1270956361756998171016981 59576079457359289266421)
                      ·
                        rfl

theorem cell23_116024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_116024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116024 prefixEnd_116024 := by exact prefixLift 116024
  have htrace : WordTrace (prefixWord ++ tailWord_116024) baseStart_116024 baseEnd_116024 := by
    simpa [prefixWord, tailWord_116024, baseEnd_116024] using wordTrace_append hprefix tailTrace_116024
  have hstable : (prefixWord ++ tailWord_116024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116024).length < 2 ^ (prefixWord ++ tailWord_116024).sum := by decide
  have hdescent : baseEnd_116024 < baseStart_116024 := by decide
  rcases family_descends (prefixWord ++ tailWord_116024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116045 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_116045 : Nat := 118140960795 + 116045 * 2 ^ 59
def prefixEnd_116045 : Nat := 4983230072969 + 3 ^ 40 * 116045 * 2
def baseEnd_116045 : Nat := 59586862551103707103825

theorem tailTrace_116045 : CollatzResearch.WordTrace tailWord_116045 prefixEnd_116045 59586862551103707103825 := by
  unfold tailWord_116045
  simp only [CollatzResearch.WordTrace]
  refine ⟨4232508864596258753245589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2821672576397505835497059 4232508864596258753245589)
  ·
    refine ⟨198398853027949629058387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4232508864596258753245589 198398853027949629058387)
    ·
      refine ⟨297598279541924443587581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198398853027949629058387 297598279541924443587581)
      ·
        refine ⟨111599354828221666345343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297598279541924443587581 111599354828221666345343)
        ·
          refine ⟨167399032242332499518015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111599354828221666345343 167399032242332499518015)
          ·
            refine ⟨251098548363498749277023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167399032242332499518015 251098548363498749277023)
            ·
              refine ⟨376647822545248123915535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251098548363498749277023 376647822545248123915535)
              ·
                refine ⟨564971733817872185873303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376647822545248123915535 564971733817872185873303)
                ·
                  refine ⟨847457600726808278809955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 564971733817872185873303 847457600726808278809955)
                  ·
                    refine ⟨1271186401090212418214933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 847457600726808278809955 1271186401090212418214933)
                    ·
                      refine ⟨59586862551103707103825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1271186401090212418214933 59586862551103707103825)
                      ·
                        rfl

theorem cell23_116045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_116045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116045 prefixEnd_116045 := by exact prefixLift 116045
  have htrace : WordTrace (prefixWord ++ tailWord_116045) baseStart_116045 baseEnd_116045 := by
    simpa [prefixWord, tailWord_116045, baseEnd_116045] using wordTrace_append hprefix tailTrace_116045
  have hstable : (prefixWord ++ tailWord_116045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116045).length < 2 ^ (prefixWord ++ tailWord_116045).sum := by decide
  have hdescent : baseEnd_116045 < baseStart_116045 := by decide
  rcases family_descends (prefixWord ++ tailWord_116045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116058 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2]
def baseStart_116058 : Nat := 118140960795 + 116058 * 2 ^ 59
def prefixEnd_116058 : Nat := 4983230072969 + 3 ^ 40 * 116058 * 2
def baseEnd_116058 : Nat := 59593537799612156241265

theorem tailTrace_116058 : CollatzResearch.WordTrace tailWord_116058 prefixEnd_116058 59593537799612156241265 := by
  unfold tailWord_116058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1058245753387290493367207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2821988675699441315645885 1058245753387290493367207)
  ·
    refine ⟨1587368630080935740050811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1058245753387290493367207 1587368630080935740050811)
    ·
      refine ⟨2381052945121403610076217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1587368630080935740050811 2381052945121403610076217)
      ·
        refine ⟨1785789708841052707557163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2381052945121403610076217 1785789708841052707557163)
        ·
          refine ⟨2678684563261579061335745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1785789708841052707557163 2678684563261579061335745)
          ·
            refine ⟨2009013422446184296001809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2678684563261579061335745 2009013422446184296001809)
            ·
              refine ⟨1506760066834638222001357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2009013422446184296001809 1506760066834638222001357)
              ·
                refine ⟨565035025062989333250509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1506760066834638222001357 565035025062989333250509)
                ·
                  refine ⟨211888134398620999968941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565035025062989333250509 211888134398620999968941)
                  ·
                    refine ⟨79458050399482874988353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 211888134398620999968941 79458050399482874988353)
                    ·
                      refine ⟨59593537799612156241265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 79458050399482874988353 59593537799612156241265)
                      ·
                        rfl

theorem cell23_116058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_116058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116058 prefixEnd_116058 := by exact prefixLift 116058
  have htrace : WordTrace (prefixWord ++ tailWord_116058) baseStart_116058 baseEnd_116058 := by
    simpa [prefixWord, tailWord_116058, baseEnd_116058] using wordTrace_append hprefix tailTrace_116058
  have hstable : (prefixWord ++ tailWord_116058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116058).length < 2 ^ (prefixWord ++ tailWord_116058).sum := by decide
  have hdescent : baseEnd_116058 < baseStart_116058 := by decide
  rcases family_descends (prefixWord ++ tailWord_116058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116091 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 3]
def baseStart_116091 : Nat := 118140960795 + 116091 * 2 ^ 59
def prefixEnd_116091 : Nat := 4983230072969 + 3 ^ 40 * 116091 * 2
def baseEnd_116091 : Nat := 59610482661210527128613

theorem tailTrace_116091 : CollatzResearch.WordTrace tailWord_116091 prefixEnd_116091 59610482661210527128613 := by
  unfold tailWord_116091
  simp only [CollatzResearch.WordTrace]
  refine ⟨4234186622429608609420127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2822791081619739072946751 4234186622429608609420127)
  ·
    refine ⟨6351279933644412914130191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4234186622429608609420127 6351279933644412914130191)
    ·
      refine ⟨9526919900466619371195287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6351279933644412914130191 9526919900466619371195287)
      ·
        refine ⟨14290379850699929056792931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9526919900466619371195287 14290379850699929056792931)
        ·
          refine ⟨21435569776049893585189397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14290379850699929056792931 21435569776049893585189397)
          ·
            refine ⟨1004792333252338761805753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21435569776049893585189397 1004792333252338761805753)
            ·
              refine ⟨753594249939254071354315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1004792333252338761805753 753594249939254071354315)
              ·
                refine ⟨1130391374908881107031473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753594249939254071354315 1130391374908881107031473)
                ·
                  refine ⟨847793531181660830273605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1130391374908881107031473 847793531181660830273605)
                  ·
                    refine ⟨158961287096561405676301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 847793531181660830273605 158961287096561405676301)
                    ·
                      refine ⟨59610482661210527128613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 158961287096561405676301 59610482661210527128613)
                      ·
                        rfl

theorem cell23_116091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 3].length) (baseStart_116091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116091 prefixEnd_116091 := by exact prefixLift 116091
  have htrace : WordTrace (prefixWord ++ tailWord_116091) baseStart_116091 baseEnd_116091 := by
    simpa [prefixWord, tailWord_116091, baseEnd_116091] using wordTrace_append hprefix tailTrace_116091
  have hstable : (prefixWord ++ tailWord_116091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116091).length < 2 ^ (prefixWord ++ tailWord_116091).sum := by decide
  have hdescent : baseEnd_116091 < baseStart_116091 := by decide
  rcases family_descends (prefixWord ++ tailWord_116091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116101 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 2, 2, 4]
def baseStart_116101 : Nat := 118140960795 + 116101 * 2 ^ 59
def prefixEnd_116101 : Nat := 4983230072969 + 3 ^ 40 * 116101 * 2
def baseEnd_116101 : Nat := 59615617467755488003567

theorem tailTrace_116101 : CollatzResearch.WordTrace tailWord_116101 prefixEnd_116101 59615617467755488003567 := by
  unfold tailWord_116101
  simp only [CollatzResearch.WordTrace]
  refine ⟨4234551352393380317284157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2823034234928920211522771 4234551352393380317284157)
  ·
    refine ⟨1587956757147517618981559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4234551352393380317284157 1587956757147517618981559)
    ·
      refine ⟨2381935135721276428472339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1587956757147517618981559 2381935135721276428472339)
      ·
        refine ⟨3572902703581914642708509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2381935135721276428472339 3572902703581914642708509)
        ·
          refine ⟨1339838513843217991015691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3572902703581914642708509 1339838513843217991015691)
          ·
            refine ⟨2009757770764826986523537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1339838513843217991015691 2009757770764826986523537)
            ·
              refine ⟨1507318328073620239892653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2009757770764826986523537 1507318328073620239892653)
              ·
                refine ⟨565244373027607589959745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1507318328073620239892653 565244373027607589959745)
                ·
                  refine ⟨423933279770705692469809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565244373027607589959745 423933279770705692469809)
                  ·
                    refine ⟨317949959828029269352357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 423933279770705692469809 317949959828029269352357)
                    ·
                      refine ⟨59615617467755488003567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 317949959828029269352357 59615617467755488003567)
                      ·
                        rfl

theorem cell23_116101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_116101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116101 prefixEnd_116101 := by exact prefixLift 116101
  have htrace : WordTrace (prefixWord ++ tailWord_116101) baseStart_116101 baseEnd_116101 := by
    simpa [prefixWord, tailWord_116101, baseEnd_116101] using wordTrace_append hprefix tailTrace_116101
  have hstable : (prefixWord ++ tailWord_116101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116101).length < 2 ^ (prefixWord ++ tailWord_116101).sum := by decide
  have hdescent : baseEnd_116101 < baseStart_116101 := by decide
  rcases family_descends (prefixWord ++ tailWord_116101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116126 : List Nat := [4, 3, 1, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_116126 : Nat := 118140960795 + 116126 * 2 ^ 59
def prefixEnd_116126 : Nat := 4983230072969 + 3 ^ 40 * 116126 * 2
def baseEnd_116126 : Nat := 59628454484117890190953

theorem tailTrace_116126 : CollatzResearch.WordTrace tailWord_116126 prefixEnd_116126 59628454484117890190953 := by
  unfold tailWord_116126
  simp only [CollatzResearch.WordTrace]
  refine ⟨529432897162851198368029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2823642118201873057962821 529432897162851198368029)
  ·
    refine ⟨198537336436069199388011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 529432897162851198368029 198537336436069199388011)
    ·
      refine ⟨297806004654103799082017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198537336436069199388011 297806004654103799082017)
      ·
        refine ⟨223354503490577849311513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297806004654103799082017 223354503490577849311513)
        ·
          refine ⟨167515877617933386983635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223354503490577849311513 167515877617933386983635)
          ·
            refine ⟨251273816426900080475453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167515877617933386983635 251273816426900080475453)
            ·
              refine ⟨94227681160087530178295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251273816426900080475453 94227681160087530178295)
              ·
                refine ⟨141341521740131295267443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94227681160087530178295 141341521740131295267443)
                ·
                  refine ⟨212012282610196942901165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141341521740131295267443 212012282610196942901165)
                  ·
                    refine ⟨79504605978823853587937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212012282610196942901165 79504605978823853587937)
                    ·
                      refine ⟨59628454484117890190953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 79504605978823853587937 59628454484117890190953)
                      ·
                        rfl

theorem cell23_116126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_116126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116126 prefixEnd_116126 := by exact prefixLift 116126
  have htrace : WordTrace (prefixWord ++ tailWord_116126) baseStart_116126 baseEnd_116126 := by
    simpa [prefixWord, tailWord_116126, baseEnd_116126] using wordTrace_append hprefix tailTrace_116126
  have hstable : (prefixWord ++ tailWord_116126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116126).length < 2 ^ (prefixWord ++ tailWord_116126).sum := by decide
  have hdescent : baseEnd_116126 < baseStart_116126 := by decide
  rcases family_descends (prefixWord ++ tailWord_116126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116128 : List Nat := [2, 1, 1, 4, 1, 2, 2, 5, 5]
def baseStart_116128 : Nat := 118140960795 + 116128 * 2 ^ 59
def prefixEnd_116128 : Nat := 4983230072969 + 3 ^ 40 * 116128 * 2
def baseEnd_116128 : Nat := 6625497938380764707327

theorem tailTrace_116128 : CollatzResearch.WordTrace tailWord_116128 prefixEnd_116128 6625497938380764707327 := by
  unfold tailWord_116128
  simp only [CollatzResearch.WordTrace]
  refine ⟨2117768061647781964258519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2823690748863709285678025 2117768061647781964258519)
  ·
    refine ⟨3176652092471672946387779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2117768061647781964258519 3176652092471672946387779)
    ·
      refine ⟨4764978138707509419581669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3176652092471672946387779 4764978138707509419581669)
      ·
        refine ⟨893433401007658016171563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4764978138707509419581669 893433401007658016171563)
        ·
          refine ⟨1340150101511487024257345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893433401007658016171563 1340150101511487024257345)
          ·
            refine ⟨1005112576133615268193009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1340150101511487024257345 1005112576133615268193009)
            ·
              refine ⟨753834432100211451144757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1005112576133615268193009 753834432100211451144757)
              ·
                refine ⟨70671978009394823544821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 753834432100211451144757 70671978009394823544821)
                ·
                  refine ⟨6625497938380764707327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70671978009394823544821 6625497938380764707327)
                  ·
                    rfl

theorem cell23_116128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 5].length) (baseStart_116128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116128 prefixEnd_116128 := by exact prefixLift 116128
  have htrace : WordTrace (prefixWord ++ tailWord_116128) baseStart_116128 baseEnd_116128 := by
    simpa [prefixWord, tailWord_116128, baseEnd_116128] using wordTrace_append hprefix tailTrace_116128
  have hstable : (prefixWord ++ tailWord_116128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116128).length < 2 ^ (prefixWord ++ tailWord_116128).sum := by decide
  have hdescent : baseEnd_116128 < baseStart_116128 := by decide
  rcases family_descends (prefixWord ++ tailWord_116128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116151 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 5]
def baseStart_116151 : Nat := 118140960795 + 116151 * 2 ^ 59
def prefixEnd_116151 : Nat := 4983230072969 + 3 ^ 40 * 116151 * 2
def baseEnd_116151 : Nat := 59641291500480292378337

theorem tailTrace_116151 : CollatzResearch.WordTrace tailWord_116151 prefixEnd_116151 59641291500480292378337 := by
  unfold tailWord_116151
  simp only [CollatzResearch.WordTrace]
  refine ⟨4236375002212238856604307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2824250001474825904402871 4236375002212238856604307)
  ·
    refine ⟨6354562503318358284906461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4236375002212238856604307 6354562503318358284906461)
    ·
      refine ⟨2382960938744384356839923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6354562503318358284906461 2382960938744384356839923)
      ·
        refine ⟨3574441408116576535259885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2382960938744384356839923 3574441408116576535259885)
        ·
          refine ⟨1340415528043716200722457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3574441408116576535259885 1340415528043716200722457)
          ·
            refine ⟨1005311646032787150541843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1340415528043716200722457 1005311646032787150541843)
            ·
              refine ⟨1507967469049180725812765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005311646032787150541843 1507967469049180725812765)
              ·
                refine ⟨565487800893442772179787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1507967469049180725812765 565487800893442772179787)
                ·
                  refine ⟨848231701340164158269681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565487800893442772179787 848231701340164158269681)
                  ·
                    refine ⟨636173776005123118702261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 848231701340164158269681 636173776005123118702261)
                    ·
                      refine ⟨59641291500480292378337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 636173776005123118702261 59641291500480292378337)
                      ·
                        rfl

theorem cell23_116151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_116151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116151 prefixEnd_116151 := by exact prefixLift 116151
  have htrace : WordTrace (prefixWord ++ tailWord_116151) baseStart_116151 baseEnd_116151 := by
    simpa [prefixWord, tailWord_116151, baseEnd_116151] using wordTrace_append hprefix tailTrace_116151
  have hstable : (prefixWord ++ tailWord_116151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116151).length < 2 ^ (prefixWord ++ tailWord_116151).sum := by decide
  have hdescent : baseEnd_116151 < baseStart_116151 := by decide
  rcases family_descends (prefixWord ++ tailWord_116151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116191 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 6]
def baseStart_116191 : Nat := 118140960795 + 116191 * 2 ^ 59
def prefixEnd_116191 : Nat := 4983230072969 + 3 ^ 40 * 116191 * 2
def baseEnd_116191 : Nat := 59661830726660135878153

theorem tailTrace_116191 : CollatzResearch.WordTrace tailWord_116191 prefixEnd_116191 59661830726660135878153 := by
  unfold tailWord_116191
  simp only [CollatzResearch.WordTrace]
  refine ⟨4237833922067325688060427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2825222614711550458706951 4237833922067325688060427)
  ·
    refine ⟨6356750883100988532090641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4237833922067325688060427 6356750883100988532090641)
    ·
      refine ⟨4767563162325741399067981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6356750883100988532090641 4767563162325741399067981)
      ·
        refine ⟨1787836185872153024650493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4767563162325741399067981 1787836185872153024650493)
        ·
          refine ⟨670438569702057384243935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1787836185872153024650493 670438569702057384243935)
          ·
            refine ⟨1005657854553086076365903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670438569702057384243935 1005657854553086076365903)
            ·
              refine ⟨1508486781829629114548855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005657854553086076365903 1508486781829629114548855)
              ·
                refine ⟨2262730172744443671823283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508486781829629114548855 2262730172744443671823283)
                ·
                  refine ⟨3394095259116665507734925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2262730172744443671823283 3394095259116665507734925)
                  ·
                    refine ⟨1272785722168749565400597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3394095259116665507734925 1272785722168749565400597)
                    ·
                      refine ⟨59661830726660135878153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1272785722168749565400597 59661830726660135878153)
                      ·
                        rfl

theorem cell23_116191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_116191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116191 prefixEnd_116191 := by exact prefixLift 116191
  have htrace : WordTrace (prefixWord ++ tailWord_116191) baseStart_116191 baseEnd_116191 := by
    simpa [prefixWord, tailWord_116191, baseEnd_116191] using wordTrace_append hprefix tailTrace_116191
  have hstable : (prefixWord ++ tailWord_116191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116191).length < 2 ^ (prefixWord ++ tailWord_116191).sum := by decide
  have hdescent : baseEnd_116191 < baseStart_116191 := by decide
  rcases family_descends (prefixWord ++ tailWord_116191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116195 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 2, 4, 2]
def baseStart_116195 : Nat := 118140960795 + 116195 * 2 ^ 59
def prefixEnd_116195 : Nat := 4983230072969 + 3 ^ 40 * 116195 * 2
def baseEnd_116195 : Nat := 59663884649278120228135

theorem tailTrace_116195 : CollatzResearch.WordTrace tailWord_116195 prefixEnd_116195 59663884649278120228135 := by
  unfold tailWord_116195
  simp only [CollatzResearch.WordTrace]
  refine ⟨4237979814052834371206039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2825319876035222914137359 4237979814052834371206039)
  ·
    refine ⟨6356969721079251556809059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4237979814052834371206039 6356969721079251556809059)
    ·
      refine ⟨9535454581618877335213589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6356969721079251556809059 9535454581618877335213589)
      ·
        refine ⟨446974433513384875088137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9535454581618877335213589 446974433513384875088137)
        ·
          refine ⟨335230825135038656316103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446974433513384875088137 335230825135038656316103)
          ·
            refine ⟨502846237702557984474155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335230825135038656316103 502846237702557984474155)
            ·
              refine ⟨754269356553836976711233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502846237702557984474155 754269356553836976711233)
              ·
                refine ⟨565702017415377732533425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754269356553836976711233 565702017415377732533425)
                ·
                  refine ⟨424276513061533299400069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565702017415377732533425 424276513061533299400069)
                  ·
                    refine ⟨79551846199037493637513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 424276513061533299400069 79551846199037493637513)
                    ·
                      refine ⟨59663884649278120228135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 79551846199037493637513 59663884649278120228135)
                      ·
                        rfl

theorem cell23_116195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_116195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116195 prefixEnd_116195 := by exact prefixLift 116195
  have htrace : WordTrace (prefixWord ++ tailWord_116195) baseStart_116195 baseEnd_116195 := by
    simpa [prefixWord, tailWord_116195, baseEnd_116195] using wordTrace_append hprefix tailTrace_116195
  have hstable : (prefixWord ++ tailWord_116195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116195).length < 2 ^ (prefixWord ++ tailWord_116195).sum := by decide
  have hdescent : baseEnd_116195 < baseStart_116195 := by decide
  rcases family_descends (prefixWord ++ tailWord_116195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116255 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 4, 3, 2]
def baseStart_116255 : Nat := 118140960795 + 116255 * 2 ^ 59
def prefixEnd_116255 : Nat := 4983230072969 + 3 ^ 40 * 116255 * 2
def baseEnd_116255 : Nat := 59694693488547885477859

theorem tailTrace_116255 : CollatzResearch.WordTrace tailWord_116255 prefixEnd_116255 59694693488547885477859 := by
  unfold tailWord_116255
  simp only [CollatzResearch.WordTrace]
  refine ⟨4240168193835464618390219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2826778795890309745593479 4240168193835464618390219)
  ·
    refine ⟨6360252290753196927585329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4240168193835464618390219 6360252290753196927585329)
    ·
      refine ⟨4770189218064897695688997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6360252290753196927585329 4770189218064897695688997)
      ·
        refine ⟨894410478387168317941687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4770189218064897695688997 894410478387168317941687)
        ·
          refine ⟨1341615717580752476912531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894410478387168317941687 1341615717580752476912531)
          ·
            refine ⟨2012423576371128715368797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1341615717580752476912531 2012423576371128715368797)
            ·
              refine ⟨754658841139173268263299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2012423576371128715368797 754658841139173268263299)
              ·
                refine ⟨1131988261708759902394949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 754658841139173268263299 1131988261708759902394949)
                ·
                  refine ⟨212247799070392481699053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1131988261708759902394949 212247799070392481699053)
                  ·
                    refine ⟨79592924651397180637145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212247799070392481699053 79592924651397180637145)
                    ·
                      refine ⟨59694693488547885477859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 79592924651397180637145 59694693488547885477859)
                      ·
                        rfl

theorem cell23_116255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_116255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116255 prefixEnd_116255 := by exact prefixLift 116255
  have htrace : WordTrace (prefixWord ++ tailWord_116255) baseStart_116255 baseEnd_116255 := by
    simpa [prefixWord, tailWord_116255, baseEnd_116255] using wordTrace_append hprefix tailTrace_116255
  have hstable : (prefixWord ++ tailWord_116255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116255).length < 2 ^ (prefixWord ++ tailWord_116255).sum := by decide
  have hdescent : baseEnd_116255 < baseStart_116255 := by decide
  rcases family_descends (prefixWord ++ tailWord_116255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116295 : List Nat := [1, 1, 4, 1, 5, 1, 1, 2, 1, 6]
def baseStart_116295 : Nat := 118140960795 + 116295 * 2 ^ 59
def prefixEnd_116295 : Nat := 4983230072969 + 3 ^ 40 * 116295 * 2
def baseEnd_116295 : Nat := 19905077571575909659225

theorem tailTrace_116295 : CollatzResearch.WordTrace tailWord_116295 prefixEnd_116295 19905077571575909659225 := by
  unfold tailWord_116295
  simp only [CollatzResearch.WordTrace]
  refine ⟨4241627113690551449846339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2827751409127034299897559 4241627113690551449846339)
  ·
    refine ⟨6362440670535827174769509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4241627113690551449846339 6362440670535827174769509)
    ·
      refine ⟨1192957625725467595269283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6362440670535827174769509 1192957625725467595269283)
      ·
        refine ⟨1789436438588201392903925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1192957625725467595269283 1789436438588201392903925)
        ·
          refine ⟨167759666117643880584743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1789436438588201392903925 167759666117643880584743)
          ·
            refine ⟨251639499176465820877115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167759666117643880584743 251639499176465820877115)
            ·
              refine ⟨377459248764698731315673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251639499176465820877115 377459248764698731315673)
              ·
                refine ⟨283094436573524048486755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377459248764698731315673 283094436573524048486755)
                ·
                  refine ⟨424641654860286072730133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283094436573524048486755 424641654860286072730133)
                  ·
                    refine ⟨19905077571575909659225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 424641654860286072730133 19905077571575909659225)
                    ·
                      rfl

theorem cell23_116295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_116295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116295 prefixEnd_116295 := by exact prefixLift 116295
  have htrace : WordTrace (prefixWord ++ tailWord_116295) baseStart_116295 baseEnd_116295 := by
    simpa [prefixWord, tailWord_116295, baseEnd_116295] using wordTrace_append hprefix tailTrace_116295
  have hstable : (prefixWord ++ tailWord_116295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116295).length < 2 ^ (prefixWord ++ tailWord_116295).sum := by decide
  have hdescent : baseEnd_116295 < baseStart_116295 := by decide
  rcases family_descends (prefixWord ++ tailWord_116295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116325 : List Nat := [1, 3, 1, 3, 3, 3, 1, 8]
def baseStart_116325 : Nat := 118140960795 + 116325 * 2 ^ 59
def prefixEnd_116325 : Nat := 4983230072969 + 3 ^ 40 * 116325 * 2
def baseEnd_116325 : Nat := 2212245819791207837131

theorem tailTrace_116325 : CollatzResearch.WordTrace tailWord_116325 prefixEnd_116325 2212245819791207837131 := by
  unfold tailWord_116325
  simp only [CollatzResearch.WordTrace]
  refine ⟨4242721303581866573438429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2828480869054577715625619 4242721303581866573438429)
  ·
    refine ⟨1591020488843199965039411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4242721303581866573438429 1591020488843199965039411)
    ·
      refine ⟨2386530733264799947559117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1591020488843199965039411 2386530733264799947559117)
      ·
        refine ⟨894949024974299980334669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2386530733264799947559117 894949024974299980334669)
        ·
          refine ⟨335605884365362492625501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 894949024974299980334669 335605884365362492625501)
          ·
            refine ⟨125852206637010934734563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335605884365362492625501 125852206637010934734563)
            ·
              refine ⟨188778309955516402101845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125852206637010934734563 188778309955516402101845)
              ·
                refine ⟨2212245819791207837131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 188778309955516402101845 2212245819791207837131)
                ·
                  rfl

theorem cell23_116325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 8].length) (baseStart_116325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116325 prefixEnd_116325 := by exact prefixLift 116325
  have htrace : WordTrace (prefixWord ++ tailWord_116325) baseStart_116325 baseEnd_116325 := by
    simpa [prefixWord, tailWord_116325, baseEnd_116325] using wordTrace_append hprefix tailTrace_116325
  have hstable : (prefixWord ++ tailWord_116325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116325).length < 2 ^ (prefixWord ++ tailWord_116325).sum := by decide
  have hdescent : baseEnd_116325 < baseStart_116325 := by decide
  rcases family_descends (prefixWord ++ tailWord_116325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116335 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 6, 1, 3]
def baseStart_116335 : Nat := 118140960795 + 116335 * 2 ^ 59
def prefixEnd_116335 : Nat := 4983230072969 + 3 ^ 40 * 116335 * 2
def baseEnd_116335 : Nat := 59735771940907572477491

theorem tailTrace_116335 : CollatzResearch.WordTrace tailWord_116335 prefixEnd_116335 59735771940907572477491 := by
  unfold tailWord_116335
  simp only [CollatzResearch.WordTrace]
  refine ⟨4243086033545638281302459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2828724022363758854201639 4243086033545638281302459)
  ·
    refine ⟨6364629050318457421953689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4243086033545638281302459 6364629050318457421953689)
    ·
      refine ⟨4773471787738843066465267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6364629050318457421953689 4773471787738843066465267)
      ·
        refine ⟨7160207681608264599697901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4773471787738843066465267 7160207681608264599697901)
        ·
          refine ⟨2685077880603099224886713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7160207681608264599697901 2685077880603099224886713)
          ·
            refine ⟨2013808410452324418665035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2685077880603099224886713 2013808410452324418665035)
            ·
              refine ⟨3020712615678486627997553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2013808410452324418665035 3020712615678486627997553)
              ·
                refine ⟨2265534461758864970998165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3020712615678486627997553 2265534461758864970998165)
                ·
                  refine ⟨106196927894946795515539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2265534461758864970998165 106196927894946795515539)
                  ·
                    refine ⟨159295391842420193273309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106196927894946795515539 159295391842420193273309)
                    ·
                      refine ⟨59735771940907572477491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 159295391842420193273309 59735771940907572477491)
                      ·
                        rfl

theorem cell23_116335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 1, 3].length) (baseStart_116335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116335 prefixEnd_116335 := by exact prefixLift 116335
  have htrace : WordTrace (prefixWord ++ tailWord_116335) baseStart_116335 baseEnd_116335 := by
    simpa [prefixWord, tailWord_116335, baseEnd_116335] using wordTrace_append hprefix tailTrace_116335
  have hstable : (prefixWord ++ tailWord_116335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116335).length < 2 ^ (prefixWord ++ tailWord_116335).sum := by decide
  have hdescent : baseEnd_116335 < baseStart_116335 := by decide
  rcases family_descends (prefixWord ++ tailWord_116335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116342 : List Nat := [5, 1, 1, 2, 2, 2, 3, 7]
def baseStart_116342 : Nat := 118140960795 + 116342 * 2 ^ 59
def prefixEnd_116342 : Nat := 4983230072969 + 3 ^ 40 * 116342 * 2
def baseEnd_116342 : Nat := 2212569122425520188517

theorem tailTrace_116342 : CollatzResearch.WordTrace tailWord_116342 prefixEnd_116342 2212569122425520188517 := by
  unfold tailWord_116342
  simp only [CollatzResearch.WordTrace]
  refine ⟨265208834032517404800455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2828894229680185651204853 265208834032517404800455)
  ·
    refine ⟨397813251048776107200683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265208834032517404800455 397813251048776107200683)
    ·
      refine ⟨596719876573164160801025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397813251048776107200683 596719876573164160801025)
      ·
        refine ⟨447539907429873120600769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596719876573164160801025 447539907429873120600769)
        ·
          refine ⟨335654930572404840450577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447539907429873120600769 335654930572404840450577)
          ·
            refine ⟨251741197929303630337933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335654930572404840450577 251741197929303630337933)
            ·
              refine ⟨94402949223488861376725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251741197929303630337933 94402949223488861376725)
              ·
                refine ⟨2212569122425520188517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 94402949223488861376725 2212569122425520188517)
                ·
                  rfl

theorem cell23_116342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_116342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116342 prefixEnd_116342 := by exact prefixLift 116342
  have htrace : WordTrace (prefixWord ++ tailWord_116342) baseStart_116342 baseEnd_116342 := by
    simpa [prefixWord, tailWord_116342, baseEnd_116342] using wordTrace_append hprefix tailTrace_116342
  have hstable : (prefixWord ++ tailWord_116342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116342).length < 2 ^ (prefixWord ++ tailWord_116342).sum := by decide
  have hdescent : baseEnd_116342 < baseStart_116342 := by decide
  rcases family_descends (prefixWord ++ tailWord_116342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116348 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_116348 : Nat := 118140960795 + 116348 * 2 ^ 59
def prefixEnd_116348 : Nat := 4983230072969 + 3 ^ 40 * 116348 * 2
def baseEnd_116348 : Nat := 59742447189416021614931

theorem tailTrace_116348 : CollatzResearch.WordTrace tailWord_116348 prefixEnd_116348 59742447189416021614931 := by
  unfold tailWord_116348
  simp only [CollatzResearch.WordTrace]
  refine ⟨2121780091249270750762849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2829040121665694334350465 2121780091249270750762849)
  ·
    refine ⟨1591335068436953063072137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2121780091249270750762849 1591335068436953063072137)
    ·
      refine ⟨1193501301327714797304103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1591335068436953063072137 1193501301327714797304103)
      ·
        refine ⟨1790251951991572195956155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1193501301327714797304103 1790251951991572195956155)
        ·
          refine ⟨2685377927987358293934233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1790251951991572195956155 2685377927987358293934233)
          ·
            refine ⟨2014033445990518720450675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2685377927987358293934233 2014033445990518720450675)
            ·
              refine ⟨3021050168985778080676013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2014033445990518720450675 3021050168985778080676013)
              ·
                refine ⟨1132893813369666780253505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3021050168985778080676013 1132893813369666780253505)
                ·
                  refine ⟨849670360027250085190129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1132893813369666780253505 849670360027250085190129)
                  ·
                    refine ⟨637252770020437563892597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 849670360027250085190129 637252770020437563892597)
                    ·
                      refine ⟨59742447189416021614931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 637252770020437563892597 59742447189416021614931)
                      ·
                        rfl

theorem cell23_116348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_116348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116348 prefixEnd_116348 := by exact prefixLift 116348
  have htrace : WordTrace (prefixWord ++ tailWord_116348) baseStart_116348 baseEnd_116348 := by
    simpa [prefixWord, tailWord_116348, baseEnd_116348] using wordTrace_append hprefix tailTrace_116348
  have hstable : (prefixWord ++ tailWord_116348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116348).length < 2 ^ (prefixWord ++ tailWord_116348).sum := by decide
  have hdescent : baseEnd_116348 < baseStart_116348 := by decide
  rcases family_descends (prefixWord ++ tailWord_116348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116356 : List Nat := [2, 3, 2, 1, 4, 2, 2, 1, 1, 2, 3]
def baseStart_116356 : Nat := 118140960795 + 116356 * 2 ^ 59
def prefixEnd_116356 : Nat := 4983230072969 + 3 ^ 40 * 116356 * 2
def baseEnd_116356 : Nat := 59746555034651990314895

theorem tailTrace_116356 : CollatzResearch.WordTrace tailWord_116356 prefixEnd_116356 59746555034651990314895 := by
  unfold tailWord_116356
  simp only [CollatzResearch.WordTrace]
  refine ⟨2121925983234779433908461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2829234644313039245211281 2121925983234779433908461)
  ·
    refine ⟨795722243713042287715673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2121925983234779433908461 795722243713042287715673)
    ·
      refine ⟨596791682784781715786755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 795722243713042287715673 596791682784781715786755)
      ·
        refine ⟨895187524177172573680133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596791682784781715786755 895187524177172573680133)
        ·
          refine ⟨167847660783219857565025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 895187524177172573680133 167847660783219857565025)
          ·
            refine ⟨125885745587414893173769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167847660783219857565025 125885745587414893173769)
            ·
              refine ⟨94414309190561169880327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125885745587414893173769 94414309190561169880327)
              ·
                refine ⟨141621463785841754820491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94414309190561169880327 141621463785841754820491)
                ·
                  refine ⟨212432195678762632230737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141621463785841754820491 212432195678762632230737)
                  ·
                    refine ⟨159324146759071974173053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 212432195678762632230737 159324146759071974173053)
                    ·
                      refine ⟨59746555034651990314895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 159324146759071974173053 59746555034651990314895)
                      ·
                        rfl

theorem cell23_116356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_116356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116356 prefixEnd_116356 := by exact prefixLift 116356
  have htrace : WordTrace (prefixWord ++ tailWord_116356) baseStart_116356 baseEnd_116356 := by
    simpa [prefixWord, tailWord_116356, baseEnd_116356] using wordTrace_append hprefix tailTrace_116356
  have hstable : (prefixWord ++ tailWord_116356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116356).length < 2 ^ (prefixWord ++ tailWord_116356).sum := by decide
  have hdescent : baseEnd_116356 < baseStart_116356 := by decide
  rcases family_descends (prefixWord ++ tailWord_116356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116385 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 2, 6]
def baseStart_116385 : Nat := 118140960795 + 116385 * 2 ^ 59
def prefixEnd_116385 : Nat := 4983230072969 + 3 ^ 40 * 116385 * 2
def baseEnd_116385 : Nat := 19920481991210792284087

theorem tailTrace_116385 : CollatzResearch.WordTrace tailWord_116385 prefixEnd_116385 19920481991210792284087 := by
  unfold tailWord_116385
  simp only [CollatzResearch.WordTrace]
  refine ⟨4244909683364496820622609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2829939788909664547081739 4244909683364496820622609)
  ·
    refine ⟨3183682262523372615466957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4244909683364496820622609 3183682262523372615466957)
    ·
      refine ⟨1193880848446264730800109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3183682262523372615466957 1193880848446264730800109)
      ·
        refine ⟨447705318167349274050041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1193880848446264730800109 447705318167349274050041)
        ·
          refine ⟨335778988625511955537531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447705318167349274050041 335778988625511955537531)
          ·
            refine ⟨503668482938267933306297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335778988625511955537531 503668482938267933306297)
            ·
              refine ⟨377751362203700949979723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503668482938267933306297 377751362203700949979723)
              ·
                refine ⟨566627043305551424969585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377751362203700949979723 566627043305551424969585)
                ·
                  refine ⟨424970282479163568727189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 566627043305551424969585 424970282479163568727189)
                  ·
                    refine ⟨19920481991210792284087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 424970282479163568727189 19920481991210792284087)
                    ·
                      rfl

theorem cell23_116385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_116385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116385 prefixEnd_116385 := by exact prefixLift 116385
  have htrace : WordTrace (prefixWord ++ tailWord_116385) baseStart_116385 baseEnd_116385 := by
    simpa [prefixWord, tailWord_116385, baseEnd_116385] using wordTrace_append hprefix tailTrace_116385
  have hstable : (prefixWord ++ tailWord_116385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116385).length < 2 ^ (prefixWord ++ tailWord_116385).sum := by decide
  have hdescent : baseEnd_116385 < baseStart_116385 := by decide
  rcases family_descends (prefixWord ++ tailWord_116385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116386 : List Nat := [3, 3, 1, 4, 1, 2, 1, 1, 1, 3, 3]
def baseStart_116386 : Nat := 118140960795 + 116386 * 2 ^ 59
def prefixEnd_116386 : Nat := 4983230072969 + 3 ^ 40 * 116386 * 2
def baseEnd_116386 : Nat := 59761959454286872939757

theorem tailTrace_116386 : CollatzResearch.WordTrace tailWord_116386 prefixEnd_116386 59761959454286872939757 := by
  unfold tailWord_116386
  simp only [CollatzResearch.WordTrace]
  refine ⟨1061236539090218497852253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2829964104240582660939341 1061236539090218497852253)
  ·
    refine ⟨397963702158831936694595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1061236539090218497852253 397963702158831936694595)
    ·
      refine ⟨596945553238247905041893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397963702158831936694595 596945553238247905041893)
      ·
        refine ⟨111927291232171482195355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 596945553238247905041893 111927291232171482195355)
        ·
          refine ⟨167890936848257223293033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111927291232171482195355 167890936848257223293033)
          ·
            refine ⟨125918202636192917469775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167890936848257223293033 125918202636192917469775)
            ·
              refine ⟨188877303954289376204663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125918202636192917469775 188877303954289376204663)
              ·
                refine ⟨283315955931434064306995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188877303954289376204663 283315955931434064306995)
                ·
                  refine ⟨424973933897151096460493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283315955931434064306995 424973933897151096460493)
                  ·
                    refine ⟨159365225211431661172685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 424973933897151096460493 159365225211431661172685)
                    ·
                      refine ⟨59761959454286872939757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 159365225211431661172685 59761959454286872939757)
                      ·
                        rfl

theorem cell23_116386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_116386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116386 prefixEnd_116386 := by exact prefixLift 116386
  have htrace : WordTrace (prefixWord ++ tailWord_116386) baseStart_116386 baseEnd_116386 := by
    simpa [prefixWord, tailWord_116386, baseEnd_116386] using wordTrace_append hprefix tailTrace_116386
  have hstable : (prefixWord ++ tailWord_116386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116386).length < 2 ^ (prefixWord ++ tailWord_116386).sum := by decide
  have hdescent : baseEnd_116386 < baseStart_116386 := by decide
  rcases family_descends (prefixWord ++ tailWord_116386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116462 : List Nat := [4, 1, 2, 1, 1, 2, 4, 1, 2, 5]
def baseStart_116462 : Nat := 118140960795 + 116462 * 2 ^ 59
def prefixEnd_116462 : Nat := 4983230072969 + 3 ^ 40 * 116462 * 2
def baseEnd_116462 : Nat := 19933661328009525196469

theorem tailTrace_116462 : CollatzResearch.WordTrace tailWord_116462 prefixEnd_116462 19933661328009525196469 := by
  unfold tailWord_116462
  simp only [CollatzResearch.WordTrace]
  refine ⟨530964763010692371396955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2831812069390359314117093 530964763010692371396955)
  ·
    refine ⟨796447144516038557095433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 530964763010692371396955 796447144516038557095433)
    ·
      refine ⟨597335358387028917821575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 796447144516038557095433 597335358387028917821575)
      ·
        refine ⟨896003037580543376732363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597335358387028917821575 896003037580543376732363)
        ·
          refine ⟨1344004556370815065098545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896003037580543376732363 1344004556370815065098545)
          ·
            refine ⟨1008003417278111298823909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1344004556370815065098545 1008003417278111298823909)
            ·
              refine ⟨189000640739645868529483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1008003417278111298823909 189000640739645868529483)
              ·
                refine ⟨283500961109468802794225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189000640739645868529483 283500961109468802794225)
                ·
                  refine ⟨212625720832101602095669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283500961109468802794225 212625720832101602095669)
                  ·
                    refine ⟨19933661328009525196469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 212625720832101602095669 19933661328009525196469)
                    ·
                      rfl

theorem cell23_116462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_116462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116462 prefixEnd_116462 := by exact prefixLift 116462
  have htrace : WordTrace (prefixWord ++ tailWord_116462) baseStart_116462 baseEnd_116462 := by
    simpa [prefixWord, tailWord_116462, baseEnd_116462] using wordTrace_append hprefix tailTrace_116462
  have hstable : (prefixWord ++ tailWord_116462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116462).length < 2 ^ (prefixWord ++ tailWord_116462).sum := by decide
  have hdescent : baseEnd_116462 < baseStart_116462 := by decide
  rcases family_descends (prefixWord ++ tailWord_116462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116475 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 7, 4]
def baseStart_116475 : Nat := 118140960795 + 116475 * 2 ^ 59
def prefixEnd_116475 : Nat := 4983230072969 + 3 ^ 40 * 116475 * 2
def baseEnd_116475 : Nat := 19935886410845674908949

theorem tailTrace_116475 : CollatzResearch.WordTrace tailWord_116475 prefixEnd_116475 19935886410845674908949 := by
  unfold tailWord_116475
  simp only [CollatzResearch.WordTrace]
  refine ⟨4248192253038442191398879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2832128168692294794265919 4248192253038442191398879)
  ·
    refine ⟨6372288379557663287098319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4248192253038442191398879 6372288379557663287098319)
    ·
      refine ⟨9558432569336494930647479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6372288379557663287098319 9558432569336494930647479)
      ·
        refine ⟨14337648854004742395971219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9558432569336494930647479 14337648854004742395971219)
        ·
          refine ⟨21506473281007113593956829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14337648854004742395971219 21506473281007113593956829)
          ·
            refine ⟨8064927480377667597733811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21506473281007113593956829 8064927480377667597733811)
            ·
              refine ⟨12097391220566501396600717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8064927480377667597733811 12097391220566501396600717)
              ·
                refine ⟨4536521707712438023725269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12097391220566501396600717 4536521707712438023725269)
                ·
                  refine ⟨106324727524510266181061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4536521707712438023725269 106324727524510266181061)
                  ·
                    refine ⟨19935886410845674908949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106324727524510266181061 19935886410845674908949)
                    ·
                      rfl

theorem cell23_116475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 4].length) (baseStart_116475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116475 prefixEnd_116475 := by exact prefixLift 116475
  have htrace : WordTrace (prefixWord ++ tailWord_116475) baseStart_116475 baseEnd_116475 := by
    simpa [prefixWord, tailWord_116475, baseEnd_116475] using wordTrace_append hprefix tailTrace_116475
  have hstable : (prefixWord ++ tailWord_116475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116475).length < 2 ^ (prefixWord ++ tailWord_116475).sum := by decide
  have hdescent : baseEnd_116475 < baseStart_116475 := by decide
  rcases family_descends (prefixWord ++ tailWord_116475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116485 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 5, 4, 3]
def baseStart_116485 : Nat := 118140960795 + 116485 * 2 ^ 59
def prefixEnd_116485 : Nat := 4983230072969 + 3 ^ 40 * 116485 * 2
def baseEnd_116485 : Nat := 59812794039081985601801

theorem tailTrace_116485 : CollatzResearch.WordTrace tailWord_116485 prefixEnd_116485 59812794039081985601801 := by
  unfold tailWord_116485
  simp only [CollatzResearch.WordTrace]
  refine ⟨4248556983002213899262909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2832371322001475932841939 4248556983002213899262909)
  ·
    refine ⟨1593208868625830212223591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4248556983002213899262909 1593208868625830212223591)
    ·
      refine ⟨2389813302938745318335387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1593208868625830212223591 2389813302938745318335387)
      ·
        refine ⟨3584719954408117977503081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2389813302938745318335387 3584719954408117977503081)
        ·
          refine ⟨2688539965806088483127311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3584719954408117977503081 2688539965806088483127311)
          ·
            refine ⟨4032809948709132724690967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2688539965806088483127311 4032809948709132724690967)
            ·
              refine ⟨6049214923063699087036451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4032809948709132724690967 6049214923063699087036451)
              ·
                refine ⟨9073822384595548630554677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6049214923063699087036451 9073822384595548630554677)
                ·
                  refine ⟨850670848555832684114501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9073822384595548630554677 850670848555832684114501)
                  ·
                    refine ⟨159500784104218628271469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 850670848555832684114501 159500784104218628271469)
                    ·
                      refine ⟨59812794039081985601801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 159500784104218628271469 59812794039081985601801)
                      ·
                        rfl

theorem cell23_116485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_116485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116485 prefixEnd_116485 := by exact prefixLift 116485
  have htrace : WordTrace (prefixWord ++ tailWord_116485) baseStart_116485 baseEnd_116485 := by
    simpa [prefixWord, tailWord_116485, baseEnd_116485] using wordTrace_append hprefix tailTrace_116485
  have hstable : (prefixWord ++ tailWord_116485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116485).length < 2 ^ (prefixWord ++ tailWord_116485).sum := by decide
  have hdescent : baseEnd_116485 < baseStart_116485 := by decide
  rcases family_descends (prefixWord ++ tailWord_116485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116535 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 5, 5]
def baseStart_116535 : Nat := 118140960795 + 116535 * 2 ^ 59
def prefixEnd_116535 : Nat := 4983230072969 + 3 ^ 40 * 116535 * 2
def baseEnd_116535 : Nat := 19946156023935596658857

theorem tailTrace_116535 : CollatzResearch.WordTrace tailWord_116535 prefixEnd_116535 19946156023935596658857 := by
  unfold tailWord_116535
  simp only [CollatzResearch.WordTrace]
  refine ⟨4250380632821072438583059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2833587088547381625722039 4250380632821072438583059)
  ·
    refine ⟨6375570949231608657874589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4250380632821072438583059 6375570949231608657874589)
    ·
      refine ⟨2390839105961853246702971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6375570949231608657874589 2390839105961853246702971)
      ·
        refine ⟨3586258658942779870054457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2390839105961853246702971 3586258658942779870054457)
        ·
          refine ⟨2689693994207084902540843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3586258658942779870054457 2689693994207084902540843)
          ·
            refine ⟨4034540991310627353811265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2689693994207084902540843 4034540991310627353811265)
            ·
              refine ⟨3025905743482970515358449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4034540991310627353811265 3025905743482970515358449)
              ·
                refine ⟨2269429307612227886518837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3025905743482970515358449 2269429307612227886518837)
                ·
                  refine ⟨212758997588646364361141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2269429307612227886518837 212758997588646364361141)
                  ·
                    refine ⟨19946156023935596658857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 212758997588646364361141 19946156023935596658857)
                    ·
                      rfl

theorem cell23_116535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_116535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116535 prefixEnd_116535 := by exact prefixLift 116535
  have htrace : WordTrace (prefixWord ++ tailWord_116535) baseStart_116535 baseEnd_116535 := by
    simpa [prefixWord, tailWord_116535, baseEnd_116535] using wordTrace_append hprefix tailTrace_116535
  have hstable : (prefixWord ++ tailWord_116535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116535).length < 2 ^ (prefixWord ++ tailWord_116535).sum := by decide
  have hdescent : baseEnd_116535 < baseStart_116535 := by decide
  rcases family_descends (prefixWord ++ tailWord_116535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116542 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_116542 : Nat := 118140960795 + 116542 * 2 ^ 59
def prefixEnd_116542 : Nat := 4983230072969 + 3 ^ 40 * 116542 * 2
def baseEnd_116542 : Nat := 59842062436388262589039

theorem tailTrace_116542 : CollatzResearch.WordTrace tailWord_116542 prefixEnd_116542 59842062436388262589039 := by
  unfold tailWord_116542
  simp only [CollatzResearch.WordTrace]
  refine ⟨531329492974464079260985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2833757295863808422725253 531329492974464079260985)
  ·
    refine ⟨398497119730848059445739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 531329492974464079260985 398497119730848059445739)
    ·
      refine ⟨597745679596272089168609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398497119730848059445739 597745679596272089168609)
      ·
        refine ⟨448309259697204066876457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597745679596272089168609 448309259697204066876457)
        ·
          refine ⟨336231944772903050157343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448309259697204066876457 336231944772903050157343)
          ·
            refine ⟨504347917159354575236015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336231944772903050157343 504347917159354575236015)
            ·
              refine ⟨756521875739031862854023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504347917159354575236015 756521875739031862854023)
              ·
                refine ⟨1134782813608547794281035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756521875739031862854023 1134782813608547794281035)
                ·
                  refine ⟨1702174220412821691421553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134782813608547794281035 1702174220412821691421553)
                  ·
                    refine ⟨1276630665309616268566165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1702174220412821691421553 1276630665309616268566165)
                    ·
                      refine ⟨59842062436388262589039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1276630665309616268566165 59842062436388262589039)
                      ·
                        rfl

theorem cell23_116542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_116542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116542 prefixEnd_116542 := by exact prefixLift 116542
  have htrace : WordTrace (prefixWord ++ tailWord_116542) baseStart_116542 baseEnd_116542 := by
    simpa [prefixWord, tailWord_116542, baseEnd_116542] using wordTrace_append hprefix tailTrace_116542
  have hstable : (prefixWord ++ tailWord_116542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116542).length < 2 ^ (prefixWord ++ tailWord_116542).sum := by decide
  have hdescent : baseEnd_116542 < baseStart_116542 := by decide
  rcases family_descends (prefixWord ++ tailWord_116542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116549 : List Nat := [1, 3, 1, 1, 1, 2, 6, 1, 3, 1, 3]
def baseStart_116549 : Nat := 118140960795 + 116549 * 2 ^ 59
def prefixEnd_116549 : Nat := 4983230072969 + 3 ^ 40 * 116549 * 2
def baseEnd_116549 : Nat := 59845656800969735201507

theorem tailTrace_116549 : CollatzResearch.WordTrace tailWord_116549 prefixEnd_116549 59845656800969735201507 := by
  unfold tailWord_116549
  simp only [CollatzResearch.WordTrace]
  refine ⟨4250891254770352829592701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2833927503180235219728467 4250891254770352829592701)
  ·
    refine ⟨1594084220538882311097263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4250891254770352829592701 1594084220538882311097263)
    ·
      refine ⟨2391126330808323466645895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1594084220538882311097263 2391126330808323466645895)
      ·
        refine ⟨3586689496212485199968843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2391126330808323466645895 3586689496212485199968843)
        ·
          refine ⟨5380034244318727799953265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3586689496212485199968843 5380034244318727799953265)
          ·
            refine ⟨4035025683239045849964949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5380034244318727799953265 4035025683239045849964949)
            ·
              refine ⟨189141828901830274217107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4035025683239045849964949 189141828901830274217107)
              ·
                refine ⟨283712743352745411325661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189141828901830274217107 283712743352745411325661)
                ·
                  refine ⟨106392278757279529247123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283712743352745411325661 106392278757279529247123)
                  ·
                    refine ⟨159588418135919293870685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106392278757279529247123 159588418135919293870685)
                    ·
                      refine ⟨59845656800969735201507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 159588418135919293870685 59845656800969735201507)
                      ·
                        rfl

theorem cell23_116549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 1, 3].length) (baseStart_116549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116549 prefixEnd_116549 := by exact prefixLift 116549
  have htrace : WordTrace (prefixWord ++ tailWord_116549) baseStart_116549 baseEnd_116549 := by
    simpa [prefixWord, tailWord_116549, baseEnd_116549] using wordTrace_append hprefix tailTrace_116549
  have hstable : (prefixWord ++ tailWord_116549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116549).length < 2 ^ (prefixWord ++ tailWord_116549).sum := by decide
  have hdescent : baseEnd_116549 < baseStart_116549 := by decide
  rcases family_descends (prefixWord ++ tailWord_116549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116589 : List Nat := [1, 5, 1, 1, 1, 1, 4, 3, 1, 1, 4]
def baseStart_116589 : Nat := 118140960795 + 116589 * 2 ^ 59
def prefixEnd_116589 : Nat := 4983230072969 + 3 ^ 40 * 116589 * 2
def baseEnd_116589 : Nat := 59866196027149578701323

theorem tailTrace_116589 : CollatzResearch.WordTrace tailWord_116589 prefixEnd_116589 59866196027149578701323 := by
  unfold tailWord_116589
  simp only [CollatzResearch.WordTrace]
  refine ⟨4252350174625439661048821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2834900116416959774032547 4252350174625439661048821)
  ·
    refine ⟨398657828871134968223327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4252350174625439661048821 398657828871134968223327)
    ·
      refine ⟨597986743306702452334991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398657828871134968223327 597986743306702452334991)
      ·
        refine ⟨896980114960053678502487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597986743306702452334991 896980114960053678502487)
        ·
          refine ⟨1345470172440080517753731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896980114960053678502487 1345470172440080517753731)
          ·
            refine ⟨2018205258660120776630597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345470172440080517753731 2018205258660120776630597)
            ·
              refine ⟨378413485998772645618237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2018205258660120776630597 378413485998772645618237)
              ·
                refine ⟨141905057249539742106839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378413485998772645618237 141905057249539742106839)
                ·
                  refine ⟨212857585874309613160259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141905057249539742106839 212857585874309613160259)
                  ·
                    refine ⟨319286378811464419740389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 212857585874309613160259 319286378811464419740389)
                    ·
                      refine ⟨59866196027149578701323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 319286378811464419740389 59866196027149578701323)
                      ·
                        rfl

theorem cell23_116589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_116589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116589 prefixEnd_116589 := by exact prefixLift 116589
  have htrace : WordTrace (prefixWord ++ tailWord_116589) baseStart_116589 baseEnd_116589 := by
    simpa [prefixWord, tailWord_116589, baseEnd_116589] using wordTrace_append hprefix tailTrace_116589
  have hstable : (prefixWord ++ tailWord_116589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116589).length < 2 ^ (prefixWord ++ tailWord_116589).sum := by decide
  have hdescent : baseEnd_116589 < baseStart_116589 := by decide
  rcases family_descends (prefixWord ++ tailWord_116589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116592 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 3]
def baseStart_116592 : Nat := 118140960795 + 116592 * 2 ^ 59
def prefixEnd_116592 : Nat := 4983230072969 + 3 ^ 40 * 116592 * 2
def baseEnd_116592 : Nat := 59867736469113066963809

theorem tailTrace_116592 : CollatzResearch.WordTrace tailWord_116592 prefixEnd_116592 59867736469113066963809 := by
  unfold tailWord_116592
  simp only [CollatzResearch.WordTrace]
  refine ⟨2126229796807285586704015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2834973062409714115605353 2126229796807285586704015)
  ·
    refine ⟨3189344695210928380056023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2126229796807285586704015 3189344695210928380056023)
    ·
      refine ⟨4784017042816392570084035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3189344695210928380056023 4784017042816392570084035)
      ·
        refine ⟨7176025564224588855126053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4784017042816392570084035 7176025564224588855126053)
        ·
          refine ⟨1345504793292110410336135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7176025564224588855126053 1345504793292110410336135)
          ·
            refine ⟨2018257189938165615504203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345504793292110410336135 2018257189938165615504203)
            ·
              refine ⟨3027385784907248423256305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2018257189938165615504203 3027385784907248423256305)
              ·
                refine ⟨2270539338680436317442229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3027385784907248423256305 2270539338680436317442229)
                ·
                  refine ⟨212863063001290904760209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2270539338680436317442229 212863063001290904760209)
                  ·
                    refine ⟨159647297250968178570157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 212863063001290904760209 159647297250968178570157)
                    ·
                      refine ⟨59867736469113066963809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 159647297250968178570157 59867736469113066963809)
                      ·
                        rfl

theorem cell23_116592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 3].length) (baseStart_116592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116592 prefixEnd_116592 := by exact prefixLift 116592
  have htrace : WordTrace (prefixWord ++ tailWord_116592) baseStart_116592 baseEnd_116592 := by
    simpa [prefixWord, tailWord_116592, baseEnd_116592] using wordTrace_append hprefix tailTrace_116592
  have hstable : (prefixWord ++ tailWord_116592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116592).length < 2 ^ (prefixWord ++ tailWord_116592).sum := by decide
  have hdescent : baseEnd_116592 < baseStart_116592 := by decide
  rcases family_descends (prefixWord ++ tailWord_116592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116616 : List Nat := [2, 1, 3, 3, 3, 1, 1, 3, 2, 4]
def baseStart_116616 : Nat := 118140960795 + 116616 * 2 ^ 59
def prefixEnd_116616 : Nat := 4983230072969 + 3 ^ 40 * 116616 * 2
def baseEnd_116616 : Nat := 19960020001606991021233

theorem tailTrace_116616 : CollatzResearch.WordTrace tailWord_116616 prefixEnd_116616 19960020001606991021233 := by
  unfold tailWord_116616
  simp only [CollatzResearch.WordTrace]
  refine ⟨2126667472763811636140851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2835556630351748848187801 2126667472763811636140851)
  ·
    refine ⟨3190001209145717454211277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2126667472763811636140851 3190001209145717454211277)
    ·
      refine ⟨1196250453429644045329229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3190001209145717454211277 1196250453429644045329229)
      ·
        refine ⟨448593920036116516998461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1196250453429644045329229 448593920036116516998461)
        ·
          refine ⟨168222720013543693874423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448593920036116516998461 168222720013543693874423)
          ·
            refine ⟨252334080020315540811635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168222720013543693874423 252334080020315540811635)
            ·
              refine ⟨378501120030473311217453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252334080020315540811635 378501120030473311217453)
              ·
                refine ⟨141937920011427491706545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378501120030473311217453 141937920011427491706545)
                ·
                  refine ⟨106453440008570618779909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141937920011427491706545 106453440008570618779909)
                  ·
                    refine ⟨19960020001606991021233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106453440008570618779909 19960020001606991021233)
                    ·
                      rfl

theorem cell23_116616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_116616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116616 prefixEnd_116616 := by exact prefixLift 116616
  have htrace : WordTrace (prefixWord ++ tailWord_116616) baseStart_116616 baseEnd_116616 := by
    simpa [prefixWord, tailWord_116616, baseEnd_116616] using wordTrace_append hprefix tailTrace_116616
  have hstable : (prefixWord ++ tailWord_116616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116616).length < 2 ^ (prefixWord ++ tailWord_116616).sum := by decide
  have hdescent : baseEnd_116616 < baseStart_116616 := by decide
  rcases family_descends (prefixWord ++ tailWord_116616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116626 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_116626 : Nat := 118140960795 + 116626 * 2 ^ 59
def prefixEnd_116626 : Nat := 4983230072969 + 3 ^ 40 * 116626 * 2
def baseEnd_116626 : Nat := 59885194811365933938653

theorem tailTrace_116626 : CollatzResearch.WordTrace tailWord_116626 prefixEnd_116626 59885194811365933938653 := by
  unfold tailWord_116626
  simp only [CollatzResearch.WordTrace]
  refine ⟨1063424918872848745036433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2835799783660929986763821 1063424918872848745036433)
  ·
    refine ⟨797568689154636558777325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1063424918872848745036433 797568689154636558777325)
    ·
      refine ⟨299088258432988709541497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 797568689154636558777325 299088258432988709541497)
      ·
        refine ⟨224316193824741532156123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299088258432988709541497 224316193824741532156123)
        ·
          refine ⟨336474290737112298234185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224316193824741532156123 336474290737112298234185)
          ·
            refine ⟨252355718052834223675639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336474290737112298234185 252355718052834223675639)
            ·
              refine ⟨378533577079251335513459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252355718052834223675639 378533577079251335513459)
              ·
                refine ⟨567800365618877003270189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378533577079251335513459 567800365618877003270189)
                ·
                  refine ⟨212925137107078876226321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 567800365618877003270189 212925137107078876226321)
                  ·
                    refine ⟨159693852830309157169741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 212925137107078876226321 159693852830309157169741)
                    ·
                      refine ⟨59885194811365933938653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 159693852830309157169741 59885194811365933938653)
                      ·
                        rfl

theorem cell23_116626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_116626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116626 prefixEnd_116626 := by exact prefixLift 116626
  have htrace : WordTrace (prefixWord ++ tailWord_116626) baseStart_116626 baseEnd_116626 := by
    simpa [prefixWord, tailWord_116626, baseEnd_116626] using wordTrace_append hprefix tailTrace_116626
  have hstable : (prefixWord ++ tailWord_116626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116626).length < 2 ^ (prefixWord ++ tailWord_116626).sum := by decide
  have hdescent : baseEnd_116626 < baseStart_116626 := by decide
  rcases family_descends (prefixWord ++ tailWord_116626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116657 : List Nat := [1, 2, 2, 4, 2, 3, 2, 2, 1, 2, 2]
def baseStart_116657 : Nat := 118140960795 + 116657 * 2 ^ 59
def prefixEnd_116657 : Nat := 4983230072969 + 3 ^ 40 * 116657 * 2
def baseEnd_116657 : Nat := 59901112711655312651011

theorem tailTrace_116657 : CollatzResearch.WordTrace tailWord_116657 prefixEnd_116657 59901112711655312651011 := by
  unfold tailWord_116657
  simp only [CollatzResearch.WordTrace]
  refine ⟨4254830338379087274524225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2836553558919391516349483 4254830338379087274524225)
  ·
    refine ⟨3191122753784315455893169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4254830338379087274524225 3191122753784315455893169)
    ·
      refine ⟨2393342065338236591919877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3191122753784315455893169 2393342065338236591919877)
      ·
        refine ⟨448751637250919360984977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2393342065338236591919877 448751637250919360984977)
        ·
          refine ⟨336563727938189520738733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448751637250919360984977 336563727938189520738733)
          ·
            refine ⟨126211397976821070277025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336563727938189520738733 126211397976821070277025)
            ·
              refine ⟨94658548482615802707769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126211397976821070277025 94658548482615802707769)
              ·
                refine ⟨70993911361961852030827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94658548482615802707769 70993911361961852030827)
                ·
                  refine ⟨106490867042942778046241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70993911361961852030827 106490867042942778046241)
                  ·
                    refine ⟨79868150282207083534681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106490867042942778046241 79868150282207083534681)
                    ·
                      refine ⟨59901112711655312651011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 79868150282207083534681 59901112711655312651011)
                      ·
                        rfl

theorem cell23_116657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_116657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116657 prefixEnd_116657 := by exact prefixLift 116657
  have htrace : WordTrace (prefixWord ++ tailWord_116657) baseStart_116657 baseEnd_116657 := by
    simpa [prefixWord, tailWord_116657, baseEnd_116657] using wordTrace_append hprefix tailTrace_116657
  have hstable : (prefixWord ++ tailWord_116657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116657).length < 2 ^ (prefixWord ++ tailWord_116657).sum := by decide
  have hdescent : baseEnd_116657 < baseStart_116657 := by decide
  rcases family_descends (prefixWord ++ tailWord_116657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116672 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 2, 6]
def baseStart_116672 : Nat := 118140960795 + 116672 * 2 ^ 59
def prefixEnd_116672 : Nat := 4983230072969 + 3 ^ 40 * 116672 * 2
def baseEnd_116672 : Nat := 19969604973824251321147

theorem tailTrace_116672 : CollatzResearch.WordTrace tailWord_116672 prefixEnd_116672 19969604973824251321147 := by
  unfold tailWord_116672
  simp only [CollatzResearch.WordTrace]
  refine ⟨2127688716662372418160135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2836918288883163224213513 2127688716662372418160135)
  ·
    refine ⟨3191533074993558627240203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2127688716662372418160135 3191533074993558627240203)
    ·
      refine ⟨4787299612490337940860305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3191533074993558627240203 4787299612490337940860305)
      ·
        refine ⟨3590474709367753455645229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4787299612490337940860305 3590474709367753455645229)
        ·
          refine ⟨1346428016012907545866961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3590474709367753455645229 1346428016012907545866961)
          ·
            refine ⟨1009821012009680659400221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1346428016012907545866961 1009821012009680659400221)
            ·
              refine ⟨378682879503630247275083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1009821012009680659400221 378682879503630247275083)
              ·
                refine ⟨568024319255445370912625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378682879503630247275083 568024319255445370912625)
                ·
                  refine ⟨426018239441584028184469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568024319255445370912625 426018239441584028184469)
                  ·
                    refine ⟨19969604973824251321147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 426018239441584028184469 19969604973824251321147)
                    ·
                      rfl

theorem cell23_116672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 2, 6].length) (baseStart_116672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116672 prefixEnd_116672 := by exact prefixLift 116672
  have htrace : WordTrace (prefixWord ++ tailWord_116672) baseStart_116672 baseEnd_116672 := by
    simpa [prefixWord, tailWord_116672, baseEnd_116672] using wordTrace_append hprefix tailTrace_116672
  have hstable : (prefixWord ++ tailWord_116672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116672).length < 2 ^ (prefixWord ++ tailWord_116672).sum := by decide
  have hdescent : baseEnd_116672 < baseStart_116672 := by decide
  rcases family_descends (prefixWord ++ tailWord_116672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116682 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_116682 : Nat := 118140960795 + 116682 * 2 ^ 59
def prefixEnd_116682 : Nat := 4983230072969 + 3 ^ 40 * 116682 * 2
def baseEnd_116682 : Nat := 59913949728017714838395

theorem tailTrace_116682 : CollatzResearch.WordTrace tailWord_116682 prefixEnd_116682 59913949728017714838395 := by
  unfold tailWord_116682
  simp only [CollatzResearch.WordTrace]
  refine ⟨1063935540822129136046075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2837161442192344362789533 1063935540822129136046075)
  ·
    refine ⟨1595903311233193704069113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1063935540822129136046075 1595903311233193704069113)
    ·
      refine ⟨1196927483424895278051835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1595903311233193704069113 1196927483424895278051835)
      ·
        refine ⟨1795391225137342917077753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1196927483424895278051835 1795391225137342917077753)
        ·
          refine ⟨1346543418853007187808315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1795391225137342917077753 1346543418853007187808315)
          ·
            refine ⟨2019815128279510781712473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346543418853007187808315 2019815128279510781712473)
            ·
              refine ⟨1514861346209633086284355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2019815128279510781712473 1514861346209633086284355)
              ·
                refine ⟨2272292019314449629426533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1514861346209633086284355 2272292019314449629426533)
                ·
                  refine ⟨426054753621459305517475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2272292019314449629426533 426054753621459305517475)
                  ·
                    refine ⟨639082130432188958276213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 426054753621459305517475 639082130432188958276213)
                    ·
                      refine ⟨59913949728017714838395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 639082130432188958276213 59913949728017714838395)
                      ·
                        rfl

theorem cell23_116682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_116682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116682 prefixEnd_116682 := by exact prefixLift 116682
  have htrace : WordTrace (prefixWord ++ tailWord_116682) baseStart_116682 baseEnd_116682 := by
    simpa [prefixWord, tailWord_116682, baseEnd_116682] using wordTrace_append hprefix tailTrace_116682
  have hstable : (prefixWord ++ tailWord_116682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116682).length < 2 ^ (prefixWord ++ tailWord_116682).sum := by decide
  have hdescent : baseEnd_116682 < baseStart_116682 := by decide
  rcases family_descends (prefixWord ++ tailWord_116682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116696 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 4, 2, 2]
def baseStart_116696 : Nat := 118140960795 + 116696 * 2 ^ 59
def prefixEnd_116696 : Nat := 4983230072969 + 3 ^ 40 * 116696 * 2
def baseEnd_116696 : Nat := 59921138457180660063331

theorem tailTrace_116696 : CollatzResearch.WordTrace tailWord_116696 prefixEnd_116696 59921138457180660063331 := by
  unfold tailWord_116696
  simp only [CollatzResearch.WordTrace]
  refine ⟨2128126392618898467596971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2837501856825197956795961 2128126392618898467596971)
  ·
    refine ⟨3192189588928347701395457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2128126392618898467596971 3192189588928347701395457)
    ·
      refine ⟨2394142191696260776046593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3192189588928347701395457 2394142191696260776046593)
      ·
        refine ⟨1795606643772195582034945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2394142191696260776046593 1795606643772195582034945)
        ·
          refine ⟨1346704982829146686526209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1795606643772195582034945 1346704982829146686526209)
          ·
            refine ⟨1010028737121860014894657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1346704982829146686526209 1010028737121860014894657)
            ·
              refine ⟨757521552841395011170993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1010028737121860014894657 757521552841395011170993)
              ·
                refine ⟨568141164631046258378245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 757521552841395011170993 568141164631046258378245)
                ·
                  refine ⟨106526468368321173445921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 568141164631046258378245 106526468368321173445921)
                  ·
                    refine ⟨79894851276240880084441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106526468368321173445921 79894851276240880084441)
                    ·
                      refine ⟨59921138457180660063331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 79894851276240880084441 59921138457180660063331)
                      ·
                        rfl

theorem cell23_116696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_116696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116696 prefixEnd_116696 := by exact prefixLift 116696
  have htrace : WordTrace (prefixWord ++ tailWord_116696) baseStart_116696 baseEnd_116696 := by
    simpa [prefixWord, tailWord_116696, baseEnd_116696] using wordTrace_append hprefix tailTrace_116696
  have hstable : (prefixWord ++ tailWord_116696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116696).length < 2 ^ (prefixWord ++ tailWord_116696).sum := by decide
  have hdescent : baseEnd_116696 < baseStart_116696 := by decide
  rcases family_descends (prefixWord ++ tailWord_116696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116719 : List Nat := [1, 1, 2, 1, 4, 2, 1, 6, 5]
def baseStart_116719 : Nat := 118140960795 + 116719 * 2 ^ 59
def prefixEnd_116719 : Nat := 4983230072969 + 3 ^ 40 * 116719 * 2
def baseEnd_116719 : Nat := 6659216501359341119525

theorem tailTrace_116719 : CollatzResearch.WordTrace tailWord_116719 prefixEnd_116719 6659216501359341119525 := by
  unfold tailWord_116719
  simp only [CollatzResearch.WordTrace]
  refine ⟨4257091664154471863281211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2838061109436314575520807 4257091664154471863281211)
  ·
    refine ⟨6385637496231707794921817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4257091664154471863281211 6385637496231707794921817)
    ·
      refine ⟨4789228122173780846191363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6385637496231707794921817 4789228122173780846191363)
      ·
        refine ⟨7183842183260671269287045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4789228122173780846191363 7183842183260671269287045)
        ·
          refine ⟨1346970409361375862991321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7183842183260671269287045 1346970409361375862991321)
          ·
            refine ⟨1010227807021031897243491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1346970409361375862991321 1010227807021031897243491)
            ·
              refine ⟨1515341710531547845865237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010227807021031897243491 1515341710531547845865237)
              ·
                refine ⟨71031642681166305274933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1515341710531547845865237 71031642681166305274933)
                ·
                  refine ⟨6659216501359341119525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71031642681166305274933 6659216501359341119525)
                  ·
                    rfl

theorem cell23_116719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 5].length) (baseStart_116719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116719 prefixEnd_116719 := by exact prefixLift 116719
  have htrace : WordTrace (prefixWord ++ tailWord_116719) baseStart_116719 baseEnd_116719 := by
    simpa [prefixWord, tailWord_116719, baseEnd_116719] using wordTrace_append hprefix tailTrace_116719
  have hstable : (prefixWord ++ tailWord_116719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116719).length < 2 ^ (prefixWord ++ tailWord_116719).sum := by decide
  have hdescent : baseEnd_116719 < baseStart_116719 := by decide
  rcases family_descends (prefixWord ++ tailWord_116719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116729 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 2, 3, 3]
def baseStart_116729 : Nat := 118140960795 + 116729 * 2 ^ 59
def prefixEnd_116729 : Nat := 4983230072969 + 3 ^ 40 * 116729 * 2
def baseEnd_116729 : Nat := 59938083318779030950679

theorem tailTrace_116729 : CollatzResearch.WordTrace tailWord_116729 prefixEnd_116729 59938083318779030950679 := by
  unfold tailWord_116729
  simp only [CollatzResearch.WordTrace]
  refine ⟨4257456394118243571145241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2838304262745495714096827 4257456394118243571145241)
  ·
    refine ⟨3193092295588682678358931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4257456394118243571145241 3193092295588682678358931)
    ·
      refine ⟨4789638443383024017538397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3193092295588682678358931 4789638443383024017538397)
      ·
        refine ⟨1796114416268634006576899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4789638443383024017538397 1796114416268634006576899)
        ·
          refine ⟨2694171624402951009865349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1796114416268634006576899 2694171624402951009865349)
          ·
            refine ⟨505157179575553314349753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2694171624402951009865349 505157179575553314349753)
            ·
              refine ⟨378867884681664985762315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505157179575553314349753 378867884681664985762315)
              ·
                refine ⟨568301827022497478643473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378867884681664985762315 568301827022497478643473)
                ·
                  refine ⟨426226370266873108982605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568301827022497478643473 426226370266873108982605)
                  ·
                    refine ⟨159834888850077415868477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 426226370266873108982605 159834888850077415868477)
                    ·
                      refine ⟨59938083318779030950679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 159834888850077415868477 59938083318779030950679)
                      ·
                        rfl

theorem cell23_116729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_116729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116729 prefixEnd_116729 := by exact prefixLift 116729
  have htrace : WordTrace (prefixWord ++ tailWord_116729) baseStart_116729 baseEnd_116729 := by
    simpa [prefixWord, tailWord_116729, baseEnd_116729] using wordTrace_append hprefix tailTrace_116729
  have hstable : (prefixWord ++ tailWord_116729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116729).length < 2 ^ (prefixWord ++ tailWord_116729).sum := by decide
  have hdescent : baseEnd_116729 < baseStart_116729 := by decide
  rcases family_descends (prefixWord ++ tailWord_116729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116732 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 3, 7]
def baseStart_116732 : Nat := 118140960795 + 116732 * 2 ^ 59
def prefixEnd_116732 : Nat := 4983230072969 + 3 ^ 40 * 116732 * 2
def baseEnd_116732 : Nat := 19979874586914173071055

theorem tailTrace_116732 : CollatzResearch.WordTrace tailWord_116732 prefixEnd_116732 19979874586914173071055 := by
  unfold tailWord_116732
  simp only [CollatzResearch.WordTrace]
  refine ⟨2128782906553687541752225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2838377208738250055669633 2128782906553687541752225)
  ·
    refine ⟨1596587179915265656314169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2128782906553687541752225 1596587179915265656314169)
    ·
      refine ⟨1197440384936449242235627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1596587179915265656314169 1197440384936449242235627)
      ·
        refine ⟨1796160577404673863353441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1197440384936449242235627 1796160577404673863353441)
        ·
          refine ⟨1347120433053505397515081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1796160577404673863353441 1347120433053505397515081)
          ·
            refine ⟨1010340324790129048136311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1347120433053505397515081 1010340324790129048136311)
            ·
              refine ⟨1515510487185193572204467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010340324790129048136311 1515510487185193572204467)
              ·
                refine ⟨2273265730777790358306701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1515510487185193572204467 2273265730777790358306701)
                ·
                  refine ⟨852474649041671384365013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2273265730777790358306701 852474649041671384365013)
                  ·
                    refine ⟨19979874586914173071055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 852474649041671384365013 19979874586914173071055)
                    ·
                      rfl

theorem cell23_116732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_116732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116732 prefixEnd_116732 := by exact prefixLift 116732
  have htrace : WordTrace (prefixWord ++ tailWord_116732) baseStart_116732 baseEnd_116732 := by
    simpa [prefixWord, tailWord_116732, baseEnd_116732] using wordTrace_append hprefix tailTrace_116732
  have hstable : (prefixWord ++ tailWord_116732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116732).length < 2 ^ (prefixWord ++ tailWord_116732).sum := by decide
  have hdescent : baseEnd_116732 < baseStart_116732 := by decide
  rcases family_descends (prefixWord ++ tailWord_116732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116739 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 2, 5, 2]
def baseStart_116739 : Nat := 118140960795 + 116739 * 2 ^ 59
def prefixEnd_116739 : Nat := 4983230072969 + 3 ^ 40 * 116739 * 2
def baseEnd_116739 : Nat := 59943218125323991825633

theorem tailTrace_116739 : CollatzResearch.WordTrace tailWord_116739 prefixEnd_116739 59943218125323991825633 := by
  unfold tailWord_116739
  simp only [CollatzResearch.WordTrace]
  refine ⟨4257821124082015279009271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2838547416054676852672847 4257821124082015279009271)
  ·
    refine ⟨6386731686123022918513907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4257821124082015279009271 6386731686123022918513907)
    ·
      refine ⟨9580097529184534377770861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6386731686123022918513907 9580097529184534377770861)
      ·
        refine ⟨3592536573444200391664073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9580097529184534377770861 3592536573444200391664073)
        ·
          refine ⟨2694402430083150293748055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3592536573444200391664073 2694402430083150293748055)
          ·
            refine ⟨4041603645124725440622083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2694402430083150293748055 4041603645124725440622083)
            ·
              refine ⟨6062405467687088160933125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4041603645124725440622083 6062405467687088160933125)
              ·
                refine ⟨1136701025191329030174961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6062405467687088160933125 1136701025191329030174961)
                ·
                  refine ⟨852525768893496772631221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1136701025191329030174961 852525768893496772631221)
                  ·
                    refine ⟨79924290833765322434177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 852525768893496772631221 79924290833765322434177)
                    ·
                      refine ⟨59943218125323991825633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 79924290833765322434177 59943218125323991825633)
                      ·
                        rfl

theorem cell23_116739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 5, 2].length) (baseStart_116739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116739 prefixEnd_116739 := by exact prefixLift 116739
  have htrace : WordTrace (prefixWord ++ tailWord_116739) baseStart_116739 baseEnd_116739 := by
    simpa [prefixWord, tailWord_116739, baseEnd_116739] using wordTrace_append hprefix tailTrace_116739
  have hstable : (prefixWord ++ tailWord_116739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116739).length < 2 ^ (prefixWord ++ tailWord_116739).sum := by decide
  have hdescent : baseEnd_116739 < baseStart_116739 := by decide
  rcases family_descends (prefixWord ++ tailWord_116739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116779 : List Nat := [1, 1, 1, 1, 2, 1, 4, 5, 3, 4]
def baseStart_116779 : Nat := 118140960795 + 116779 * 2 ^ 59
def prefixEnd_116779 : Nat := 4983230072969 + 3 ^ 40 * 116779 * 2
def baseEnd_116779 : Nat := 19987919117167945108483

theorem tailTrace_116779 : CollatzResearch.WordTrace tailWord_116779 prefixEnd_116779 19987919117167945108483 := by
  unfold tailWord_116779
  simp only [CollatzResearch.WordTrace]
  refine ⟨4259280043937102110465391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2839520029291401406976927 4259280043937102110465391)
  ·
    refine ⟨6388920065905653165698087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4259280043937102110465391 6388920065905653165698087)
    ·
      refine ⟨9583380098858479748547131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6388920065905653165698087 9583380098858479748547131)
      ·
        refine ⟨14375070148287719622820697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9583380098858479748547131 14375070148287719622820697)
        ·
          refine ⟨10781302611215789717115523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14375070148287719622820697 10781302611215789717115523)
          ·
            refine ⟨16171953916823684575673285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10781302611215789717115523 16171953916823684575673285)
            ·
              refine ⟨3032241359404440857938741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16171953916823684575673285 3032241359404440857938741)
              ·
                refine ⟨284272627444166330431757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3032241359404440857938741 284272627444166330431757)
                ·
                  refine ⟨106602235291562373911909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284272627444166330431757 106602235291562373911909)
                  ·
                    refine ⟨19987919117167945108483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106602235291562373911909 19987919117167945108483)
                    ·
                      rfl

theorem cell23_116779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 4].length) (baseStart_116779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116779 prefixEnd_116779 := by exact prefixLift 116779
  have htrace : WordTrace (prefixWord ++ tailWord_116779) baseStart_116779 baseEnd_116779 := by
    simpa [prefixWord, tailWord_116779, baseEnd_116779] using wordTrace_append hprefix tailTrace_116779
  have hstable : (prefixWord ++ tailWord_116779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116779).length < 2 ^ (prefixWord ++ tailWord_116779).sum := by decide
  have hdescent : baseEnd_116779 < baseStart_116779 := by decide
  rcases family_descends (prefixWord ++ tailWord_116779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116789 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_116789 : Nat := 118140960795 + 116789 * 2 ^ 59
def prefixEnd_116789 : Nat := 4983230072969 + 3 ^ 40 * 116789 * 2
def baseEnd_116789 : Nat := 59968892158048796200403

theorem tailTrace_116789 : CollatzResearch.WordTrace tailWord_116789 prefixEnd_116789 59968892158048796200403 := by
  unfold tailWord_116789
  simp only [CollatzResearch.WordTrace]
  refine ⟨4259644773900873818329421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2839763182600582545552947 4259644773900873818329421)
  ·
    refine ⟨1597366790212827681873533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4259644773900873818329421 1597366790212827681873533)
    ·
      refine ⟨599012546329810380702575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1597366790212827681873533 599012546329810380702575)
      ·
        refine ⟨898518819494715571053863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599012546329810380702575 898518819494715571053863)
        ·
          refine ⟨1347778229242073356580795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 898518819494715571053863 1347778229242073356580795)
          ·
            refine ⟨2021667343863110034871193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347778229242073356580795 2021667343863110034871193)
            ·
              refine ⟨1516250507897332526153395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2021667343863110034871193 1516250507897332526153395)
              ·
                refine ⟨2274375761845998789230093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516250507897332526153395 2274375761845998789230093)
                ·
                  refine ⟨852890910692249545961285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2274375761845998789230093 852890910692249545961285)
                  ·
                    refine ⟨159917045754796789867741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 852890910692249545961285 159917045754796789867741)
                    ·
                      refine ⟨59968892158048796200403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 159917045754796789867741 59968892158048796200403)
                      ·
                        rfl

theorem cell23_116789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_116789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116789 prefixEnd_116789 := by exact prefixLift 116789
  have htrace : WordTrace (prefixWord ++ tailWord_116789) baseStart_116789 baseEnd_116789 := by
    simpa [prefixWord, tailWord_116789, baseEnd_116789] using wordTrace_append hprefix tailTrace_116789
  have hstable : (prefixWord ++ tailWord_116789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116789).length < 2 ^ (prefixWord ++ tailWord_116789).sum := by decide
  have hdescent : baseEnd_116789 < baseStart_116789 := by decide
  rcases family_descends (prefixWord ++ tailWord_116789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116839 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 5, 5]
def baseStart_116839 : Nat := 118140960795 + 116839 * 2 ^ 59
def prefixEnd_116839 : Nat := 4983230072969 + 3 ^ 40 * 116839 * 2
def baseEnd_116839 : Nat := 19998188730257866858391

theorem tailTrace_116839 : CollatzResearch.WordTrace tailWord_116839 prefixEnd_116839 19998188730257866858391 := by
  unfold tailWord_116839
  simp only [CollatzResearch.WordTrace]
  refine ⟨4261468423719732357649571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2840978949146488238433047 4261468423719732357649571)
  ·
    refine ⟨6392202635579598536474357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4261468423719732357649571 6392202635579598536474357)
    ·
      refine ⟨599268997085587362794471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6392202635579598536474357 599268997085587362794471)
      ·
        refine ⟨898903495628381044191707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599268997085587362794471 898903495628381044191707)
        ·
          refine ⟨1348355243442571566287561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 898903495628381044191707 1348355243442571566287561)
          ·
            refine ⟨1011266432581928674715671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1348355243442571566287561 1011266432581928674715671)
            ·
              refine ⟨1516899648872893012073507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011266432581928674715671 1516899648872893012073507)
              ·
                refine ⟨2275349473309339518110261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516899648872893012073507 2275349473309339518110261)
                ·
                  refine ⟨213314013122750579822837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2275349473309339518110261 213314013122750579822837)
                  ·
                    refine ⟨19998188730257866858391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 213314013122750579822837 19998188730257866858391)
                    ·
                      rfl

theorem cell23_116839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_116839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116839 prefixEnd_116839 := by exact prefixLift 116839
  have htrace : WordTrace (prefixWord ++ tailWord_116839) baseStart_116839 baseEnd_116839 := by
    simpa [prefixWord, tailWord_116839, baseEnd_116839] using wordTrace_append hprefix tailTrace_116839
  have hstable : (prefixWord ++ tailWord_116839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116839).length < 2 ^ (prefixWord ++ tailWord_116839).sum := by decide
  have hdescent : baseEnd_116839 < baseStart_116839 := by decide
  rcases family_descends (prefixWord ++ tailWord_116839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116889 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 3, 2, 4]
def baseStart_116889 : Nat := 118140960795 + 116889 * 2 ^ 59
def prefixEnd_116889 : Nat := 4983230072969 + 3 ^ 40 * 116889 * 2
def baseEnd_116889 : Nat := 60020240223498404949943

theorem tailTrace_116889 : CollatzResearch.WordTrace tailWord_116889 prefixEnd_116889 60020240223498404949943 := by
  unfold tailWord_116889
  simp only [CollatzResearch.WordTrace]
  refine ⟨4263292073538590896969721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2842194715692393931313147 4263292073538590896969721)
  ·
    refine ⟨3197469055153943172727291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4263292073538590896969721 3197469055153943172727291)
    ·
      refine ⟨4796203582730914759090937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3197469055153943172727291 4796203582730914759090937)
      ·
        refine ⟨3597152687048186069318203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4796203582730914759090937 3597152687048186069318203)
        ·
          refine ⟨5395729030572279103977305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3597152687048186069318203 5395729030572279103977305)
          ·
            refine ⟨4046796772929209327982979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5395729030572279103977305 4046796772929209327982979)
            ·
              refine ⟨6070195159393813991974469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4046796772929209327982979 6070195159393813991974469)
              ·
                refine ⟨1138161592386340123495213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6070195159393813991974469 1138161592386340123495213)
                ·
                  refine ⟨426810597144877546310705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1138161592386340123495213 426810597144877546310705)
                  ·
                    refine ⟨320107947858658159733029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 426810597144877546310705 320107947858658159733029)
                    ·
                      refine ⟨60020240223498404949943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 320107947858658159733029 60020240223498404949943)
                      ·
                        rfl

theorem cell23_116889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_116889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116889 prefixEnd_116889 := by exact prefixLift 116889
  have htrace : WordTrace (prefixWord ++ tailWord_116889) baseStart_116889 baseEnd_116889 := by
    simpa [prefixWord, tailWord_116889, baseEnd_116889] using wordTrace_append hprefix tailTrace_116889
  have hstable : (prefixWord ++ tailWord_116889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116889).length < 2 ^ (prefixWord ++ tailWord_116889).sum := by decide
  have hdescent : baseEnd_116889 < baseStart_116889 := by decide
  rcases family_descends (prefixWord ++ tailWord_116889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116896 : List Nat := [2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 5]
def baseStart_116896 : Nat := 118140960795 + 116896 * 2 ^ 59
def prefixEnd_116896 : Nat := 4983230072969 + 3 ^ 40 * 116896 * 2
def baseEnd_116896 : Nat := 60023834588079877562411

theorem tailTrace_116896 : CollatzResearch.WordTrace tailWord_116896 prefixEnd_116896 60023834588079877562411 := by
  unfold tailWord_116896
  simp only [CollatzResearch.WordTrace]
  refine ⟨2131773692256615546237271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2842364923008820728316361 2131773692256615546237271)
  ·
    refine ⟨3197660538384923319355907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2131773692256615546237271 3197660538384923319355907)
    ·
      refine ⟨4796490807577384979033861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3197660538384923319355907 4796490807577384979033861)
      ·
        refine ⟨899342026420759683568849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4796490807577384979033861 899342026420759683568849)
        ·
          refine ⟨674506519815569762676637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 899342026420759683568849 674506519815569762676637)
          ·
            refine ⟨252939944930838661003739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 674506519815569762676637 252939944930838661003739)
            ·
              refine ⟨379409917396257991505609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252939944930838661003739 379409917396257991505609)
              ·
                refine ⟨284557438047193493629207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379409917396257991505609 284557438047193493629207)
                ·
                  refine ⟨426836157070790240443811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284557438047193493629207 426836157070790240443811)
                  ·
                    refine ⟨640254235606185360665717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 426836157070790240443811 640254235606185360665717)
                    ·
                      refine ⟨60023834588079877562411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 640254235606185360665717 60023834588079877562411)
                      ·
                        rfl

theorem cell23_116896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_116896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116896 prefixEnd_116896 := by exact prefixLift 116896
  have htrace : WordTrace (prefixWord ++ tailWord_116896) baseStart_116896 baseEnd_116896 := by
    simpa [prefixWord, tailWord_116896, baseEnd_116896] using wordTrace_append hprefix tailTrace_116896
  have hstable : (prefixWord ++ tailWord_116896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116896).length < 2 ^ (prefixWord ++ tailWord_116896).sum := by decide
  have hdescent : baseEnd_116896 < baseStart_116896 := by decide
  rcases family_descends (prefixWord ++ tailWord_116896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116930 : List Nat := [3, 5, 1, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_116930 : Nat := 118140960795 + 116930 * 2 ^ 59
def prefixEnd_116930 : Nat := 4983230072969 + 3 ^ 40 * 116930 * 2
def baseEnd_116930 : Nat := 60041292930332744537255

theorem tailTrace_116930 : CollatzResearch.WordTrace tailWord_116930 prefixEnd_116930 60041292930332744537255 := by
  unfold tailWord_116930
  simp only [CollatzResearch.WordTrace]
  refine ⟨1066196866597513724803061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2843191644260036599474829 1066196866597513724803061)
  ·
    refine ⟨99955956243516911700287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1066196866597513724803061 99955956243516911700287)
    ·
      refine ⟨149933934365275367550431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99955956243516911700287 149933934365275367550431)
      ·
        refine ⟨224900901547913051325647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149933934365275367550431 224900901547913051325647)
        ·
          refine ⟨337351352321869576988471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224900901547913051325647 337351352321869576988471)
          ·
            refine ⟨506027028482804365482707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337351352321869576988471 506027028482804365482707)
            ·
              refine ⟨759040542724206548224061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506027028482804365482707 759040542724206548224061)
              ·
                refine ⟨284640203521577455584023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 759040542724206548224061 284640203521577455584023)
                ·
                  refine ⟨426960305282366183376035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284640203521577455584023 426960305282366183376035)
                  ·
                    refine ⟨640440457923549275064053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 426960305282366183376035 640440457923549275064053)
                    ·
                      refine ⟨60041292930332744537255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 640440457923549275064053 60041292930332744537255)
                      ·
                        rfl

theorem cell23_116930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_116930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116930 prefixEnd_116930 := by exact prefixLift 116930
  have htrace : WordTrace (prefixWord ++ tailWord_116930) baseStart_116930 baseEnd_116930 := by
    simpa [prefixWord, tailWord_116930, baseEnd_116930] using wordTrace_append hprefix tailTrace_116930
  have hstable : (prefixWord ++ tailWord_116930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116930).length < 2 ^ (prefixWord ++ tailWord_116930).sum := by decide
  have hdescent : baseEnd_116930 < baseStart_116930 := by decide
  rcases family_descends (prefixWord ++ tailWord_116930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116939 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 5]
def baseStart_116939 : Nat := 118140960795 + 116939 * 2 ^ 59
def prefixEnd_116939 : Nat := 4983230072969 + 3 ^ 40 * 116939 * 2
def baseEnd_116939 : Nat := 60045914256223209324713

theorem tailTrace_116939 : CollatzResearch.WordTrace tailWord_116939 prefixEnd_116939 60045914256223209324713 := by
  unfold tailWord_116939
  simp only [CollatzResearch.WordTrace]
  refine ⟨4265115723357449436289871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2843410482238299624193247 4265115723357449436289871)
  ·
    refine ⟨6397673585036174154434807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4265115723357449436289871 6397673585036174154434807)
    ·
      refine ⟨9596510377554261231652211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6397673585036174154434807 9596510377554261231652211)
      ·
        refine ⟨14394765566331391847478317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9596510377554261231652211 14394765566331391847478317)
        ·
          refine ⟨5398037087374271942804369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14394765566331391847478317 5398037087374271942804369)
          ·
            refine ⟨4048527815530703957103277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5398037087374271942804369 4048527815530703957103277)
            ·
              refine ⟨1518197930824013983913729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4048527815530703957103277 1518197930824013983913729)
              ·
                refine ⟨1138648448118010487935297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1518197930824013983913729 1138648448118010487935297)
                ·
                  refine ⟨853986336088507865951473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1138648448118010487935297 853986336088507865951473)
                  ·
                    refine ⟨640489752066380899463605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 853986336088507865951473 640489752066380899463605)
                    ·
                      refine ⟨60045914256223209324713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 640489752066380899463605 60045914256223209324713)
                      ·
                        rfl

theorem cell23_116939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 5].length) (baseStart_116939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116939 prefixEnd_116939 := by exact prefixLift 116939
  have htrace : WordTrace (prefixWord ++ tailWord_116939) baseStart_116939 baseEnd_116939 := by
    simpa [prefixWord, tailWord_116939, baseEnd_116939] using wordTrace_append hprefix tailTrace_116939
  have hstable : (prefixWord ++ tailWord_116939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116939).length < 2 ^ (prefixWord ++ tailWord_116939).sum := by decide
  have hdescent : baseEnd_116939 < baseStart_116939 := by decide
  rcases family_descends (prefixWord ++ tailWord_116939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116943 : List Nat := [1, 1, 2, 1, 1, 3, 4, 4, 2, 1, 3]
def baseStart_116943 : Nat := 118140960795 + 116943 * 2 ^ 59
def prefixEnd_116943 : Nat := 4983230072969 + 3 ^ 40 * 116943 * 2
def baseEnd_116943 : Nat := 60047968178841193674695

theorem tailTrace_116943 : CollatzResearch.WordTrace tailWord_116943 prefixEnd_116943 60047968178841193674695 := by
  unfold tailWord_116943
  simp only [CollatzResearch.WordTrace]
  refine ⟨4265261615342958119435483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2843507743561972079623655 4265261615342958119435483)
  ·
    refine ⟨6397892423014437179153225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4265261615342958119435483 6397892423014437179153225)
    ·
      refine ⟨4798419317260827884364919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6397892423014437179153225 4798419317260827884364919)
      ·
        refine ⟨7197628975891241826547379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4798419317260827884364919 7197628975891241826547379)
        ·
          refine ⟨10796443463836862739821069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7197628975891241826547379 10796443463836862739821069)
          ·
            refine ⟨4048666298938823527432901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10796443463836862739821069 4048666298938823527432901)
            ·
              refine ⟨759124931051029411393669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4048666298938823527432901 759124931051029411393669)
              ·
                refine ⟨142335924572068014636313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 759124931051029411393669 142335924572068014636313)
                ·
                  refine ⟨106751943429051010977235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142335924572068014636313 106751943429051010977235)
                  ·
                    refine ⟨160127915143576516465853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106751943429051010977235 160127915143576516465853)
                    ·
                      refine ⟨60047968178841193674695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 160127915143576516465853 60047968178841193674695)
                      ·
                        rfl

theorem cell23_116943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 1, 3].length) (baseStart_116943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116943 prefixEnd_116943 := by exact prefixLift 116943
  have htrace : WordTrace (prefixWord ++ tailWord_116943) baseStart_116943 baseEnd_116943 := by
    simpa [prefixWord, tailWord_116943, baseEnd_116943] using wordTrace_append hprefix tailTrace_116943
  have hstable : (prefixWord ++ tailWord_116943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116943).length < 2 ^ (prefixWord ++ tailWord_116943).sum := by decide
  have hdescent : baseEnd_116943 < baseStart_116943 := by decide
  rcases family_descends (prefixWord ++ tailWord_116943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116959 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 1, 8]
def baseStart_116959 : Nat := 118140960795 + 116959 * 2 ^ 59
def prefixEnd_116959 : Nat := 4983230072969 + 3 ^ 40 * 116959 * 2
def baseEnd_116959 : Nat := 20018727956437710358207

theorem tailTrace_116959 : CollatzResearch.WordTrace tailWord_116959 prefixEnd_116959 20018727956437710358207 := by
  unfold tailWord_116959
  simp only [CollatzResearch.WordTrace]
  refine ⟨4265845183284992852017931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2843896788856661901345287 4265845183284992852017931)
  ·
    refine ⟨6398767774927489278026897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4265845183284992852017931 6398767774927489278026897)
    ·
      refine ⟨4799075831195616958520173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6398767774927489278026897 4799075831195616958520173)
      ·
        refine ⟨1799653436698356359445065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4799075831195616958520173 1799653436698356359445065)
        ·
          refine ⟨1349740077523767269583799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1799653436698356359445065 1349740077523767269583799)
          ·
            refine ⟨2024610116285650904375699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349740077523767269583799 2024610116285650904375699)
            ·
              refine ⟨3036915174428476356563549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2024610116285650904375699 3036915174428476356563549)
              ·
                refine ⟨1138843190410678633711331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3036915174428476356563549 1138843190410678633711331)
                ·
                  refine ⟨1708264785616017950566997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1138843190410678633711331 1708264785616017950566997)
                  ·
                    refine ⟨20018727956437710358207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1708264785616017950566997 20018727956437710358207)
                    ·
                      rfl

theorem cell23_116959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 8].length) (baseStart_116959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116959 prefixEnd_116959 := by exact prefixLift 116959
  have htrace : WordTrace (prefixWord ++ tailWord_116959) baseStart_116959 baseEnd_116959 := by
    simpa [prefixWord, tailWord_116959, baseEnd_116959] using wordTrace_append hprefix tailTrace_116959
  have hstable : (prefixWord ++ tailWord_116959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116959).length < 2 ^ (prefixWord ++ tailWord_116959).sum := by decide
  have hdescent : baseEnd_116959 < baseStart_116959 := by decide
  rcases family_descends (prefixWord ++ tailWord_116959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116969 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 3, 3, 5]
def baseStart_116969 : Nat := 118140960795 + 116969 * 2 ^ 59
def prefixEnd_116969 : Nat := 4983230072969 + 3 ^ 40 * 116969 * 2
def baseEnd_116969 : Nat := 60061318675858091949575

theorem tailTrace_116969 : CollatzResearch.WordTrace tailWord_116969 prefixEnd_116969 60061318675858091949575 := by
  unfold tailWord_116969
  simp only [CollatzResearch.WordTrace]
  refine ⟨4266209913248764559881961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2844139942165843039921307 4266209913248764559881961)
  ·
    refine ⟨3199657434936573419911471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4266209913248764559881961 3199657434936573419911471)
    ·
      refine ⟨4799486152404860129867207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3199657434936573419911471 4799486152404860129867207)
      ·
        refine ⟨7199229228607290194800811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4799486152404860129867207 7199229228607290194800811)
        ·
          refine ⟨10798843842910935292201217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7199229228607290194800811 10798843842910935292201217)
          ·
            refine ⟨8099132882183201469150913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10798843842910935292201217 8099132882183201469150913)
            ·
              refine ⟨6074349661637401101863185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8099132882183201469150913 6074349661637401101863185)
              ·
                refine ⟨4555762246228050826397389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6074349661637401101863185 4555762246228050826397389)
                ·
                  refine ⟨1708410842335519059899021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4555762246228050826397389 1708410842335519059899021)
                  ·
                    refine ⟨640654065875819647462133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1708410842335519059899021 640654065875819647462133)
                    ·
                      refine ⟨60061318675858091949575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 640654065875819647462133 60061318675858091949575)
                      ·
                        rfl

theorem cell23_116969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_116969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116969 prefixEnd_116969 := by exact prefixLift 116969
  have htrace : WordTrace (prefixWord ++ tailWord_116969) baseStart_116969 baseEnd_116969 := by
    simpa [prefixWord, tailWord_116969, baseEnd_116969] using wordTrace_append hprefix tailTrace_116969
  have hstable : (prefixWord ++ tailWord_116969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116969).length < 2 ^ (prefixWord ++ tailWord_116969).sum := by decide
  have hdescent : baseEnd_116969 < baseStart_116969 := by decide
  rcases family_descends (prefixWord ++ tailWord_116969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116986 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5]
def baseStart_116986 : Nat := 118140960795 + 116986 * 2 ^ 59
def prefixEnd_116986 : Nat := 4983230072969 + 3 ^ 40 * 116986 * 2
def baseEnd_116986 : Nat := 60070047846984525436997

theorem tailTrace_116986 : CollatzResearch.WordTrace tailWord_116986 prefixEnd_116986 60070047846984525436997 := by
  unfold tailWord_116986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1066707488546794115812703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2844553302791450975500541 1066707488546794115812703)
  ·
    refine ⟨1600061232820191173719055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1066707488546794115812703 1600061232820191173719055)
    ·
      refine ⟨2400091849230286760578583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1600061232820191173719055 2400091849230286760578583)
      ·
        refine ⟨3600137773845430140867875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2400091849230286760578583 3600137773845430140867875)
        ·
          refine ⟨5400206660768145211301813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3600137773845430140867875 5400206660768145211301813)
          ·
            refine ⟨506269374447013613559545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5400206660768145211301813 506269374447013613559545)
            ·
              refine ⟨379702030835260210169659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506269374447013613559545 379702030835260210169659)
              ·
                refine ⟨569553046252890315254489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379702030835260210169659 569553046252890315254489)
                ·
                  refine ⟨427164784689667736440867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 569553046252890315254489 427164784689667736440867)
                  ·
                    refine ⟨640747177034501604661301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 427164784689667736440867 640747177034501604661301)
                    ·
                      refine ⟨60070047846984525436997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 640747177034501604661301 60070047846984525436997)
                      ·
                        rfl

theorem cell23_116986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_116986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_116986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_116986 prefixEnd_116986 := by exact prefixLift 116986
  have htrace : WordTrace (prefixWord ++ tailWord_116986) baseStart_116986 baseEnd_116986 := by
    simpa [prefixWord, tailWord_116986, baseEnd_116986] using wordTrace_append hprefix tailTrace_116986
  have hstable : (prefixWord ++ tailWord_116986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116986).length < 2 ^ (prefixWord ++ tailWord_116986).sum := by decide
  have hdescent : baseEnd_116986 < baseStart_116986 := by decide
  rcases family_descends (prefixWord ++ tailWord_116986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117006 : List Nat := [4, 1, 1, 2, 1, 2, 2, 3, 7]
def baseStart_117006 : Nat := 118140960795 + 117006 * 2 ^ 59
def prefixEnd_117006 : Nat := 4983230072969 + 3 ^ 40 * 117006 * 2
def baseEnd_117006 : Nat := 6675590828897160798545

theorem tailTrace_117006 : CollatzResearch.WordTrace tailWord_117006 prefixEnd_117006 6675590828897160798545 := by
  unfold tailWord_117006
  simp only [CollatzResearch.WordTrace]
  refine ⟨533444926764339984872359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2845039609409813252652581 533444926764339984872359)
  ·
    refine ⟨800167390146509977308539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 533444926764339984872359 800167390146509977308539)
    ·
      refine ⟨1200251085219764965962809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 800167390146509977308539 1200251085219764965962809)
      ·
        refine ⟨900188313914823724472107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1200251085219764965962809 900188313914823724472107)
        ·
          refine ⟨1350282470872235586708161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900188313914823724472107 1350282470872235586708161)
          ·
            refine ⟨1012711853154176690031121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1350282470872235586708161 1012711853154176690031121)
            ·
              refine ⟨759533889865632517523341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1012711853154176690031121 759533889865632517523341)
              ·
                refine ⟨284825208699612194071253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 759533889865632517523341 284825208699612194071253)
                ·
                  refine ⟨6675590828897160798545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 284825208699612194071253 6675590828897160798545)
                  ·
                    rfl

theorem cell23_117006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_117006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117006 prefixEnd_117006 := by exact prefixLift 117006
  have htrace : WordTrace (prefixWord ++ tailWord_117006) baseStart_117006 baseEnd_117006 := by
    simpa [prefixWord, tailWord_117006, baseEnd_117006] using wordTrace_append hprefix tailTrace_117006
  have hstable : (prefixWord ++ tailWord_117006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117006).length < 2 ^ (prefixWord ++ tailWord_117006).sum := by decide
  have hdescent : baseEnd_117006 < baseStart_117006 := by decide
  rcases family_descends (prefixWord ++ tailWord_117006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117038 : List Nat := [4, 1, 3, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_117038 : Nat := 118140960795 + 117038 * 2 ^ 59
def prefixEnd_117038 : Nat := 4983230072969 + 3 ^ 40 * 117038 * 2
def baseEnd_117038 : Nat := 60096748841018321986759

theorem tailTrace_117038 : CollatzResearch.WordTrace tailWord_117038 prefixEnd_117038 60096748841018321986759 := by
  unfold tailWord_117038
  simp only [CollatzResearch.WordTrace]
  refine ⟨533590818749848668017971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2845817699999192896095845 533590818749848668017971)
  ·
    refine ⟨800386228124773002026957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 533590818749848668017971 800386228124773002026957)
    ·
      refine ⟨300144835546789875760109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 800386228124773002026957 300144835546789875760109)
      ·
        refine ⟨112554313330046203410041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300144835546789875760109 112554313330046203410041)
        ·
          refine ⟨84415734997534652557531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112554313330046203410041 84415734997534652557531)
          ·
            refine ⟨126623602496301978836297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84415734997534652557531 126623602496301978836297)
            ·
              refine ⟨94967701872226484127223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126623602496301978836297 94967701872226484127223)
              ·
                refine ⟨142451552808339726190835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94967701872226484127223 142451552808339726190835)
                ·
                  refine ⟨213677329212509589286253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142451552808339726190835 213677329212509589286253)
                  ·
                    refine ⟨80128998454691095982345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 213677329212509589286253 80128998454691095982345)
                    ·
                      refine ⟨60096748841018321986759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 80128998454691095982345 60096748841018321986759)
                      ·
                        rfl

theorem cell23_117038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_117038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117038 prefixEnd_117038 := by exact prefixLift 117038
  have htrace : WordTrace (prefixWord ++ tailWord_117038) baseStart_117038 baseEnd_117038 := by
    simpa [prefixWord, tailWord_117038, baseEnd_117038] using wordTrace_append hprefix tailTrace_117038
  have hstable : (prefixWord ++ tailWord_117038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117038).length < 2 ^ (prefixWord ++ tailWord_117038).sum := by decide
  have hdescent : baseEnd_117038 < baseStart_117038 := by decide
  rcases family_descends (prefixWord ++ tailWord_117038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117093 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 1, 4, 3]
def baseStart_117093 : Nat := 118140960795 + 117093 * 2 ^ 59
def prefixEnd_117093 : Nat := 4983230072969 + 3 ^ 40 * 117093 * 2
def baseEnd_117093 : Nat := 60124990277015606799005

theorem tailTrace_117093 : CollatzResearch.WordTrace tailWord_117093 prefixEnd_117093 60124990277015606799005 := by
  unfold tailWord_117093
  simp only [CollatzResearch.WordTrace]
  refine ⟨4270732564799533737395933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2847155043199689158263955 4270732564799533737395933)
  ·
    refine ⟨1601524711799825151523475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4270732564799533737395933 1601524711799825151523475)
    ·
      refine ⟨2402287067699737727285213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1601524711799825151523475 2402287067699737727285213)
      ·
        refine ⟨900857650387401647731955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2402287067699737727285213 900857650387401647731955)
        ·
          refine ⟨1351286475581102471597933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900857650387401647731955 1351286475581102471597933)
          ·
            refine ⟨506732428342913426849225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1351286475581102471597933 506732428342913426849225)
            ·
              refine ⟨380049321257185070136919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506732428342913426849225 380049321257185070136919)
              ·
                refine ⟨570073981885777605205379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380049321257185070136919 570073981885777605205379)
                ·
                  refine ⟨855110972828666407808069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570073981885777605205379 855110972828666407808069)
                  ·
                    refine ⟨160333307405374951464013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 855110972828666407808069 160333307405374951464013)
                    ·
                      refine ⟨60124990277015606799005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 160333307405374951464013 60124990277015606799005)
                      ·
                        rfl

theorem cell23_117093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_117093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117093 prefixEnd_117093 := by exact prefixLift 117093
  have htrace : WordTrace (prefixWord ++ tailWord_117093) baseStart_117093 baseEnd_117093 := by
    simpa [prefixWord, tailWord_117093, baseEnd_117093] using wordTrace_append hprefix tailTrace_117093
  have hstable : (prefixWord ++ tailWord_117093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117093).length < 2 ^ (prefixWord ++ tailWord_117093).sum := by decide
  have hdescent : baseEnd_117093 < baseStart_117093 := by decide
  rcases family_descends (prefixWord ++ tailWord_117093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117116 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_117116 : Nat := 118140960795 + 117116 * 2 ^ 59
def prefixEnd_117116 : Nat := 4983230072969 + 3 ^ 40 * 117116 * 2
def baseEnd_117116 : Nat := 60136800332069016811399

theorem tailTrace_117116 : CollatzResearch.WordTrace tailWord_117116 prefixEnd_117116 60136800332069016811399 := by
  unfold tailWord_117116
  simp only [CollatzResearch.WordTrace]
  refine ⟨2135785721858104332741601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2847714295810805776988801 2135785721858104332741601)
  ·
    refine ⟨1601839291393578249556201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2135785721858104332741601 1601839291393578249556201)
    ·
      refine ⟨1201379468545183687167151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1601839291393578249556201 1201379468545183687167151)
      ·
        refine ⟨1802069202817775530750727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1201379468545183687167151 1802069202817775530750727)
        ·
          refine ⟨2703103804226663296126091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1802069202817775530750727 2703103804226663296126091)
          ·
            refine ⟨4054655706339994944189137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2703103804226663296126091 4054655706339994944189137)
            ·
              refine ⟨3040991779754996208141853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4054655706339994944189137 3040991779754996208141853)
              ·
                refine ⟨1140371917408123578053195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3040991779754996208141853 1140371917408123578053195)
                ·
                  refine ⟨1710557876112185367079793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140371917408123578053195 1710557876112185367079793)
                  ·
                    refine ⟨1282918407084139025309845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1710557876112185367079793 1282918407084139025309845)
                    ·
                      refine ⟨60136800332069016811399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1282918407084139025309845 60136800332069016811399)
                      ·
                        rfl

theorem cell23_117116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_117116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117116 prefixEnd_117116 := by exact prefixLift 117116
  have htrace : WordTrace (prefixWord ++ tailWord_117116) baseStart_117116 baseEnd_117116 := by
    simpa [prefixWord, tailWord_117116, baseEnd_117116] using wordTrace_append hprefix tailTrace_117116
  have hstable : (prefixWord ++ tailWord_117116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117116).length < 2 ^ (prefixWord ++ tailWord_117116).sum := by decide
  have hdescent : baseEnd_117116 < baseStart_117116 := by decide
  rcases family_descends (prefixWord ++ tailWord_117116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117157 : List Nat := [1, 3, 1, 2, 1, 1, 4, 5, 1, 1, 3]
def baseStart_117157 : Nat := 118140960795 + 117157 * 2 ^ 59
def prefixEnd_117157 : Nat := 4983230072969 + 3 ^ 40 * 117157 * 2
def baseEnd_117157 : Nat := 60157853038903356398711

theorem tailTrace_117157 : CollatzResearch.WordTrace tailWord_117157 prefixEnd_117157 60157853038903356398711 := by
  unfold tailWord_117157
  simp only [CollatzResearch.WordTrace]
  refine ⟨4273066836567672667725725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2848711224378448445150483 4273066836567672667725725)
  ·
    refine ⟨1602400063712877250397147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4273066836567672667725725 1602400063712877250397147)
    ·
      refine ⟨2403600095569315875595721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1602400063712877250397147 2403600095569315875595721)
      ·
        refine ⟨1802700071676986906696791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2403600095569315875595721 1802700071676986906696791)
        ·
          refine ⟨2704050107515480360045187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1802700071676986906696791 2704050107515480360045187)
          ·
            refine ⟨4056075161273220540067781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2704050107515480360045187 4056075161273220540067781)
            ·
              refine ⟨760514092738728851262709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4056075161273220540067781 760514092738728851262709)
              ·
                refine ⟨71298196194255829805879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 760514092738728851262709 71298196194255829805879)
                ·
                  refine ⟨106947294291383744708819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71298196194255829805879 106947294291383744708819)
                  ·
                    refine ⟨160420941437075617063229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106947294291383744708819 160420941437075617063229)
                    ·
                      refine ⟨60157853038903356398711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 160420941437075617063229 60157853038903356398711)
                      ·
                        rfl

theorem cell23_117157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 1, 1, 3].length) (baseStart_117157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117157 prefixEnd_117157 := by exact prefixLift 117157
  have htrace : WordTrace (prefixWord ++ tailWord_117157) baseStart_117157 baseEnd_117157 := by
    simpa [prefixWord, tailWord_117157, baseEnd_117157] using wordTrace_append hprefix tailTrace_117157
  have hstable : (prefixWord ++ tailWord_117157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117157).length < 2 ^ (prefixWord ++ tailWord_117157).sum := by decide
  have hdescent : baseEnd_117157 < baseStart_117157 := by decide
  rcases family_descends (prefixWord ++ tailWord_117157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117180 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 3, 1, 4]
def baseStart_117180 : Nat := 118140960795 + 117180 * 2 ^ 59
def prefixEnd_117180 : Nat := 4983230072969 + 3 ^ 40 * 117180 * 2
def baseEnd_117180 : Nat := 60169663093956766411105

theorem tailTrace_117180 : CollatzResearch.WordTrace tailWord_117180 prefixEnd_117180 60169663093956766411105 := by
  unfold tailWord_117180
  simp only [CollatzResearch.WordTrace]
  refine ⟨2136952857742173797906497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2849270476989565063875329 2136952857742173797906497)
  ·
    refine ⟨1602714643306630348429873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2136952857742173797906497 1602714643306630348429873)
    ·
      refine ⟨1202035982479972761322405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1602714643306630348429873 1202035982479972761322405)
      ·
        refine ⟨225381746714994892747951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1202035982479972761322405 225381746714994892747951)
        ·
          refine ⟨338072620072492339121927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225381746714994892747951 338072620072492339121927)
          ·
            refine ⟨507108930108738508682891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338072620072492339121927 507108930108738508682891)
            ·
              refine ⟨760663395163107763024337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507108930108738508682891 760663395163107763024337)
              ·
                refine ⟨570497546372330822268253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 760663395163107763024337 570497546372330822268253)
                ·
                  refine ⟨213936579889624058350595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570497546372330822268253 213936579889624058350595)
                  ·
                    refine ⟨320904869834436087525893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 213936579889624058350595 320904869834436087525893)
                    ·
                      refine ⟨60169663093956766411105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 320904869834436087525893 60169663093956766411105)
                      ·
                        rfl

theorem cell23_117180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_117180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117180 prefixEnd_117180 := by exact prefixLift 117180
  have htrace : WordTrace (prefixWord ++ tailWord_117180) baseStart_117180 baseEnd_117180 := by
    simpa [prefixWord, tailWord_117180, baseEnd_117180] using wordTrace_append hprefix tailTrace_117180
  have hstable : (prefixWord ++ tailWord_117180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117180).length < 2 ^ (prefixWord ++ tailWord_117180).sum := by decide
  have hdescent : baseEnd_117180 < baseStart_117180 := by decide
  rcases family_descends (prefixWord ++ tailWord_117180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117193 : List Nat := [1, 2, 1, 1, 2, 1, 5, 3, 1, 2, 4]
def baseStart_117193 : Nat := 118140960795 + 117193 * 2 ^ 59
def prefixEnd_117193 : Nat := 4983230072969 + 3 ^ 40 * 117193 * 2
def baseEnd_117193 : Nat := 60176338342465215548545

theorem tailTrace_117193 : CollatzResearch.WordTrace tailWord_117193 prefixEnd_117193 60176338342465215548545 := by
  unfold tailWord_117193
  simp only [CollatzResearch.WordTrace]
  refine ⟨4274379864437250816036233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2849586576291500544024155 4274379864437250816036233)
  ·
    refine ⟨3205784898327938112027175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4274379864437250816036233 3205784898327938112027175)
    ·
      refine ⟨4808677347491907168040763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3205784898327938112027175 4808677347491907168040763)
      ·
        refine ⟨7213016021237860752061145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4808677347491907168040763 7213016021237860752061145)
        ·
          refine ⟨5409762015928395564045859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7213016021237860752061145 5409762015928395564045859)
          ·
            refine ⟨8114643023892593346068789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5409762015928395564045859 8114643023892593346068789)
            ·
              refine ⟨760747783489930626193949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8114643023892593346068789 760747783489930626193949)
              ·
                refine ⟨285280418808723984822731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 760747783489930626193949 285280418808723984822731)
                ·
                  refine ⟨427920628213085977234097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285280418808723984822731 427920628213085977234097)
                  ·
                    refine ⟨320940471159814482925573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 427920628213085977234097 320940471159814482925573)
                    ·
                      refine ⟨60176338342465215548545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 320940471159814482925573 60176338342465215548545)
                      ·
                        rfl

theorem cell23_117193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 2, 4].length) (baseStart_117193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117193 prefixEnd_117193 := by exact prefixLift 117193
  have htrace : WordTrace (prefixWord ++ tailWord_117193) baseStart_117193 baseEnd_117193 := by
    simpa [prefixWord, tailWord_117193, baseEnd_117193] using wordTrace_append hprefix tailTrace_117193
  have hstable : (prefixWord ++ tailWord_117193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117193).length < 2 ^ (prefixWord ++ tailWord_117193).sum := by decide
  have hdescent : baseEnd_117193 < baseStart_117193 := by decide
  rcases family_descends (prefixWord ++ tailWord_117193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117253 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 2, 3, 4]
def baseStart_117253 : Nat := 118140960795 + 117253 * 2 ^ 59
def prefixEnd_117253 : Nat := 4983230072969 + 3 ^ 40 * 117253 * 2
def baseEnd_117253 : Nat := 60207147181734980798269

theorem tailTrace_117253 : CollatzResearch.WordTrace tailWord_117253 prefixEnd_117253 60207147181734980798269 := by
  unfold tailWord_117253
  simp only [CollatzResearch.WordTrace]
  refine ⟨4276568244219881063220413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2851045496146587375480275 4276568244219881063220413)
  ·
    refine ⟨1603713091582455398707655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4276568244219881063220413 1603713091582455398707655)
    ·
      refine ⟨2405569637373683098061483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1603713091582455398707655 2405569637373683098061483)
      ·
        refine ⟨3608354456060524647092225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2405569637373683098061483 3608354456060524647092225)
        ·
          refine ⟨2706265842045393485319169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3608354456060524647092225 2706265842045393485319169)
          ·
            refine ⟨2029699381534045113989377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2706265842045393485319169 2029699381534045113989377)
            ·
              refine ⟨1522274536150533835492033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2029699381534045113989377 1522274536150533835492033)
              ·
                refine ⟨1141705902112900376619025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1522274536150533835492033 1141705902112900376619025)
                ·
                  refine ⟨856279426584675282464269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1141705902112900376619025 856279426584675282464269)
                  ·
                    refine ⟨321104784969253230924101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 856279426584675282464269 321104784969253230924101)
                    ·
                      refine ⟨60207147181734980798269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 321104784969253230924101 60207147181734980798269)
                      ·
                        rfl

theorem cell23_117253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_117253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117253 prefixEnd_117253 := by exact prefixLift 117253
  have htrace : WordTrace (prefixWord ++ tailWord_117253) baseStart_117253 baseEnd_117253 := by
    simpa [prefixWord, tailWord_117253, baseEnd_117253] using wordTrace_append hprefix tailTrace_117253
  have hstable : (prefixWord ++ tailWord_117253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117253).length < 2 ^ (prefixWord ++ tailWord_117253).sum := by decide
  have hdescent : baseEnd_117253 < baseStart_117253 := by decide
  rcases family_descends (prefixWord ++ tailWord_117253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117254 : List Nat := [6, 2, 1, 1, 1, 2, 1, 9]
def baseStart_117254 : Nat := 118140960795 + 117254 * 2 ^ 59
def prefixEnd_117254 : Nat := 4983230072969 + 3 ^ 40 * 117254 * 2
def baseEnd_117254 : Nat := 2229913357866276921695

theorem tailTrace_117254 : CollatzResearch.WordTrace tailWord_117254 prefixEnd_117254 2229913357866276921695 := by
  unfold tailWord_117254
  simp only [CollatzResearch.WordTrace]
  refine ⟨133643897413008069812713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2851069811477505489337877 133643897413008069812713)
  ·
    refine ⟨100232923059756052359535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133643897413008069812713 100232923059756052359535)
    ·
      refine ⟨150349384589634078539303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100232923059756052359535 150349384589634078539303)
      ·
        refine ⟨225524076884451117808955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150349384589634078539303 225524076884451117808955)
        ·
          refine ⟨338286115326676676713433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225524076884451117808955 338286115326676676713433)
          ·
            refine ⟨253714586495007507535075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338286115326676676713433 253714586495007507535075)
            ·
              refine ⟨380571879742511261302613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253714586495007507535075 380571879742511261302613)
              ·
                refine ⟨2229913357866276921695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 380571879742511261302613 2229913357866276921695)
                ·
                  rfl

theorem cell23_117254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_117254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117254 prefixEnd_117254 := by exact prefixLift 117254
  have htrace : WordTrace (prefixWord ++ tailWord_117254) baseStart_117254 baseEnd_117254 := by
    simpa [prefixWord, tailWord_117254, baseEnd_117254] using wordTrace_append hprefix tailTrace_117254
  have hstable : (prefixWord ++ tailWord_117254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117254).length < 2 ^ (prefixWord ++ tailWord_117254).sum := by decide
  have hdescent : baseEnd_117254 < baseStart_117254 := by decide
  rcases family_descends (prefixWord ++ tailWord_117254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117273 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 2, 1, 5]
def baseStart_117273 : Nat := 118140960795 + 117273 * 2 ^ 59
def prefixEnd_117273 : Nat := 4983230072969 + 3 ^ 40 * 117273 * 2
def baseEnd_117273 : Nat := 60217416794824902548177

theorem tailTrace_117273 : CollatzResearch.WordTrace tailWord_117273 prefixEnd_117273 60217416794824902548177 := by
  unfold tailWord_117273
  simp only [CollatzResearch.WordTrace]
  refine ⟨4277297704147424478948473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2851531802764949652632315 4277297704147424478948473)
  ·
    refine ⟨3207973278110568359211355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4277297704147424478948473 3207973278110568359211355)
    ·
      refine ⟨4811959917165852538817033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3207973278110568359211355 4811959917165852538817033)
      ·
        refine ⟨3608969937874389404112775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4811959917165852538817033 3608969937874389404112775)
        ·
          refine ⟨5413454906811584106169163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3608969937874389404112775 5413454906811584106169163)
          ·
            refine ⟨8120182360217376159253745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5413454906811584106169163 8120182360217376159253745)
            ·
              refine ⟨6090136770163032119440309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8120182360217376159253745 6090136770163032119440309)
              ·
                refine ⟨570950322202784261197529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6090136770163032119440309 570950322202784261197529)
                ·
                  refine ⟨428212741652088195898147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 570950322202784261197529 428212741652088195898147)
                  ·
                    refine ⟨642319112478132293847221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 428212741652088195898147 642319112478132293847221)
                    ·
                      refine ⟨60217416794824902548177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 642319112478132293847221 60217416794824902548177)
                      ·
                        rfl

theorem cell23_117273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_117273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117273 prefixEnd_117273 := by exact prefixLift 117273
  have htrace : WordTrace (prefixWord ++ tailWord_117273) baseStart_117273 baseEnd_117273 := by
    simpa [prefixWord, tailWord_117273, baseEnd_117273] using wordTrace_append hprefix tailTrace_117273
  have hstable : (prefixWord ++ tailWord_117273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117273).length < 2 ^ (prefixWord ++ tailWord_117273).sum := by decide
  have hdescent : baseEnd_117273 < baseStart_117273 := by decide
  rcases family_descends (prefixWord ++ tailWord_117273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117304 : List Nat := [2, 1, 2, 1, 4, 1, 3, 3, 2, 2, 2]
def baseStart_117304 : Nat := 118140960795 + 117304 * 2 ^ 59
def prefixEnd_117304 : Nat := 4983230072969 + 3 ^ 40 * 117304 * 2
def baseEnd_117304 : Nat := 60233334695114281260535

theorem tailTrace_117304 : CollatzResearch.WordTrace tailWord_117304 prefixEnd_117304 60233334695114281260535 := by
  unfold tailWord_117304
  simp only [CollatzResearch.WordTrace]
  refine ⟨2139214183517558386663483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2852285578023411182217977 2139214183517558386663483)
  ·
    refine ⟨3208821275276337579995225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2139214183517558386663483 3208821275276337579995225)
    ·
      refine ⟨2406615956457253184996419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3208821275276337579995225 2406615956457253184996419)
      ·
        refine ⟨3609923934685879777494629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2406615956457253184996419 3609923934685879777494629)
        ·
          refine ⟨676860737753602458280243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3609923934685879777494629 676860737753602458280243)
          ·
            refine ⟨1015291106630403687420365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676860737753602458280243 1015291106630403687420365)
            ·
              refine ⟨380734164986401382782637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1015291106630403687420365 380734164986401382782637)
              ·
                refine ⟨142775311869900518543489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 380734164986401382782637 142775311869900518543489)
                ·
                  refine ⟨107081483902425388907617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142775311869900518543489 107081483902425388907617)
                  ·
                    refine ⟨80311112926819041680713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107081483902425388907617 80311112926819041680713)
                    ·
                      refine ⟨60233334695114281260535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 80311112926819041680713 60233334695114281260535)
                      ·
                        rfl

theorem cell23_117304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 2, 2, 2].length) (baseStart_117304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117304 prefixEnd_117304 := by exact prefixLift 117304
  have htrace : WordTrace (prefixWord ++ tailWord_117304) baseStart_117304 baseEnd_117304 := by
    simpa [prefixWord, tailWord_117304, baseEnd_117304] using wordTrace_append hprefix tailTrace_117304
  have hstable : (prefixWord ++ tailWord_117304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117304).length < 2 ^ (prefixWord ++ tailWord_117304).sum := by decide
  have hdescent : baseEnd_117304 < baseStart_117304 := by decide
  rcases family_descends (prefixWord ++ tailWord_117304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117323 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 1, 7]
def baseStart_117323 : Nat := 118140960795 + 117323 * 2 ^ 59
def prefixEnd_117323 : Nat := 4983230072969 + 3 ^ 40 * 117323 * 2
def baseEnd_117323 : Nat := 20081030275849902307649

theorem tailTrace_117323 : CollatzResearch.WordTrace tailWord_117323 prefixEnd_117323 20081030275849902307649 := by
  unfold tailWord_117323
  simp only [CollatzResearch.WordTrace]
  refine ⟨4279121353966283018268623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2852747569310855345512415 4279121353966283018268623)
  ·
    refine ⟨6418682030949424527402935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4279121353966283018268623 6418682030949424527402935)
    ·
      refine ⟨9628023046424136791104403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6418682030949424527402935 9628023046424136791104403)
      ·
        refine ⟨14442034569636205186656605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9628023046424136791104403 14442034569636205186656605)
        ·
          refine ⟨5415762963613576944996227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14442034569636205186656605 5415762963613576944996227)
          ·
            refine ⟨8123644445420365417494341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5415762963613576944996227 8123644445420365417494341)
            ·
              refine ⟨1523183333516318515780189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8123644445420365417494341 1523183333516318515780189)
              ·
                refine ⟨571193750068619443417571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1523183333516318515780189 571193750068619443417571)
                ·
                  refine ⟨856790625102929165126357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 571193750068619443417571 856790625102929165126357)
                  ·
                    refine ⟨20081030275849902307649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 856790625102929165126357 20081030275849902307649)
                    ·
                      rfl

theorem cell23_117323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 7].length) (baseStart_117323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117323 prefixEnd_117323 := by exact prefixLift 117323
  have htrace : WordTrace (prefixWord ++ tailWord_117323) baseStart_117323 baseEnd_117323 := by
    simpa [prefixWord, tailWord_117323, baseEnd_117323] using wordTrace_append hprefix tailTrace_117323
  have hstable : (prefixWord ++ tailWord_117323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117323).length < 2 ^ (prefixWord ++ tailWord_117323).sum := by decide
  have hdescent : baseEnd_117323 < baseStart_117323 := by decide
  rcases family_descends (prefixWord ++ tailWord_117323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117353 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 2, 8]
def baseStart_117353 : Nat := 118140960795 + 117353 * 2 ^ 59
def prefixEnd_117353 : Nat := 4983230072969 + 3 ^ 40 * 117353 * 2
def baseEnd_117353 : Nat := 20086165082394863182603

theorem tailTrace_117353 : CollatzResearch.WordTrace tailWord_117353 prefixEnd_117353 20086165082394863182603 := by
  unfold tailWord_117353
  simp only [CollatzResearch.WordTrace]
  refine ⟨4280215543857598141860713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2853477029238398761240475 4280215543857598141860713)
  ·
    refine ⟨3210161657893198606395535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4280215543857598141860713 3210161657893198606395535)
    ·
      refine ⟨4815242486839797909593303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3210161657893198606395535 4815242486839797909593303)
      ·
        refine ⟨7222863730259696864389955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4815242486839797909593303 7222863730259696864389955)
        ·
          refine ⟨10834295595389545296584933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7222863730259696864389955 10834295595389545296584933)
          ·
            refine ⟨2031430424135539743109675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10834295595389545296584933 2031430424135539743109675)
            ·
              refine ⟨3047145636203309614664513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2031430424135539743109675 3047145636203309614664513)
              ·
                refine ⟨2285359227152482210998385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3047145636203309614664513 2285359227152482210998385)
                ·
                  refine ⟨1714019420364361658248789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2285359227152482210998385 1714019420364361658248789)
                  ·
                    refine ⟨20086165082394863182603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1714019420364361658248789 20086165082394863182603)
                    ·
                      rfl

theorem cell23_117353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 8].length) (baseStart_117353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117353 prefixEnd_117353 := by exact prefixLift 117353
  have htrace : WordTrace (prefixWord ++ tailWord_117353) baseStart_117353 baseEnd_117353 := by
    simpa [prefixWord, tailWord_117353, baseEnd_117353] using wordTrace_append hprefix tailTrace_117353
  have hstable : (prefixWord ++ tailWord_117353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117353).length < 2 ^ (prefixWord ++ tailWord_117353).sum := by decide
  have hdescent : baseEnd_117353 < baseStart_117353 := by decide
  rcases family_descends (prefixWord ++ tailWord_117353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117377 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 1, 6, 2]
def baseStart_117377 : Nat := 118140960795 + 117377 * 2 ^ 59
def prefixEnd_117377 : Nat := 4983230072969 + 3 ^ 40 * 117377 * 2
def baseEnd_117377 : Nat := 60270818782892495647699

theorem tailTrace_117377 : CollatzResearch.WordTrace tailWord_117377 prefixEnd_117377 60270818782892495647699 := by
  unfold tailWord_117377
  simp only [CollatzResearch.WordTrace]
  refine ⟨4281090895770650240734385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2854060597180433493822923 4281090895770650240734385)
  ·
    refine ⟨3210818171827987680550789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4281090895770650240734385 3210818171827987680550789)
    ·
      refine ⟨602028407217747690103273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3210818171827987680550789 602028407217747690103273)
      ·
        refine ⟨451521305413310767577455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602028407217747690103273 451521305413310767577455)
        ·
          refine ⟨677281958119966151366183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451521305413310767577455 677281958119966151366183)
          ·
            refine ⟨1015922937179949227049275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677281958119966151366183 1015922937179949227049275)
            ·
              refine ⟨1523884405769923840573913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015922937179949227049275 1523884405769923840573913)
              ·
                refine ⟨1142913304327442880430435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1523884405769923840573913 1142913304327442880430435)
                ·
                  refine ⟨1714369956491164320645653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142913304327442880430435 1714369956491164320645653)
                  ·
                    refine ⟨80361091710523327530265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1714369956491164320645653 80361091710523327530265)
                    ·
                      refine ⟨60270818782892495647699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 80361091710523327530265 60270818782892495647699)
                      ·
                        rfl

theorem cell23_117377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_117377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117377 prefixEnd_117377 := by exact prefixLift 117377
  have htrace : WordTrace (prefixWord ++ tailWord_117377) baseStart_117377 baseEnd_117377 := by
    simpa [prefixWord, tailWord_117377, baseEnd_117377] using wordTrace_append hprefix tailTrace_117377
  have hstable : (prefixWord ++ tailWord_117377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117377).length < 2 ^ (prefixWord ++ tailWord_117377).sum := by decide
  have hdescent : baseEnd_117377 < baseStart_117377 := by decide
  rcases family_descends (prefixWord ++ tailWord_117377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117390 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_117390 : Nat := 118140960795 + 117390 * 2 ^ 59
def prefixEnd_117390 : Nat := 4983230072969 + 3 ^ 40 * 117390 * 2
def baseEnd_117390 : Nat := 60277494031400944785139

theorem tailTrace_117390 : CollatzResearch.WordTrace tailWord_117390 prefixEnd_117390 60277494031400944785139 := by
  unfold tailWord_117390
  simp only [CollatzResearch.WordTrace]
  refine ⟨535195630590444182619703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2854376696482368973971749 535195630590444182619703)
  ·
    refine ⟨802793445885666273929555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 535195630590444182619703 802793445885666273929555)
    ·
      refine ⟨1204190168828499410894333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 802793445885666273929555 1204190168828499410894333)
      ·
        refine ⟨451571313310687279085375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1204190168828499410894333 451571313310687279085375)
        ·
          refine ⟨677356969966030918628063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451571313310687279085375 677356969966030918628063)
          ·
            refine ⟨1016035454949046377942095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677356969966030918628063 1016035454949046377942095)
            ·
              refine ⟨1524053182423569566913143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016035454949046377942095 1524053182423569566913143)
              ·
                refine ⟨2286079773635354350369715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1524053182423569566913143 2286079773635354350369715)
                ·
                  refine ⟨3429119660453031525554573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2286079773635354350369715 3429119660453031525554573)
                  ·
                    refine ⟨1285919872669886822082965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3429119660453031525554573 1285919872669886822082965)
                    ·
                      refine ⟨60277494031400944785139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1285919872669886822082965 60277494031400944785139)
                      ·
                        rfl

theorem cell23_117390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_117390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117390 prefixEnd_117390 := by exact prefixLift 117390
  have htrace : WordTrace (prefixWord ++ tailWord_117390) baseStart_117390 baseEnd_117390 := by
    simpa [prefixWord, tailWord_117390, baseEnd_117390] using wordTrace_append hprefix tailTrace_117390
  have hstable : (prefixWord ++ tailWord_117390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117390).length < 2 ^ (prefixWord ++ tailWord_117390).sum := by decide
  have hdescent : baseEnd_117390 < baseStart_117390 := by decide
  rcases family_descends (prefixWord ++ tailWord_117390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117394 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_117394 : Nat := 118140960795 + 117394 * 2 ^ 59
def prefixEnd_117394 : Nat := 4983230072969 + 3 ^ 40 * 117394 * 2
def baseEnd_117394 : Nat := 60279547954018929135121

theorem tailTrace_117394 : CollatzResearch.WordTrace tailWord_117394 prefixEnd_117394 60279547954018929135121 := by
  unfold tailWord_117394
  simp only [CollatzResearch.WordTrace]
  refine ⟨1070427734177265536025809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2854473957806041429402157 1070427734177265536025809)
  ·
    refine ⟨802820800632949152019357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1070427734177265536025809 802820800632949152019357)
    ·
      refine ⟨301057800237355932007259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 802820800632949152019357 301057800237355932007259)
      ·
        refine ⟨451586700356033898010889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301057800237355932007259 451586700356033898010889)
        ·
          refine ⟨338690025267025423508167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451586700356033898010889 338690025267025423508167)
          ·
            refine ⟨508035037900538135262251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338690025267025423508167 508035037900538135262251)
            ·
              refine ⟨762052556850807202893377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508035037900538135262251 762052556850807202893377)
              ·
                refine ⟨571539417638105402170033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 762052556850807202893377 571539417638105402170033)
                ·
                  refine ⟨428654563228579051627525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 571539417638105402170033 428654563228579051627525)
                  ·
                    refine ⟨80372730605358572180161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 428654563228579051627525 80372730605358572180161)
                    ·
                      refine ⟨60279547954018929135121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 80372730605358572180161 60279547954018929135121)
                      ·
                        rfl

theorem cell23_117394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_117394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117394 prefixEnd_117394 := by exact prefixLift 117394
  have htrace : WordTrace (prefixWord ++ tailWord_117394) baseStart_117394 baseEnd_117394 := by
    simpa [prefixWord, tailWord_117394, baseEnd_117394] using wordTrace_append hprefix tailTrace_117394
  have hstable : (prefixWord ++ tailWord_117394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117394).length < 2 ^ (prefixWord ++ tailWord_117394).sum := by decide
  have hdescent : baseEnd_117394 < baseStart_117394 := by decide
  rcases family_descends (prefixWord ++ tailWord_117394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117400 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 8]
def baseStart_117400 : Nat := 118140960795 + 117400 * 2 ^ 59
def prefixEnd_117400 : Nat := 4983230072969 + 3 ^ 40 * 117400 * 2
def baseEnd_117400 : Nat := 6698069870882878406677

theorem tailTrace_117400 : CollatzResearch.WordTrace tailWord_117400 prefixEnd_117400 6698069870882878406677 := by
  unfold tailWord_117400
  simp only [CollatzResearch.WordTrace]
  refine ⟨2140964887343662584410827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2854619849791550112547769 2140964887343662584410827)
  ·
    refine ⟨3211447331015493876616241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2140964887343662584410827 3211447331015493876616241)
    ·
      refine ⟨2408585498261620407462181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3211447331015493876616241 2408585498261620407462181)
      ·
        refine ⟨451609780924053826399159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2408585498261620407462181 451609780924053826399159)
        ·
          refine ⟨677414671386080739598739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451609780924053826399159 677414671386080739598739)
          ·
            refine ⟨1016122007079121109398109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677414671386080739598739 1016122007079121109398109)
            ·
              refine ⟨381045752654670416024291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1016122007079121109398109 381045752654670416024291)
              ·
                refine ⟨571568628982005624036437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381045752654670416024291 571568628982005624036437)
                ·
                  refine ⟨6698069870882878406677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 571568628982005624036437 6698069870882878406677)
                  ·
                    rfl

theorem cell23_117400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 8].length) (baseStart_117400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117400 prefixEnd_117400 := by exact prefixLift 117400
  have htrace : WordTrace (prefixWord ++ tailWord_117400) baseStart_117400 baseEnd_117400 := by
    simpa [prefixWord, tailWord_117400, baseEnd_117400] using wordTrace_append hprefix tailTrace_117400
  have hstable : (prefixWord ++ tailWord_117400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117400).length < 2 ^ (prefixWord ++ tailWord_117400).sum := by decide
  have hdescent : baseEnd_117400 < baseStart_117400 := by decide
  rcases family_descends (prefixWord ++ tailWord_117400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117404 : List Nat := [2, 2, 3, 2, 2, 2, 2, 1, 3, 4]
def baseStart_117404 : Nat := 118140960795 + 117404 * 2 ^ 59
def prefixEnd_117404 : Nat := 4983230072969 + 3 ^ 40 * 117404 * 2
def baseEnd_117404 : Nat := 20094894253521296670025

theorem tailTrace_117404 : CollatzResearch.WordTrace tailWord_117404 prefixEnd_117404 20094894253521296670025 := by
  unfold tailWord_117404
  simp only [CollatzResearch.WordTrace]
  refine ⟨2141037833336416925983633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2854717111115222567978177 2141037833336416925983633)
  ·
    refine ⟨1605778375002312694487725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2141037833336416925983633 1605778375002312694487725)
    ·
      refine ⟨602166890625867260432897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1605778375002312694487725 602166890625867260432897)
      ·
        refine ⟨451625167969400445324673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602166890625867260432897 451625167969400445324673)
        ·
          refine ⟨338718875977050333993505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451625167969400445324673 338718875977050333993505)
          ·
            refine ⟨254039156982787750495129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338718875977050333993505 254039156982787750495129)
            ·
              refine ⟨190529367737090812871347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254039156982787750495129 190529367737090812871347)
              ·
                refine ⟨285794051605636219307021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190529367737090812871347 285794051605636219307021)
                ·
                  refine ⟨107172769352113582240133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285794051605636219307021 107172769352113582240133)
                  ·
                    refine ⟨20094894253521296670025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107172769352113582240133 20094894253521296670025)
                    ·
                      rfl

theorem cell23_117404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_117404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117404 prefixEnd_117404 := by exact prefixLift 117404
  have htrace : WordTrace (prefixWord ++ tailWord_117404) baseStart_117404 baseEnd_117404 := by
    simpa [prefixWord, tailWord_117404, baseEnd_117404] using wordTrace_append hprefix tailTrace_117404
  have hstable : (prefixWord ++ tailWord_117404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117404).length < 2 ^ (prefixWord ++ tailWord_117404).sum := by decide
  have hdescent : baseEnd_117404 < baseStart_117404 := by decide
  rcases family_descends (prefixWord ++ tailWord_117404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117454 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2]
def baseStart_117454 : Nat := 118140960795 + 117454 * 2 ^ 59
def prefixEnd_117454 : Nat := 4983230072969 + 3 ^ 40 * 117454 * 2
def baseEnd_117454 : Nat := 60310356793288694384845

theorem tailTrace_117454 : CollatzResearch.WordTrace tailWord_117454 prefixEnd_117454 60310356793288694384845 := by
  unfold tailWord_117454
  simp only [CollatzResearch.WordTrace]
  refine ⟨535487414561461548910927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2855932877661128260858277 535487414561461548910927)
  ·
    refine ⟨803231121842192323366391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 535487414561461548910927 803231121842192323366391)
    ·
      refine ⟨1204846682763288485049587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 803231121842192323366391 1204846682763288485049587)
      ·
        refine ⟨1807270024144932727574381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1204846682763288485049587 1807270024144932727574381)
        ·
          refine ⟨677726259054349772840393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1807270024144932727574381 677726259054349772840393)
          ·
            refine ⟨508294694290762329630295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 677726259054349772840393 508294694290762329630295)
            ·
              refine ⟨762442041436143494445443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508294694290762329630295 762442041436143494445443)
              ·
                refine ⟨1143663062154215241668165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762442041436143494445443 1143663062154215241668165)
                ·
                  refine ⟨214436824153915357812781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1143663062154215241668165 214436824153915357812781)
                  ·
                    refine ⟨80413809057718259179793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 214436824153915357812781 80413809057718259179793)
                    ·
                      refine ⟨60310356793288694384845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 80413809057718259179793 60310356793288694384845)
                      ·
                        rfl

theorem cell23_117454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_117454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117454 prefixEnd_117454 := by exact prefixLift 117454
  have htrace : WordTrace (prefixWord ++ tailWord_117454) baseStart_117454 baseEnd_117454 := by
    simpa [prefixWord, tailWord_117454, baseEnd_117454] using wordTrace_append hprefix tailTrace_117454
  have hstable : (prefixWord ++ tailWord_117454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117454).length < 2 ^ (prefixWord ++ tailWord_117454).sum := by decide
  have hdescent : baseEnd_117454 < baseStart_117454 := by decide
  rcases family_descends (prefixWord ++ tailWord_117454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117484 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 5, 2, 2]
def baseStart_117484 : Nat := 118140960795 + 117484 * 2 ^ 59
def prefixEnd_117484 : Nat := 4983230072969 + 3 ^ 40 * 117484 * 2
def baseEnd_117484 : Nat := 60325761212923577009707

theorem tailTrace_117484 : CollatzResearch.WordTrace tailWord_117484 prefixEnd_117484 60325761212923577009707 := by
  unfold tailWord_117484
  simp only [CollatzResearch.WordTrace]
  refine ⟨2142496753191503757439753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2856662337588671676586337 2142496753191503757439753)
  ·
    refine ⟨1606872564893627818079815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2142496753191503757439753 1606872564893627818079815)
    ·
      refine ⟨2410308847340441727119723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1606872564893627818079815 2410308847340441727119723)
      ·
        refine ⟨3615463271010662590679585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2410308847340441727119723 3615463271010662590679585)
        ·
          refine ⟨2711597453257996943009689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3615463271010662590679585 2711597453257996943009689)
          ·
            refine ⟨2033698089943497707257267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2711597453257996943009689 2033698089943497707257267)
            ·
              refine ⟨3050547134915246560885901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2033698089943497707257267 3050547134915246560885901)
              ·
                refine ⟨1143955175593217460332213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3050547134915246560885901 1143955175593217460332213)
                ·
                  refine ⟨107245797711864136906145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1143955175593217460332213 107245797711864136906145)
                  ·
                    refine ⟨80434348283898102679609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107245797711864136906145 80434348283898102679609)
                    ·
                      refine ⟨60325761212923577009707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 80434348283898102679609 60325761212923577009707)
                      ·
                        rfl

theorem cell23_117484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 2, 2].length) (baseStart_117484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117484 prefixEnd_117484 := by exact prefixLift 117484
  have htrace : WordTrace (prefixWord ++ tailWord_117484) baseStart_117484 baseEnd_117484 := by
    simpa [prefixWord, tailWord_117484, baseEnd_117484] using wordTrace_append hprefix tailTrace_117484
  have hstable : (prefixWord ++ tailWord_117484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117484).length < 2 ^ (prefixWord ++ tailWord_117484).sum := by decide
  have hdescent : baseEnd_117484 < baseStart_117484 := by decide
  rcases family_descends (prefixWord ++ tailWord_117484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117511 : List Nat := [1, 1, 4, 4, 1, 2, 2, 2, 2, 4]
def baseStart_117511 : Nat := 118140960795 + 117511 * 2 ^ 59
def prefixEnd_117511 : Nat := 4983230072969 + 3 ^ 40 * 117511 * 2
def baseEnd_117511 : Nat := 20113208396864990457361

theorem tailTrace_117511 : CollatzResearch.WordTrace tailWord_117511 prefixEnd_117511 20113208396864990457361 := by
  unfold tailWord_117511
  simp only [CollatzResearch.WordTrace]
  refine ⟨4285978277285191126112387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2857318851523460750741591 4285978277285191126112387)
  ·
    refine ⟨6428967415927786689168581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4285978277285191126112387 6428967415927786689168581)
    ·
      refine ⟨1205431390486460004219109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6428967415927786689168581 1205431390486460004219109)
      ·
        refine ⟨226018385716211250791083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1205431390486460004219109 226018385716211250791083)
        ·
          refine ⟨339027578574316876186625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226018385716211250791083 339027578574316876186625)
          ·
            refine ⟨254270683930737657139969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339027578574316876186625 254270683930737657139969)
            ·
              refine ⟨190703012948053242854977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254270683930737657139969 190703012948053242854977)
              ·
                refine ⟨143027259711039932141233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190703012948053242854977 143027259711039932141233)
                ·
                  refine ⟨107270444783279949105925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143027259711039932141233 107270444783279949105925)
                  ·
                    refine ⟨20113208396864990457361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107270444783279949105925 20113208396864990457361)
                    ·
                      rfl

theorem cell23_117511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_117511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117511 prefixEnd_117511 := by exact prefixLift 117511
  have htrace : WordTrace (prefixWord ++ tailWord_117511) baseStart_117511 baseEnd_117511 := by
    simpa [prefixWord, tailWord_117511, baseEnd_117511] using wordTrace_append hprefix tailTrace_117511
  have hstable : (prefixWord ++ tailWord_117511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117511).length < 2 ^ (prefixWord ++ tailWord_117511).sum := by decide
  have hdescent : baseEnd_117511 < baseStart_117511 := by decide
  rcases family_descends (prefixWord ++ tailWord_117511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117567 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 2, 6]
def baseStart_117567 : Nat := 118140960795 + 117567 * 2 ^ 59
def prefixEnd_117567 : Nat := 4983230072969 + 3 ^ 40 * 117567 * 2
def baseEnd_117567 : Nat := 20122793369082250757275

theorem tailTrace_117567 : CollatzResearch.WordTrace tailWord_117567 prefixEnd_117567 20122793369082250757275 := by
  unfold tailWord_117567
  simp only [CollatzResearch.WordTrace]
  refine ⟨4288020765082312690150955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2858680510054875126767303 4288020765082312690150955)
  ·
    refine ⟨6432031147623469035226433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4288020765082312690150955 6432031147623469035226433)
    ·
      refine ⟨4824023360717601776419825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6432031147623469035226433 4824023360717601776419825)
      ·
        refine ⟨3618017520538201332314869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4824023360717601776419825 3618017520538201332314869)
        ·
          refine ⟨339189142550456374904519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3618017520538201332314869 339189142550456374904519)
          ·
            refine ⟨508783713825684562356779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339189142550456374904519 508783713825684562356779)
            ·
              refine ⟨763175570738526843535169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508783713825684562356779 763175570738526843535169)
              ·
                refine ⟨572381678053895132651377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 763175570738526843535169 572381678053895132651377)
                ·
                  refine ⟨429286258540421349488533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572381678053895132651377 429286258540421349488533)
                  ·
                    refine ⟨20122793369082250757275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 429286258540421349488533 20122793369082250757275)
                    ·
                      rfl

theorem cell23_117567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 6].length) (baseStart_117567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117567 prefixEnd_117567 := by exact prefixLift 117567
  have htrace : WordTrace (prefixWord ++ tailWord_117567) baseStart_117567 baseEnd_117567 := by
    simpa [prefixWord, tailWord_117567, baseEnd_117567] using wordTrace_append hprefix tailTrace_117567
  have hstable : (prefixWord ++ tailWord_117567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117567).length < 2 ^ (prefixWord ++ tailWord_117567).sum := by decide
  have hdescent : baseEnd_117567 < baseStart_117567 := by decide
  rcases family_descends (prefixWord ++ tailWord_117567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117591 : List Nat := [1, 1, 3, 2, 4, 1, 3, 1, 1, 4, 2]
def baseStart_117591 : Nat := 118140960795 + 117591 * 2 ^ 59
def prefixEnd_117591 : Nat := 4983230072969 + 3 ^ 40 * 117591 * 2
def baseEnd_117591 : Nat := 60380703642954658371715

theorem tailTrace_117591 : CollatzResearch.WordTrace tailWord_117591 prefixEnd_117591 60380703642954658371715 := by
  unfold tailWord_117591
  simp only [CollatzResearch.WordTrace]
  refine ⟨4288896116995364789024627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2859264077996909859349751 4288896116995364789024627)
  ·
    refine ⟨6433344175493047183536941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4288896116995364789024627 6433344175493047183536941)
    ·
      refine ⟨2412504065809892693826353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6433344175493047183536941 2412504065809892693826353)
      ·
        refine ⟨1809378049357419520369765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2412504065809892693826353 1809378049357419520369765)
        ·
          refine ⟨339258384254516160069331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1809378049357419520369765 339258384254516160069331)
          ·
            refine ⟨508887576381774240103997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339258384254516160069331 508887576381774240103997)
            ·
              refine ⟨190832841143165340038999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 508887576381774240103997 190832841143165340038999)
              ·
                refine ⟨286249261714748010058499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190832841143165340038999 286249261714748010058499)
                ·
                  refine ⟨429373892572122015087749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 286249261714748010058499 429373892572122015087749)
                  ·
                    refine ⟨80507604857272877828953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 429373892572122015087749 80507604857272877828953)
                    ·
                      refine ⟨60380703642954658371715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 80507604857272877828953 60380703642954658371715)
                      ·
                        rfl

theorem cell23_117591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_117591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117591 prefixEnd_117591 := by exact prefixLift 117591
  have htrace : WordTrace (prefixWord ++ tailWord_117591) baseStart_117591 baseEnd_117591 := by
    simpa [prefixWord, tailWord_117591, baseEnd_117591] using wordTrace_append hprefix tailTrace_117591
  have hstable : (prefixWord ++ tailWord_117591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117591).length < 2 ^ (prefixWord ++ tailWord_117591).sum := by decide
  have hdescent : baseEnd_117591 < baseStart_117591 := by decide
  rcases family_descends (prefixWord ++ tailWord_117591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117627 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 4, 5]
def baseStart_117627 : Nat := 118140960795 + 117627 * 2 ^ 59
def prefixEnd_117627 : Nat := 4983230072969 + 3 ^ 40 * 117627 * 2
def baseEnd_117627 : Nat := 20133062982172172507183

theorem tailTrace_117627 : CollatzResearch.WordTrace tailWord_117627 prefixEnd_117627 20133062982172172507183 := by
  unfold tailWord_117627
  simp only [CollatzResearch.WordTrace]
  refine ⟨4290209144864942937335135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2860139429909961958223423 4290209144864942937335135)
  ·
    refine ⟨6435313717297414406002703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4290209144864942937335135 6435313717297414406002703)
    ·
      refine ⟨9652970575946121609004055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6435313717297414406002703 9652970575946121609004055)
      ·
        refine ⟨14479455863919182413506083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9652970575946121609004055 14479455863919182413506083)
        ·
          refine ⟨21719183795878773620259125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14479455863919182413506083 21719183795878773620259125)
          ·
            refine ⟨2036173480863635026899293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21719183795878773620259125 2036173480863635026899293)
            ·
              refine ⟨763565055323863135087235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2036173480863635026899293 763565055323863135087235)
              ·
                refine ⟨1145347582985794702630853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763565055323863135087235 1145347582985794702630853)
                ·
                  refine ⟨214752671809836506743285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1145347582985794702630853 214752671809836506743285)
                  ·
                    refine ⟨20133062982172172507183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 214752671809836506743285 20133062982172172507183)
                    ·
                      rfl

theorem cell23_117627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 5].length) (baseStart_117627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117627 prefixEnd_117627 := by exact prefixLift 117627
  have htrace : WordTrace (prefixWord ++ tailWord_117627) baseStart_117627 baseEnd_117627 := by
    simpa [prefixWord, tailWord_117627, baseEnd_117627] using wordTrace_append hprefix tailTrace_117627
  have hstable : (prefixWord ++ tailWord_117627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117627).length < 2 ^ (prefixWord ++ tailWord_117627).sum := by decide
  have hdescent : baseEnd_117627 < baseStart_117627 := by decide
  rcases family_descends (prefixWord ++ tailWord_117627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117637 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 1, 1, 7]
def baseStart_117637 : Nat := 118140960795 + 117637 * 2 ^ 59
def prefixEnd_117637 : Nat := 4983230072969 + 3 ^ 40 * 117637 * 2
def baseEnd_117637 : Nat := 60404323753061478396503

theorem tailTrace_117637 : CollatzResearch.WordTrace tailWord_117637 prefixEnd_117637 60404323753061478396503 := by
  unfold tailWord_117637
  simp only [CollatzResearch.WordTrace]
  refine ⟨4290573874828714645199165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2860382583219143096799443 4290573874828714645199165)
  ·
    refine ⟨1608965203060767991949687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4290573874828714645199165 1608965203060767991949687)
    ·
      refine ⟨2413447804591151987924531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1608965203060767991949687 2413447804591151987924531)
      ·
        refine ⟨3620171706886727981886797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2413447804591151987924531 3620171706886727981886797)
        ·
          refine ⟨1357564390082522993207549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3620171706886727981886797 1357564390082522993207549)
          ·
            refine ⟨509086646280946122452831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1357564390082522993207549 509086646280946122452831)
            ·
              refine ⟨763629969421419183679247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509086646280946122452831 763629969421419183679247)
              ·
                refine ⟨1145444954132128775518871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763629969421419183679247 1145444954132128775518871)
                ·
                  refine ⟨1718167431198193163278307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1145444954132128775518871 1718167431198193163278307)
                  ·
                    refine ⟨2577251146797289744917461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1718167431198193163278307 2577251146797289744917461)
                    ·
                      refine ⟨60404323753061478396503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2577251146797289744917461 60404323753061478396503)
                      ·
                        rfl

theorem cell23_117637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_117637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117637 prefixEnd_117637 := by exact prefixLift 117637
  have htrace : WordTrace (prefixWord ++ tailWord_117637) baseStart_117637 baseEnd_117637 := by
    simpa [prefixWord, tailWord_117637, baseEnd_117637] using wordTrace_append hprefix tailTrace_117637
  have hstable : (prefixWord ++ tailWord_117637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117637).length < 2 ^ (prefixWord ++ tailWord_117637).sum := by decide
  have hdescent : baseEnd_117637 < baseStart_117637 := by decide
  rcases family_descends (prefixWord ++ tailWord_117637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117642 : List Nat := [3, 1, 2, 4, 1, 3, 2, 1, 2, 2, 2]
def baseStart_117642 : Nat := 118140960795 + 117642 * 2 ^ 59
def prefixEnd_117642 : Nat := 4983230072969 + 3 ^ 40 * 117642 * 2
def baseEnd_117642 : Nat := 60406891156333958833981

theorem tailTrace_117642 : CollatzResearch.WordTrace tailWord_117642 prefixEnd_117642 60406891156333958833981 := by
  unfold tailWord_117642
  simp only [CollatzResearch.WordTrace]
  refine ⟨1072689059952650124782795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2860504159873733666087453 1072689059952650124782795)
  ·
    refine ⟨1609033589928975187174193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1072689059952650124782795 1609033589928975187174193)
    ·
      refine ⟨1206775192446731390380645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1609033589928975187174193 1206775192446731390380645)
      ·
        refine ⟨226270348583762135696371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1206775192446731390380645 226270348583762135696371)
        ·
          refine ⟨339405522875643203544557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226270348583762135696371 339405522875643203544557)
          ·
            refine ⟨127277071078366201329209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 339405522875643203544557 127277071078366201329209)
            ·
              refine ⟨95457803308774650996907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127277071078366201329209 95457803308774650996907)
              ·
                refine ⟨143186704963161976495361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95457803308774650996907 143186704963161976495361)
                ·
                  refine ⟨107390028722371482371521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143186704963161976495361 107390028722371482371521)
                  ·
                    refine ⟨80542521541778611778641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107390028722371482371521 80542521541778611778641)
                    ·
                      refine ⟨60406891156333958833981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 80542521541778611778641 60406891156333958833981)
                      ·
                        rfl

theorem cell23_117642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_117642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117642 prefixEnd_117642 := by exact prefixLift 117642
  have htrace : WordTrace (prefixWord ++ tailWord_117642) baseStart_117642 baseEnd_117642 := by
    simpa [prefixWord, tailWord_117642, baseEnd_117642] using wordTrace_append hprefix tailTrace_117642
  have hstable : (prefixWord ++ tailWord_117642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117642).length < 2 ^ (prefixWord ++ tailWord_117642).sum := by decide
  have hdescent : baseEnd_117642 < baseStart_117642 := by decide
  rcases family_descends (prefixWord ++ tailWord_117642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117664 : List Nat := [2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 4]
def baseStart_117664 : Nat := 118140960795 + 117664 * 2 ^ 59
def prefixEnd_117664 : Nat := 4983230072969 + 3 ^ 40 * 117664 * 2
def baseEnd_117664 : Nat := 60418187730732872758879

theorem tailTrace_117664 : CollatzResearch.WordTrace tailWord_117664 prefixEnd_117664 60418187730732872758879 := by
  unfold tailWord_117664
  simp only [CollatzResearch.WordTrace]
  refine ⟨2145779322865449128216023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2861039097153932170954697 2145779322865449128216023)
  ·
    refine ⟨3218668984298173692324035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2145779322865449128216023 3218668984298173692324035)
    ·
      refine ⟨4828003476447260538486053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3218668984298173692324035 4828003476447260538486053)
      ·
        refine ⟨905250651833861350966135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4828003476447260538486053 905250651833861350966135)
        ·
          refine ⟨1357875977750792026449203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905250651833861350966135 1357875977750792026449203)
          ·
            refine ⟨2036813966626188039673805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1357875977750792026449203 2036813966626188039673805)
            ·
              refine ⟨763805237484820514877677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2036813966626188039673805 763805237484820514877677)
              ·
                refine ⟨286426964056807693079129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 763805237484820514877677 286426964056807693079129)
                ·
                  refine ⟨214820223042605769809347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286426964056807693079129 214820223042605769809347)
                  ·
                    refine ⟨322230334563908654714021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 214820223042605769809347 322230334563908654714021)
                    ·
                      refine ⟨60418187730732872758879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 322230334563908654714021 60418187730732872758879)
                      ·
                        rfl

theorem cell23_117664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_117664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117664 prefixEnd_117664 := by exact prefixLift 117664
  have htrace : WordTrace (prefixWord ++ tailWord_117664) baseStart_117664 baseEnd_117664 := by
    simpa [prefixWord, tailWord_117664, baseEnd_117664] using wordTrace_append hprefix tailTrace_117664
  have hstable : (prefixWord ++ tailWord_117664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117664).length < 2 ^ (prefixWord ++ tailWord_117664).sum := by decide
  have hdescent : baseEnd_117664 < baseStart_117664 := by decide
  rcases family_descends (prefixWord ++ tailWord_117664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117687 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 8]
def baseStart_117687 : Nat := 118140960795 + 117687 * 2 ^ 59
def prefixEnd_117687 : Nat := 4983230072969 + 3 ^ 40 * 117687 * 2
def baseEnd_117687 : Nat := 6714444198420698085697

theorem tailTrace_117687 : CollatzResearch.WordTrace tailWord_117687 prefixEnd_117687 6714444198420698085697 := by
  unfold tailWord_117687
  simp only [CollatzResearch.WordTrace]
  refine ⟨4292397524647573184519315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2861598349765048789679543 4292397524647573184519315)
  ·
    refine ⟨6438596286971359776778973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4292397524647573184519315 6438596286971359776778973)
    ·
      refine ⟨2414473607614259916292115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6438596286971359776778973 2414473607614259916292115)
      ·
        refine ⟨3621710411421389874438173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2414473607614259916292115 3621710411421389874438173)
        ·
          refine ⟨1358141404283021202914315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3621710411421389874438173 1358141404283021202914315)
          ·
            refine ⟨2037212106424531804371473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1358141404283021202914315 2037212106424531804371473)
            ·
              refine ⟨1527909079818398853278605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2037212106424531804371473 1527909079818398853278605)
              ·
                refine ⟨572965904931899569979477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1527909079818398853278605 572965904931899569979477)
                ·
                  refine ⟨6714444198420698085697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 572965904931899569979477 6714444198420698085697)
                  ·
                    rfl

theorem cell23_117687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 8].length) (baseStart_117687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117687 prefixEnd_117687 := by exact prefixLift 117687
  have htrace : WordTrace (prefixWord ++ tailWord_117687) baseStart_117687 baseEnd_117687 := by
    simpa [prefixWord, tailWord_117687, baseEnd_117687] using wordTrace_append hprefix tailTrace_117687
  have hstable : (prefixWord ++ tailWord_117687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117687).length < 2 ^ (prefixWord ++ tailWord_117687).sum := by decide
  have hdescent : baseEnd_117687 < baseStart_117687 := by decide
  rcases family_descends (prefixWord ++ tailWord_117687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117718 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_117718 : Nat := 118140960795 + 117718 * 2 ^ 59
def prefixEnd_117718 : Nat := 4983230072969 + 3 ^ 40 * 117718 * 2
def baseEnd_117718 : Nat := 60445915686075661483631

theorem tailTrace_117718 : CollatzResearch.WordTrace tailWord_117718 prefixEnd_117718 60445915686075661483631 := by
  unfold tailWord_117718
  simp only [CollatzResearch.WordTrace]
  refine ⟨268345511720954092431113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2862352125023510319265205 268345511720954092431113)
  ·
    refine ⟨201259133790715569323335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268345511720954092431113 201259133790715569323335)
    ·
      refine ⟨301888700686073353985003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201259133790715569323335 301888700686073353985003)
      ·
        refine ⟨452833051029110030977505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301888700686073353985003 452833051029110030977505)
        ·
          refine ⟨339624788271832523233129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452833051029110030977505 339624788271832523233129)
          ·
            refine ⟨254718591203874392424847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339624788271832523233129 254718591203874392424847)
            ·
              refine ⟨382077886805811588637271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254718591203874392424847 382077886805811588637271)
              ·
                refine ⟨573116830208717382955907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382077886805811588637271 573116830208717382955907)
                ·
                  refine ⟨859675245313076074433861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 573116830208717382955907 859675245313076074433861)
                  ·
                    refine ⟨161189108496201763956349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 859675245313076074433861 161189108496201763956349)
                    ·
                      refine ⟨60445915686075661483631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 161189108496201763956349 60445915686075661483631)
                      ·
                        rfl

theorem cell23_117718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_117718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117718 prefixEnd_117718 := by exact prefixLift 117718
  have htrace : WordTrace (prefixWord ++ tailWord_117718) baseStart_117718 baseEnd_117718 := by
    simpa [prefixWord, tailWord_117718, baseEnd_117718] using wordTrace_append hprefix tailTrace_117718
  have hstable : (prefixWord ++ tailWord_117718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117718).length < 2 ^ (prefixWord ++ tailWord_117718).sum := by decide
  have hdescent : baseEnd_117718 < baseStart_117718 := by decide
  rcases family_descends (prefixWord ++ tailWord_117718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117725 : List Nat := [1, 4, 3, 1, 2, 2, 2, 3, 1, 4]
def baseStart_117725 : Nat := 118140960795 + 117725 * 2 ^ 59
def prefixEnd_117725 : Nat := 4983230072969 + 3 ^ 40 * 117725 * 2
def baseEnd_117725 : Nat := 20149836683552378032033

theorem tailTrace_117725 : CollatzResearch.WordTrace tailWord_117725 prefixEnd_117725 20149836683552378032033 := by
  unfold tailWord_117725
  simp only [CollatzResearch.WordTrace]
  refine ⟨4293783498509905674402629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2862522332339937116268419 4293783498509905674402629)
  ·
    refine ⟨805084405970607313950493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4293783498509905674402629 805084405970607313950493)
    ·
      refine ⟨301906652238977742731435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 805084405970607313950493 301906652238977742731435)
      ·
        refine ⟨452859978358466614097153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301906652238977742731435 452859978358466614097153)
        ·
          refine ⟨339644983768849960572865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452859978358466614097153 339644983768849960572865)
          ·
            refine ⟨254733737826637470429649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339644983768849960572865 254733737826637470429649)
            ·
              refine ⟨191050303369978102822237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254733737826637470429649 191050303369978102822237)
              ·
                refine ⟨71643863763741788558339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191050303369978102822237 71643863763741788558339)
                ·
                  refine ⟨107465795645612682837509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71643863763741788558339 107465795645612682837509)
                  ·
                    refine ⟨20149836683552378032033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107465795645612682837509 20149836683552378032033)
                    ·
                      rfl

theorem cell23_117725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_117725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117725 prefixEnd_117725 := by exact prefixLift 117725
  have htrace : WordTrace (prefixWord ++ tailWord_117725) baseStart_117725 baseEnd_117725 := by
    simpa [prefixWord, tailWord_117725, baseEnd_117725] using wordTrace_append hprefix tailTrace_117725
  have hstable : (prefixWord ++ tailWord_117725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117725).length < 2 ^ (prefixWord ++ tailWord_117725).sum := by decide
  have hdescent : baseEnd_117725 < baseStart_117725 := by decide
  rcases family_descends (prefixWord ++ tailWord_117725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117731 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 5, 1, 3]
def baseStart_117731 : Nat := 118140960795 + 117731 * 2 ^ 59
def prefixEnd_117731 : Nat := 4983230072969 + 3 ^ 40 * 117731 * 2
def baseEnd_117731 : Nat := 60452590934584110621071

theorem tailTrace_117731 : CollatzResearch.WordTrace tailWord_117731 prefixEnd_117731 60452590934584110621071 := by
  unfold tailWord_117731
  simp only [CollatzResearch.WordTrace]
  refine ⟨4294002336488168699121047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2862668224325445799414031 4294002336488168699121047)
  ·
    refine ⟨6441003504732253048681571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4294002336488168699121047 6441003504732253048681571)
    ·
      refine ⟨9661505257098379573022357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6441003504732253048681571 9661505257098379573022357)
      ·
        refine ⟨452883058926486542485423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9661505257098379573022357 452883058926486542485423)
        ·
          refine ⟨679324588389729813728135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452883058926486542485423 679324588389729813728135)
          ·
            refine ⟨1018986882584594720592203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679324588389729813728135 1018986882584594720592203)
            ·
              refine ⟨1528480323876892080888305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1018986882584594720592203 1528480323876892080888305)
              ·
                refine ⟨1146360242907669060666229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1528480323876892080888305 1146360242907669060666229)
                ·
                  refine ⟨107471272772593974437459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1146360242907669060666229 107471272772593974437459)
                  ·
                    refine ⟨161206909158890961656189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107471272772593974437459 161206909158890961656189)
                    ·
                      refine ⟨60452590934584110621071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 161206909158890961656189 60452590934584110621071)
                      ·
                        rfl

theorem cell23_117731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_117731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117731 prefixEnd_117731 := by exact prefixLift 117731
  have htrace : WordTrace (prefixWord ++ tailWord_117731) baseStart_117731 baseEnd_117731 := by
    simpa [prefixWord, tailWord_117731, baseEnd_117731] using wordTrace_append hprefix tailTrace_117731
  have hstable : (prefixWord ++ tailWord_117731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117731).length < 2 ^ (prefixWord ++ tailWord_117731).sum := by decide
  have hdescent : baseEnd_117731 < baseStart_117731 := by decide
  rcases family_descends (prefixWord ++ tailWord_117731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117747 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 2, 10]
def baseStart_117747 : Nat := 118140960795 + 117747 * 2 ^ 59
def prefixEnd_117747 : Nat := 4983230072969 + 3 ^ 40 * 117747 * 2
def baseEnd_117747 : Nat := 20153602208352016006999

theorem tailTrace_117747 : CollatzResearch.WordTrace tailWord_117747 prefixEnd_117747 20153602208352016006999 := by
  unfold tailWord_117747
  simp only [CollatzResearch.WordTrace]
  refine ⟨4294585904430203431703495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2863057269620135621135663 4294585904430203431703495)
  ·
    refine ⟨6441878856645305147555243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4294585904430203431703495 6441878856645305147555243)
    ·
      refine ⟨9662818284967957721332865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6441878856645305147555243 9662818284967957721332865)
      ·
        refine ⟨7247113713725968290999649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9662818284967957721332865 7247113713725968290999649)
        ·
          refine ⟨5435335285294476218249737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7247113713725968290999649 5435335285294476218249737)
          ·
            refine ⟨4076501463970857163687303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5435335285294476218249737 4076501463970857163687303)
            ·
              refine ⟨6114752195956285745530955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4076501463970857163687303 6114752195956285745530955)
              ·
                refine ⟨9172128293934428618296433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6114752195956285745530955 9172128293934428618296433)
                ·
                  refine ⟨6879096220450821463722325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9172128293934428618296433 6879096220450821463722325)
                  ·
                    refine ⟨20153602208352016006999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 6879096220450821463722325 20153602208352016006999)
                    ·
                      rfl

theorem cell23_117747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 10].length) (baseStart_117747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117747 prefixEnd_117747 := by exact prefixLift 117747
  have htrace : WordTrace (prefixWord ++ tailWord_117747) baseStart_117747 baseEnd_117747 := by
    simpa [prefixWord, tailWord_117747, baseEnd_117747] using wordTrace_append hprefix tailTrace_117747
  have hstable : (prefixWord ++ tailWord_117747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117747).length < 2 ^ (prefixWord ++ tailWord_117747).sum := by decide
  have hdescent : baseEnd_117747 < baseStart_117747 := by decide
  rcases family_descends (prefixWord ++ tailWord_117747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117754 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4]
def baseStart_117754 : Nat := 118140960795 + 117754 * 2 ^ 59
def prefixEnd_117754 : Nat := 4983230072969 + 3 ^ 40 * 117754 * 2
def baseEnd_117754 : Nat := 60464400989637520633465

theorem tailTrace_117754 : CollatzResearch.WordTrace tailWord_117754 prefixEnd_117754 60464400989637520633465 := by
  unfold tailWord_117754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1073710303851210906802079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2863227476936562418138877 1073710303851210906802079)
  ·
    refine ⟨1610565455776816360203119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1073710303851210906802079 1610565455776816360203119)
    ·
      refine ⟨2415848183665224540304679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1610565455776816360203119 2415848183665224540304679)
      ·
        refine ⟨3623772275497836810457019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2415848183665224540304679 3623772275497836810457019)
        ·
          refine ⟨5435658413246755215685529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3623772275497836810457019 5435658413246755215685529)
          ·
            refine ⟨4076743809935066411764147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5435658413246755215685529 4076743809935066411764147)
            ·
              refine ⟨6115115714902599617646221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4076743809935066411764147 6115115714902599617646221)
              ·
                refine ⟨2293168393088474856617333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6115115714902599617646221 2293168393088474856617333)
                ·
                  refine ⟨214984536852044517807875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2293168393088474856617333 214984536852044517807875)
                  ·
                    refine ⟨322476805278066776711813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 214984536852044517807875 322476805278066776711813)
                    ·
                      refine ⟨60464400989637520633465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 322476805278066776711813 60464400989637520633465)
                      ·
                        rfl

theorem cell23_117754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_117754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117754 prefixEnd_117754 := by exact prefixLift 117754
  have htrace : WordTrace (prefixWord ++ tailWord_117754) baseStart_117754 baseEnd_117754 := by
    simpa [prefixWord, tailWord_117754, baseEnd_117754] using wordTrace_append hprefix tailTrace_117754
  have hstable : (prefixWord ++ tailWord_117754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117754).length < 2 ^ (prefixWord ++ tailWord_117754).sum := by decide
  have hdescent : baseEnd_117754 < baseStart_117754 := by decide
  rcases family_descends (prefixWord ++ tailWord_117754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117771 : List Nat := [1, 1, 1, 1, 6, 2, 1, 4, 1, 1, 4]
def baseStart_117771 : Nat := 118140960795 + 117771 * 2 ^ 59
def prefixEnd_117771 : Nat := 4983230072969 + 3 ^ 40 * 117771 * 2
def baseEnd_117771 : Nat := 60473130160763954120887

theorem tailTrace_117771 : CollatzResearch.WordTrace tailWord_117771 prefixEnd_117771 60473130160763954120887 := by
  unfold tailWord_117771
  simp only [CollatzResearch.WordTrace]
  refine ⟨4295461256343255530577167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2863640837562170353718111 4295461256343255530577167)
  ·
    refine ⟨6443191884514883295865751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4295461256343255530577167 6443191884514883295865751)
    ·
      refine ⟨9664787826772324943798627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6443191884514883295865751 9664787826772324943798627)
      ·
        refine ⟨14497181740158487415697941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9664787826772324943798627 14497181740158487415697941)
        ·
          refine ⟨679555394069929097610841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14497181740158487415697941 679555394069929097610841)
          ·
            refine ⟨509666545552446823208131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 679555394069929097610841 509666545552446823208131)
            ·
              refine ⟨764499818328670234812197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509666545552446823208131 764499818328670234812197)
              ·
                refine ⟨143343715936625669027287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 764499818328670234812197 143343715936625669027287)
                ·
                  refine ⟨215015573904938503540931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143343715936625669027287 215015573904938503540931)
                  ·
                    refine ⟨322523360857407755311397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 215015573904938503540931 322523360857407755311397)
                    ·
                      refine ⟨60473130160763954120887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 322523360857407755311397 60473130160763954120887)
                      ·
                        rfl

theorem cell23_117771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 1, 4].length) (baseStart_117771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117771 prefixEnd_117771 := by exact prefixLift 117771
  have htrace : WordTrace (prefixWord ++ tailWord_117771) baseStart_117771 baseEnd_117771 := by
    simpa [prefixWord, tailWord_117771, baseEnd_117771] using wordTrace_append hprefix tailTrace_117771
  have hstable : (prefixWord ++ tailWord_117771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117771).length < 2 ^ (prefixWord ++ tailWord_117771).sum := by decide
  have hdescent : baseEnd_117771 < baseStart_117771 := by decide
  rcases family_descends (prefixWord ++ tailWord_117771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117781 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 4, 4]
def baseStart_117781 : Nat := 118140960795 + 117781 * 2 ^ 59
def prefixEnd_117781 : Nat := 4983230072969 + 3 ^ 40 * 117781 * 2
def baseEnd_117781 : Nat := 20159421655769638331947

theorem tailTrace_117781 : CollatzResearch.WordTrace tailWord_117781 prefixEnd_117781 20159421655769638331947 := by
  unfold tailWord_117781
  simp only [CollatzResearch.WordTrace]
  refine ⟨4295825986307027238441197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2863883990871351492294131 4295825986307027238441197)
  ·
    refine ⟨1610934744865135214415449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4295825986307027238441197 1610934744865135214415449)
    ·
      refine ⟨1208201058648851410811587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1610934744865135214415449 1208201058648851410811587)
      ·
        refine ⟨1812301587973277116217381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1208201058648851410811587 1812301587973277116217381)
        ·
          refine ⟨339806547744989459290759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1812301587973277116217381 339806547744989459290759)
          ·
            refine ⟨509709821617484188936139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339806547744989459290759 509709821617484188936139)
            ·
              refine ⟨764564732426226283404209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509709821617484188936139 764564732426226283404209)
              ·
                refine ⟨573423549319669712553157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 764564732426226283404209 573423549319669712553157)
                ·
                  refine ⟨107516915497438071103717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 573423549319669712553157 107516915497438071103717)
                  ·
                    refine ⟨20159421655769638331947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107516915497438071103717 20159421655769638331947)
                    ·
                      rfl

theorem cell23_117781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_117781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117781 prefixEnd_117781 := by exact prefixLift 117781
  have htrace : WordTrace (prefixWord ++ tailWord_117781) baseStart_117781 baseEnd_117781 := by
    simpa [prefixWord, tailWord_117781, baseEnd_117781] using wordTrace_append hprefix tailTrace_117781
  have hstable : (prefixWord ++ tailWord_117781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117781).length < 2 ^ (prefixWord ++ tailWord_117781).sum := by decide
  have hdescent : baseEnd_117781 < baseStart_117781 := by decide
  rcases family_descends (prefixWord ++ tailWord_117781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117791 : List Nat := [1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 5]
def baseStart_117791 : Nat := 118140960795 + 117791 * 2 ^ 59
def prefixEnd_117791 : Nat := 4983230072969 + 3 ^ 40 * 117791 * 2
def baseEnd_117791 : Nat := 60483399773853875870795

theorem tailTrace_117791 : CollatzResearch.WordTrace tailWord_117791 prefixEnd_117791 60483399773853875870795 := by
  unfold tailWord_117791
  simp only [CollatzResearch.WordTrace]
  refine ⟨4296190716270798946305227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2864127144180532630870151 4296190716270798946305227)
  ·
    refine ⟨6444286074406198419457841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4296190716270798946305227 6444286074406198419457841)
    ·
      refine ⟨4833214555804648814593381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6444286074406198419457841 4833214555804648814593381)
      ·
        refine ⟨906227729213371652736259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4833214555804648814593381 906227729213371652736259)
        ·
          refine ⟨1359341593820057479104389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906227729213371652736259 1359341593820057479104389)
          ·
            refine ⟨254876548841260777332073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1359341593820057479104389 254876548841260777332073)
            ·
              refine ⟨191157411630945582999055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254876548841260777332073 191157411630945582999055)
              ·
                refine ⟨286736117446418374498583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191157411630945582999055 286736117446418374498583)
                ·
                  refine ⟨430104176169627561747875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 286736117446418374498583 430104176169627561747875)
                  ·
                    refine ⟨645156264254441342621813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 430104176169627561747875 645156264254441342621813)
                    ·
                      refine ⟨60483399773853875870795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 645156264254441342621813 60483399773853875870795)
                      ·
                        rfl

theorem cell23_117791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_117791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117791 prefixEnd_117791 := by exact prefixLift 117791
  have htrace : WordTrace (prefixWord ++ tailWord_117791) baseStart_117791 baseEnd_117791 := by
    simpa [prefixWord, tailWord_117791, baseEnd_117791] using wordTrace_append hprefix tailTrace_117791
  have hstable : (prefixWord ++ tailWord_117791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117791).length < 2 ^ (prefixWord ++ tailWord_117791).sum := by decide
  have hdescent : baseEnd_117791 < baseStart_117791 := by decide
  rcases family_descends (prefixWord ++ tailWord_117791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117794 : List Nat := [3, 3, 1, 1, 1, 3, 11]
def baseStart_117794 : Nat := 118140960795 + 117794 * 2 ^ 59
def prefixEnd_117794 : Nat := 4983230072969 + 3 ^ 40 * 117794 * 2
def baseEnd_117794 : Nat := 746727656985399557201

theorem tailTrace_117794 : CollatzResearch.WordTrace tailWord_117794 prefixEnd_117794 746727656985399557201 := by
  unfold tailWord_117794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1074075033814982614666109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2864200090173286972442957 1074075033814982614666109)
  ·
    refine ⟨402778137680618480499791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1074075033814982614666109 402778137680618480499791)
    ·
      refine ⟨604167206520927720749687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402778137680618480499791 604167206520927720749687)
      ·
        refine ⟨906250809781391581124531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604167206520927720749687 906250809781391581124531)
        ·
          refine ⟨1359376214672087371686797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906250809781391581124531 1359376214672087371686797)
          ·
            refine ⟨509766080502032764382549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1359376214672087371686797 509766080502032764382549)
            ·
              refine ⟨746727656985399557201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 509766080502032764382549 746727656985399557201)
              ·
                rfl

theorem cell23_117794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 11].length) (baseStart_117794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117794 prefixEnd_117794 := by exact prefixLift 117794
  have htrace : WordTrace (prefixWord ++ tailWord_117794) baseStart_117794 baseEnd_117794 := by
    simpa [prefixWord, tailWord_117794, baseEnd_117794] using wordTrace_append hprefix tailTrace_117794
  have hstable : (prefixWord ++ tailWord_117794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117794).length < 2 ^ (prefixWord ++ tailWord_117794).sum := by decide
  have hdescent : baseEnd_117794 < baseStart_117794 := by decide
  rcases family_descends (prefixWord ++ tailWord_117794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117799 : List Nat := [1, 1, 7, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_117799 : Nat := 118140960795 + 117799 * 2 ^ 59
def prefixEnd_117799 : Nat := 4983230072969 + 3 ^ 40 * 117799 * 2
def baseEnd_117799 : Nat := 60487507619089844570759

theorem tailTrace_117799 : CollatzResearch.WordTrace tailWord_117799 prefixEnd_117799 60487507619089844570759 := by
  unfold tailWord_117799
  simp only [CollatzResearch.WordTrace]
  refine ⟨4296482500241816312596451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2864321666827877541730967 4296482500241816312596451)
  ·
    refine ⟨6444723750362724468894677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4296482500241816312596451 6444723750362724468894677)
    ·
      refine ⟨151048212899126354739719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 6444723750362724468894677 151048212899126354739719)
      ·
        refine ⟨226572319348689532109579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151048212899126354739719 226572319348689532109579)
        ·
          refine ⟨339858479023034298164369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226572319348689532109579 339858479023034298164369)
          ·
            refine ⟨254893859267275723623277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339858479023034298164369 254893859267275723623277)
            ·
              refine ⟨95585197225228396358729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254893859267275723623277 95585197225228396358729)
              ·
                refine ⟨71688897918921297269047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95585197225228396358729 71688897918921297269047)
                ·
                  refine ⟨107533346878381945903571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71688897918921297269047 107533346878381945903571)
                  ·
                    refine ⟨161300020317572918855357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107533346878381945903571 161300020317572918855357)
                    ·
                      refine ⟨60487507619089844570759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 161300020317572918855357 60487507619089844570759)
                      ·
                        rfl

theorem cell23_117799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_117799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117799 prefixEnd_117799 := by exact prefixLift 117799
  have htrace : WordTrace (prefixWord ++ tailWord_117799) baseStart_117799 baseEnd_117799 := by
    simpa [prefixWord, tailWord_117799, baseEnd_117799] using wordTrace_append hprefix tailTrace_117799
  have hstable : (prefixWord ++ tailWord_117799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117799).length < 2 ^ (prefixWord ++ tailWord_117799).sum := by decide
  have hdescent : baseEnd_117799 < baseStart_117799 := by decide
  rcases family_descends (prefixWord ++ tailWord_117799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117834 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_117834 : Nat := 118140960795 + 117834 * 2 ^ 59
def prefixEnd_117834 : Nat := 4983230072969 + 3 ^ 40 * 117834 * 2
def baseEnd_117834 : Nat := 60505479441997207633097

theorem tailTrace_117834 : CollatzResearch.WordTrace tailWord_117834 prefixEnd_117834 60505479441997207633097 := by
  unfold tailWord_117834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1074439763778754322530139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2865172703410011526747037 1074439763778754322530139)
  ·
    refine ⟨1611659645668131483795209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1074439763778754322530139 1611659645668131483795209)
    ·
      refine ⟨1208744734251098612846407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1611659645668131483795209 1208744734251098612846407)
      ·
        refine ⟨1813117101376647919269611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1208744734251098612846407 1813117101376647919269611)
        ·
          refine ⟨2719675652064971878904417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1813117101376647919269611 2719675652064971878904417)
          ·
            refine ⟨2039756739048728909178313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2719675652064971878904417 2039756739048728909178313)
            ·
              refine ⟨1529817554286546681883735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2039756739048728909178313 1529817554286546681883735)
              ·
                refine ⟨2294726331429820022825603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1529817554286546681883735 2294726331429820022825603)
                ·
                  refine ⟨3442089497144730034238405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2294726331429820022825603 3442089497144730034238405)
                  ·
                    refine ⟨645391780714636881419701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3442089497144730034238405 645391780714636881419701)
                    ·
                      refine ⟨60505479441997207633097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 645391780714636881419701 60505479441997207633097)
                      ·
                        rfl

theorem cell23_117834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_117834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117834 prefixEnd_117834 := by exact prefixLift 117834
  have htrace : WordTrace (prefixWord ++ tailWord_117834) baseStart_117834 baseEnd_117834 := by
    simpa [prefixWord, tailWord_117834, baseEnd_117834] using wordTrace_append hprefix tailTrace_117834
  have hstable : (prefixWord ++ tailWord_117834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117834).length < 2 ^ (prefixWord ++ tailWord_117834).sum := by decide
  have hdescent : baseEnd_117834 < baseStart_117834 := by decide
  rcases family_descends (prefixWord ++ tailWord_117834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117912 : List Nat := [2, 1, 2, 4, 2, 1, 3, 2, 2, 2, 2]
def baseStart_117912 : Nat := 118140960795 + 117912 * 2 ^ 59
def prefixEnd_117912 : Nat := 4983230072969 + 3 ^ 40 * 117912 * 2
def baseEnd_117912 : Nat := 60545530933047902457739

theorem tailTrace_117912 : CollatzResearch.WordTrace tailWord_117912 prefixEnd_117912 60545530933047902457739 := by
  unfold tailWord_117912
  simp only [CollatzResearch.WordTrace]
  refine ⟨2150301974416218305729995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2867069299221624407639993 2150301974416218305729995)
  ·
    refine ⟨3225452961624327458594993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2150301974416218305729995 3225452961624327458594993)
    ·
      refine ⟨2419089721218245593946245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3225452961624327458594993 2419089721218245593946245)
      ·
        refine ⟨453579322728421048864921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2419089721218245593946245 453579322728421048864921)
        ·
          refine ⟨340184492046315786648691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453579322728421048864921 340184492046315786648691)
          ·
            refine ⟨510276738069473679973037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340184492046315786648691 510276738069473679973037)
            ·
              refine ⟨191353776776052629989889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 510276738069473679973037 191353776776052629989889)
              ·
                refine ⟨143515332582039472492417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191353776776052629989889 143515332582039472492417)
                ·
                  refine ⟨107636499436529604369313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143515332582039472492417 107636499436529604369313)
                  ·
                    refine ⟨80727374577397203276985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107636499436529604369313 80727374577397203276985)
                    ·
                      refine ⟨60545530933047902457739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 80727374577397203276985 60545530933047902457739)
                      ·
                        rfl

theorem cell23_117912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_117912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117912 prefixEnd_117912 := by exact prefixLift 117912
  have htrace : WordTrace (prefixWord ++ tailWord_117912) baseStart_117912 baseEnd_117912 := by
    simpa [prefixWord, tailWord_117912, baseEnd_117912] using wordTrace_append hprefix tailTrace_117912
  have hstable : (prefixWord ++ tailWord_117912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117912).length < 2 ^ (prefixWord ++ tailWord_117912).sum := by decide
  have hdescent : baseEnd_117912 < baseStart_117912 := by decide
  rcases family_descends (prefixWord ++ tailWord_117912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117918 : List Nat := [4, 3, 1, 1, 2, 1, 1, 3, 7]
def baseStart_117918 : Nat := 118140960795 + 117918 * 2 ^ 59
def prefixEnd_117918 : Nat := 4983230072969 + 3 ^ 40 * 117918 * 2
def baseEnd_117918 : Nat := 6727623535219430998079

theorem tailTrace_117918 : CollatzResearch.WordTrace tailWord_117918 prefixEnd_117918 6727623535219430998079 := by
  unfold tailWord_117918
  simp only [CollatzResearch.WordTrace]
  refine ⟨537602848351337454522301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2867215191207133090785605 537602848351337454522301)
  ·
    refine ⟨201601068131751545445863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 537602848351337454522301 201601068131751545445863)
    ·
      refine ⟨302401602197627318168795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201601068131751545445863 302401602197627318168795)
      ·
        refine ⟨453602403296440977253193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302401602197627318168795 453602403296440977253193)
        ·
          refine ⟨340201802472330732939895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453602403296440977253193 340201802472330732939895)
          ·
            refine ⟨510302703708496099409843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340201802472330732939895 510302703708496099409843)
            ·
              refine ⟨765454055562744149114765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510302703708496099409843 765454055562744149114765)
              ·
                refine ⟨287045270836029055918037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 765454055562744149114765 287045270836029055918037)
                ·
                  refine ⟨6727623535219430998079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 287045270836029055918037 6727623535219430998079)
                  ·
                    rfl

theorem cell23_117918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_117918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117918 prefixEnd_117918 := by exact prefixLift 117918
  have htrace : WordTrace (prefixWord ++ tailWord_117918) baseStart_117918 baseEnd_117918 := by
    simpa [prefixWord, tailWord_117918, baseEnd_117918] using wordTrace_append hprefix tailTrace_117918
  have hstable : (prefixWord ++ tailWord_117918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117918).length < 2 ^ (prefixWord ++ tailWord_117918).sum := by decide
  have hdescent : baseEnd_117918 < baseStart_117918 := by decide
  rcases family_descends (prefixWord ++ tailWord_117918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117951 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 4]
def baseStart_117951 : Nat := 118140960795 + 117951 * 2 ^ 59
def prefixEnd_117951 : Nat := 4983230072969 + 3 ^ 40 * 117951 * 2
def baseEnd_117951 : Nat := 60565556678573249870059

theorem tailTrace_117951 : CollatzResearch.WordTrace tailWord_117951 prefixEnd_117951 60565556678573249870059 := by
  unfold tailWord_117951
  simp only [CollatzResearch.WordTrace]
  refine ⟨4302026395691146272129707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2868017597127430848086471 4302026395691146272129707)
  ·
    refine ⟨6453039593536719408194561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4302026395691146272129707 6453039593536719408194561)
    ·
      refine ⟨4839779695152539556145921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6453039593536719408194561 4839779695152539556145921)
      ·
        refine ⟨3629834771364404667109441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4839779695152539556145921 3629834771364404667109441)
        ·
          refine ⟨2722376078523303500332081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3629834771364404667109441 2722376078523303500332081)
          ·
            refine ⟨2041782058892477625249061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2722376078523303500332081 2041782058892477625249061)
            ·
              refine ⟨382834136042339554734199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2041782058892477625249061 382834136042339554734199)
              ·
                refine ⟨574251204063509332101299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382834136042339554734199 574251204063509332101299)
                ·
                  refine ⟨861376806095263998151949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574251204063509332101299 861376806095263998151949)
                  ·
                    refine ⟨323016302285723999306981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 861376806095263998151949 323016302285723999306981)
                    ·
                      refine ⟨60565556678573249870059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 323016302285723999306981 60565556678573249870059)
                      ·
                        rfl

theorem cell23_117951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_117951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117951 prefixEnd_117951 := by exact prefixLift 117951
  have htrace : WordTrace (prefixWord ++ tailWord_117951) baseStart_117951 baseEnd_117951 := by
    simpa [prefixWord, tailWord_117951, baseEnd_117951] using wordTrace_append hprefix tailTrace_117951
  have hstable : (prefixWord ++ tailWord_117951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117951).length < 2 ^ (prefixWord ++ tailWord_117951).sum := by decide
  have hdescent : baseEnd_117951 < baseStart_117951 := by decide
  rcases family_descends (prefixWord ++ tailWord_117951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117952 : List Nat := [2, 1, 1, 2, 7, 1, 1, 3, 5]
def baseStart_117952 : Nat := 118140960795 + 117952 * 2 ^ 59
def prefixEnd_117952 : Nat := 4983230072969 + 3 ^ 40 * 117952 * 2
def baseEnd_117952 : Nat := 6729563351025305106395

theorem tailTrace_117952 : CollatzResearch.WordTrace tailWord_117952 prefixEnd_117952 6729563351025305106395 := by
  unfold tailWord_117952
  simp only [CollatzResearch.WordTrace]
  refine ⟨2151031434343761721458055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2868041912458348961944073 2151031434343761721458055)
  ·
    refine ⟨3226547151515642582187083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2151031434343761721458055 3226547151515642582187083)
    ·
      refine ⟨4839820727273463873280625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3226547151515642582187083 4839820727273463873280625)
      ·
        refine ⟨3629865545455097904960469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4839820727273463873280625 3629865545455097904960469)
        ·
          refine ⟨85074973721603857147511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 3629865545455097904960469 85074973721603857147511)
          ·
            refine ⟨127612460582405785721267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85074973721603857147511 127612460582405785721267)
            ·
              refine ⟨191418690873608678581901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127612460582405785721267 191418690873608678581901)
              ·
                refine ⟨71782009077603254468213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191418690873608678581901 71782009077603254468213)
                ·
                  refine ⟨6729563351025305106395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71782009077603254468213 6729563351025305106395)
                  ·
                    rfl

theorem cell23_117952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 5].length) (baseStart_117952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_117952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_117952 prefixEnd_117952 := by exact prefixLift 117952
  have htrace : WordTrace (prefixWord ++ tailWord_117952) baseStart_117952 baseEnd_117952 := by
    simpa [prefixWord, tailWord_117952, baseEnd_117952] using wordTrace_append hprefix tailTrace_117952
  have hstable : (prefixWord ++ tailWord_117952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117952).length < 2 ^ (prefixWord ++ tailWord_117952).sum := by decide
  have hdescent : baseEnd_117952 < baseStart_117952 := by decide
  rcases family_descends (prefixWord ++ tailWord_117952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118069 : List Nat := [1, 3, 3, 1, 2, 3, 2, 3, 1, 1, 3]
def baseStart_118069 : Nat := 118140960795 + 118069 * 2 ^ 59
def prefixEnd_118069 : Nat := 4983230072969 + 3 ^ 40 * 118069 * 2
def baseEnd_118069 : Nat := 60626147395803788194517

theorem tailTrace_118069 : CollatzResearch.WordTrace tailWord_118069 prefixEnd_118069 60626147395803788194517 := by
  unfold tailWord_118069
  simp only [CollatzResearch.WordTrace]
  refine ⟨4306330209263652424925261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2870886806175768283283507 4306330209263652424925261)
  ·
    refine ⟨1614873828473869659346973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4306330209263652424925261 1614873828473869659346973)
    ·
      refine ⟨605577685677701122255115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1614873828473869659346973 605577685677701122255115)
      ·
        refine ⟨908366528516551683382673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605577685677701122255115 908366528516551683382673)
        ·
          refine ⟨681274896387413762537005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 908366528516551683382673 681274896387413762537005)
          ·
            refine ⟨255478086145280160951377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 681274896387413762537005 255478086145280160951377)
            ·
              refine ⟨191608564608960120713533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255478086145280160951377 191608564608960120713533)
              ·
                refine ⟨71853211728360045267575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191608564608960120713533 71853211728360045267575)
                ·
                  refine ⟨107779817592540067901363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71853211728360045267575 107779817592540067901363)
                  ·
                    refine ⟨161669726388810101852045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107779817592540067901363 161669726388810101852045)
                    ·
                      refine ⟨60626147395803788194517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 161669726388810101852045 60626147395803788194517)
                      ·
                        rfl

theorem cell23_118069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_118069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118069 prefixEnd_118069 := by exact prefixLift 118069
  have htrace : WordTrace (prefixWord ++ tailWord_118069) baseStart_118069 baseEnd_118069 := by
    simpa [prefixWord, tailWord_118069, baseEnd_118069] using wordTrace_append hprefix tailTrace_118069
  have hstable : (prefixWord ++ tailWord_118069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118069).length < 2 ^ (prefixWord ++ tailWord_118069).sum := by decide
  have hdescent : baseEnd_118069 < baseStart_118069 := by decide
  rcases family_descends (prefixWord ++ tailWord_118069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118071 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 6]
def baseStart_118071 : Nat := 118140960795 + 118071 * 2 ^ 59
def prefixEnd_118071 : Nat := 4983230072969 + 3 ^ 40 * 118071 * 2
def baseEnd_118071 : Nat := 60627174357112780369507

theorem tailTrace_118071 : CollatzResearch.WordTrace tailWord_118071 prefixEnd_118071 60627174357112780369507 := by
  unfold tailWord_118071
  simp only [CollatzResearch.WordTrace]
  refine ⟨4306403155256406766498067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2870935436837604510998711 4306403155256406766498067)
  ·
    refine ⟨6459604732884610149747101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4306403155256406766498067 6459604732884610149747101)
    ·
      refine ⟨2422351774831728806155163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6459604732884610149747101 2422351774831728806155163)
      ·
        refine ⟨3633527662247593209232745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2422351774831728806155163 3633527662247593209232745)
        ·
          refine ⟨2725145746685694906924559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3633527662247593209232745 2725145746685694906924559)
          ·
            refine ⟨4087718620028542360386839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2725145746685694906924559 4087718620028542360386839)
            ·
              refine ⟨6131577930042813540580259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4087718620028542360386839 6131577930042813540580259)
              ·
                refine ⟨9197366895064220310870389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6131577930042813540580259 9197366895064220310870389)
                ·
                  refine ⟨862253146412270654144099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9197366895064220310870389 862253146412270654144099)
                  ·
                    refine ⟨1293379719618405981216149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 862253146412270654144099 1293379719618405981216149)
                    ·
                      refine ⟨60627174357112780369507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1293379719618405981216149 60627174357112780369507)
                      ·
                        rfl

theorem cell23_118071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_118071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118071 prefixEnd_118071 := by exact prefixLift 118071
  have htrace : WordTrace (prefixWord ++ tailWord_118071) baseStart_118071 baseEnd_118071 := by
    simpa [prefixWord, tailWord_118071, baseEnd_118071] using wordTrace_append hprefix tailTrace_118071
  have hstable : (prefixWord ++ tailWord_118071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118071).length < 2 ^ (prefixWord ++ tailWord_118071).sum := by decide
  have hdescent : baseEnd_118071 < baseStart_118071 := by decide
  rcases family_descends (prefixWord ++ tailWord_118071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118092 : List Nat := [2, 2, 1, 3, 2, 2, 1, 3, 3, 2, 2]
def baseStart_118092 : Nat := 118140960795 + 118092 * 2 ^ 59
def prefixEnd_118092 : Nat := 4983230072969 + 3 ^ 40 * 118092 * 2
def baseEnd_118092 : Nat := 60637957450857198206911

theorem tailTrace_118092 : CollatzResearch.WordTrace tailWord_118092 prefixEnd_118092 60637957450857198206911 := by
  unfold tailWord_118092
  simp only [CollatzResearch.WordTrace]
  refine ⟨2153584544090163676506265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2871446058786884902008353 2153584544090163676506265)
  ·
    refine ⟨1615188408067622757379699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2153584544090163676506265 1615188408067622757379699)
    ·
      refine ⟨2422782612101434136069549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1615188408067622757379699 2422782612101434136069549)
      ·
        refine ⟨908543479538037801026081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2422782612101434136069549 908543479538037801026081)
        ·
          refine ⟨681407609653528350769561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 908543479538037801026081 681407609653528350769561)
          ·
            refine ⟨511055707240146263077171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 681407609653528350769561 511055707240146263077171)
            ·
              refine ⟨766583560860219394615757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511055707240146263077171 766583560860219394615757)
              ·
                refine ⟨287468835322582272980909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 766583560860219394615757 287468835322582272980909)
                ·
                  refine ⟨107800813245968352367841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287468835322582272980909 107800813245968352367841)
                  ·
                    refine ⟨80850609934476264275881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107800813245968352367841 80850609934476264275881)
                    ·
                      refine ⟨60637957450857198206911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 80850609934476264275881 60637957450857198206911)
                      ·
                        rfl

theorem cell23_118092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_118092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118092 prefixEnd_118092 := by exact prefixLift 118092
  have htrace : WordTrace (prefixWord ++ tailWord_118092) baseStart_118092 baseEnd_118092 := by
    simpa [prefixWord, tailWord_118092, baseEnd_118092] using wordTrace_append hprefix tailTrace_118092
  have hstable : (prefixWord ++ tailWord_118092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118092).length < 2 ^ (prefixWord ++ tailWord_118092).sum := by decide
  have hdescent : baseEnd_118092 < baseStart_118092 := by decide
  rcases family_descends (prefixWord ++ tailWord_118092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118112 : List Nat := [2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 3]
def baseStart_118112 : Nat := 118140960795 + 118112 * 2 ^ 59
def prefixEnd_118112 : Nat := 4983230072969 + 3 ^ 40 * 118112 * 2
def baseEnd_118112 : Nat := 60648227063947119956819

theorem tailTrace_118112 : CollatzResearch.WordTrace tailWord_118112 prefixEnd_118112 60648227063947119956819 := by
  unfold tailWord_118112
  simp only [CollatzResearch.WordTrace]
  refine ⟨2153949274053935384370295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2871932365405247179160393 2153949274053935384370295)
  ·
    refine ⟨3230923911080903076555443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2153949274053935384370295 3230923911080903076555443)
    ·
      refine ⟨4846385866621354614833165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3230923911080903076555443 4846385866621354614833165)
      ·
        refine ⟨1817394699983007980562437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4846385866621354614833165 1817394699983007980562437)
        ·
          refine ⟨340761506246813996355457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1817394699983007980562437 340761506246813996355457)
          ·
            refine ⟨255571129685110497266593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340761506246813996355457 255571129685110497266593)
            ·
              refine ⟨191678347263832872949945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255571129685110497266593 191678347263832872949945)
              ·
                refine ⟨143758760447874654712459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191678347263832872949945 143758760447874654712459)
                ·
                  refine ⟨215638140671811982068689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143758760447874654712459 215638140671811982068689)
                  ·
                    refine ⟨161728605503858986551517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 215638140671811982068689 161728605503858986551517)
                    ·
                      refine ⟨60648227063947119956819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 161728605503858986551517 60648227063947119956819)
                      ·
                        rfl

theorem cell23_118112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_118112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118112 prefixEnd_118112 := by exact prefixLift 118112
  have htrace : WordTrace (prefixWord ++ tailWord_118112) baseStart_118112 baseEnd_118112 := by
    simpa [prefixWord, tailWord_118112, baseEnd_118112] using wordTrace_append hprefix tailTrace_118112
  have hstable : (prefixWord ++ tailWord_118112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118112).length < 2 ^ (prefixWord ++ tailWord_118112).sum := by decide
  have hdescent : baseEnd_118112 < baseStart_118112 := by decide
  rcases family_descends (prefixWord ++ tailWord_118112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118115 : List Nat := [1, 1, 1, 5, 2, 4, 2, 7]
def baseStart_118115 : Nat := 118140960795 + 118115 * 2 ^ 59
def prefixEnd_118115 : Nat := 4983230072969 + 3 ^ 40 * 118115 * 2
def baseEnd_118115 : Nat := 2246287685404096600715

theorem tailTrace_118115 : CollatzResearch.WordTrace tailWord_118115 prefixEnd_118115 2246287685404096600715 := by
  unfold tailWord_118115
  simp only [CollatzResearch.WordTrace]
  refine ⟨4308007967097002281099799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2872005311398001520733199 4308007967097002281099799)
  ·
    refine ⟨6462011950645503421649699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4308007967097002281099799 6462011950645503421649699)
    ·
      refine ⟨9693017925968255132474549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6462011950645503421649699 9693017925968255132474549)
      ·
        refine ⟨908720430559523918669489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9693017925968255132474549 908720430559523918669489)
        ·
          refine ⟨681540322919642939002117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 908720430559523918669489 681540322919642939002117)
          ·
            refine ⟨127788810547433051062897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 681540322919642939002117 127788810547433051062897)
            ·
              refine ⟨95841607910574788297173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127788810547433051062897 95841607910574788297173)
              ·
                refine ⟨2246287685404096600715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 95841607910574788297173 2246287685404096600715)
                ·
                  rfl

theorem cell23_118115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 7].length) (baseStart_118115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118115 prefixEnd_118115 := by exact prefixLift 118115
  have htrace : WordTrace (prefixWord ++ tailWord_118115) baseStart_118115 baseEnd_118115 := by
    simpa [prefixWord, tailWord_118115, baseEnd_118115] using wordTrace_append hprefix tailTrace_118115
  have hstable : (prefixWord ++ tailWord_118115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118115).length < 2 ^ (prefixWord ++ tailWord_118115).sum := by decide
  have hdescent : baseEnd_118115 < baseStart_118115 := by decide
  rcases family_descends (prefixWord ++ tailWord_118115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118169 : List Nat := [1, 2, 1, 2, 1, 7, 1, 2, 1, 3, 2]
def baseStart_118169 : Nat := 118140960795 + 118169 * 2 ^ 59
def prefixEnd_118169 : Nat := 4983230072969 + 3 ^ 40 * 118169 * 2
def baseEnd_118169 : Nat := 60677495461253396944057

theorem tailTrace_118169 : CollatzResearch.WordTrace tailWord_118169 prefixEnd_118169 60677495461253396944057 := by
  unfold tailWord_118169
  simp only [CollatzResearch.WordTrace]
  refine ⟨4309977508901369503565561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2873318339267579669043707 4309977508901369503565561)
  ·
    refine ⟨3232483131676027127674171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4309977508901369503565561 3232483131676027127674171)
    ·
      refine ⟨4848724697514040691511257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3232483131676027127674171 4848724697514040691511257)
      ·
        refine ⟨3636543523135530518633443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4848724697514040691511257 3636543523135530518633443)
        ·
          refine ⟨5454815284703295777950165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3636543523135530518633443 5454815284703295777950165)
          ·
            refine ⟨127847233235233494795707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 5454815284703295777950165 127847233235233494795707)
            ·
              refine ⟨191770849852850242193561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127847233235233494795707 191770849852850242193561)
              ·
                refine ⟨143828137389637681645171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191770849852850242193561 143828137389637681645171)
                ·
                  refine ⟨215742206084456522467757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143828137389637681645171 215742206084456522467757)
                  ·
                    refine ⟨80903327281671195925409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 215742206084456522467757 80903327281671195925409)
                    ·
                      refine ⟨60677495461253396944057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 80903327281671195925409 60677495461253396944057)
                      ·
                        rfl

theorem cell23_118169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 3, 2].length) (baseStart_118169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118169 prefixEnd_118169 := by exact prefixLift 118169
  have htrace : WordTrace (prefixWord ++ tailWord_118169) baseStart_118169 baseEnd_118169 := by
    simpa [prefixWord, tailWord_118169, baseEnd_118169] using wordTrace_append hprefix tailTrace_118169
  have hstable : (prefixWord ++ tailWord_118169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118169).length < 2 ^ (prefixWord ++ tailWord_118169).sum := by decide
  have hdescent : baseEnd_118169 < baseStart_118169 := by decide
  rcases family_descends (prefixWord ++ tailWord_118169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118199 : List Nat := [1, 1, 3, 1, 3, 2, 4, 2, 2, 2, 2]
def baseStart_118199 : Nat := 118140960795 + 118199 * 2 ^ 59
def prefixEnd_118199 : Nat := 4983230072969 + 3 ^ 40 * 118199 * 2
def baseEnd_118199 : Nat := 60692899880888279568919

theorem tailTrace_118199 : CollatzResearch.WordTrace tailWord_118199 prefixEnd_118199 60692899880888279568919 := by
  unfold tailWord_118199
  simp only [CollatzResearch.WordTrace]
  refine ⟨4311071698792684627157651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2874047799195123084771767 4311071698792684627157651)
  ·
    refine ⟨6466607548189026940736477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4311071698792684627157651 6466607548189026940736477)
    ·
      refine ⟨2424977830570885102776179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6466607548189026940736477 2424977830570885102776179)
      ·
        refine ⟨3637466745856327654164269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2424977830570885102776179 3637466745856327654164269)
        ·
          refine ⟨1364050029696122870311601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3637466745856327654164269 1364050029696122870311601)
          ·
            refine ⟨1023037522272092152733701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1364050029696122870311601 1023037522272092152733701)
            ·
              refine ⟨191819535426017278637569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1023037522272092152733701 191819535426017278637569)
              ·
                refine ⟨143864651569512958978177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191819535426017278637569 143864651569512958978177)
                ·
                  refine ⟨107898488677134719233633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143864651569512958978177 107898488677134719233633)
                  ·
                    refine ⟨80923866507851039425225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107898488677134719233633 80923866507851039425225)
                    ·
                      refine ⟨60692899880888279568919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 80923866507851039425225 60692899880888279568919)
                      ·
                        rfl

theorem cell23_118199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 2, 2].length) (baseStart_118199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118199 prefixEnd_118199 := by exact prefixLift 118199
  have htrace : WordTrace (prefixWord ++ tailWord_118199) baseStart_118199 baseEnd_118199 := by
    simpa [prefixWord, tailWord_118199, baseEnd_118199] using wordTrace_append hprefix tailTrace_118199
  have hstable : (prefixWord ++ tailWord_118199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118199).length < 2 ^ (prefixWord ++ tailWord_118199).sum := by decide
  have hdescent : baseEnd_118199 < baseStart_118199 := by decide
  rcases family_descends (prefixWord ++ tailWord_118199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118212 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_118212 : Nat := 118140960795 + 118212 * 2 ^ 59
def prefixEnd_118212 : Nat := 4983230072969 + 3 ^ 40 * 118212 * 2
def baseEnd_118212 : Nat := 60699575129396728706359

theorem tailTrace_118212 : CollatzResearch.WordTrace tailWord_118212 prefixEnd_118212 60699575129396728706359 := by
  unfold tailWord_118212
  simp only [CollatzResearch.WordTrace]
  refine ⟨2155772923872793923690445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2874363898497058564920593 2155772923872793923690445)
  ·
    refine ⟨808414846452297721383917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2155772923872793923690445 808414846452297721383917)
    ·
      refine ⟨303155567419611645518969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 808414846452297721383917 303155567419611645518969)
      ·
        refine ⟨227366675564708734139227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303155567419611645518969 227366675564708734139227)
        ·
          refine ⟨341050013347063101208841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227366675564708734139227 341050013347063101208841)
          ·
            refine ⟨255787510010297325906631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341050013347063101208841 255787510010297325906631)
            ·
              refine ⟨383681265015445988859947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255787510010297325906631 383681265015445988859947)
              ·
                refine ⟨575521897523168983289921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383681265015445988859947 575521897523168983289921)
                ·
                  refine ⟨431641423142376737467441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575521897523168983289921 431641423142376737467441)
                  ·
                    refine ⟨323731067356782553100581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 431641423142376737467441 323731067356782553100581)
                    ·
                      refine ⟨60699575129396728706359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 323731067356782553100581 60699575129396728706359)
                      ·
                        rfl

theorem cell23_118212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_118212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118212 prefixEnd_118212 := by exact prefixLift 118212
  have htrace : WordTrace (prefixWord ++ tailWord_118212) baseStart_118212 baseEnd_118212 := by
    simpa [prefixWord, tailWord_118212, baseEnd_118212] using wordTrace_append hprefix tailTrace_118212
  have hstable : (prefixWord ++ tailWord_118212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118212).length < 2 ^ (prefixWord ++ tailWord_118212).sum := by decide
  have hdescent : baseEnd_118212 < baseStart_118212 := by decide
  rcases family_descends (prefixWord ++ tailWord_118212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118215 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 3]
def baseStart_118215 : Nat := 118140960795 + 118215 * 2 ^ 59
def prefixEnd_118215 : Nat := 4983230072969 + 3 ^ 40 * 118215 * 2
def baseEnd_118215 : Nat := 60701115571360216968845

theorem tailTrace_118215 : CollatzResearch.WordTrace tailWord_118215 prefixEnd_118215 60701115571360216968845 := by
  unfold tailWord_118215
  simp only [CollatzResearch.WordTrace]
  refine ⟨4311655266734719359740099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2874436844489812906493399 4311655266734719359740099)
  ·
    refine ⟨6467482900102079039610149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4311655266734719359740099 6467482900102079039610149)
    ·
      refine ⟨1212653043769139819926903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6467482900102079039610149 1212653043769139819926903)
      ·
        refine ⟨1818979565653709729890355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1212653043769139819926903 1818979565653709729890355)
        ·
          refine ⟨2728469348480564594835533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818979565653709729890355 2728469348480564594835533)
          ·
            refine ⟨1023176005680211723063325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2728469348480564594835533 1023176005680211723063325)
            ·
              refine ⟨383691002130079396148747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1023176005680211723063325 383691002130079396148747)
              ·
                refine ⟨575536503195119094223121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383691002130079396148747 575536503195119094223121)
                ·
                  refine ⟨431652377396339320667341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575536503195119094223121 431652377396339320667341)
                  ·
                    refine ⟨161869641523627245250253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 431652377396339320667341 161869641523627245250253)
                    ·
                      refine ⟨60701115571360216968845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 161869641523627245250253 60701115571360216968845)
                      ·
                        rfl

theorem cell23_118215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_118215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118215 prefixEnd_118215 := by exact prefixLift 118215
  have htrace : WordTrace (prefixWord ++ tailWord_118215) baseStart_118215 baseEnd_118215 := by
    simpa [prefixWord, tailWord_118215, baseEnd_118215] using wordTrace_append hprefix tailTrace_118215
  have hstable : (prefixWord ++ tailWord_118215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118215).length < 2 ^ (prefixWord ++ tailWord_118215).sum := by decide
  have hdescent : baseEnd_118215 < baseStart_118215 := by decide
  rcases family_descends (prefixWord ++ tailWord_118215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118255 : List Nat := [1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 4]
def baseStart_118255 : Nat := 118140960795 + 118255 * 2 ^ 59
def prefixEnd_118255 : Nat := 4983230072969 + 3 ^ 40 * 118255 * 2
def baseEnd_118255 : Nat := 60721654797540060468661

theorem tailTrace_118255 : CollatzResearch.WordTrace tailWord_118255 prefixEnd_118255 60721654797540060468661 := by
  unfold tailWord_118255
  simp only [CollatzResearch.WordTrace]
  refine ⟨4313114186589806191196219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2875409457726537460797479 4313114186589806191196219)
  ·
    refine ⟨6469671279884709286794329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4313114186589806191196219 6469671279884709286794329)
    ·
      refine ⟨4852253459913531965095747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6469671279884709286794329 4852253459913531965095747)
      ·
        refine ⟨7278380189870297947643621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4852253459913531965095747 7278380189870297947643621)
        ·
          refine ⟨1364696285600680865183179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7278380189870297947643621 1364696285600680865183179)
          ·
            refine ⟨2047044428401021297774769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1364696285600680865183179 2047044428401021297774769)
            ·
              refine ⟨1535283321300765973331077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2047044428401021297774769 1535283321300765973331077)
              ·
                refine ⟨287865622743893619999577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1535283321300765973331077 287865622743893619999577)
                ·
                  refine ⟨215899217057920214999683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287865622743893619999577 215899217057920214999683)
                  ·
                    refine ⟨323848825586880322499525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 215899217057920214999683 323848825586880322499525)
                    ·
                      refine ⟨60721654797540060468661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 323848825586880322499525 60721654797540060468661)
                      ·
                        rfl

theorem cell23_118255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 4].length) (baseStart_118255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118255 prefixEnd_118255 := by exact prefixLift 118255
  have htrace : WordTrace (prefixWord ++ tailWord_118255) baseStart_118255 baseEnd_118255 := by
    simpa [prefixWord, tailWord_118255, baseEnd_118255] using wordTrace_append hprefix tailTrace_118255
  have hstable : (prefixWord ++ tailWord_118255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118255).length < 2 ^ (prefixWord ++ tailWord_118255).sum := by decide
  have hdescent : baseEnd_118255 < baseStart_118255 := by decide
  rcases family_descends (prefixWord ++ tailWord_118255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118275 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 3]
def baseStart_118275 : Nat := 118140960795 + 118275 * 2 ^ 59
def prefixEnd_118275 : Nat := 4983230072969 + 3 ^ 40 * 118275 * 2
def baseEnd_118275 : Nat := 60731924410629982218569

theorem tailTrace_118275 : CollatzResearch.WordTrace tailWord_118275 prefixEnd_118275 60731924410629982218569 := by
  unfold tailWord_118275
  simp only [CollatzResearch.WordTrace]
  refine ⟨4313843646517349606924279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2875895764344899737949519 4313843646517349606924279)
  ·
    refine ⟨6470765469776024410386419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4313843646517349606924279 6470765469776024410386419)
    ·
      refine ⟨9706148204664036615579629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6470765469776024410386419 9706148204664036615579629)
      ·
        refine ⟨3639805576749013730842361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9706148204664036615579629 3639805576749013730842361)
        ·
          refine ⟨2729854182561760298131771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3639805576749013730842361 2729854182561760298131771)
          ·
            refine ⟨4094781273842640447197657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2729854182561760298131771 4094781273842640447197657)
            ·
              refine ⟨3071085955381980335398243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4094781273842640447197657 3071085955381980335398243)
              ·
                refine ⟨4606628933072970503097365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3071085955381980335398243 4606628933072970503097365)
                ·
                  refine ⟨215935731237795492332689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4606628933072970503097365 215935731237795492332689)
                  ·
                    refine ⟨161951798428346619249517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 215935731237795492332689 161951798428346619249517)
                    ·
                      refine ⟨60731924410629982218569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 161951798428346619249517 60731924410629982218569)
                      ·
                        rfl

theorem cell23_118275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_118275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118275 prefixEnd_118275 := by exact prefixLift 118275
  have htrace : WordTrace (prefixWord ++ tailWord_118275) baseStart_118275 baseEnd_118275 := by
    simpa [prefixWord, tailWord_118275, baseEnd_118275] using wordTrace_append hprefix tailTrace_118275
  have hstable : (prefixWord ++ tailWord_118275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118275).length < 2 ^ (prefixWord ++ tailWord_118275).sum := by decide
  have hdescent : baseEnd_118275 < baseStart_118275 := by decide
  rcases family_descends (prefixWord ++ tailWord_118275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118282 : List Nat := [3, 1, 2, 2, 2, 2, 2, 2, 3, 4]
def baseStart_118282 : Nat := 118140960795 + 118282 * 2 ^ 59
def prefixEnd_118282 : Nat := 4983230072969 + 3 ^ 40 * 118282 * 2
def baseEnd_118282 : Nat := 20245172925070484943679

theorem tailTrace_118282 : CollatzResearch.WordTrace tailWord_118282 prefixEnd_118282 20245172925070484943679 := by
  unfold tailWord_118282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1078524739372997450607275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2876065971661326534952733 1078524739372997450607275)
  ·
    refine ⟨1617787109059496175910913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1078524739372997450607275 1617787109059496175910913)
    ·
      refine ⟨1213340331794622131933185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1617787109059496175910913 1213340331794622131933185)
      ·
        refine ⟨910005248845966598949889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1213340331794622131933185 910005248845966598949889)
        ·
          refine ⟨682503936634474949212417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 910005248845966598949889 682503936634474949212417)
          ·
            refine ⟨511877952475856211909313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682503936634474949212417 511877952475856211909313)
            ·
              refine ⟨383908464356892158931985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511877952475856211909313 383908464356892158931985)
              ·
                refine ⟨287931348267669119198989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383908464356892158931985 287931348267669119198989)
                ·
                  refine ⟨107974255600375919699621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287931348267669119198989 107974255600375919699621)
                  ·
                    refine ⟨20245172925070484943679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107974255600375919699621 20245172925070484943679)
                    ·
                      rfl

theorem cell23_118282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_118282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118282 prefixEnd_118282 := by exact prefixLift 118282
  have htrace : WordTrace (prefixWord ++ tailWord_118282) baseStart_118282 baseEnd_118282 := by
    simpa [prefixWord, tailWord_118282, baseEnd_118282] using wordTrace_append hprefix tailTrace_118282
  have hstable : (prefixWord ++ tailWord_118282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118282).length < 2 ^ (prefixWord ++ tailWord_118282).sum := by decide
  have hdescent : baseEnd_118282 < baseStart_118282 := by decide
  rcases family_descends (prefixWord ++ tailWord_118282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118329 : List Nat := [1, 2, 1, 5, 1, 4, 2, 1, 6]
def baseStart_118329 : Nat := 118140960795 + 118329 * 2 ^ 59
def prefixEnd_118329 : Nat := 4983230072969 + 3 ^ 40 * 118329 * 2
def baseEnd_118329 : Nat := 6751072485108085660369

theorem tailTrace_118329 : CollatzResearch.WordTrace tailWord_118329 prefixEnd_118329 6751072485108085660369 := by
  unfold tailWord_118329
  simp only [CollatzResearch.WordTrace]
  refine ⟨4315813188321716829390041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2877208792214477886260027 4315813188321716829390041)
  ·
    refine ⟨3236859891241287622042531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4315813188321716829390041 3236859891241287622042531)
    ·
      refine ⟨4855289836861931433063797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3236859891241287622042531 4855289836861931433063797)
      ·
        refine ⟨455183422205806071849731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4855289836861931433063797 455183422205806071849731)
        ·
          refine ⟨682775133308709107774597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455183422205806071849731 682775133308709107774597)
          ·
            refine ⟨128020337495382957707737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 682775133308709107774597 128020337495382957707737)
            ·
              refine ⟨96015253121537218280803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128020337495382957707737 96015253121537218280803)
              ·
                refine ⟨144022879682305827421205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96015253121537218280803 144022879682305827421205)
                ·
                  refine ⟨6751072485108085660369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144022879682305827421205 6751072485108085660369)
                  ·
                    rfl

theorem cell23_118329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 6].length) (baseStart_118329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118329 prefixEnd_118329 := by exact prefixLift 118329
  have htrace : WordTrace (prefixWord ++ tailWord_118329) baseStart_118329 baseEnd_118329 := by
    simpa [prefixWord, tailWord_118329, baseEnd_118329] using wordTrace_append hprefix tailTrace_118329
  have hstable : (prefixWord ++ tailWord_118329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118329).length < 2 ^ (prefixWord ++ tailWord_118329).sum := by decide
  have hdescent : baseEnd_118329 < baseStart_118329 := by decide
  rcases family_descends (prefixWord ++ tailWord_118329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118356 : List Nat := [2, 4, 1, 1, 1, 2, 2, 5, 1, 1, 3]
def baseStart_118356 : Nat := 118140960795 + 118356 * 2 ^ 59
def prefixEnd_118356 : Nat := 4983230072969 + 3 ^ 40 * 118356 * 2
def baseEnd_118356 : Nat := 60773516343644165305697

theorem tailTrace_118356 : CollatzResearch.WordTrace tailWord_118356 prefixEnd_118356 60773516343644165305697 := by
  unfold tailWord_118356
  simp only [CollatzResearch.WordTrace]
  refine ⟨2158398979611950220311461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2877865306149266960415281 2158398979611950220311461)
  ·
    refine ⟨404699808677240666308399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2158398979611950220311461 404699808677240666308399)
    ·
      refine ⟨607049713015860999462599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404699808677240666308399 607049713015860999462599)
      ·
        refine ⟨910574569523791499193899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607049713015860999462599 910574569523791499193899)
        ·
          refine ⟨1365861854285687248790849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910574569523791499193899 1365861854285687248790849)
          ·
            refine ⟨1024396390714265436593137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1365861854285687248790849 1024396390714265436593137)
            ·
              refine ⟨768297293035699077444853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1024396390714265436593137 768297293035699077444853)
              ·
                refine ⟨72027871222096788510455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 768297293035699077444853 72027871222096788510455)
                ·
                  refine ⟨108041806833145182765683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72027871222096788510455 108041806833145182765683)
                  ·
                    refine ⟨162062710249717774148525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108041806833145182765683 162062710249717774148525)
                    ·
                      refine ⟨60773516343644165305697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 162062710249717774148525 60773516343644165305697)
                      ·
                        rfl

theorem cell23_118356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_118356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118356 prefixEnd_118356 := by exact prefixLift 118356
  have htrace : WordTrace (prefixWord ++ tailWord_118356) baseStart_118356 baseEnd_118356 := by
    simpa [prefixWord, tailWord_118356, baseEnd_118356] using wordTrace_append hprefix tailTrace_118356
  have hstable : (prefixWord ++ tailWord_118356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118356).length < 2 ^ (prefixWord ++ tailWord_118356).sum := by decide
  have hdescent : baseEnd_118356 < baseStart_118356 := by decide
  rcases family_descends (prefixWord ++ tailWord_118356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118359 : List Nat := [1, 1, 3, 2, 2, 4, 3, 1, 1, 5]
def baseStart_118359 : Nat := 118140960795 + 118359 * 2 ^ 59
def prefixEnd_118359 : Nat := 4983230072969 + 3 ^ 40 * 118359 * 2
def baseEnd_118359 : Nat := 20258352261869217856061

theorem tailTrace_118359 : CollatzResearch.WordTrace tailWord_118359 prefixEnd_118359 20258352261869217856061 := by
  unfold tailWord_118359
  simp only [CollatzResearch.WordTrace]
  refine ⟨4316907378213031952982131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2877938252142021301988087 4316907378213031952982131)
  ·
    refine ⟨6475361067319547929473197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4316907378213031952982131 6475361067319547929473197)
    ·
      refine ⟨2428260400244830473552449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6475361067319547929473197 2428260400244830473552449)
      ·
        refine ⟨1821195300183622855164337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2428260400244830473552449 1821195300183622855164337)
        ·
          refine ⟨1365896475137717141373253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1821195300183622855164337 1365896475137717141373253)
          ·
            refine ⟨256105589088321964007485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1365896475137717141373253 256105589088321964007485)
            ·
              refine ⟨96039595908120736502807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256105589088321964007485 96039595908120736502807)
              ·
                refine ⟨144059393862181104754211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96039595908120736502807 144059393862181104754211)
                ·
                  refine ⟨216089090793271657131317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144059393862181104754211 216089090793271657131317)
                  ·
                    refine ⟨20258352261869217856061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 216089090793271657131317 20258352261869217856061)
                    ·
                      rfl

theorem cell23_118359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 1, 5].length) (baseStart_118359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118359 prefixEnd_118359 := by exact prefixLift 118359
  have htrace : WordTrace (prefixWord ++ tailWord_118359) baseStart_118359 baseEnd_118359 := by
    simpa [prefixWord, tailWord_118359, baseEnd_118359] using wordTrace_append hprefix tailTrace_118359
  have hstable : (prefixWord ++ tailWord_118359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118359).length < 2 ^ (prefixWord ++ tailWord_118359).sum := by decide
  have hdescent : baseEnd_118359 < baseStart_118359 := by decide
  rcases family_descends (prefixWord ++ tailWord_118359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118362 : List Nat := [3, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4]
def baseStart_118362 : Nat := 118140960795 + 118362 * 2 ^ 59
def prefixEnd_118362 : Nat := 4983230072969 + 3 ^ 40 * 118362 * 2
def baseEnd_118362 : Nat := 60776597227571141830669

theorem tailTrace_118362 : CollatzResearch.WordTrace tailWord_118362 prefixEnd_118362 60776597227571141830669 := by
  unfold tailWord_118362
  simp only [CollatzResearch.WordTrace]
  refine ⟨1079254199300540866335335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2878011198134775643560893 1079254199300540866335335)
  ·
    refine ⟨1618881298950811299503003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1079254199300540866335335 1618881298950811299503003)
    ·
      refine ⟨2428321948426216949254505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1618881298950811299503003 2428321948426216949254505)
      ·
        refine ⟨1821241461319662711940879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2428321948426216949254505 1821241461319662711940879)
        ·
          refine ⟨2731862191979494067911319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1821241461319662711940879 2731862191979494067911319)
          ·
            refine ⟨4097793287969241101866979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2731862191979494067911319 4097793287969241101866979)
            ·
              refine ⟨6146689931953861652800469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4097793287969241101866979 6146689931953861652800469)
              ·
                refine ⟨144063045280168632487511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6146689931953861652800469 144063045280168632487511)
                ·
                  refine ⟨216094567920252948731267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144063045280168632487511 216094567920252948731267)
                  ·
                    refine ⟨324141851880379423096901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 216094567920252948731267 324141851880379423096901)
                    ·
                      refine ⟨60776597227571141830669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 324141851880379423096901 60776597227571141830669)
                      ·
                        rfl

theorem cell23_118362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_118362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118362 prefixEnd_118362 := by exact prefixLift 118362
  have htrace : WordTrace (prefixWord ++ tailWord_118362) baseStart_118362 baseEnd_118362 := by
    simpa [prefixWord, tailWord_118362, baseEnd_118362] using wordTrace_append hprefix tailTrace_118362
  have hstable : (prefixWord ++ tailWord_118362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118362).length < 2 ^ (prefixWord ++ tailWord_118362).sum := by decide
  have hdescent : baseEnd_118362 < baseStart_118362 := by decide
  rcases family_descends (prefixWord ++ tailWord_118362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118373 : List Nat := [1, 3, 1, 3, 3, 1, 4, 2, 1, 1, 3]
def baseStart_118373 : Nat := 118140960795 + 118373 * 2 ^ 59
def prefixEnd_118373 : Nat := 4983230072969 + 3 ^ 40 * 118373 * 2
def baseEnd_118373 : Nat := 60782245514770598793119

theorem tailTrace_118373 : CollatzResearch.WordTrace tailWord_118373 prefixEnd_118373 60782245514770598793119 := by
  unfold tailWord_118373
  simp only [CollatzResearch.WordTrace]
  refine ⟨4317418000162312343991773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2878278666774874895994515 4317418000162312343991773)
  ·
    refine ⟨1619031750060867128996915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4317418000162312343991773 1619031750060867128996915)
    ·
      refine ⟨2428547625091300693495373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1619031750060867128996915 2428547625091300693495373)
      ·
        refine ⟨910705359409237760060765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2428547625091300693495373 910705359409237760060765)
        ·
          refine ⟨341514509778464160022787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 910705359409237760060765 341514509778464160022787)
          ·
            refine ⟨512271764667696240034181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341514509778464160022787 512271764667696240034181)
            ·
              refine ⟨96050955875193045006409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 512271764667696240034181 96050955875193045006409)
              ·
                refine ⟨72038216906394783754807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96050955875193045006409 72038216906394783754807)
                ·
                  refine ⟨108057325359592175632211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72038216906394783754807 108057325359592175632211)
                  ·
                    refine ⟨162085988039388263448317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108057325359592175632211 162085988039388263448317)
                    ·
                      refine ⟨60782245514770598793119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 162085988039388263448317 60782245514770598793119)
                      ·
                        rfl

theorem cell23_118373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_118373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118373 prefixEnd_118373 := by exact prefixLift 118373
  have htrace : WordTrace (prefixWord ++ tailWord_118373) baseStart_118373 baseEnd_118373 := by
    simpa [prefixWord, tailWord_118373, baseEnd_118373] using wordTrace_append hprefix tailTrace_118373
  have hstable : (prefixWord ++ tailWord_118373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118373).length < 2 ^ (prefixWord ++ tailWord_118373).sum := by decide
  have hdescent : baseEnd_118373 < baseStart_118373 := by decide
  rcases family_descends (prefixWord ++ tailWord_118373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118375 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_118375 : Nat := 118140960795 + 118375 * 2 ^ 59
def prefixEnd_118375 : Nat := 4983230072969 + 3 ^ 40 * 118375 * 2
def baseEnd_118375 : Nat := 60783272476079590968109

theorem tailTrace_118375 : CollatzResearch.WordTrace tailWord_118375 prefixEnd_118375 60783272476079590968109 := by
  unfold tailWord_118375
  simp only [CollatzResearch.WordTrace]
  refine ⟨4317490946155066685564579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2878327297436711123709719 4317490946155066685564579)
  ·
    refine ⟨6476236419232600028346869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4317490946155066685564579 6476236419232600028346869)
    ·
      refine ⟨607147164303056252657519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6476236419232600028346869 607147164303056252657519)
      ·
        refine ⟨910720746454584378986279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607147164303056252657519 910720746454584378986279)
        ·
          refine ⟨1366081119681876568479419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910720746454584378986279 1366081119681876568479419)
          ·
            refine ⟨2049121679522814852719129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1366081119681876568479419 2049121679522814852719129)
            ·
              refine ⟨1536841259642111139539347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2049121679522814852719129 1536841259642111139539347)
              ·
                refine ⟨2305261889463166709309021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1536841259642111139539347 2305261889463166709309021)
                ·
                  refine ⟨864473208548687515990883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2305261889463166709309021 864473208548687515990883)
                  ·
                    refine ⟨1296709812823031273986325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 864473208548687515990883 1296709812823031273986325)
                    ·
                      refine ⟨60783272476079590968109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1296709812823031273986325 60783272476079590968109)
                      ·
                        rfl

theorem cell23_118375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_118375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_118375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_118375 prefixEnd_118375 := by exact prefixLift 118375
  have htrace : WordTrace (prefixWord ++ tailWord_118375) baseStart_118375 baseEnd_118375 := by
    simpa [prefixWord, tailWord_118375, baseEnd_118375] using wordTrace_append hprefix tailTrace_118375
  have hstable : (prefixWord ++ tailWord_118375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118375).length < 2 ^ (prefixWord ++ tailWord_118375).sum := by decide
  have hdescent : baseEnd_118375 < baseStart_118375 := by decide
  rcases family_descends (prefixWord ++ tailWord_118375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
