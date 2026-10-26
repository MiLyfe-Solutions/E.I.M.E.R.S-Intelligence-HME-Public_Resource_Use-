import V185TrunkScan22Chunk182

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1632484 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_1632484 : Nat := 118140960795 + 1632484 * 2 ^ 59
def prefixEnd_1632484 : Nat := 4983230072969 + 3 ^ 40 * 1632484 * 2
def baseEnd_1632484 : Nat := 558832635182997421694899

theorem tailTrace_1632484 : CollatzResearch.WordTrace tailWord_1632484 prefixEnd_1632484 558832635182997421694899 := by
  unfold tailWord_1632484
  simp only [CollatzResearch.WordTrace]
  refine ⟨29770791508898374457712253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39694388678531165943616337 29770791508898374457712253)
  ·
    refine ⟨11164046815836890421642095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29770791508898374457712253 11164046815836890421642095)
    ·
      refine ⟨16746070223755335632463143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11164046815836890421642095 16746070223755335632463143)
      ·
        refine ⟨25119105335633003448694715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16746070223755335632463143 25119105335633003448694715)
        ·
          refine ⟨37678658003449505173042073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25119105335633003448694715 37678658003449505173042073)
          ·
            refine ⟨28258993502587128879781555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37678658003449505173042073 28258993502587128879781555)
            ·
              refine ⟨42388490253880693319672333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28258993502587128879781555 42388490253880693319672333)
              ·
                refine ⟨15895683845205259994877125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42388490253880693319672333 15895683845205259994877125)
                ·
                  refine ⟨2980440720975986249039461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15895683845205259994877125 2980440720975986249039461)
                  ·
                    refine ⟨558832635182997421694899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2980440720975986249039461 558832635182997421694899)
                    ·
                      rfl

theorem cell22_1632484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_1632484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632484 prefixEnd_1632484 := by exact prefixLift 1632484
  have htrace : WordTrace (prefixWord ++ tailWord_1632484) baseStart_1632484 baseEnd_1632484 := by
    simpa [prefixWord, tailWord_1632484, baseEnd_1632484] using wordTrace_append hprefix tailTrace_1632484
  have hstable : (prefixWord ++ tailWord_1632484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632484).length < 2 ^ (prefixWord ++ tailWord_1632484).sum := by decide
  have hdescent : baseEnd_1632484 < baseStart_1632484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632516 : List Nat := [2, 3, 2, 2, 3, 1, 1, 8]
def baseStart_1632516 : Nat := 118140960795 + 1632516 * 2 ^ 59
def prefixEnd_1632516 : Nat := 4983230072969 + 3 ^ 40 * 1632516 * 2
def baseEnd_1632516 : Nat := 62093732159662222766089

theorem tailTrace_1632516 : CollatzResearch.WordTrace tailWord_1632516 prefixEnd_1632516 62093732159662222766089 := by
  unfold tailWord_1632516
  simp only [CollatzResearch.WordTrace]
  refine ⟨29771375076840409190294701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39695166769120545587059601 29771375076840409190294701)
  ·
    refine ⟨11164265653815153446360513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29771375076840409190294701 11164265653815153446360513)
    ·
      refine ⟨8373199240361365084770385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11164265653815153446360513 8373199240361365084770385)
      ·
        refine ⟨6279899430271023813577789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8373199240361365084770385 6279899430271023813577789)
        ·
          refine ⟨2354962286351633930091671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6279899430271023813577789 2354962286351633930091671)
          ·
            refine ⟨3532443429527450895137507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354962286351633930091671 3532443429527450895137507)
            ·
              refine ⟨5298665144291176342706261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3532443429527450895137507 5298665144291176342706261)
              ·
                refine ⟨62093732159662222766089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5298665144291176342706261 62093732159662222766089)
                ·
                  rfl

theorem cell22_1632516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 8].length) (baseStart_1632516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632516 prefixEnd_1632516 := by exact prefixLift 1632516
  have htrace : WordTrace (prefixWord ++ tailWord_1632516) baseStart_1632516 baseEnd_1632516 := by
    simpa [prefixWord, tailWord_1632516, baseEnd_1632516] using wordTrace_append hprefix tailTrace_1632516
  have hstable : (prefixWord ++ tailWord_1632516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632516).length < 2 ^ (prefixWord ++ tailWord_1632516).sum := by decide
  have hdescent : baseEnd_1632516 < baseStart_1632516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632548 : List Nat := [2, 3, 1, 3, 1, 2, 3, 1, 3, 3]
def baseStart_1632548 : Nat := 118140960795 + 1632548 * 2 ^ 59
def prefixEnd_1632548 : Nat := 4983230072969 + 3 ^ 40 * 1632548 * 2
def baseEnd_1632548 : Nat := 558854543690922588094703

theorem tailTrace_1632548 : CollatzResearch.WordTrace tailWord_1632548 prefixEnd_1632548 558854543690922588094703 := by
  unfold tailWord_1632548
  simp only [CollatzResearch.WordTrace]
  refine ⟨29771958644782443922877149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39695944859709925230502865 29771958644782443922877149)
  ·
    refine ⟨11164484491793416471078931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29771958644782443922877149 11164484491793416471078931)
    ·
      refine ⟨16746726737690124706618397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11164484491793416471078931 16746726737690124706618397)
      ·
        refine ⟨6280022526633796764981899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16746726737690124706618397 6280022526633796764981899)
        ·
          refine ⟨9420033789950695147472849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6280022526633796764981899 9420033789950695147472849)
          ·
            refine ⟨7065025342463021360604637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9420033789950695147472849 7065025342463021360604637)
            ·
              refine ⟨2649384503423633010226739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7065025342463021360604637 2649384503423633010226739)
              ·
                refine ⟨3974076755135449515340109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649384503423633010226739 3974076755135449515340109)
                ·
                  refine ⟨1490278783175793568252541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3974076755135449515340109 1490278783175793568252541)
                  ·
                    refine ⟨558854543690922588094703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1490278783175793568252541 558854543690922588094703)
                    ·
                      rfl

theorem cell22_1632548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_1632548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632548 prefixEnd_1632548 := by exact prefixLift 1632548
  have htrace : WordTrace (prefixWord ++ tailWord_1632548) baseStart_1632548 baseEnd_1632548 := by
    simpa [prefixWord, tailWord_1632548, baseEnd_1632548] using wordTrace_append hprefix tailTrace_1632548
  have hstable : (prefixWord ++ tailWord_1632548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632548).length < 2 ^ (prefixWord ++ tailWord_1632548).sum := by decide
  have hdescent : baseEnd_1632548 < baseStart_1632548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632554 : List Nat := [3, 1, 4, 2, 3, 1, 2, 1, 2, 3]
def baseStart_1632554 : Nat := 118140960795 + 1632554 * 2 ^ 59
def prefixEnd_1632554 : Nat := 4983230072969 + 3 ^ 40 * 1632554 * 2
def baseEnd_1632554 : Nat := 558856597613540572444685

theorem tailTrace_1632554 : CollatzResearch.WordTrace tailWord_1632554 prefixEnd_1632554 558856597613540572444685 := by
  unfold tailWord_1632554
  simp only [CollatzResearch.WordTrace]
  refine ⟨14886034031885787717618179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39696090751695433913648477 14886034031885787717618179)
  ·
    refine ⟨22329051047828681576427269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14886034031885787717618179 22329051047828681576427269)
    ·
      refine ⟨4186697071467877795580113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22329051047828681576427269 4186697071467877795580113)
      ·
        refine ⟨3140022803600908346685085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4186697071467877795580113 3140022803600908346685085)
        ·
          refine ⟨1177508551350340630006907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3140022803600908346685085 1177508551350340630006907)
          ·
            refine ⟨1766262827025510945010361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177508551350340630006907 1766262827025510945010361)
            ·
              refine ⟨1324697120269133208757771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1766262827025510945010361 1324697120269133208757771)
              ·
                refine ⟨1987045680403699813136657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1324697120269133208757771 1987045680403699813136657)
                ·
                  refine ⟨1490284260302774859852493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1987045680403699813136657 1490284260302774859852493)
                  ·
                    refine ⟨558856597613540572444685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1490284260302774859852493 558856597613540572444685)
                    ·
                      rfl

theorem cell22_1632554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_1632554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632554 prefixEnd_1632554 := by exact prefixLift 1632554
  have htrace : WordTrace (prefixWord ++ tailWord_1632554) baseStart_1632554 baseEnd_1632554 := by
    simpa [prefixWord, tailWord_1632554, baseEnd_1632554] using wordTrace_append hprefix tailTrace_1632554
  have hstable : (prefixWord ++ tailWord_1632554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632554).length < 2 ^ (prefixWord ++ tailWord_1632554).sum := by decide
  have hdescent : baseEnd_1632554 < baseStart_1632554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632559 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 2, 5]
def baseStart_1632559 : Nat := 118140960795 + 1632559 * 2 ^ 59
def prefixEnd_1632559 : Nat := 4983230072969 + 3 ^ 40 * 1632559 * 2
def baseEnd_1632559 : Nat := 558858309215722226069669

theorem tailTrace_1632559 : CollatzResearch.WordTrace tailWord_1632559 prefixEnd_1632559 558858309215722226069669 := by
  unfold tailWord_1632559
  simp only [CollatzResearch.WordTrace]
  refine ⟨59544318492525036724404731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39696212328350024482936487 59544318492525036724404731)
  ·
    refine ⟨89316477738787555086607097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59544318492525036724404731 89316477738787555086607097)
    ·
      refine ⟨66987358304090666314955323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89316477738787555086607097 66987358304090666314955323)
      ·
        refine ⟨100481037456135999472432985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66987358304090666314955323 100481037456135999472432985)
        ·
          refine ⟨75360778092101999604324739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100481037456135999472432985 75360778092101999604324739)
          ·
            refine ⟨113041167138152999406487109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75360778092101999604324739 113041167138152999406487109)
            ·
              refine ⟨21195218838403687388716333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113041167138152999406487109 21195218838403687388716333)
              ·
                refine ⟨7948207064401382770768625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21195218838403687388716333 7948207064401382770768625)
                ·
                  refine ⟨5961155298301037078076469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7948207064401382770768625 5961155298301037078076469)
                  ·
                    refine ⟨558858309215722226069669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5961155298301037078076469 558858309215722226069669)
                    ·
                      rfl

theorem cell22_1632559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_1632559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632559 prefixEnd_1632559 := by exact prefixLift 1632559
  have htrace : WordTrace (prefixWord ++ tailWord_1632559) baseStart_1632559 baseEnd_1632559 := by
    simpa [prefixWord, tailWord_1632559, baseEnd_1632559] using wordTrace_append hprefix tailTrace_1632559
  have hstable : (prefixWord ++ tailWord_1632559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632559).length < 2 ^ (prefixWord ++ tailWord_1632559).sum := by decide
  have hdescent : baseEnd_1632559 < baseStart_1632559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632619 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 3, 6]
def baseStart_1632619 : Nat := 118140960795 + 1632619 * 2 ^ 59
def prefixEnd_1632619 : Nat := 4983230072969 + 3 ^ 40 * 1632619 * 2
def baseEnd_1632619 : Nat := 558878848441902069569485

theorem tailTrace_1632619 : CollatzResearch.WordTrace tailWord_1632619 prefixEnd_1632619 558878848441902069569485 := by
  unfold tailWord_1632619
  simp only [CollatzResearch.WordTrace]
  refine ⟨59546506872307666971588911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39697671248205111314392607 59546506872307666971588911)
  ·
    refine ⟨89319760308461500457383367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59546506872307666971588911 89319760308461500457383367)
    ·
      refine ⟨133979640462692250686075051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89319760308461500457383367 133979640462692250686075051)
      ·
        refine ⟨200969460694038376029112577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133979640462692250686075051 200969460694038376029112577)
        ·
          refine ⟨150727095520528782021834433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200969460694038376029112577 150727095520528782021834433)
          ·
            refine ⟨113045321640396586516375825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150727095520528782021834433 113045321640396586516375825)
            ·
              refine ⟨84783991230297439887281869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113045321640396586516375825 84783991230297439887281869)
              ·
                refine ⟨31793996711361539957730701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84783991230297439887281869 31793996711361539957730701)
                ·
                  refine ⟨11922748766760577484149013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31793996711361539957730701 11922748766760577484149013)
                  ·
                    refine ⟨558878848441902069569485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11922748766760577484149013 558878848441902069569485)
                    ·
                      rfl

theorem cell22_1632619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 6].length) (baseStart_1632619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632619 prefixEnd_1632619 := by exact prefixLift 1632619
  have htrace : WordTrace (prefixWord ++ tailWord_1632619) baseStart_1632619 baseEnd_1632619 := by
    simpa [prefixWord, tailWord_1632619, baseEnd_1632619] using wordTrace_append hprefix tailTrace_1632619
  have hstable : (prefixWord ++ tailWord_1632619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632619).length < 2 ^ (prefixWord ++ tailWord_1632619).sum := by decide
  have hdescent : baseEnd_1632619 < baseStart_1632619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632636 : List Nat := [2, 2, 2, 1, 1, 1, 2, 5, 2, 4]
def baseStart_1632636 : Nat := 118140960795 + 1632636 * 2 ^ 59
def prefixEnd_1632636 : Nat := 4983230072969 + 3 ^ 40 * 1632636 * 2
def baseEnd_1632636 : Nat := 558884667889319691894433

theorem tailTrace_1632636 : CollatzResearch.WordTrace tailWord_1632636 prefixEnd_1632636 558884667889319691894433 := by
  unfold tailWord_1632636
  simp only [CollatzResearch.WordTrace]
  refine ⟨29773563456623039437478881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39698084608830719249971841 29773563456623039437478881)
  ·
    refine ⟨22330172592467279578109161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29773563456623039437478881 22330172592467279578109161)
    ·
      refine ⟨16747629444350459683581871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22330172592467279578109161 16747629444350459683581871)
      ·
        refine ⟨25121444166525689525372807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16747629444350459683581871 25121444166525689525372807)
        ·
          refine ⟨37682166249788534288059211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25121444166525689525372807 37682166249788534288059211)
          ·
            refine ⟨56523249374682801432088817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37682166249788534288059211 56523249374682801432088817)
            ·
              refine ⟨42392437031012101074066613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56523249374682801432088817 42392437031012101074066613)
              ·
                refine ⟨3974290971657384475693745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42392437031012101074066613 3974290971657384475693745)
                ·
                  refine ⟨2980718228743038356770309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3974290971657384475693745 2980718228743038356770309)
                  ·
                    refine ⟨558884667889319691894433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2980718228743038356770309 558884667889319691894433)
                    ·
                      rfl

theorem cell22_1632636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_1632636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632636 prefixEnd_1632636 := by exact prefixLift 1632636
  have htrace : WordTrace (prefixWord ++ tailWord_1632636) baseStart_1632636 baseEnd_1632636 := by
    simpa [prefixWord, tailWord_1632636, baseEnd_1632636] using wordTrace_append hprefix tailTrace_1632636
  have hstable : (prefixWord ++ tailWord_1632636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632636).length < 2 ^ (prefixWord ++ tailWord_1632636).sum := by decide
  have hdescent : baseEnd_1632636 < baseStart_1632636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632642 : List Nat := [3, 4, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_1632642 : Nat := 118140960795 + 1632642 * 2 ^ 59
def prefixEnd_1632642 : Nat := 4983230072969 + 3 ^ 40 * 1632642 * 2
def baseEnd_1632642 : Nat := 558886721811937676244415

theorem tailTrace_1632642 : CollatzResearch.WordTrace tailWord_1632642 prefixEnd_1632642 558886721811937676244415 := by
  unfold tailWord_1632642
  simp only [CollatzResearch.WordTrace]
  refine ⟨14886836437806085474919045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39698230500816227933117453 14886836437806085474919045)
  ·
    refine ⟨2791281832088641026547321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14886836437806085474919045 2791281832088641026547321)
    ·
      refine ⟨2093461374066480769910491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2791281832088641026547321 2093461374066480769910491)
      ·
        refine ⟨3140192061099721154865737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2093461374066480769910491 3140192061099721154865737)
        ·
          refine ⟨2355144045824790866149303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3140192061099721154865737 2355144045824790866149303)
          ·
            refine ⟨3532716068737186299223955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2355144045824790866149303 3532716068737186299223955)
            ·
              refine ⟨5299074103105779448835933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3532716068737186299223955 5299074103105779448835933)
              ·
                refine ⟨1987152788664667293313475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5299074103105779448835933 1987152788664667293313475)
                ·
                  refine ⟨2980729182997000939970213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1987152788664667293313475 2980729182997000939970213)
                  ·
                    refine ⟨558886721811937676244415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2980729182997000939970213 558886721811937676244415)
                    ·
                      rfl

theorem cell22_1632642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_1632642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632642 prefixEnd_1632642 := by exact prefixLift 1632642
  have htrace : WordTrace (prefixWord ++ tailWord_1632642) baseStart_1632642 baseEnd_1632642 := by
    simpa [prefixWord, tailWord_1632642, baseEnd_1632642] using wordTrace_append hprefix tailTrace_1632642
  have hstable : (prefixWord ++ tailWord_1632642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632642).length < 2 ^ (prefixWord ++ tailWord_1632642).sum := by decide
  have hdescent : baseEnd_1632642 < baseStart_1632642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632743 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 3, 4]
def baseStart_1632743 : Nat := 118140960795 + 1632743 * 2 ^ 59
def prefixEnd_1632743 : Nat := 4983230072969 + 3 ^ 40 * 1632743 * 2
def baseEnd_1632743 : Nat := 558921296176007079469105

theorem tailTrace_1632743 : CollatzResearch.WordTrace tailWord_1632743 prefixEnd_1632743 558921296176007079469105 := by
  unfold tailWord_1632743
  simp only [CollatzResearch.WordTrace]
  refine ⟨59551029523858436149102883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39700686349238957432735255 59551029523858436149102883)
  ·
    refine ⟨89326544285787654223654325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59551029523858436149102883 89326544285787654223654325)
    ·
      refine ⟨8374363526792592583467593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89326544285787654223654325 8374363526792592583467593)
      ·
        refine ⟨6280772645094444437600695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8374363526792592583467593 6280772645094444437600695)
        ·
          refine ⟨9421158967641666656401043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6280772645094444437600695 9421158967641666656401043)
          ·
            refine ⟨14131738451462499984601565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9421158967641666656401043 14131738451462499984601565)
            ·
              refine ⟨5299401919298437494225587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14131738451462499984601565 5299401919298437494225587)
              ·
                refine ⟨7949102878947656241338381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5299401919298437494225587 7949102878947656241338381)
                ·
                  refine ⟨2980913579605371090501893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7949102878947656241338381 2980913579605371090501893)
                  ·
                    refine ⟨558921296176007079469105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2980913579605371090501893 558921296176007079469105)
                    ·
                      rfl

theorem cell22_1632743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_1632743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632743 prefixEnd_1632743 := by exact prefixLift 1632743
  have htrace : WordTrace (prefixWord ++ tailWord_1632743) baseStart_1632743 baseEnd_1632743 := by
    simpa [prefixWord, tailWord_1632743, baseEnd_1632743] using wordTrace_append hprefix tailTrace_1632743
  have hstable : (prefixWord ++ tailWord_1632743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632743).length < 2 ^ (prefixWord ++ tailWord_1632743).sum := by decide
  have hdescent : baseEnd_1632743 < baseStart_1632743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632760 : List Nat := [2, 1, 2, 1, 1, 4, 5, 1, 1, 4]
def baseStart_1632760 : Nat := 118140960795 + 1632760 * 2 ^ 59
def prefixEnd_1632760 : Nat := 4983230072969 + 3 ^ 40 * 1632760 * 2
def baseEnd_1632760 : Nat := 558927115623424701794053

theorem tailTrace_1632760 : CollatzResearch.WordTrace tailWord_1632760 prefixEnd_1632760 558927115623424701794053 := by
  unfold tailWord_1632760
  simp only [CollatzResearch.WordTrace]
  refine ⟨29775824782398424026235867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39701099709864565368314489 29775824782398424026235867)
  ·
    refine ⟨44663737173597636039353801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29775824782398424026235867 44663737173597636039353801)
    ·
      refine ⟨33497802880198227029515351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44663737173597636039353801 33497802880198227029515351)
      ·
        refine ⟨50246704320297340544273027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33497802880198227029515351 50246704320297340544273027)
        ·
          refine ⟨75370056480446010816409541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50246704320297340544273027 75370056480446010816409541)
          ·
            refine ⟨14131885590083627028076789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75370056480446010816409541 14131885590083627028076789)
            ·
              refine ⟨1324864274070340033882199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14131885590083627028076789 1324864274070340033882199)
              ·
                refine ⟨1987296411105510050823299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1324864274070340033882199 1987296411105510050823299)
                ·
                  refine ⟨2980944616658265076234949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1987296411105510050823299 2980944616658265076234949)
                  ·
                    refine ⟨558927115623424701794053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2980944616658265076234949 558927115623424701794053)
                    ·
                      rfl

theorem cell22_1632760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 1, 4].length) (baseStart_1632760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632760 prefixEnd_1632760 := by exact prefixLift 1632760
  have htrace : WordTrace (prefixWord ++ tailWord_1632760) baseStart_1632760 baseEnd_1632760 := by
    simpa [prefixWord, tailWord_1632760, baseEnd_1632760] using wordTrace_append hprefix tailTrace_1632760
  have hstable : (prefixWord ++ tailWord_1632760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632760).length < 2 ^ (prefixWord ++ tailWord_1632760).sum := by decide
  have hdescent : baseEnd_1632760 < baseStart_1632760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632773 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 4, 3]
def baseStart_1632773 : Nat := 118140960795 + 1632773 * 2 ^ 59
def prefixEnd_1632773 : Nat := 4983230072969 + 3 ^ 40 * 1632773 * 2
def baseEnd_1632773 : Nat := 558931565789097001219013

theorem tailTrace_1632773 : CollatzResearch.WordTrace tailWord_1632773 prefixEnd_1632773 558931565789097001219013 := by
  unfold tailWord_1632773
  simp only [CollatzResearch.WordTrace]
  refine ⟨59552123713749751272694973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39701415809166500848463315 59552123713749751272694973)
  ·
    refine ⟨22332046392656156727260615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59552123713749751272694973 22332046392656156727260615)
    ·
      refine ⟨33498069588984235090890923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22332046392656156727260615 33498069588984235090890923)
      ·
        refine ⟨50247104383476352636336385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33498069588984235090890923 50247104383476352636336385)
        ·
          refine ⟨37685328287607264477252289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50247104383476352636336385 37685328287607264477252289)
          ·
            refine ⟨28263996215705448357939217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37685328287607264477252289 28263996215705448357939217)
            ·
              refine ⟨21197997161779086268454413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28263996215705448357939217 21197997161779086268454413)
              ·
                refine ⟨7949248935667157350670405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21197997161779086268454413 7949248935667157350670405)
                ·
                  refine ⟨1490484175437592003250701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7949248935667157350670405 1490484175437592003250701)
                  ·
                    refine ⟨558931565789097001219013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1490484175437592003250701 558931565789097001219013)
                    ·
                      rfl

theorem cell22_1632773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_1632773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632773 prefixEnd_1632773 := by exact prefixLift 1632773
  have htrace : WordTrace (prefixWord ++ tailWord_1632773) baseStart_1632773 baseEnd_1632773 := by
    simpa [prefixWord, tailWord_1632773, baseEnd_1632773] using wordTrace_append hprefix tailTrace_1632773
  have hstable : (prefixWord ++ tailWord_1632773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632773).length < 2 ^ (prefixWord ++ tailWord_1632773).sum := by decide
  have hdescent : baseEnd_1632773 < baseStart_1632773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632886 : List Nat := [5, 1, 1, 2, 4, 1, 1, 1, 3, 3]
def baseStart_1632886 : Nat := 118140960795 + 1632886 * 2 ^ 59
def prefixEnd_1632886 : Nat := 4983230072969 + 3 ^ 40 * 1632886 * 2
def baseEnd_1632886 : Nat := 558970247998402373143667

theorem tailTrace_1632886 : CollatzResearch.WordTrace tailWord_1632886 prefixEnd_1632886 558970247998402373143667 := by
  unfold tailWord_1632886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3722265322646273223222407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39704163441560247714372341 3722265322646273223222407)
  ·
    refine ⟨5583397983969409834833611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3722265322646273223222407 5583397983969409834833611)
    ·
      refine ⟨8375096975954114752250417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5583397983969409834833611 8375096975954114752250417)
      ·
        refine ⟨6281322731965586064187813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8375096975954114752250417 6281322731965586064187813)
        ·
          refine ⟨1177748012243547387035215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6281322731965586064187813 1177748012243547387035215)
          ·
            refine ⟨1766622018365321080552823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177748012243547387035215 1766622018365321080552823)
            ·
              refine ⟨2649933027547981620829235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1766622018365321080552823 2649933027547981620829235)
              ·
                refine ⟨3974899541321972431243853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649933027547981620829235 3974899541321972431243853)
                ·
                  refine ⟨1490587327995739661716445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3974899541321972431243853 1490587327995739661716445)
                  ·
                    refine ⟨558970247998402373143667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1490587327995739661716445 558970247998402373143667)
                    ·
                      rfl

theorem cell22_1632886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_1632886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632886 prefixEnd_1632886 := by exact prefixLift 1632886
  have htrace : WordTrace (prefixWord ++ tailWord_1632886) baseStart_1632886 baseEnd_1632886 := by
    simpa [prefixWord, tailWord_1632886, baseEnd_1632886] using wordTrace_append hprefix tailTrace_1632886
  have hstable : (prefixWord ++ tailWord_1632886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632886).length < 2 ^ (prefixWord ++ tailWord_1632886).sum := by decide
  have hdescent : baseEnd_1632886 < baseStart_1632886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632925 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 6, 3]
def baseStart_1632925 : Nat := 118140960795 + 1632925 * 2 ^ 59
def prefixEnd_1632925 : Nat := 4983230072969 + 3 ^ 40 * 1632925 * 2
def baseEnd_1632925 : Nat := 558983598495419271418547

theorem tailTrace_1632925 : CollatzResearch.WordTrace tailWord_1632925 prefixEnd_1632925 558983598495419271418547 := by
  unfold tailWord_1632925
  simp only [CollatzResearch.WordTrace]
  refine ⟨59557667609199081232228229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39705111739466054154818819 59557667609199081232228229)
  ·
    refine ⟨11167062676724827731042793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59557667609199081232228229 11167062676724827731042793)
    ·
      refine ⟨8375297007543620798282095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11167062676724827731042793 8375297007543620798282095)
      ·
        refine ⟨12562945511315431197423143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8375297007543620798282095 12562945511315431197423143)
        ·
          refine ⟨18844418266973146796134715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12562945511315431197423143 18844418266973146796134715)
          ·
            refine ⟨28266627400459720194202073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18844418266973146796134715 28266627400459720194202073)
            ·
              refine ⟨21199970550344790145651555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28266627400459720194202073 21199970550344790145651555)
              ·
                refine ⟨31799955825517185218477333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21199970550344790145651555 31799955825517185218477333)
                ·
                  refine ⟨1490622929321118057116125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31799955825517185218477333 1490622929321118057116125)
                  ·
                    refine ⟨558983598495419271418547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1490622929321118057116125 558983598495419271418547)
                    ·
                      rfl

theorem cell22_1632925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_1632925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632925 prefixEnd_1632925 := by exact prefixLift 1632925
  have htrace : WordTrace (prefixWord ++ tailWord_1632925) baseStart_1632925 baseEnd_1632925 := by
    simpa [prefixWord, tailWord_1632925, baseEnd_1632925] using wordTrace_append hprefix tailTrace_1632925
  have hstable : (prefixWord ++ tailWord_1632925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632925).length < 2 ^ (prefixWord ++ tailWord_1632925).sum := by decide
  have hdescent : baseEnd_1632925 < baseStart_1632925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632929 : List Nat := [1, 2, 3, 3, 3, 1, 3, 1, 1, 4]
def baseStart_1632929 : Nat := 118140960795 + 1632929 * 2 ^ 59
def prefixEnd_1632929 : Nat := 4983230072969 + 3 ^ 40 * 1632929 * 2
def baseEnd_1632929 : Nat := 558984967777164594318535

theorem tailTrace_1632929 : CollatzResearch.WordTrace tailWord_1632929 prefixEnd_1632929 558984967777164594318535 := by
  unfold tailWord_1632929
  simp only [CollatzResearch.WordTrace]
  refine ⟨59557813501184589915373841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39705209000789726610249227 59557813501184589915373841)
  ·
    refine ⟨44668360125888442436530381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59557813501184589915373841 44668360125888442436530381)
    ·
      refine ⟨16750635047208165913698893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44668360125888442436530381 16750635047208165913698893)
      ·
        refine ⟨6281488142703062217637085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16750635047208165913698893 6281488142703062217637085)
        ·
          refine ⟨2355558053513648331613907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6281488142703062217637085 2355558053513648331613907)
          ·
            refine ⟨3533337080270472497420861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2355558053513648331613907 3533337080270472497420861)
            ·
              refine ⟨1325001405101427186532823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3533337080270472497420861 1325001405101427186532823)
              ·
                refine ⟨1987502107652140779799235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1325001405101427186532823 1987502107652140779799235)
                ·
                  refine ⟨2981253161478211169698853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1987502107652140779799235 2981253161478211169698853)
                  ·
                    refine ⟨558984967777164594318535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2981253161478211169698853 558984967777164594318535)
                    ·
                      rfl

theorem cell22_1632929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_1632929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632929 prefixEnd_1632929 := by exact prefixLift 1632929
  have htrace : WordTrace (prefixWord ++ tailWord_1632929) baseStart_1632929 baseEnd_1632929 := by
    simpa [prefixWord, tailWord_1632929, baseEnd_1632929] using wordTrace_append hprefix tailTrace_1632929
  have hstable : (prefixWord ++ tailWord_1632929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632929).length < 2 ^ (prefixWord ++ tailWord_1632929).sum := by decide
  have hdescent : baseEnd_1632929 < baseStart_1632929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632953 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 2, 7]
def baseStart_1632953 : Nat := 118140960795 + 1632953 * 2 ^ 59
def prefixEnd_1632953 : Nat := 4983230072969 + 3 ^ 40 * 1632953 * 2
def baseEnd_1632953 : Nat := 558993183467636531718461

theorem tailTrace_1632953 : CollatzResearch.WordTrace tailWord_1632953 prefixEnd_1632953 558993183467636531718461 := by
  unfold tailWord_1632953
  simp only [CollatzResearch.WordTrace]
  refine ⟨59558688853097642014247513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39705792568731761342831675 59558688853097642014247513)
  ·
    refine ⟨44669016639823231510685635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59558688853097642014247513 44669016639823231510685635)
    ·
      refine ⟨67003524959734847266028453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44669016639823231510685635 67003524959734847266028453)
      ·
        refine ⟨12563160929950283862380335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67003524959734847266028453 12563160929950283862380335)
        ·
          refine ⟨18844741394925425793570503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12563160929950283862380335 18844741394925425793570503)
          ·
            refine ⟨28267112092388138690355755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18844741394925425793570503 28267112092388138690355755)
            ·
              refine ⟨42400668138582208035533633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28267112092388138690355755 42400668138582208035533633)
              ·
                refine ⟨31800501103936656026650225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42400668138582208035533633 31800501103936656026650225)
                ·
                  refine ⟨23850375827952492019987669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31800501103936656026650225 23850375827952492019987669)
                  ·
                    refine ⟨558993183467636531718461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23850375827952492019987669 558993183467636531718461)
                    ·
                      rfl

theorem cell22_1632953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_1632953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632953 prefixEnd_1632953 := by exact prefixLift 1632953
  have htrace : WordTrace (prefixWord ++ tailWord_1632953) baseStart_1632953 baseEnd_1632953 := by
    simpa [prefixWord, tailWord_1632953, baseEnd_1632953] using wordTrace_append hprefix tailTrace_1632953
  have hstable : (prefixWord ++ tailWord_1632953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632953).length < 2 ^ (prefixWord ++ tailWord_1632953).sum := by decide
  have hdescent : baseEnd_1632953 < baseStart_1632953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632972 : List Nat := [2, 2, 1, 5, 1, 2, 3, 6]
def baseStart_1632972 : Nat := 118140960795 + 1632972 * 2 ^ 59
def prefixEnd_1632972 : Nat := 4983230072969 + 3 ^ 40 * 1632972 * 2
def baseEnd_1632972 : Nat := 62111076395102979499267

theorem tailTrace_1632972 : CollatzResearch.WordTrace tailWord_1632972 prefixEnd_1632972 62111076395102979499267 := by
  unfold tailWord_1632972
  simp only [CollatzResearch.WordTrace]
  refine ⟨29779690920014404129594585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39706254560019205506126113 29779690920014404129594585)
  ·
    refine ⟨22334768190010803097195939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29779690920014404129594585 22334768190010803097195939)
    ·
      refine ⟨33502152285016204645793909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22334768190010803097195939 33502152285016204645793909)
      ·
        refine ⟨3140826776720269185543179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33502152285016204645793909 3140826776720269185543179)
        ·
          refine ⟨4711240165080403778314769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3140826776720269185543179 4711240165080403778314769)
          ·
            refine ⟨3533430123810302833736077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4711240165080403778314769 3533430123810302833736077)
            ·
              refine ⟨1325036296428863562651029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3533430123810302833736077 1325036296428863562651029)
              ·
                refine ⟨62111076395102979499267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1325036296428863562651029 62111076395102979499267)
                ·
                  rfl

theorem cell22_1632972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 6].length) (baseStart_1632972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632972 prefixEnd_1632972 := by exact prefixLift 1632972
  have htrace : WordTrace (prefixWord ++ tailWord_1632972) baseStart_1632972 baseEnd_1632972 := by
    simpa [prefixWord, tailWord_1632972, baseEnd_1632972] using wordTrace_append hprefix tailTrace_1632972
  have hstable : (prefixWord ++ tailWord_1632972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632972).length < 2 ^ (prefixWord ++ tailWord_1632972).sum := by decide
  have hdescent : baseEnd_1632972 < baseStart_1632972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633120 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 1, 8]
def baseStart_1633120 : Nat := 118140960795 + 1633120 * 2 ^ 59
def prefixEnd_1633120 : Nat := 4983230072969 + 3 ^ 40 * 1633120 * 2
def baseEnd_1633120 : Nat := 559050350980503762792949

theorem tailTrace_1633120 : CollatzResearch.WordTrace tailWord_1633120 prefixEnd_1633120 559050350980503762792949 := by
  unfold tailWord_1633120
  simp only [CollatzResearch.WordTrace]
  refine ⟨29782389921746314767788407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39709853228995086357051209 29782389921746314767788407)
  ·
    refine ⟨44673584882619472151682611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29782389921746314767788407 44673584882619472151682611)
    ·
      refine ⟨67010377323929208227523917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44673584882619472151682611 67010377323929208227523917)
      ·
        refine ⟨25128891496473453085321469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67010377323929208227523917 25128891496473453085321469)
        ·
          refine ⟨9423334311177544906995551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25128891496473453085321469 9423334311177544906995551)
          ·
            refine ⟨14135001466766317360493327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9423334311177544906995551 14135001466766317360493327)
            ·
              refine ⟨21202502200149476040739991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14135001466766317360493327 21202502200149476040739991)
              ·
                refine ⟨31803753300224214061109987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21202502200149476040739991 31803753300224214061109987)
                ·
                  refine ⟨47705629950336321091664981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31803753300224214061109987 47705629950336321091664981)
                  ·
                    refine ⟨559050350980503762792949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47705629950336321091664981 559050350980503762792949)
                    ·
                      rfl

theorem cell22_1633120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_1633120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633120 prefixEnd_1633120 := by exact prefixLift 1633120
  have htrace : WordTrace (prefixWord ++ tailWord_1633120) baseStart_1633120 baseEnd_1633120 := by
    simpa [prefixWord, tailWord_1633120, baseEnd_1633120] using wordTrace_append hprefix tailTrace_1633120
  have hstable : (prefixWord ++ tailWord_1633120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633120).length < 2 ^ (prefixWord ++ tailWord_1633120).sum := by decide
  have hdescent : baseEnd_1633120 < baseStart_1633120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633186 : List Nat := [3, 3, 1, 2, 2, 2, 3, 1, 5]
def baseStart_1633186 : Nat := 118140960795 + 1633186 * 2 ^ 59
def prefixEnd_1633186 : Nat := 4983230072969 + 3 ^ 40 * 1633186 * 2
def baseEnd_1633186 : Nat := 186357648043100530214249

theorem tailTrace_1633186 : CollatzResearch.WordTrace tailWord_1633186 prefixEnd_1633186 186357648043100530214249 := by
  unfold tailWord_1633186
  simp only [CollatzResearch.WordTrace]
  refine ⟨14891796765313380701869853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39711458040835681871652941 14891796765313380701869853)
  ·
    refine ⟨5584423786992517763201195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14891796765313380701869853 5584423786992517763201195)
    ·
      refine ⟨8376635680488776644801793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5584423786992517763201195 8376635680488776644801793)
      ·
        refine ⟨6282476760366582483601345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8376635680488776644801793 6282476760366582483601345)
        ·
          refine ⟨4711857570274936862701009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6282476760366582483601345 4711857570274936862701009)
          ·
            refine ⟨3533893177706202647025757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4711857570274936862701009 3533893177706202647025757)
            ·
              refine ⟨1325209941639825992634659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3533893177706202647025757 1325209941639825992634659)
              ·
                refine ⟨1987814912459738988951989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1325209941639825992634659 1987814912459738988951989)
                ·
                  refine ⟨186357648043100530214249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1987814912459738988951989 186357648043100530214249)
                  ·
                    rfl

theorem cell22_1633186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_1633186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633186 prefixEnd_1633186 := by exact prefixLift 1633186
  have htrace : WordTrace (prefixWord ++ tailWord_1633186) baseStart_1633186 baseEnd_1633186 := by
    simpa [prefixWord, tailWord_1633186, baseEnd_1633186] using wordTrace_append hprefix tailTrace_1633186
  have hstable : (prefixWord ++ tailWord_1633186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633186).length < 2 ^ (prefixWord ++ tailWord_1633186).sum := by decide
  have hdescent : baseEnd_1633186 < baseStart_1633186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633227 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 4, 4]
def baseStart_1633227 : Nat := 118140960795 + 1633227 * 2 ^ 59
def prefixEnd_1633227 : Nat := 4983230072969 + 3 ^ 40 * 1633227 * 2
def baseEnd_1633227 : Nat := 559086979267191150367621

theorem tailTrace_1633227 : CollatzResearch.WordTrace tailWord_1633227 prefixEnd_1633227 559086979267191150367621 := by
  unfold tailWord_1633227
  simp only [CollatzResearch.WordTrace]
  refine ⟨59568682454104986809721935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39712454969403324539814623 59568682454104986809721935)
  ·
    refine ⟨89353023681157480214582903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59568682454104986809721935 89353023681157480214582903)
    ·
      refine ⟨134029535521736220321874355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89353023681157480214582903 134029535521736220321874355)
      ·
        refine ⟨201044303282604330482811533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134029535521736220321874355 201044303282604330482811533)
        ·
          refine ⟨75391613730976623931054325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201044303282604330482811533 75391613730976623931054325)
          ·
            refine ⟨7067963787279058493536343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75391613730976623931054325 7067963787279058493536343)
            ·
              refine ⟨10601945680918587740304515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7067963787279058493536343 10601945680918587740304515)
              ·
                refine ⟨15902918521377881610456773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10601945680918587740304515 15902918521377881610456773)
                ·
                  refine ⟨2981797222758352801960645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15902918521377881610456773 2981797222758352801960645)
                  ·
                    refine ⟨559086979267191150367621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2981797222758352801960645 559086979267191150367621)
                    ·
                      rfl

theorem cell22_1633227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 4].length) (baseStart_1633227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633227 prefixEnd_1633227 := by exact prefixLift 1633227
  have htrace : WordTrace (prefixWord ++ tailWord_1633227) baseStart_1633227 baseEnd_1633227 := by
    simpa [prefixWord, tailWord_1633227, baseEnd_1633227] using wordTrace_append hprefix tailTrace_1633227
  have hstable : (prefixWord ++ tailWord_1633227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633227).length < 2 ^ (prefixWord ++ tailWord_1633227).sum := by decide
  have hdescent : baseEnd_1633227 < baseStart_1633227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633231 : List Nat := [1, 1, 2, 1, 1, 7, 3, 2, 4]
def baseStart_1633231 : Nat := 118140960795 + 1633231 * 2 ^ 59
def prefixEnd_1633231 : Nat := 4983230072969 + 3 ^ 40 * 1633231 * 2
def baseEnd_1633231 : Nat := 186362782849645491089203

theorem tailTrace_1633231 : CollatzResearch.WordTrace tailWord_1633231 prefixEnd_1633231 186362782849645491089203 := by
  unfold tailWord_1633231
  simp only [CollatzResearch.WordTrace]
  refine ⟨59568828346090495492867547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39712552230726996995245031 59568828346090495492867547)
  ·
    refine ⟨89353242519135743239301321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59568828346090495492867547 89353242519135743239301321)
    ·
      refine ⟨67014931889351807429475991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89353242519135743239301321 67014931889351807429475991)
      ·
        refine ⟨100522397834027711144213987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67014931889351807429475991 100522397834027711144213987)
        ·
          refine ⟨150783596751041566716320981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100522397834027711144213987 150783596751041566716320981)
          ·
            refine ⟨3533990548852536719913773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 150783596751041566716320981 3533990548852536719913773)
            ·
              refine ⟨1325246455819701269967665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3533990548852536719913773 1325246455819701269967665)
              ·
                refine ⟨993934841864775952475749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1325246455819701269967665 993934841864775952475749)
                ·
                  refine ⟨186362782849645491089203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 993934841864775952475749 186362782849645491089203)
                  ·
                    rfl

theorem cell22_1633231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 4].length) (baseStart_1633231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633231 prefixEnd_1633231 := by exact prefixLift 1633231
  have htrace : WordTrace (prefixWord ++ tailWord_1633231) baseStart_1633231 baseEnd_1633231 := by
    simpa [prefixWord, tailWord_1633231, baseEnd_1633231] using wordTrace_append hprefix tailTrace_1633231
  have hstable : (prefixWord ++ tailWord_1633231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633231).length < 2 ^ (prefixWord ++ tailWord_1633231).sum := by decide
  have hdescent : baseEnd_1633231 < baseStart_1633231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633242 : List Nat := [3, 1, 1, 2, 4, 1, 1, 9]
def baseStart_1633242 : Nat := 118140960795 + 1633242 * 2 ^ 59
def prefixEnd_1633242 : Nat := 4983230072969 + 3 ^ 40 * 1633242 * 2
def baseEnd_1633242 : Nat := 62121346008192901249175

theorem tailTrace_1633242 : CollatzResearch.WordTrace tailWord_1633242 prefixEnd_1633242 62121346008192901249175 := by
  unfold tailWord_1633242
  simp only [CollatzResearch.WordTrace]
  refine ⟨14892307387262661092879495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39712819699367096247678653 14892307387262661092879495)
  ·
    refine ⟨22338461080893991639319243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14892307387262661092879495 22338461080893991639319243)
    ·
      refine ⟨33507691621340987458978865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22338461080893991639319243 33507691621340987458978865)
      ·
        refine ⟨25130768716005740594234149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33507691621340987458978865 25130768716005740594234149)
        ·
          refine ⟨4712019134251076361418903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25130768716005740594234149 4712019134251076361418903)
          ·
            refine ⟨7068028701376614542128355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4712019134251076361418903 7068028701376614542128355)
            ·
              refine ⟨10602043052064921813192533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7068028701376614542128355 10602043052064921813192533)
              ·
                refine ⟨62121346008192901249175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10602043052064921813192533 62121346008192901249175)
                ·
                  rfl

theorem cell22_1633242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 9].length) (baseStart_1633242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633242 prefixEnd_1633242 := by exact prefixLift 1633242
  have htrace : WordTrace (prefixWord ++ tailWord_1633242) baseStart_1633242 baseEnd_1633242 := by
    simpa [prefixWord, tailWord_1633242, baseEnd_1633242] using wordTrace_append hprefix tailTrace_1633242
  have hstable : (prefixWord ++ tailWord_1633242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633242).length < 2 ^ (prefixWord ++ tailWord_1633242).sum := by decide
  have hdescent : baseEnd_1633242 < baseStart_1633242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633282 : List Nat := [3, 4, 1, 3, 1, 2, 2, 2, 4]
def baseStart_1633282 : Nat := 118140960795 + 1633282 * 2 ^ 59
def prefixEnd_1633282 : Nat := 4983230072969 + 3 ^ 40 * 1633282 * 2
def baseEnd_1633282 : Nat := 186368602297063113414151

theorem tailTrace_1633282 : CollatzResearch.WordTrace tailWord_1633282 prefixEnd_1633282 186368602297063113414151 := by
  unfold tailWord_1633282
  simp only [CollatzResearch.WordTrace]
  refine ⟨14892672117226432800743525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39713792312603820801982733 14892672117226432800743525)
  ·
    refine ⟨2792376021979956150139411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14892672117226432800743525 2792376021979956150139411)
    ·
      refine ⟨4188564032969934225209117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2792376021979956150139411 4188564032969934225209117)
      ·
        refine ⟨1570711512363725334453419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4188564032969934225209117 1570711512363725334453419)
        ·
          refine ⟨2356067268545588001680129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1570711512363725334453419 2356067268545588001680129)
          ·
            refine ⟨1767050451409191001260097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2356067268545588001680129 1767050451409191001260097)
            ·
              refine ⟨1325287838556893250945073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1767050451409191001260097 1325287838556893250945073)
              ·
                refine ⟨993965878917669938208805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1325287838556893250945073 993965878917669938208805)
                ·
                  refine ⟨186368602297063113414151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 993965878917669938208805 186368602297063113414151)
                  ·
                    rfl

theorem cell22_1633282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_1633282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633282 prefixEnd_1633282 := by exact prefixLift 1633282
  have htrace : WordTrace (prefixWord ++ tailWord_1633282) baseStart_1633282 baseEnd_1633282 := by
    simpa [prefixWord, tailWord_1633282, baseEnd_1633282] using wordTrace_append hprefix tailTrace_1633282
  have hstable : (prefixWord ++ tailWord_1633282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633282).length < 2 ^ (prefixWord ++ tailWord_1633282).sum := by decide
  have hdescent : baseEnd_1633282 < baseStart_1633282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633304 : List Nat := [2, 1, 2, 3, 2, 2, 2, 3, 5]
def baseStart_1633304 : Nat := 118140960795 + 1633304 * 2 ^ 59
def prefixEnd_1633304 : Nat := 4983230072969 + 3 ^ 40 * 1633304 * 2
def baseEnd_1633304 : Nat := 186371112646929538730795

theorem tailTrace_1633304 : CollatzResearch.WordTrace tailWord_1633304 prefixEnd_1633304 186371112646929538730795 := by
  unfold tailWord_1633304
  simp only [CollatzResearch.WordTrace]
  refine ⟨29785745437413014480137483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39714327249884019306849977 29785745437413014480137483)
  ·
    refine ⟨44678618156119521720206225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29785745437413014480137483 44678618156119521720206225)
    ·
      refine ⟨33508963617089641290154669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44678618156119521720206225 33508963617089641290154669)
      ·
        refine ⟨12565861356408615483808001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33508963617089641290154669 12565861356408615483808001)
        ·
          refine ⟨9424396017306461612856001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12565861356408615483808001 9424396017306461612856001)
          ·
            refine ⟨7068297012979846209642001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9424396017306461612856001 7068297012979846209642001)
            ·
              refine ⟨5301222759734884657231501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7068297012979846209642001 5301222759734884657231501)
              ·
                refine ⟨1987958534900581746461813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5301222759734884657231501 1987958534900581746461813)
                ·
                  refine ⟨186371112646929538730795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1987958534900581746461813 186371112646929538730795)
                  ·
                    rfl

theorem cell22_1633304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 5].length) (baseStart_1633304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633304 prefixEnd_1633304 := by exact prefixLift 1633304
  have htrace : WordTrace (prefixWord ++ tailWord_1633304) baseStart_1633304 baseEnd_1633304 := by
    simpa [prefixWord, tailWord_1633304, baseEnd_1633304] using wordTrace_append hprefix tailTrace_1633304
  have hstable : (prefixWord ++ tailWord_1633304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633304).length < 2 ^ (prefixWord ++ tailWord_1633304).sum := by decide
  have hdescent : baseEnd_1633304 < baseStart_1633304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633379 : List Nat := [1, 1, 1, 5, 1, 1, 1, 5, 2, 4]
def baseStart_1633379 : Nat := 118140960795 + 1633379 * 2 ^ 59
def prefixEnd_1633379 : Nat := 4983230072969 + 3 ^ 40 * 1633379 * 2
def baseEnd_1633379 : Nat := 559139011973513420567155

theorem tailTrace_1633379 : CollatzResearch.WordTrace tailWord_1633379 prefixEnd_1633379 559139011973513420567155 := by
  unfold tailWord_1633379
  simp only [CollatzResearch.WordTrace]
  refine ⟨59574226349554316769255191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39716150899702877846170127 59574226349554316769255191)
  ·
    refine ⟨89361339524331475153882787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59574226349554316769255191 89361339524331475153882787)
    ·
      refine ⟨134042009286497212730824181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89361339524331475153882787 134042009286497212730824181)
      ·
        refine ⟨12566438370609113693514767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134042009286497212730824181 12566438370609113693514767)
        ·
          refine ⟨18849657555913670540272151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12566438370609113693514767 18849657555913670540272151)
          ·
            refine ⟨28274486333870505810408227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18849657555913670540272151 28274486333870505810408227)
            ·
              refine ⟨42411729500805758715612341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28274486333870505810408227 42411729500805758715612341)
              ·
                refine ⟨3976099640700539879588657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42411729500805758715612341 3976099640700539879588657)
                ·
                  refine ⟨2982074730525404909691493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3976099640700539879588657 2982074730525404909691493)
                  ·
                    refine ⟨559139011973513420567155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2982074730525404909691493 559139011973513420567155)
                    ·
                      rfl

theorem cell22_1633379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 4].length) (baseStart_1633379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633379 prefixEnd_1633379 := by exact prefixLift 1633379
  have htrace : WordTrace (prefixWord ++ tailWord_1633379) baseStart_1633379 baseEnd_1633379 := by
    simpa [prefixWord, tailWord_1633379, baseEnd_1633379] using wordTrace_append hprefix tailTrace_1633379
  have hstable : (prefixWord ++ tailWord_1633379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633379).length < 2 ^ (prefixWord ++ tailWord_1633379).sum := by decide
  have hdescent : baseEnd_1633379 < baseStart_1633379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633383 : List Nat := [1, 1, 5, 1, 1, 5, 1, 3, 4]
def baseStart_1633383 : Nat := 118140960795 + 1633383 * 2 ^ 59
def prefixEnd_1633383 : Nat := 4983230072969 + 3 ^ 40 * 1633383 * 2
def baseEnd_1633383 : Nat := 186380127085086247822381

theorem tailTrace_1633383 : CollatzResearch.WordTrace tailWord_1633383 prefixEnd_1633383 186380127085086247822381 := by
  unfold tailWord_1633383
  simp only [CollatzResearch.WordTrace]
  refine ⟨59574372241539825452400803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39716248161026550301600535 59574372241539825452400803)
  ·
    refine ⟨89361558362309738178601205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59574372241539825452400803 89361558362309738178601205)
    ·
      refine ⟨8377646096466537954243863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89361558362309738178601205 8377646096466537954243863)
      ·
        refine ⟨12566469144699806931365795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8377646096466537954243863 12566469144699806931365795)
        ·
          refine ⟨18849703717049710397048693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12566469144699806931365795 18849703717049710397048693)
          ·
            refine ⟨1767159723473410349723315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18849703717049710397048693 1767159723473410349723315)
            ·
              refine ⟨2650739585210115524584973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1767159723473410349723315 2650739585210115524584973)
              ·
                refine ⟨994027344453793321719365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2650739585210115524584973 994027344453793321719365)
                ·
                  refine ⟨186380127085086247822381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 994027344453793321719365 186380127085086247822381)
                  ·
                    rfl

theorem cell22_1633383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 4].length) (baseStart_1633383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633383 prefixEnd_1633383 := by exact prefixLift 1633383
  have htrace : WordTrace (prefixWord ++ tailWord_1633383) baseStart_1633383 baseEnd_1633383 := by
    simpa [prefixWord, tailWord_1633383, baseEnd_1633383] using wordTrace_append hprefix tailTrace_1633383
  have hstable : (prefixWord ++ tailWord_1633383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633383).length < 2 ^ (prefixWord ++ tailWord_1633383).sum := by decide
  have hdescent : baseEnd_1633383 < baseStart_1633383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633398 : List Nat := [5, 1, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_1633398 : Nat := 118140960795 + 1633398 * 2 ^ 59
def prefixEnd_1633398 : Nat := 4983230072969 + 3 ^ 40 * 1633398 * 2
def baseEnd_1633398 : Nat := 559145516061803704342097

theorem tailTrace_1633398 : CollatzResearch.WordTrace tailWord_1633398 prefixEnd_1633398 559145516061803704342097 := by
  unfold tailWord_1633398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3723432458530342688387303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39716612890990322009464565 3723432458530342688387303)
  ·
    refine ⟨5585148687795514032580955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3723432458530342688387303 5585148687795514032580955)
    ·
      refine ⟨8377723031693271048871433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5585148687795514032580955 8377723031693271048871433)
      ·
        refine ⟨6283292273769953286653575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8377723031693271048871433 6283292273769953286653575)
        ·
          refine ⟨9424938410654929929980363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6283292273769953286653575 9424938410654929929980363)
          ·
            refine ⟨14137407615982394894970545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9424938410654929929980363 14137407615982394894970545)
            ·
              refine ⟨10603055711986796171227909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14137407615982394894970545 10603055711986796171227909)
              ·
                refine ⟨1988072945997524282105233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10603055711986796171227909 1988072945997524282105233)
                ·
                  refine ⟨1491054709498143211578925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1988072945997524282105233 1491054709498143211578925)
                  ·
                    refine ⟨559145516061803704342097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1491054709498143211578925 559145516061803704342097)
                    ·
                      rfl

theorem cell22_1633398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_1633398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633398 prefixEnd_1633398 := by exact prefixLift 1633398
  have htrace : WordTrace (prefixWord ++ tailWord_1633398) baseStart_1633398 baseEnd_1633398 := by
    simpa [prefixWord, tailWord_1633398, baseEnd_1633398] using wordTrace_append hprefix tailTrace_1633398
  have hstable : (prefixWord ++ tailWord_1633398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633398).length < 2 ^ (prefixWord ++ tailWord_1633398).sum := by decide
  have hdescent : baseEnd_1633398 < baseStart_1633398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633462 : List Nat := [5, 1, 3, 2, 2, 1, 1, 7]
def baseStart_1633462 : Nat := 118140960795 + 1633462 * 2 ^ 59
def prefixEnd_1633462 : Nat := 4983230072969 + 3 ^ 40 * 1633462 * 2
def baseEnd_1633462 : Nat := 62129713841080985637989

theorem tailTrace_1633462 : CollatzResearch.WordTrace tailWord_1633462 prefixEnd_1633462 62129713841080985637989 := by
  unfold tailWord_1633462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3723578350515851371532915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39718169072169081296351093 3723578350515851371532915)
  ·
    refine ⟨5585367525773777057299373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3723578350515851371532915 5585367525773777057299373)
    ·
      refine ⟨2094512822165166396487265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5585367525773777057299373 2094512822165166396487265)
      ·
        refine ⟨1570884616623874797365449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2094512822165166396487265 1570884616623874797365449)
        ·
          refine ⟨1178163462467906098024087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1570884616623874797365449 1178163462467906098024087)
          ·
            refine ⟨1767245193701859147036131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1178163462467906098024087 1767245193701859147036131)
            ·
              refine ⟨2650867790552788720554197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1767245193701859147036131 2650867790552788720554197)
              ·
                refine ⟨62129713841080985637989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2650867790552788720554197 62129713841080985637989)
                ·
                  rfl

theorem cell22_1633462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_1633462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633462 prefixEnd_1633462 := by exact prefixLift 1633462
  have htrace : WordTrace (prefixWord ++ tailWord_1633462) baseStart_1633462 baseEnd_1633462 := by
    simpa [prefixWord, tailWord_1633462, baseEnd_1633462] using wordTrace_append hprefix tailTrace_1633462
  have hstable : (prefixWord ++ tailWord_1633462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633462).length < 2 ^ (prefixWord ++ tailWord_1633462).sum := by decide
  have hdescent : baseEnd_1633462 < baseStart_1633462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633473 : List Nat := [1, 2, 6, 1, 1, 1, 2, 3, 5]
def baseStart_1633473 : Nat := 118140960795 + 1633473 * 2 ^ 59
def prefixEnd_1633473 : Nat := 4983230072969 + 3 ^ 40 * 1633473 * 2
def baseEnd_1633473 : Nat := 186390396698176169572289

theorem tailTrace_1633473 : CollatzResearch.WordTrace tailWord_1633473 prefixEnd_1633473 186390396698176169572289 := by
  unfold tailWord_1633473
  simp only [CollatzResearch.WordTrace]
  refine ⟨59577654811213770823177073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39718436540809180548784715 59577654811213770823177073)
  ·
    refine ⟨44683241108410328117382805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59577654811213770823177073 44683241108410328117382805)
    ·
      refine ⟨2094526926956734130502319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44683241108410328117382805 2094526926956734130502319)
      ·
        refine ⟨3141790390435101195753479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2094526926956734130502319 3141790390435101195753479)
        ·
          refine ⟨4712685585652651793630219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3141790390435101195753479 4712685585652651793630219)
          ·
            refine ⟨7069028378478977690445329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4712685585652651793630219 7069028378478977690445329)
            ·
              refine ⟨5301771283859233267833997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7069028378478977690445329 5301771283859233267833997)
              ·
                refine ⟨1988164231447212475437749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5301771283859233267833997 1988164231447212475437749)
                ·
                  refine ⟨186390396698176169572289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1988164231447212475437749 186390396698176169572289)
                  ·
                    rfl

theorem cell22_1633473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 5].length) (baseStart_1633473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633473 prefixEnd_1633473 := by exact prefixLift 1633473
  have htrace : WordTrace (prefixWord ++ tailWord_1633473) baseStart_1633473 baseEnd_1633473 := by
    simpa [prefixWord, tailWord_1633473, baseEnd_1633473] using wordTrace_append hprefix tailTrace_1633473
  have hstable : (prefixWord ++ tailWord_1633473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633473).length < 2 ^ (prefixWord ++ tailWord_1633473).sum := by decide
  have hdescent : baseEnd_1633473 < baseStart_1633473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633494 : List Nat := [5, 2, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_1633494 : Nat := 118140960795 + 1633494 * 2 ^ 59
def prefixEnd_1633494 : Nat := 4983230072969 + 3 ^ 40 * 1633494 * 2
def baseEnd_1633494 : Nat := 559178378823691453941803

theorem tailTrace_1633494 : CollatzResearch.WordTrace tailWord_1633494 prefixEnd_1633494 559178378823691453941803 := by
  unfold tailWord_1633494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3723651296508605713105721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39718947162758460939794357 3723651296508605713105721)
  ·
    refine ⟨2792738472381454284829291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3723651296508605713105721 2792738472381454284829291)
    ·
      refine ⟨4189107708572181427243937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2792738472381454284829291 4189107708572181427243937)
      ·
        refine ⟨3141830781429136070432953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4189107708572181427243937 3141830781429136070432953)
        ·
          refine ⟨2356373086071852052824715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3141830781429136070432953 2356373086071852052824715)
          ·
            refine ⟨3534559629107778079237073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2356373086071852052824715 3534559629107778079237073)
            ·
              refine ⟨2650919721830833559427805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3534559629107778079237073 2650919721830833559427805)
              ·
                refine ⟨994094895686562584785427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2650919721830833559427805 994094895686562584785427)
                ·
                  refine ⟨1491142343529843877178141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 994094895686562584785427 1491142343529843877178141)
                  ·
                    refine ⟨559178378823691453941803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1491142343529843877178141 559178378823691453941803)
                    ·
                      rfl

theorem cell22_1633494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_1633494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633494 prefixEnd_1633494 := by exact prefixLift 1633494
  have htrace : WordTrace (prefixWord ++ tailWord_1633494) baseStart_1633494 baseEnd_1633494 := by
    simpa [prefixWord, tailWord_1633494, baseEnd_1633494] using wordTrace_append hprefix tailTrace_1633494
  have hstable : (prefixWord ++ tailWord_1633494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633494).length < 2 ^ (prefixWord ++ tailWord_1633494).sum := by decide
  have hdescent : baseEnd_1633494 < baseStart_1633494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633503 : List Nat := [1, 1, 2, 3, 2, 1, 6, 1, 1, 4]
def baseStart_1633503 : Nat := 118140960795 + 1633503 * 2 ^ 59
def prefixEnd_1633503 : Nat := 4983230072969 + 3 ^ 40 * 1633503 * 2
def baseEnd_1633503 : Nat := 559181459707618430466775

theorem tailTrace_1633503 : CollatzResearch.WordTrace tailWord_1633503 prefixEnd_1633503 559181459707618430466775 := by
  unfold tailWord_1633503
  simp only [CollatzResearch.WordTrace]
  refine ⟨59578749001105085946769163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39719166000736723964512775 59578749001105085946769163)
  ·
    refine ⟨89368123501657628920153745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59578749001105085946769163 89368123501657628920153745)
    ·
      refine ⟨67026092626243221690115309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89368123501657628920153745 67026092626243221690115309)
      ·
        refine ⟨25134784734841208133793241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67026092626243221690115309 25134784734841208133793241)
        ·
          refine ⟨18851088551130906100344931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25134784734841208133793241 18851088551130906100344931)
          ·
            refine ⟨28276632826696359150517397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18851088551130906100344931 28276632826696359150517397)
            ·
              refine ⟨1325467163751391835180503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28276632826696359150517397 1325467163751391835180503)
              ·
                refine ⟨1988200745627087752770755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1325467163751391835180503 1988200745627087752770755)
                ·
                  refine ⟨2982301118440631629156133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988200745627087752770755 2982301118440631629156133)
                  ·
                    refine ⟨559181459707618430466775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2982301118440631629156133 559181459707618430466775)
                    ·
                      rfl

theorem cell22_1633503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 1, 4].length) (baseStart_1633503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633503 prefixEnd_1633503 := by exact prefixLift 1633503
  have htrace : WordTrace (prefixWord ++ tailWord_1633503) baseStart_1633503 baseEnd_1633503 := by
    simpa [prefixWord, tailWord_1633503, baseEnd_1633503] using wordTrace_append hprefix tailTrace_1633503
  have hstable : (prefixWord ++ tailWord_1633503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633503).length < 2 ^ (prefixWord ++ tailWord_1633503).sum := by decide
  have hdescent : baseEnd_1633503 < baseStart_1633503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633518 : List Nat := [4, 1, 2, 1, 1, 1, 4, 4, 4]
def baseStart_1633518 : Nat := 118140960795 + 1633518 * 2 ^ 59
def prefixEnd_1633518 : Nat := 4983230072969 + 3 ^ 40 * 1633518 * 2
def baseEnd_1633518 : Nat := 186395531504721130447243

theorem tailTrace_1633518 : CollatzResearch.WordTrace tailWord_1633518 prefixEnd_1633518 186395531504721130447243 := by
  unfold tailWord_1633518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7447412012006342938570651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39719530730700495672376805 7447412012006342938570651)
  ·
    refine ⟨11171118018009514407855977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7447412012006342938570651 11171118018009514407855977)
    ·
      refine ⟨8378338513507135805891983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11171118018009514407855977 8378338513507135805891983)
      ·
        refine ⟨12567507770260703708837975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8378338513507135805891983 12567507770260703708837975)
        ·
          refine ⟨18851261655391055563256963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12567507770260703708837975 18851261655391055563256963)
          ·
            refine ⟨28276892483086583344885445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18851261655391055563256963 28276892483086583344885445)
            ·
              refine ⟨5301917340578734377166021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28276892483086583344885445 5301917340578734377166021)
              ·
                refine ⟨994109501358512695718629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5301917340578734377166021 994109501358512695718629)
                ·
                  refine ⟨186395531504721130447243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 994109501358512695718629 186395531504721130447243)
                  ·
                    rfl

theorem cell22_1633518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_1633518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633518 prefixEnd_1633518 := by exact prefixLift 1633518
  have htrace : WordTrace (prefixWord ++ tailWord_1633518) baseStart_1633518 baseEnd_1633518 := by
    simpa [prefixWord, tailWord_1633518, baseEnd_1633518] using wordTrace_append hprefix tailTrace_1633518
  have hstable : (prefixWord ++ tailWord_1633518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633518).length < 2 ^ (prefixWord ++ tailWord_1633518).sum := by decide
  have hdescent : baseEnd_1633518 < baseStart_1633518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633524 : List Nat := [2, 6, 1, 2, 1, 1, 3, 1, 5]
def baseStart_1633524 : Nat := 118140960795 + 1633524 * 2 ^ 59
def prefixEnd_1633524 : Nat := 4983230072969 + 3 ^ 40 * 1633524 * 2
def baseEnd_1633524 : Nat := 186396216145593791897237

theorem tailTrace_1633524 : CollatzResearch.WordTrace tailWord_1633524 prefixEnd_1633524 186396216145593791897237 := by
  unfold tailWord_1633524
  simp only [CollatzResearch.WordTrace]
  refine ⟨29789757467014503266641813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39719676622686004355522417 29789757467014503266641813)
  ·
    refine ⟨1396394881266304840623835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29789757467014503266641813 1396394881266304840623835)
    ·
      refine ⟨2094592321899457260935753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1396394881266304840623835 2094592321899457260935753)
      ·
        refine ⟨1570944241424592945701815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2094592321899457260935753 1570944241424592945701815)
        ·
          refine ⟨2356416362136889418552723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1570944241424592945701815 2356416362136889418552723)
          ·
            refine ⟨3534624543205334127829085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2356416362136889418552723 3534624543205334127829085)
            ·
              refine ⟨1325484203702000297935907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3534624543205334127829085 1325484203702000297935907)
              ·
                refine ⟨1988226305553000446903861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1325484203702000297935907 1988226305553000446903861)
                ·
                  refine ⟨186396216145593791897237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1988226305553000446903861 186396216145593791897237)
                  ·
                    rfl

theorem cell22_1633524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_1633524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633524 prefixEnd_1633524 := by exact prefixLift 1633524
  have htrace : WordTrace (prefixWord ++ tailWord_1633524) baseStart_1633524 baseEnd_1633524 := by
    simpa [prefixWord, tailWord_1633524, baseEnd_1633524] using wordTrace_append hprefix tailTrace_1633524
  have hstable : (prefixWord ++ tailWord_1633524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633524).length < 2 ^ (prefixWord ++ tailWord_1633524).sum := by decide
  have hdescent : baseEnd_1633524 < baseStart_1633524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633529 : List Nat := [1, 2, 1, 3, 1, 1, 4, 9]
def baseStart_1633529 : Nat := 118140960795 + 1633529 * 2 ^ 59
def prefixEnd_1633529 : Nat := 4983230072969 + 3 ^ 40 * 1633529 * 2
def baseEnd_1633529 : Nat := 62132262226551447701855

theorem tailTrace_1633529 : CollatzResearch.WordTrace tailWord_1633529 prefixEnd_1633529 62132262226551447701855 := by
  unfold tailWord_1633529
  simp only [CollatzResearch.WordTrace]
  refine ⟨59579697299010892387215641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39719798199340594924810427 59579697299010892387215641)
  ·
    refine ⟨44684772974258169290411731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59579697299010892387215641 44684772974258169290411731)
    ·
      refine ⟨67027159461387253935617597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44684772974258169290411731 67027159461387253935617597)
      ·
        refine ⟨25135184798020220225856599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67027159461387253935617597 25135184798020220225856599)
        ·
          refine ⟨37702777197030330338784899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25135184798020220225856599 37702777197030330338784899)
          ·
            refine ⟨56554165795545495508177349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37702777197030330338784899 56554165795545495508177349)
            ·
              refine ⟨10603906086664780407783253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56554165795545495508177349 10603906086664780407783253)
              ·
                refine ⟨62132262226551447701855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10603906086664780407783253 62132262226551447701855)
                ·
                  rfl

theorem cell22_1633529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 9].length) (baseStart_1633529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633529 prefixEnd_1633529 := by exact prefixLift 1633529
  have htrace : WordTrace (prefixWord ++ tailWord_1633529) baseStart_1633529 baseEnd_1633529 := by
    simpa [prefixWord, tailWord_1633529, baseEnd_1633529] using wordTrace_append hprefix tailTrace_1633529
  have hstable : (prefixWord ++ tailWord_1633529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633529).length < 2 ^ (prefixWord ++ tailWord_1633529).sum := by decide
  have hdescent : baseEnd_1633529 < baseStart_1633529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633668 : List Nat := [2, 3, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_1633668 : Nat := 118140960795 + 1633668 * 2 ^ 59
def prefixEnd_1633668 : Nat := 4983230072969 + 3 ^ 40 * 1633668 * 2
def baseEnd_1633668 : Nat := 559237942579613000091269

theorem tailTrace_1633668 : CollatzResearch.WordTrace tailWord_1633668 prefixEnd_1633668 559237942579613000091269 := by
  unfold tailWord_1633668
  simp only [CollatzResearch.WordTrace]
  refine ⟨29792383522753659563262829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39723178030338212751017105 29792383522753659563262829)
  ·
    refine ⟨11172143821032622336223561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29792383522753659563262829 11172143821032622336223561)
    ·
      refine ⟨8379107865774466752167671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11172143821032622336223561 8379107865774466752167671)
      ·
        refine ⟨12568661798661700128251507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8379107865774466752167671 12568661798661700128251507)
        ·
          refine ⟨18852992697992550192377261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12568661798661700128251507 18852992697992550192377261)
          ·
            refine ⟨7069872261747206322141473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18852992697992550192377261 7069872261747206322141473)
            ·
              refine ⟨5302404196310404741606105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7069872261747206322141473 5302404196310404741606105)
              ·
                refine ⟨3976803147232803556204579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5302404196310404741606105 3976803147232803556204579)
                ·
                  refine ⟨5965204720849205334306869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3976803147232803556204579 5965204720849205334306869)
                  ·
                    refine ⟨559237942579613000091269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5965204720849205334306869 559237942579613000091269)
                    ·
                      rfl

theorem cell22_1633668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_1633668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633668 prefixEnd_1633668 := by exact prefixLift 1633668
  have htrace : WordTrace (prefixWord ++ tailWord_1633668) baseStart_1633668 baseEnd_1633668 := by
    simpa [prefixWord, tailWord_1633668, baseEnd_1633668] using wordTrace_append hprefix tailTrace_1633668
  have hstable : (prefixWord ++ tailWord_1633668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633668).length < 2 ^ (prefixWord ++ tailWord_1633668).sum := by decide
  have hdescent : baseEnd_1633668 < baseStart_1633668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633672 : List Nat := [2, 1, 3, 3, 1, 4, 2, 1, 1, 4]
def baseStart_1633672 : Nat := 118140960795 + 1633672 * 2 ^ 59
def prefixEnd_1633672 : Nat := 4983230072969 + 3 ^ 40 * 1633672 * 2
def baseEnd_1633672 : Nat := 559239311861358322991257

theorem tailTrace_1633672 : CollatzResearch.WordTrace tailWord_1633672 prefixEnd_1633672 559239311861358322991257 := by
  unfold tailWord_1633672
  simp only [CollatzResearch.WordTrace]
  refine ⟨29792456468746413904835635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39723275291661885206447513 29792456468746413904835635)
  ·
    refine ⟨44688684703119620857253453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29792456468746413904835635 44688684703119620857253453)
    ·
      refine ⟨16758256763669857821470045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44688684703119620857253453 16758256763669857821470045)
      ·
        refine ⟨6284346286376196683051267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16758256763669857821470045 6284346286376196683051267)
        ·
          refine ⟨9426519429564295024576901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6284346286376196683051267 9426519429564295024576901)
          ·
            refine ⟨1767472393043305317108169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9426519429564295024576901 1767472393043305317108169)
            ·
              refine ⟨1325604294782478987831127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1767472393043305317108169 1325604294782478987831127)
              ·
                refine ⟨1988406442173718481746691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1325604294782478987831127 1988406442173718481746691)
                ·
                  refine ⟨2982609663260577722620037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988406442173718481746691 2982609663260577722620037)
                  ·
                    refine ⟨559239311861358322991257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2982609663260577722620037 559239311861358322991257)
                    ·
                      rfl

theorem cell22_1633672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_1633672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633672 prefixEnd_1633672 := by exact prefixLift 1633672
  have htrace : WordTrace (prefixWord ++ tailWord_1633672) baseStart_1633672 baseEnd_1633672 := by
    simpa [prefixWord, tailWord_1633672, baseEnd_1633672] using wordTrace_append hprefix tailTrace_1633672
  have hstable : (prefixWord ++ tailWord_1633672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633672).length < 2 ^ (prefixWord ++ tailWord_1633672).sum := by decide
  have hdescent : baseEnd_1633672 < baseStart_1633672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633685 : List Nat := [1, 3, 2, 1, 1, 2, 5, 2, 2, 3]
def baseStart_1633685 : Nat := 118140960795 + 1633685 * 2 ^ 59
def prefixEnd_1633685 : Nat := 4983230072969 + 3 ^ 40 * 1633685 * 2
def baseEnd_1633685 : Nat := 559243762027030622416217

theorem tailTrace_1633685 : CollatzResearch.WordTrace tailWord_1633685 prefixEnd_1633685 559243762027030622416217 := by
  unfold tailWord_1633685
  simp only [CollatzResearch.WordTrace]
  refine ⟨59585387086445731029894509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39723591390963820686596339 59585387086445731029894509)
  ·
    refine ⟨22344520157417149136210441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59585387086445731029894509 22344520157417149136210441)
    ·
      refine ⟨16758390118062861852157831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22344520157417149136210441 16758390118062861852157831)
      ·
        refine ⟨25137585177094292778236747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16758390118062861852157831 25137585177094292778236747)
        ·
          refine ⟨37706377765641439167355121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25137585177094292778236747 37706377765641439167355121)
          ·
            refine ⟨28279783324231079375516341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37706377765641439167355121 28279783324231079375516341)
            ·
              refine ⟨2651229686646663691454657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28279783324231079375516341 2651229686646663691454657)
              ·
                refine ⟨1988422264984997768590993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2651229686646663691454657 1988422264984997768590993)
                ·
                  refine ⟨1491316698738748326443245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1988422264984997768590993 1491316698738748326443245)
                  ·
                    refine ⟨559243762027030622416217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1491316698738748326443245 559243762027030622416217)
                    ·
                      rfl

theorem cell22_1633685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_1633685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633685 prefixEnd_1633685 := by exact prefixLift 1633685
  have htrace : WordTrace (prefixWord ++ tailWord_1633685) baseStart_1633685 baseEnd_1633685 := by
    simpa [prefixWord, tailWord_1633685, baseEnd_1633685] using wordTrace_append hprefix tailTrace_1633685
  have hstable : (prefixWord ++ tailWord_1633685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633685).length < 2 ^ (prefixWord ++ tailWord_1633685).sum := by decide
  have hdescent : baseEnd_1633685 < baseStart_1633685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633711 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 2, 6]
def baseStart_1633711 : Nat := 118140960795 + 1633711 * 2 ^ 59
def prefixEnd_1633711 : Nat := 4983230072969 + 3 ^ 40 * 1633711 * 2
def baseEnd_1633711 : Nat := 559252662358375221266137

theorem tailTrace_1633711 : CollatzResearch.WordTrace tailWord_1633711 prefixEnd_1633711 559252662358375221266137 := by
  unfold tailWord_1633711
  simp only [CollatzResearch.WordTrace]
  refine ⟨59586335384351537470340987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39724223589567691646893991 59586335384351537470340987)
  ·
    refine ⟨89379503076527306205511481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59586335384351537470340987 89379503076527306205511481)
    ·
      refine ⟨67034627307395479654133611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89379503076527306205511481 67034627307395479654133611)
      ·
        refine ⟨100551940961093219481200417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67034627307395479654133611 100551940961093219481200417)
        ·
          refine ⟨75413955720819914610900313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100551940961093219481200417 75413955720819914610900313)
          ·
            refine ⟨56560466790614935958175235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75413955720819914610900313 56560466790614935958175235)
            ·
              refine ⟨84840700185922403937262853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56560466790614935958175235 84840700185922403937262853)
              ·
                refine ⟨15907631284860450738236785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84840700185922403937262853 15907631284860450738236785)
                ·
                  refine ⟨11930723463645338053677589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15907631284860450738236785 11930723463645338053677589)
                  ·
                    refine ⟨559252662358375221266137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11930723463645338053677589 559252662358375221266137)
                    ·
                      rfl

theorem cell22_1633711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_1633711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633711 prefixEnd_1633711 := by exact prefixLift 1633711
  have htrace : WordTrace (prefixWord ++ tailWord_1633711) baseStart_1633711 baseEnd_1633711 := by
    simpa [prefixWord, tailWord_1633711, baseEnd_1633711] using wordTrace_append hprefix tailTrace_1633711
  have hstable : (prefixWord ++ tailWord_1633711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633711).length < 2 ^ (prefixWord ++ tailWord_1633711).sum := by decide
  have hdescent : baseEnd_1633711 < baseStart_1633711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633818 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 1, 6]
def baseStart_1633818 : Nat := 118140960795 + 1633818 * 2 ^ 59
def prefixEnd_1633818 : Nat := 4983230072969 + 3 ^ 40 * 1633818 * 2
def baseEnd_1633818 : Nat := 559289290645062608840809

theorem tailTrace_1633818 : CollatzResearch.WordTrace tailWord_1633818 prefixEnd_1633818 559289290645062608840809 := by
  unfold tailWord_1633818
  simp only [CollatzResearch.WordTrace]
  refine ⟨14897559498740973686121527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39726825329975929829657405 14897559498740973686121527)
  ·
    refine ⟨22346339248111460529182291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14897559498740973686121527 22346339248111460529182291)
    ·
      refine ⟨33519508872167190793773437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22346339248111460529182291 33519508872167190793773437)
      ·
        refine ⟨12569815827062696547665039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33519508872167190793773437 12569815827062696547665039)
        ·
          refine ⟨18854723740594044821497559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12569815827062696547665039 18854723740594044821497559)
          ·
            refine ⟨28282085610891067232246339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18854723740594044821497559 28282085610891067232246339)
            ·
              refine ⟨42423128416336600848369509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28282085610891067232246339 42423128416336600848369509)
              ·
                refine ⟨7954336578063112659069283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42423128416336600848369509 7954336578063112659069283)
                ·
                  refine ⟨11931504867094668988603925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7954336578063112659069283 11931504867094668988603925)
                  ·
                    refine ⟨559289290645062608840809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11931504867094668988603925 559289290645062608840809)
                    ·
                      rfl

theorem cell22_1633818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_1633818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633818 prefixEnd_1633818 := by exact prefixLift 1633818
  have htrace : WordTrace (prefixWord ++ tailWord_1633818) baseStart_1633818 baseEnd_1633818 := by
    simpa [prefixWord, tailWord_1633818, baseEnd_1633818] using wordTrace_append hprefix tailTrace_1633818
  have hstable : (prefixWord ++ tailWord_1633818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633818).length < 2 ^ (prefixWord ++ tailWord_1633818).sum := by decide
  have hdescent : baseEnd_1633818 < baseStart_1633818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633820 : List Nat := [2, 2, 3, 1, 2, 1, 4, 1, 1, 5]
def baseStart_1633820 : Nat := 118140960795 + 1633820 * 2 ^ 59
def prefixEnd_1633820 : Nat := 4983230072969 + 3 ^ 40 * 1633820 * 2
def baseEnd_1633820 : Nat := 559289975285935270290803

theorem tailTrace_1633820 : CollatzResearch.WordTrace tailWord_1633820 prefixEnd_1633820 559289975285935270290803 := by
  unfold tailWord_1633820
  simp only [CollatzResearch.WordTrace]
  refine ⟨29795155470478324543029457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39726873960637766057372609 29795155470478324543029457)
  ·
    refine ⟨22346366602858743407272093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29795155470478324543029457 22346366602858743407272093)
    ·
      refine ⟨8379887476072028777727035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22346366602858743407272093 8379887476072028777727035)
      ·
        refine ⟨12569831214108043166590553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8379887476072028777727035 12569831214108043166590553)
        ·
          refine ⟨9427373410581032374942915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12569831214108043166590553 9427373410581032374942915)
          ·
            refine ⟨14141060115871548562414373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9427373410581032374942915 14141060115871548562414373)
            ·
              refine ⟨2651448771725915355452695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14141060115871548562414373 2651448771725915355452695)
              ·
                refine ⟨3977173157588873033179043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2651448771725915355452695 3977173157588873033179043)
                ·
                  refine ⟨5965759736383309549768565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3977173157588873033179043 5965759736383309549768565)
                  ·
                    refine ⟨559289975285935270290803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5965759736383309549768565 559289975285935270290803)
                    ·
                      rfl

theorem cell22_1633820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_1633820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633820 prefixEnd_1633820 := by exact prefixLift 1633820
  have htrace : WordTrace (prefixWord ++ tailWord_1633820) baseStart_1633820 baseEnd_1633820 := by
    simpa [prefixWord, tailWord_1633820, baseEnd_1633820] using wordTrace_append hprefix tailTrace_1633820
  have hstable : (prefixWord ++ tailWord_1633820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633820).length < 2 ^ (prefixWord ++ tailWord_1633820).sum := by decide
  have hdescent : baseEnd_1633820 < baseStart_1633820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633925 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 3, 4]
def baseStart_1633925 : Nat := 118140960795 + 1633925 * 2 ^ 59
def prefixEnd_1633925 : Nat := 4983230072969 + 3 ^ 40 * 1633925 * 2
def baseEnd_1633925 : Nat := 559325918931749996415481

theorem tailTrace_1633925 : CollatzResearch.WordTrace tailWord_1633925 prefixEnd_1633925 559325918931749996415481 := by
  unfold tailWord_1633925
  simp only [CollatzResearch.WordTrace]
  refine ⟨59594140605576252018631229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39729427070384168012420819 59594140605576252018631229)
  ·
    refine ⟨22347802727091094506986711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59594140605576252018631229 22347802727091094506986711)
    ·
      refine ⟨33521704090636641760480067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22347802727091094506986711 33521704090636641760480067)
      ·
        refine ⟨50282556135954962640720101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33521704090636641760480067 50282556135954962640720101)
        ·
          refine ⟨9427979275491555495135019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50282556135954962640720101 9427979275491555495135019)
          ·
            refine ⟨14141968913237333242702529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9427979275491555495135019 14141968913237333242702529)
            ·
              refine ⟨10606476684927999932026897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14141968913237333242702529 10606476684927999932026897)
              ·
                refine ⟨7954857513695999949020173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10606476684927999932026897 7954857513695999949020173)
                ·
                  refine ⟨2983071567635999980882565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7954857513695999949020173 2983071567635999980882565)
                  ·
                    refine ⟨559325918931749996415481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2983071567635999980882565 559325918931749996415481)
                    ·
                      rfl

theorem cell22_1633925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_1633925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633925 prefixEnd_1633925 := by exact prefixLift 1633925
  have htrace : WordTrace (prefixWord ++ tailWord_1633925) baseStart_1633925 baseEnd_1633925 := by
    simpa [prefixWord, tailWord_1633925, baseEnd_1633925] using wordTrace_append hprefix tailTrace_1633925
  have hstable : (prefixWord ++ tailWord_1633925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633925).length < 2 ^ (prefixWord ++ tailWord_1633925).sum := by decide
  have hdescent : baseEnd_1633925 < baseStart_1633925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633955 : List Nat := [1, 1, 1, 4, 1, 1, 5, 2, 1, 5]
def baseStart_1633955 : Nat := 118140960795 + 1633955 * 2 ^ 59
def prefixEnd_1633955 : Nat := 4983230072969 + 3 ^ 40 * 1633955 * 2
def baseEnd_1633955 : Nat := 559336188544839918165389

theorem tailTrace_1633955 : CollatzResearch.WordTrace tailWord_1633955 prefixEnd_1633955 559336188544839918165389 := by
  unfold tailWord_1633955
  simp only [CollatzResearch.WordTrace]
  refine ⟨59595234795467567142223319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39730156530311711428148879 59595234795467567142223319)
  ·
    refine ⟨89392852193201350713334979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59595234795467567142223319 89392852193201350713334979)
    ·
      refine ⟨134089278289802026070002469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89392852193201350713334979 134089278289802026070002469)
      ·
        refine ⟨25141739679337879888125463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134089278289802026070002469 25141739679337879888125463)
        ·
          refine ⟨37712609519006819832188195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25141739679337879888125463 37712609519006819832188195)
          ·
            refine ⟨56568914278510229748282293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37712609519006819832188195 56568914278510229748282293)
            ·
              refine ⟨5303335713610334038901465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56568914278510229748282293 5303335713610334038901465)
              ·
                refine ⟨3977501785207750529176099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5303335713610334038901465 3977501785207750529176099)
                ·
                  refine ⟨5966252677811625793764149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3977501785207750529176099 5966252677811625793764149)
                  ·
                    refine ⟨559336188544839918165389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5966252677811625793764149 559336188544839918165389)
                    ·
                      rfl

theorem cell22_1633955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 5].length) (baseStart_1633955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1633955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1633955 prefixEnd_1633955 := by exact prefixLift 1633955
  have htrace : WordTrace (prefixWord ++ tailWord_1633955) baseStart_1633955 baseEnd_1633955 := by
    simpa [prefixWord, tailWord_1633955, baseEnd_1633955] using wordTrace_append hprefix tailTrace_1633955
  have hstable : (prefixWord ++ tailWord_1633955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633955).length < 2 ^ (prefixWord ++ tailWord_1633955).sum := by decide
  have hdescent : baseEnd_1633955 < baseStart_1633955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634004 : List Nat := [2, 4, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_1634004 : Nat := 118140960795 + 1634004 * 2 ^ 59
def prefixEnd_1634004 : Nat := 4983230072969 + 3 ^ 40 * 1634004 * 2
def baseEnd_1634004 : Nat := 559352962246220123690239

theorem tailTrace_1634004 : CollatzResearch.WordTrace tailWord_1634004 prefixEnd_1634004 559352962246220123690239 := by
  unfold tailWord_1634004
  simp only [CollatzResearch.WordTrace]
  refine ⟨29798510986145024255378533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39731347981526699007171377 29798510986145024255378533)
  ·
    refine ⟨5587220809902192047883475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29798510986145024255378533 5587220809902192047883475)
    ·
      refine ⟨8380831214853288071825213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5587220809902192047883475 8380831214853288071825213)
      ·
        refine ⟨3142811705569983026934455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8380831214853288071825213 3142811705569983026934455)
        ·
          refine ⟨4714217558354974540401683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3142811705569983026934455 4714217558354974540401683)
          ·
            refine ⟨7071326337532461810602525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4714217558354974540401683 7071326337532461810602525)
            ·
              refine ⟨2651747376574673178975947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7071326337532461810602525 2651747376574673178975947)
              ·
                refine ⟨3977621064862009768463921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2651747376574673178975947 3977621064862009768463921)
                ·
                  refine ⟨2983215798646507326347941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3977621064862009768463921 2983215798646507326347941)
                  ·
                    refine ⟨559352962246220123690239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2983215798646507326347941 559352962246220123690239)
                    ·
                      rfl

theorem cell22_1634004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_1634004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634004 prefixEnd_1634004 := by exact prefixLift 1634004
  have htrace : WordTrace (prefixWord ++ tailWord_1634004) baseStart_1634004 baseEnd_1634004 := by
    simpa [prefixWord, tailWord_1634004, baseEnd_1634004] using wordTrace_append hprefix tailTrace_1634004
  have hstable : (prefixWord ++ tailWord_1634004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634004).length < 2 ^ (prefixWord ++ tailWord_1634004).sum := by decide
  have hdescent : baseEnd_1634004 < baseStart_1634004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634023 : List Nat := [1, 1, 5, 4, 1, 2, 1, 2, 2, 3]
def baseStart_1634023 : Nat := 118140960795 + 1634023 * 2 ^ 59
def prefixEnd_1634023 : Nat := 4983230072969 + 3 ^ 40 * 1634023 * 2
def baseEnd_1634023 : Nat := 559359466334510407465181

theorem tailTrace_1634023 : CollatzResearch.WordTrace tailWord_1634023 prefixEnd_1634023 559359466334510407465181 := by
  unfold tailWord_1634023
  simp only [CollatzResearch.WordTrace]
  refine ⟨59597714959221214755698723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39731809972814143170465815 59597714959221214755698723)
  ·
    refine ⟨89396572438831822133548085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59597714959221214755698723 89396572438831822133548085)
    ·
      refine ⟨8380928666140483325020133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89396572438831822133548085 8380928666140483325020133)
      ·
        refine ⟨1571424124901340623441275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8380928666140483325020133 1571424124901340623441275)
        ·
          refine ⟨2357136187352010935161913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1571424124901340623441275 2357136187352010935161913)
          ·
            refine ⟨1767852140514008201371435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2357136187352010935161913 1767852140514008201371435)
            ·
              refine ⟨2651778210771012302057153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1767852140514008201371435 2651778210771012302057153)
              ·
                refine ⟨1988833658078259226542865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2651778210771012302057153 1988833658078259226542865)
                ·
                  refine ⟨1491625243558694419907149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1988833658078259226542865 1491625243558694419907149)
                  ·
                    refine ⟨559359466334510407465181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1491625243558694419907149 559359466334510407465181)
                    ·
                      rfl

theorem cell22_1634023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_1634023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634023 prefixEnd_1634023 := by exact prefixLift 1634023
  have htrace : WordTrace (prefixWord ++ tailWord_1634023) baseStart_1634023 baseEnd_1634023 := by
    simpa [prefixWord, tailWord_1634023, baseEnd_1634023] using wordTrace_append hprefix tailTrace_1634023
  have hstable : (prefixWord ++ tailWord_1634023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634023).length < 2 ^ (prefixWord ++ tailWord_1634023).sum := by decide
  have hdescent : baseEnd_1634023 < baseStart_1634023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634034 : List Nat := [3, 2, 1, 3, 1, 1, 4, 1, 3, 3]
def baseStart_1634034 : Nat := 118140960795 + 1634034 * 2 ^ 59
def prefixEnd_1634034 : Nat := 4983230072969 + 3 ^ 40 * 1634034 * 2
def baseEnd_1634034 : Nat := 559363231859310045440147

theorem tailTrace_1634034 : CollatzResearch.WordTrace tailWord_1634034 prefixEnd_1634034 559363231859310045440147 := by
  unfold tailWord_1634034
  simp only [CollatzResearch.WordTrace]
  refine ⟨14899529040545340908587289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39732077441454242422899437 14899529040545340908587289)
  ·
    refine ⟨11174646780409005681440467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14899529040545340908587289 11174646780409005681440467)
    ·
      refine ⟨16761970170613508522160701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11174646780409005681440467 16761970170613508522160701)
      ·
        refine ⟨6285738813980065695810263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16761970170613508522160701 6285738813980065695810263)
        ·
          refine ⟨9428608220970098543715395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6285738813980065695810263 9428608220970098543715395)
          ·
            refine ⟨14142912331455147815573093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9428608220970098543715395 14142912331455147815573093)
            ·
              refine ⟨2651796062147840215419955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14142912331455147815573093 2651796062147840215419955)
              ·
                refine ⟨3977694093221760323129933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2651796062147840215419955 3977694093221760323129933)
                ·
                  refine ⟨1491635284958160121173725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3977694093221760323129933 1491635284958160121173725)
                  ·
                    refine ⟨559363231859310045440147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1491635284958160121173725 559363231859310045440147)
                    ·
                      rfl

theorem cell22_1634034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_1634034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634034 prefixEnd_1634034 := by exact prefixLift 1634034
  have htrace : WordTrace (prefixWord ++ tailWord_1634034) baseStart_1634034 baseEnd_1634034 := by
    simpa [prefixWord, tailWord_1634034, baseEnd_1634034] using wordTrace_append hprefix tailTrace_1634034
  have hstable : (prefixWord ++ tailWord_1634034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634034).length < 2 ^ (prefixWord ++ tailWord_1634034).sum := by decide
  have hdescent : baseEnd_1634034 < baseStart_1634034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634045 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_1634045 : Nat := 118140960795 + 1634045 * 2 ^ 59
def prefixEnd_1634045 : Nat := 4983230072969 + 3 ^ 40 * 1634045 * 2
def baseEnd_1634045 : Nat := 559366997384109683415113

theorem tailTrace_1634045 : CollatzResearch.WordTrace tailWord_1634045 prefixEnd_1634045 559366997384109683415113 := by
  unfold tailWord_1634045
  simp only [CollatzResearch.WordTrace]
  refine ⟨59598517365141512512999589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39732344910094341675333059 59598517365141512512999589)
  ·
    refine ⟨11174722005964033596187423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59598517365141512512999589 11174722005964033596187423)
    ·
      refine ⟨16762083008946050394281135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11174722005964033596187423 16762083008946050394281135)
      ·
        refine ⟨25143124513419075591421703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16762083008946050394281135 25143124513419075591421703)
        ·
          refine ⟨37714686770128613387132555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25143124513419075591421703 37714686770128613387132555)
          ·
            refine ⟨56572030155192920080698833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37714686770128613387132555 56572030155192920080698833)
            ·
              refine ⟨42429022616394690060524125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56572030155192920080698833 42429022616394690060524125)
              ·
                refine ⟨15910883481148008772696547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42429022616394690060524125 15910883481148008772696547)
                ·
                  refine ⟨23866325221722013159044821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15910883481148008772696547 23866325221722013159044821)
                  ·
                    refine ⟨559366997384109683415113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23866325221722013159044821 559366997384109683415113)
                    ·
                      rfl

theorem cell22_1634045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_1634045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634045 prefixEnd_1634045 := by exact prefixLift 1634045
  have htrace : WordTrace (prefixWord ++ tailWord_1634045) baseStart_1634045 baseEnd_1634045 := by
    simpa [prefixWord, tailWord_1634045, baseEnd_1634045] using wordTrace_append hprefix tailTrace_1634045
  have hstable : (prefixWord ++ tailWord_1634045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634045).length < 2 ^ (prefixWord ++ tailWord_1634045).sum := by decide
  have hdescent : baseEnd_1634045 < baseStart_1634045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634092 : List Nat := [2, 2, 1, 1, 1, 5, 3, 1, 6]
def baseStart_1634092 : Nat := 118140960795 + 1634092 * 2 ^ 59
def prefixEnd_1634092 : Nat := 4983230072969 + 3 ^ 40 * 1634092 * 2
def baseEnd_1634092 : Nat := 186461028814872409163323

theorem tailTrace_1634092 : CollatzResearch.WordTrace tailWord_1634092 prefixEnd_1634092 186461028814872409163323 := by
  unfold tailWord_1634092
  simp only [CollatzResearch.WordTrace]
  refine ⟨29800115797985619769980265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39733487730647493026640353 29800115797985619769980265)
  ·
    refine ⟨22350086848489214827485199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29800115797985619769980265 22350086848489214827485199)
    ·
      refine ⟨33525130272733822241227799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22350086848489214827485199 33525130272733822241227799)
      ·
        refine ⟨50287695409100733361841699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33525130272733822241227799 50287695409100733361841699)
        ·
          refine ⟨75431543113651100042762549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50287695409100733361841699 75431543113651100042762549)
          ·
            refine ⟨7071707166904790629008989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75431543113651100042762549 7071707166904790629008989)
            ·
              refine ⟨2651890187589296485878371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7071707166904790629008989 2651890187589296485878371)
              ·
                refine ⟨3977835281383944728817557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2651890187589296485878371 3977835281383944728817557)
                ·
                  refine ⟨186461028814872409163323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3977835281383944728817557 186461028814872409163323)
                  ·
                    rfl

theorem cell22_1634092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_1634092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634092 prefixEnd_1634092 := by exact prefixLift 1634092
  have htrace : WordTrace (prefixWord ++ tailWord_1634092) baseStart_1634092 baseEnd_1634092 := by
    simpa [prefixWord, tailWord_1634092, baseEnd_1634092] using wordTrace_append hprefix tailTrace_1634092
  have hstable : (prefixWord ++ tailWord_1634092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634092).length < 2 ^ (prefixWord ++ tailWord_1634092).sum := by decide
  have hdescent : baseEnd_1634092 < baseStart_1634092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634111 : List Nat := [1, 1, 2, 2, 6, 2, 1, 2, 1, 4]
def baseStart_1634111 : Nat := 118140960795 + 1634111 * 2 ^ 59
def prefixEnd_1634111 : Nat := 4983230072969 + 3 ^ 40 * 1634111 * 2
def baseEnd_1634111 : Nat := 559389590532907511264911

theorem tailTrace_1634111 : CollatzResearch.WordTrace tailWord_1634111 prefixEnd_1634111 559389590532907511264911 := by
  unfold tailWord_1634111
  simp only [CollatzResearch.WordTrace]
  refine ⟨59600924582902405784902187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39733949721934937189934791 59600924582902405784902187)
  ·
    refine ⟨89401386874353608677353281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59600924582902405784902187 89401386874353608677353281)
    ·
      refine ⟨67051040155765206508014961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89401386874353608677353281 67051040155765206508014961)
      ·
        refine ⟨50288280116823904881011221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67051040155765206508014961 50288280116823904881011221)
        ·
          refine ⟨2357263130476120541297401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50288280116823904881011221 2357263130476120541297401)
          ·
            refine ⟨1767947347857090405973051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2357263130476120541297401 1767947347857090405973051)
            ·
              refine ⟨2651921021785635608959577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1767947347857090405973051 2651921021785635608959577)
              ·
                refine ⟨1988940766339226706719683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2651921021785635608959577 1988940766339226706719683)
                ·
                  refine ⟨2983411149508840060079525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988940766339226706719683 2983411149508840060079525)
                  ·
                    refine ⟨559389590532907511264911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2983411149508840060079525 559389590532907511264911)
                    ·
                      rfl

theorem cell22_1634111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 4].length) (baseStart_1634111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634111 prefixEnd_1634111 := by exact prefixLift 1634111
  have htrace : WordTrace (prefixWord ++ tailWord_1634111) baseStart_1634111 baseEnd_1634111 := by
    simpa [prefixWord, tailWord_1634111, baseEnd_1634111] using wordTrace_append hprefix tailTrace_1634111
  have hstable : (prefixWord ++ tailWord_1634111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634111).length < 2 ^ (prefixWord ++ tailWord_1634111).sum := by decide
  have hdescent : baseEnd_1634111 < baseStart_1634111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634124 : List Nat := [2, 2, 1, 3, 4, 1, 1, 2, 1, 5]
def baseStart_1634124 : Nat := 118140960795 + 1634124 * 2 ^ 59
def prefixEnd_1634124 : Nat := 4983230072969 + 3 ^ 40 * 1634124 * 2
def baseEnd_1634124 : Nat := 559394040698579810689871

theorem tailTrace_1634124 : CollatzResearch.WordTrace tailWord_1634124 prefixEnd_1634124 559394040698579810689871 := by
  unfold tailWord_1634124
  simp only [CollatzResearch.WordTrace]
  refine ⟨29800699365927654502562713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39734265821236872670083617 29800699365927654502562713)
  ·
    refine ⟨22350524524445740876922035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29800699365927654502562713 22350524524445740876922035)
    ·
      refine ⟨33525786786668611315383053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22350524524445740876922035 33525786786668611315383053)
      ·
        refine ⟨12572170045000729243268645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33525786786668611315383053 12572170045000729243268645)
        ·
          refine ⟨2357281883437636733112871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12572170045000729243268645 2357281883437636733112871)
          ·
            refine ⟨3535922825156455099669307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2357281883437636733112871 3535922825156455099669307)
            ·
              refine ⟨5303884237734682649503961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3535922825156455099669307 5303884237734682649503961)
              ·
                refine ⟨3977913178301011987127971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5303884237734682649503961 3977913178301011987127971)
                ·
                  refine ⟨5966869767451517980691957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3977913178301011987127971 5966869767451517980691957)
                  ·
                    refine ⟨559394040698579810689871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5966869767451517980691957 559394040698579810689871)
                    ·
                      rfl

theorem cell22_1634124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_1634124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634124 prefixEnd_1634124 := by exact prefixLift 1634124
  have htrace : WordTrace (prefixWord ++ tailWord_1634124) baseStart_1634124 baseEnd_1634124 := by
    simpa [prefixWord, tailWord_1634124, baseEnd_1634124] using wordTrace_append hprefix tailTrace_1634124
  have hstable : (prefixWord ++ tailWord_1634124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634124).length < 2 ^ (prefixWord ++ tailWord_1634124).sum := by decide
  have hdescent : baseEnd_1634124 < baseStart_1634124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634169 : List Nat := [1, 2, 1, 3, 2, 2, 3, 2, 3, 3]
def baseStart_1634169 : Nat := 118140960795 + 1634169 * 2 ^ 59
def prefixEnd_1634169 : Nat := 4983230072969 + 3 ^ 40 * 1634169 * 2
def baseEnd_1634169 : Nat := 559409445118214693314733

theorem tailTrace_1634169 : CollatzResearch.WordTrace tailWord_1634169 prefixEnd_1634169 559409445118214693314733 := by
  unfold tailWord_1634169
  simp only [CollatzResearch.WordTrace]
  refine ⟨59603040016692281690513561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39735360011128187793675707 59603040016692281690513561)
  ·
    refine ⟨44702280012519211267885171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59603040016692281690513561 44702280012519211267885171)
    ·
      refine ⟨67053420018778816901827757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44702280012519211267885171 67053420018778816901827757)
      ·
        refine ⟨25145032507042056338185409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67053420018778816901827757 25145032507042056338185409)
        ·
          refine ⟨18858774380281542253639057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25145032507042056338185409 18858774380281542253639057)
          ·
            refine ⟨14144080785211156690229293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18858774380281542253639057 14144080785211156690229293)
            ·
              refine ⟨5304030294454183758835985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14144080785211156690229293 5304030294454183758835985)
              ·
                refine ⟨3978022720840637819126989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5304030294454183758835985 3978022720840637819126989)
                ·
                  refine ⟨1491758520315239182172621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3978022720840637819126989 1491758520315239182172621)
                  ·
                    refine ⟨559409445118214693314733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1491758520315239182172621 559409445118214693314733)
                    ·
                      rfl

theorem cell22_1634169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 3].length) (baseStart_1634169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634169 prefixEnd_1634169 := by exact prefixLift 1634169
  have htrace : WordTrace (prefixWord ++ tailWord_1634169) baseStart_1634169 baseEnd_1634169 := by
    simpa [prefixWord, tailWord_1634169, baseEnd_1634169] using wordTrace_append hprefix tailTrace_1634169
  have hstable : (prefixWord ++ tailWord_1634169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634169).length < 2 ^ (prefixWord ++ tailWord_1634169).sum := by decide
  have hdescent : baseEnd_1634169 < baseStart_1634169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634197 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 4, 5]
def baseStart_1634197 : Nat := 118140960795 + 1634197 * 2 ^ 59
def prefixEnd_1634197 : Nat := 4983230072969 + 3 ^ 40 * 1634197 * 2
def baseEnd_1634197 : Nat := 559419030090431953614647

theorem tailTrace_1634197 : CollatzResearch.WordTrace tailWord_1634197 prefixEnd_1634197 559419030090431953614647 := by
  unfold tailWord_1634197
  simp only [CollatzResearch.WordTrace]
  refine ⟨59604061260590842472532845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39736040840393894981688563 59604061260590842472532845)
  ·
    refine ⟨22351522972721565927199817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59604061260590842472532845 22351522972721565927199817)
    ·
      refine ⟨16763642229541174445399863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22351522972721565927199817 16763642229541174445399863)
      ·
        refine ⟨25145463344311761668099795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16763642229541174445399863 25145463344311761668099795)
        ·
          refine ⟨37718195016467642502149693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25145463344311761668099795 37718195016467642502149693)
          ·
            refine ⟨14144323131175365938306135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37718195016467642502149693 14144323131175365938306135)
            ·
              refine ⟨21216484696763048907459203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14144323131175365938306135 21216484696763048907459203)
              ·
                refine ⟨31824727045144573361188805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21216484696763048907459203 31824727045144573361188805)
                ·
                  refine ⟨5967136320964607505222901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31824727045144573361188805 5967136320964607505222901)
                  ·
                    refine ⟨559419030090431953614647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5967136320964607505222901 559419030090431953614647)
                    ·
                      rfl

theorem cell22_1634197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_1634197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634197 prefixEnd_1634197 := by exact prefixLift 1634197
  have htrace : WordTrace (prefixWord ++ tailWord_1634197) baseStart_1634197 baseEnd_1634197 := by
    simpa [prefixWord, tailWord_1634197, baseEnd_1634197] using wordTrace_append hprefix tailTrace_1634197
  have hstable : (prefixWord ++ tailWord_1634197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634197).length < 2 ^ (prefixWord ++ tailWord_1634197).sum := by decide
  have hdescent : baseEnd_1634197 < baseStart_1634197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634199 : List Nat := [1, 1, 3, 3, 1, 3, 3, 2, 5]
def baseStart_1634199 : Nat := 118140960795 + 1634199 * 2 ^ 59
def prefixEnd_1634199 : Nat := 4983230072969 + 3 ^ 40 * 1634199 * 2
def baseEnd_1634199 : Nat := 186473238243768205021547

theorem tailTrace_1634199 : CollatzResearch.WordTrace tailWord_1634199 prefixEnd_1634199 186473238243768205021547 := by
  unfold tailWord_1634199
  simp only [CollatzResearch.WordTrace]
  refine ⟨59604134206583596814105651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39736089471055731209403767 59604134206583596814105651)
  ·
    refine ⟨89406201309875395221158477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59604134206583596814105651 89406201309875395221158477)
    ·
      refine ⟨33527325491203273207934429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89406201309875395221158477 33527325491203273207934429)
      ·
        refine ⟨12572747059201227452975411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33527325491203273207934429 12572747059201227452975411)
        ·
          refine ⟨18859120588801841179463117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12572747059201227452975411 18859120588801841179463117)
          ·
            refine ⟨7072170220800690442298669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18859120588801841179463117 7072170220800690442298669)
            ·
              refine ⟨2652063832800258915862001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7072170220800690442298669 2652063832800258915862001)
              ·
                refine ⟨1989047874600194186896501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2652063832800258915862001 1989047874600194186896501)
                ·
                  refine ⟨186473238243768205021547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1989047874600194186896501 186473238243768205021547)
                  ·
                    rfl

theorem cell22_1634199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 5].length) (baseStart_1634199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634199 prefixEnd_1634199 := by exact prefixLift 1634199
  have htrace : WordTrace (prefixWord ++ tailWord_1634199) baseStart_1634199 baseEnd_1634199 := by
    simpa [prefixWord, tailWord_1634199, baseEnd_1634199] using wordTrace_append hprefix tailTrace_1634199
  have hstable : (prefixWord ++ tailWord_1634199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634199).length < 2 ^ (prefixWord ++ tailWord_1634199).sum := by decide
  have hdescent : baseEnd_1634199 < baseStart_1634199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634222 : List Nat := [4, 1, 5, 1, 2, 1, 2, 6]
def baseStart_1634222 : Nat := 118140960795 + 1634222 * 2 ^ 59
def prefixEnd_1634222 : Nat := 4983230072969 + 3 ^ 40 * 1634222 * 2
def baseEnd_1634222 : Nat := 62158620900148913526619

theorem tailTrace_1634222 : CollatzResearch.WordTrace tailWord_1634222 prefixEnd_1634222 62158620900148913526619 := by
  unfold tailWord_1634222
  simp only [CollatzResearch.WordTrace]
  refine ⟨7450621635687533967774115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39736648723666847828128613 7450621635687533967774115)
  ·
    refine ⟨11175932453531300951661173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7450621635687533967774115 11175932453531300951661173)
    ·
      refine ⟨1047743667518559464218235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11175932453531300951661173 1047743667518559464218235)
      ·
        refine ⟨1571615501277839196327353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1047743667518559464218235 1571615501277839196327353)
        ·
          refine ⟨1178711625958379397245515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1571615501277839196327353 1178711625958379397245515)
          ·
            refine ⟨1768067438937569095868273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1178711625958379397245515 1768067438937569095868273)
            ·
              refine ⟨1326050579203176821901205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1768067438937569095868273 1326050579203176821901205)
              ·
                refine ⟨62158620900148913526619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1326050579203176821901205 62158620900148913526619)
                ·
                  rfl

theorem cell22_1634222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_1634222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634222 prefixEnd_1634222 := by exact prefixLift 1634222
  have htrace : WordTrace (prefixWord ++ tailWord_1634222) baseStart_1634222 baseEnd_1634222 := by
    simpa [prefixWord, tailWord_1634222, baseEnd_1634222] using wordTrace_append hprefix tailTrace_1634222
  have hstable : (prefixWord ++ tailWord_1634222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634222).length < 2 ^ (prefixWord ++ tailWord_1634222).sum := by decide
  have hdescent : baseEnd_1634222 < baseStart_1634222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634227 : List Nat := [1, 1, 1, 2, 3, 1, 3, 4, 6]
def baseStart_1634227 : Nat := 118140960795 + 1634227 * 2 ^ 59
def prefixEnd_1634227 : Nat := 4983230072969 + 3 ^ 40 * 1634227 * 2
def baseEnd_1634227 : Nat := 186476433234507291788185

theorem tailTrace_1634227 : CollatzResearch.WordTrace tailWord_1634227 prefixEnd_1634227 186476433234507291788185 := by
  unfold tailWord_1634227
  simp only [CollatzResearch.WordTrace]
  refine ⟨59605155450482157596124935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39736770300321438397416623 59605155450482157596124935)
  ·
    refine ⟨89407733175723236394187403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59605155450482157596124935 89407733175723236394187403)
    ·
      refine ⟨134111599763584854591281105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89407733175723236394187403 134111599763584854591281105)
      ·
        refine ⟨100583699822688640943460829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134111599763584854591281105 100583699822688640943460829)
        ·
          refine ⟨37718887433508240353797811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100583699822688640943460829 37718887433508240353797811)
          ·
            refine ⟨56578331150262360530696717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37718887433508240353797811 56578331150262360530696717)
            ·
              refine ⟨21216874181348385199011269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56578331150262360530696717 21216874181348385199011269)
              ·
                refine ⟨3978163909002822224814613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21216874181348385199011269 3978163909002822224814613)
                ·
                  refine ⟨186476433234507291788185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3978163909002822224814613 186476433234507291788185)
                  ·
                    rfl

theorem cell22_1634227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 6].length) (baseStart_1634227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634227 prefixEnd_1634227 := by exact prefixLift 1634227
  have htrace : WordTrace (prefixWord ++ tailWord_1634227) baseStart_1634227 baseEnd_1634227 := by
    simpa [prefixWord, tailWord_1634227, baseEnd_1634227] using wordTrace_append hprefix tailTrace_1634227
  have hstable : (prefixWord ++ tailWord_1634227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634227).length < 2 ^ (prefixWord ++ tailWord_1634227).sum := by decide
  have hdescent : baseEnd_1634227 < baseStart_1634227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634257 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 3, 6]
def baseStart_1634257 : Nat := 118140960795 + 1634257 * 2 ^ 59
def prefixEnd_1634257 : Nat := 4983230072969 + 3 ^ 40 * 1634257 * 2
def baseEnd_1634257 : Nat := 559439569316611797114463

theorem tailTrace_1634257 : CollatzResearch.WordTrace tailWord_1634257 prefixEnd_1634257 559439569316611797114463 := by
  unfold tailWord_1634257
  simp only [CollatzResearch.WordTrace]
  refine ⟨59606249640373472719717025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39737499760248981813144683 59606249640373472719717025)
  ·
    refine ⟨44704687230280104539787769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59606249640373472719717025 44704687230280104539787769)
    ·
      refine ⟨33528515422710078404840827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44704687230280104539787769 33528515422710078404840827)
      ·
        refine ⟨50292773134065117607261241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33528515422710078404840827 50292773134065117607261241)
        ·
          refine ⟨37719579850548838205445931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50292773134065117607261241 37719579850548838205445931)
          ·
            refine ⟨56579369775823257308168897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37719579850548838205445931 56579369775823257308168897)
            ·
              refine ⟨42434527331867442981126673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56579369775823257308168897 42434527331867442981126673)
              ·
                refine ⟨31825895498900582235845005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42434527331867442981126673 31825895498900582235845005)
                ·
                  refine ⟨11934710812087718338441877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31825895498900582235845005 11934710812087718338441877)
                  ·
                    refine ⟨559439569316611797114463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11934710812087718338441877 559439569316611797114463)
                    ·
                      rfl

theorem cell22_1634257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_1634257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634257 prefixEnd_1634257 := by exact prefixLift 1634257
  have htrace : WordTrace (prefixWord ++ tailWord_1634257) baseStart_1634257 baseEnd_1634257 := by
    simpa [prefixWord, tailWord_1634257, baseEnd_1634257] using wordTrace_append hprefix tailTrace_1634257
  have hstable : (prefixWord ++ tailWord_1634257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634257).length < 2 ^ (prefixWord ++ tailWord_1634257).sum := by decide
  have hdescent : baseEnd_1634257 < baseStart_1634257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634261 : List Nat := [1, 3, 2, 3, 2, 3, 1, 1, 6]
def baseStart_1634261 : Nat := 118140960795 + 1634261 * 2 ^ 59
def prefixEnd_1634261 : Nat := 4983230072969 + 3 ^ 40 * 1634261 * 2
def baseEnd_1634261 : Nat := 186480312866119040004817

theorem tailTrace_1634261 : CollatzResearch.WordTrace tailWord_1634261 prefixEnd_1634261 186480312866119040004817 := by
  unfold tailWord_1634261
  simp only [CollatzResearch.WordTrace]
  refine ⟨59606395532358981402862637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39737597021572654268575091 59606395532358981402862637)
  ·
    refine ⟨22352398324634618026073489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59606395532358981402862637 22352398324634618026073489)
    ·
      refine ⟨16764298743475963519555117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22352398324634618026073489 16764298743475963519555117)
      ·
        refine ⟨6286612028803486319833169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16764298743475963519555117 6286612028803486319833169)
        ·
          refine ⟨4714959021602614739874877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6286612028803486319833169 4714959021602614739874877)
          ·
            refine ⟨1768109633100980527453079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4714959021602614739874877 1768109633100980527453079)
            ·
              refine ⟨2652164449651470791179619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1768109633100980527453079 2652164449651470791179619)
              ·
                refine ⟨3978246674477206186769429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2652164449651470791179619 3978246674477206186769429)
                ·
                  refine ⟨186480312866119040004817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3978246674477206186769429 186480312866119040004817)
                  ·
                    rfl

theorem cell22_1634261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_1634261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634261 prefixEnd_1634261 := by exact prefixLift 1634261
  have htrace : WordTrace (prefixWord ++ tailWord_1634261) baseStart_1634261 baseEnd_1634261 := by
    simpa [prefixWord, tailWord_1634261, baseEnd_1634261] using wordTrace_append hprefix tailTrace_1634261
  have hstable : (prefixWord ++ tailWord_1634261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634261).length < 2 ^ (prefixWord ++ tailWord_1634261).sum := by decide
  have hdescent : baseEnd_1634261 < baseStart_1634261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634276 : List Nat := [2, 3, 1, 1, 1, 1, 5, 3, 2, 3]
def baseStart_1634276 : Nat := 118140960795 + 1634276 * 2 ^ 59
def prefixEnd_1634276 : Nat := 4983230072969 + 3 ^ 40 * 1634276 * 2
def baseEnd_1634276 : Nat := 559446073404902080889405

theorem tailTrace_1634276 : CollatzResearch.WordTrace tailWord_1634276 prefixEnd_1634276 559446073404902080889405 := by
  unfold tailWord_1634276
  simp only [CollatzResearch.WordTrace]
  refine ⟨29803471313652319482329341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39737961751536425976439121 29803471313652319482329341)
  ·
    refine ⟨11176301742619619805873503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29803471313652319482329341 11176301742619619805873503)
    ·
      refine ⟨16764452613929429708810255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11176301742619619805873503 16764452613929429708810255)
      ·
        refine ⟨25146678920894144563215383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16764452613929429708810255 25146678920894144563215383)
        ·
          refine ⟨37720018381341216844823075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25146678920894144563215383 37720018381341216844823075)
          ·
            refine ⟨56580027572011825267234613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37720018381341216844823075 56580027572011825267234613)
            ·
              refine ⟨5304377584876108618803245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56580027572011825267234613 5304377584876108618803245)
              ·
                refine ⟨1989141594328540732051217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5304377584876108618803245 1989141594328540732051217)
                ·
                  refine ⟨1491856195746405549038413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1989141594328540732051217 1491856195746405549038413)
                  ·
                    refine ⟨559446073404902080889405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1491856195746405549038413 559446073404902080889405)
                    ·
                      rfl

theorem cell22_1634276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_1634276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634276 prefixEnd_1634276 := by exact prefixLift 1634276
  have htrace : WordTrace (prefixWord ++ tailWord_1634276) baseStart_1634276 baseEnd_1634276 := by
    simpa [prefixWord, tailWord_1634276, baseEnd_1634276] using wordTrace_append hprefix tailTrace_1634276
  have hstable : (prefixWord ++ tailWord_1634276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634276).length < 2 ^ (prefixWord ++ tailWord_1634276).sum := by decide
  have hdescent : baseEnd_1634276 < baseStart_1634276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634304 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 7, 3]
def baseStart_1634304 : Nat := 118140960795 + 1634304 * 2 ^ 59
def prefixEnd_1634304 : Nat := 4983230072969 + 3 ^ 40 * 1634304 * 2
def baseEnd_1634304 : Nat := 559455658377119341189319

theorem tailTrace_1634304 : CollatzResearch.WordTrace tailWord_1634304 prefixEnd_1634304 559455658377119341189319 := by
  unfold tailWord_1634304
  simp only [CollatzResearch.WordTrace]
  refine ⟨29803981935601599873338983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39738642580802133164451977 29803981935601599873338983)
  ·
    refine ⟨44705972903402399810008475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29803981935601599873338983 44705972903402399810008475)
    ·
      refine ⟨67058959355103599715012713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44705972903402399810008475 67058959355103599715012713)
      ·
        refine ⟨50294219516327699786259535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67058959355103599715012713 50294219516327699786259535)
        ·
          refine ⟨75441329274491549679389303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50294219516327699786259535 75441329274491549679389303)
          ·
            refine ⟨113161993911737324519083955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75441329274491549679389303 113161993911737324519083955)
            ·
              refine ⟨169742990867605986778625933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113161993911737324519083955 169742990867605986778625933)
              ·
                refine ⟨63653621575352245041984725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169742990867605986778625933 63653621575352245041984725)
                ·
                  refine ⟨1491881755672318243171517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 63653621575352245041984725 1491881755672318243171517)
                  ·
                    refine ⟨559455658377119341189319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1491881755672318243171517 559455658377119341189319)
                    ·
                      rfl

theorem cell22_1634304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 7, 3].length) (baseStart_1634304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634304 prefixEnd_1634304 := by exact prefixLift 1634304
  have htrace : WordTrace (prefixWord ++ tailWord_1634304) baseStart_1634304 baseEnd_1634304 := by
    simpa [prefixWord, tailWord_1634304, baseEnd_1634304] using wordTrace_append hprefix tailTrace_1634304
  have hstable : (prefixWord ++ tailWord_1634304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634304).length < 2 ^ (prefixWord ++ tailWord_1634304).sum := by decide
  have hdescent : baseEnd_1634304 < baseStart_1634304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634396 : List Nat := [2, 2, 4, 1, 1, 2, 2, 2, 6]
def baseStart_1634396 : Nat := 118140960795 + 1634396 * 2 ^ 59
def prefixEnd_1634396 : Nat := 4983230072969 + 3 ^ 40 * 1634396 * 2
def baseEnd_1634396 : Nat := 186495717285753922629679

theorem tailTrace_1634396 : CollatzResearch.WordTrace tailWord_1634396 prefixEnd_1634396 186495717285753922629679 := by
  unfold tailWord_1634396
  simp only [CollatzResearch.WordTrace]
  refine ⟨29805659693434949729513521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39740879591246599639351361 29805659693434949729513521)
  ·
    refine ⟨22354244770076212297135141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29805659693434949729513521 22354244770076212297135141)
    ·
      refine ⟨4191420894389289805712839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22354244770076212297135141 4191420894389289805712839)
      ·
        refine ⟨6287131341583934708569259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4191420894389289805712839 6287131341583934708569259)
        ·
          refine ⟨9430697012375902062853889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6287131341583934708569259 9430697012375902062853889)
          ·
            refine ⟨7073022759281926547140417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9430697012375902062853889 7073022759281926547140417)
            ·
              refine ⟨5304767069461444910355313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7073022759281926547140417 5304767069461444910355313)
              ·
                refine ⟨3978575302096083682766485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5304767069461444910355313 3978575302096083682766485)
                ·
                  refine ⟨186495717285753922629679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3978575302096083682766485 186495717285753922629679)
                  ·
                    rfl

theorem cell22_1634396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_1634396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634396 prefixEnd_1634396 := by exact prefixLift 1634396
  have htrace : WordTrace (prefixWord ++ tailWord_1634396) baseStart_1634396 baseEnd_1634396 := by
    simpa [prefixWord, tailWord_1634396, baseEnd_1634396] using wordTrace_append hprefix tailTrace_1634396
  have hstable : (prefixWord ++ tailWord_1634396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634396).length < 2 ^ (prefixWord ++ tailWord_1634396).sum := by decide
  have hdescent : baseEnd_1634396 < baseStart_1634396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634409 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 1, 6]
def baseStart_1634409 : Nat := 118140960795 + 1634409 * 2 ^ 59
def prefixEnd_1634409 : Nat := 4983230072969 + 3 ^ 40 * 1634409 * 2
def baseEnd_1634409 : Nat := 559491602022934067313997

theorem tailTrace_1634409 : CollatzResearch.WordTrace tailWord_1634409 prefixEnd_1634409 559491602022934067313997 := by
  unfold tailWord_1634409
  simp only [CollatzResearch.WordTrace]
  refine ⟨59611793535822802679250281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39741195690548535119500187 59611793535822802679250281)
  ·
    refine ⟨44708845151867102009437711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59611793535822802679250281 44708845151867102009437711)
    ·
      refine ⟨67063267727800653014156567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44708845151867102009437711 67063267727800653014156567)
      ·
        refine ⟨100594901591700979521234851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67063267727800653014156567 100594901591700979521234851)
        ·
          refine ⟨150892352387551469281852277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100594901591700979521234851 150892352387551469281852277)
          ·
            refine ⟨14146158036332950245173651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150892352387551469281852277 14146158036332950245173651)
            ·
              refine ⟨21219237054499425367760477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14146158036332950245173651 21219237054499425367760477)
              ·
                refine ⟨7957213895437284512910179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21219237054499425367760477 7957213895437284512910179)
                ·
                  refine ⟨11935820843155926769365269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7957213895437284512910179 11935820843155926769365269)
                  ·
                    refine ⟨559491602022934067313997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11935820843155926769365269 559491602022934067313997)
                    ·
                      rfl

theorem cell22_1634409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_1634409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634409 prefixEnd_1634409 := by exact prefixLift 1634409
  have htrace : WordTrace (prefixWord ++ tailWord_1634409) baseStart_1634409 baseEnd_1634409 := by
    simpa [prefixWord, tailWord_1634409, baseEnd_1634409] using wordTrace_append hprefix tailTrace_1634409
  have hstable : (prefixWord ++ tailWord_1634409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634409).length < 2 ^ (prefixWord ++ tailWord_1634409).sum := by decide
  have hdescent : baseEnd_1634409 < baseStart_1634409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634561 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 3, 6]
def baseStart_1634561 : Nat := 118140960795 + 1634561 * 2 ^ 59
def prefixEnd_1634561 : Nat := 4983230072969 + 3 ^ 40 * 1634561 * 2
def baseEnd_1634561 : Nat := 559543634729256337513531

theorem tailTrace_1634561 : CollatzResearch.WordTrace tailWord_1634561 prefixEnd_1634561 559543634729256337513531 := by
  unfold tailWord_1634561
  simp only [CollatzResearch.WordTrace]
  refine ⟨59617337431272132638783537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39744891620848088425855691 59617337431272132638783537)
  ·
    refine ⟨44713003073454099479087653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59617337431272132638783537 44713003073454099479087653)
    ·
      refine ⟨8383688076272643652328935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44713003073454099479087653 8383688076272643652328935)
      ·
        refine ⟨12575532114408965478493403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8383688076272643652328935 12575532114408965478493403)
        ·
          refine ⟨18863298171613448217740105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12575532114408965478493403 18863298171613448217740105)
          ·
            refine ⟨14147473628710086163305079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18863298171613448217740105 14147473628710086163305079)
            ·
              refine ⟨21221210443065129244957619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14147473628710086163305079 21221210443065129244957619)
              ·
                refine ⟨31831815664597693867436429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21221210443065129244957619 31831815664597693867436429)
                ·
                  refine ⟨11936930874224135200288661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31831815664597693867436429 11936930874224135200288661)
                  ·
                    refine ⟨559543634729256337513531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11936930874224135200288661 559543634729256337513531)
                    ·
                      rfl

theorem cell22_1634561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_1634561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634561 prefixEnd_1634561 := by exact prefixLift 1634561
  have htrace : WordTrace (prefixWord ++ tailWord_1634561) baseStart_1634561 baseEnd_1634561 := by
    simpa [prefixWord, tailWord_1634561, baseEnd_1634561] using wordTrace_append hprefix tailTrace_1634561
  have hstable : (prefixWord ++ tailWord_1634561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634561).length < 2 ^ (prefixWord ++ tailWord_1634561).sum := by decide
  have hdescent : baseEnd_1634561 < baseStart_1634561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634567 : List Nat := [1, 1, 4, 5, 1, 1, 2, 2, 1, 4]
def baseStart_1634567 : Nat := 118140960795 + 1634567 * 2 ^ 59
def prefixEnd_1634567 : Nat := 4983230072969 + 3 ^ 40 * 1634567 * 2
def baseEnd_1634567 : Nat := 559545688651874321863513

theorem tailTrace_1634567 : CollatzResearch.WordTrace tailWord_1634567 prefixEnd_1634567 559545688651874321863513 := by
  unfold tailWord_1634567
  simp only [CollatzResearch.WordTrace]
  refine ⟨59617556269250395663501955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39745037512833597109001303 59617556269250395663501955)
  ·
    refine ⟨89426334403875593495252933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59617556269250395663501955 89426334403875593495252933)
    ·
      refine ⟨16767437700726673780359925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89426334403875593495252933 16767437700726673780359925)
      ·
        refine ⟨1571947284443125666908743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16767437700726673780359925 1571947284443125666908743)
        ·
          refine ⟨2357920926664688500363115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1571947284443125666908743 2357920926664688500363115)
          ·
            refine ⟨3536881389997032750544673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2357920926664688500363115 3536881389997032750544673)
            ·
              refine ⟨2652661042497774562908505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3536881389997032750544673 2652661042497774562908505)
              ·
                refine ⟨1989495781873330922181379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2652661042497774562908505 1989495781873330922181379)
                ·
                  refine ⟨2984243672809996383272069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1989495781873330922181379 2984243672809996383272069)
                  ·
                    refine ⟨559545688651874321863513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2984243672809996383272069 559545688651874321863513)
                    ·
                      rfl

theorem cell22_1634567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_1634567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634567 prefixEnd_1634567 := by exact prefixLift 1634567
  have htrace : WordTrace (prefixWord ++ tailWord_1634567) baseStart_1634567 baseEnd_1634567 := by
    simpa [prefixWord, tailWord_1634567, baseEnd_1634567] using wordTrace_append hprefix tailTrace_1634567
  have hstable : (prefixWord ++ tailWord_1634567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634567).length < 2 ^ (prefixWord ++ tailWord_1634567).sum := by decide
  have hdescent : baseEnd_1634567 < baseStart_1634567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634599 : List Nat := [1, 1, 8, 1, 1, 2, 1, 1, 6]
def baseStart_1634599 : Nat := 118140960795 + 1634599 * 2 ^ 59
def prefixEnd_1634599 : Nat := 4983230072969 + 3 ^ 40 * 1634599 * 2
def baseEnd_1634599 : Nat := 186518880968612301687805

theorem tailTrace_1634599 : CollatzResearch.WordTrace tailWord_1634599 prefixEnd_1634599 186518880968612301687805 := by
  unfold tailWord_1634599
  simp only [CollatzResearch.WordTrace]
  refine ⟨59618723405134465128666851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39745815603422976752444567 59618723405134465128666851)
  ·
    refine ⟨89428085107701697693000277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59618723405134465128666851 89428085107701697693000277)
    ·
      refine ⟨1047985372355879269839847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 89428085107701697693000277 1047985372355879269839847)
      ·
        refine ⟨1571978058533818904759771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1047985372355879269839847 1571978058533818904759771)
        ·
          refine ⟨2357967087800728357139657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1571978058533818904759771 2357967087800728357139657)
          ·
            refine ⟨1768475315850546267854743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2357967087800728357139657 1768475315850546267854743)
            ·
              refine ⟨2652712973775819401782115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1768475315850546267854743 2652712973775819401782115)
              ·
                refine ⟨3979069460663729102673173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2652712973775819401782115 3979069460663729102673173)
                ·
                  refine ⟨186518880968612301687805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3979069460663729102673173 186518880968612301687805)
                  ·
                    rfl

theorem cell22_1634599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 6].length) (baseStart_1634599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634599 prefixEnd_1634599 := by exact prefixLift 1634599
  have htrace : WordTrace (prefixWord ++ tailWord_1634599) baseStart_1634599 baseEnd_1634599 := by
    simpa [prefixWord, tailWord_1634599, baseEnd_1634599] using wordTrace_append hprefix tailTrace_1634599
  have hstable : (prefixWord ++ tailWord_1634599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634599).length < 2 ^ (prefixWord ++ tailWord_1634599).sum := by decide
  have hdescent : baseEnd_1634599 < baseStart_1634599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634608 : List Nat := [2, 1, 1, 1, 2, 2, 2, 5, 3, 3]
def baseStart_1634608 : Nat := 118140960795 + 1634608 * 2 ^ 59
def prefixEnd_1634608 : Nat := 4983230072969 + 3 ^ 40 * 1634608 * 2
def baseEnd_1634608 : Nat := 559559723789763881588387

theorem tailTrace_1634608 : CollatzResearch.WordTrace tailWord_1634608 prefixEnd_1634608 559559723789763881588387 := by
  unfold tailWord_1634608
  simp only [CollatzResearch.WordTrace]
  refine ⟨29809525831050929832872239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39746034441401239777162985 29809525831050929832872239)
  ·
    refine ⟨44714288746576394749308359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29809525831050929832872239 44714288746576394749308359)
    ·
      refine ⟨67071433119864592123962539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44714288746576394749308359 67071433119864592123962539)
      ·
        refine ⟨100607149679796888185943809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67071433119864592123962539 100607149679796888185943809)
        ·
          refine ⟨75455362259847666139457857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100607149679796888185943809 75455362259847666139457857)
          ·
            refine ⟨56591521694885749604593393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75455362259847666139457857 56591521694885749604593393)
            ·
              refine ⟨42443641271164312203445045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56591521694885749604593393 42443641271164312203445045)
              ·
                refine ⟨3979091369171654269072973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42443641271164312203445045 3979091369171654269072973)
                ·
                  refine ⟨1492159263439370350902365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3979091369171654269072973 1492159263439370350902365)
                  ·
                    refine ⟨559559723789763881588387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1492159263439370350902365 559559723789763881588387)
                    ·
                      rfl

theorem cell22_1634608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 3, 3].length) (baseStart_1634608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634608 prefixEnd_1634608 := by exact prefixLift 1634608
  have htrace : WordTrace (prefixWord ++ tailWord_1634608) baseStart_1634608 baseEnd_1634608 := by
    simpa [prefixWord, tailWord_1634608, baseEnd_1634608] using wordTrace_append hprefix tailTrace_1634608
  have hstable : (prefixWord ++ tailWord_1634608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634608).length < 2 ^ (prefixWord ++ tailWord_1634608).sum := by decide
  have hdescent : baseEnd_1634608 < baseStart_1634608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634683 : List Nat := [1, 1, 1, 1, 1, 8, 1, 2, 6]
def baseStart_1634683 : Nat := 118140960795 + 1634683 * 2 ^ 59
def prefixEnd_1634683 : Nat := 4983230072969 + 3 ^ 40 * 1634683 * 2
def baseEnd_1634683 : Nat := 186528465940829561987719

theorem tailTrace_1634683 : CollatzResearch.WordTrace tailWord_1634683 prefixEnd_1634683 186528465940829561987719 := by
  unfold tailWord_1634683
  simp only [CollatzResearch.WordTrace]
  refine ⟨59621787136830147474724703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39747858091220098316483135 59621787136830147474724703)
  ·
    refine ⟨89432680705245221212087055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59621787136830147474724703 89432680705245221212087055)
    ·
      refine ⟨134149021057867831818130583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89432680705245221212087055 134149021057867831818130583)
      ·
        refine ⟨201223531586801747727195875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134149021057867831818130583 201223531586801747727195875)
        ·
          refine ⟨301835297380202621590793813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201223531586801747727195875 301835297380202621590793813)
          ·
            refine ⟨3537132391174249471767115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 301835297380202621590793813 3537132391174249471767115)
            ·
              refine ⟨5305698586761374207650673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3537132391174249471767115 5305698586761374207650673)
              ·
                refine ⟨3979273940071030655738005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5305698586761374207650673 3979273940071030655738005)
                ·
                  refine ⟨186528465940829561987719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3979273940071030655738005 186528465940829561987719)
                  ·
                    rfl

theorem cell22_1634683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 6].length) (baseStart_1634683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634683 prefixEnd_1634683 := by exact prefixLift 1634683
  have htrace : WordTrace (prefixWord ++ tailWord_1634683) baseStart_1634683 baseEnd_1634683 := by
    simpa [prefixWord, tailWord_1634683, baseEnd_1634683] using wordTrace_append hprefix tailTrace_1634683
  have hstable : (prefixWord ++ tailWord_1634683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634683).length < 2 ^ (prefixWord ++ tailWord_1634683).sum := by decide
  have hdescent : baseEnd_1634683 < baseStart_1634683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634700 : List Nat := [2, 2, 1, 2, 1, 4, 1, 5, 4]
def baseStart_1634700 : Nat := 118140960795 + 1634700 * 2 ^ 59
def prefixEnd_1634700 : Nat := 4983230072969 + 3 ^ 40 * 1634700 * 2
def baseEnd_1634700 : Nat := 186530405756635436096035

theorem tailTrace_1634700 : CollatzResearch.WordTrace tailWord_1634700 prefixEnd_1634700 186530405756635436096035 := by
  unfold tailWord_1634700
  simp only [CollatzResearch.WordTrace]
  refine ⟨29811203588884279689046777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39748271451845706252062369 29811203588884279689046777)
  ·
    refine ⟨22358402691663209766785083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29811203588884279689046777 22358402691663209766785083)
    ·
      refine ⟨33537604037494814650177625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22358402691663209766785083 33537604037494814650177625)
      ·
        refine ⟨25153203028121110987633219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33537604037494814650177625 25153203028121110987633219)
        ·
          refine ⟨37729804542181666481449829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25153203028121110987633219 37729804542181666481449829)
          ·
            refine ⟨7074338351659062465271843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37729804542181666481449829 7074338351659062465271843)
            ·
              refine ⟨10611507527488593697907765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7074338351659062465271843 10611507527488593697907765)
              ·
                refine ⟨994828830702055659178853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10611507527488593697907765 994828830702055659178853)
                ·
                  refine ⟨186530405756635436096035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 994828830702055659178853 186530405756635436096035)
                  ·
                    rfl

theorem cell22_1634700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 4].length) (baseStart_1634700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634700 prefixEnd_1634700 := by exact prefixLift 1634700
  have htrace : WordTrace (prefixWord ++ tailWord_1634700) baseStart_1634700 baseEnd_1634700 := by
    simpa [prefixWord, tailWord_1634700, baseEnd_1634700] using wordTrace_append hprefix tailTrace_1634700
  have hstable : (prefixWord ++ tailWord_1634700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634700).length < 2 ^ (prefixWord ++ tailWord_1634700).sum := by decide
  have hdescent : baseEnd_1634700 < baseStart_1634700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634702 : List Nat := [4, 1, 1, 4, 1, 2, 1, 3, 1, 4]
def baseStart_1634702 : Nat := 118140960795 + 1634702 * 2 ^ 59
def prefixEnd_1634702 : Nat := 4983230072969 + 3 ^ 40 * 1634702 * 2
def baseEnd_1634702 : Nat := 559591901910778969738099

theorem tailTrace_1634702 : CollatzResearch.WordTrace tailWord_1634702 prefixEnd_1634702 559591901910778969738099 := by
  unfold tailWord_1634702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7452810015470164214958295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39748320082507542479777573 7452810015470164214958295)
  ·
    refine ⟨11179215023205246322437443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7452810015470164214958295 11179215023205246322437443)
    ·
      refine ⟨16768822534807869483656165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11179215023205246322437443 16768822534807869483656165)
      ·
        refine ⟨3144154225276475528185531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16768822534807869483656165 3144154225276475528185531)
        ·
          refine ⟨4716231337914713292278297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3144154225276475528185531 4716231337914713292278297)
          ·
            refine ⟨3537173503436034969208723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4716231337914713292278297 3537173503436034969208723)
            ·
              refine ⟨5305760255154052453813085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3537173503436034969208723 5305760255154052453813085)
              ·
                refine ⟨1989660095682769670179907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5305760255154052453813085 1989660095682769670179907)
                ·
                  refine ⟨2984490143524154505269861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1989660095682769670179907 2984490143524154505269861)
                  ·
                    refine ⟨559591901910778969738099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2984490143524154505269861 559591901910778969738099)
                    ·
                      rfl

theorem cell22_1634702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_1634702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634702 prefixEnd_1634702 := by exact prefixLift 1634702
  have htrace : WordTrace (prefixWord ++ tailWord_1634702) baseStart_1634702 baseEnd_1634702 := by
    simpa [prefixWord, tailWord_1634702, baseEnd_1634702] using wordTrace_append hprefix tailTrace_1634702
  have hstable : (prefixWord ++ tailWord_1634702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634702).length < 2 ^ (prefixWord ++ tailWord_1634702).sum := by decide
  have hdescent : baseEnd_1634702 < baseStart_1634702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634713 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 4, 4]
def baseStart_1634713 : Nat := 118140960795 + 1634713 * 2 ^ 59
def prefixEnd_1634713 : Nat := 4983230072969 + 3 ^ 40 * 1634713 * 2
def baseEnd_1634713 : Nat := 559595667435578607713065

theorem tailTrace_1634713 : CollatzResearch.WordTrace tailWord_1634713 prefixEnd_1634713 559595667435578607713065 := by
  unfold tailWord_1634713
  simp only [CollatzResearch.WordTrace]
  refine ⟨59622881326721462598316793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39748587551147641732211195 59622881326721462598316793)
  ·
    refine ⟨44717160995041096948737595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59622881326721462598316793 44717160995041096948737595)
    ·
      refine ⟨67075741492561645423106393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44717160995041096948737595 67075741492561645423106393)
      ·
        refine ⟨50306806119421234067329795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67075741492561645423106393 50306806119421234067329795)
        ·
          refine ⟨75460209179131851100994693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50306806119421234067329795 75460209179131851100994693)
          ·
            refine ⟨14148789221087222081436505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75460209179131851100994693 14148789221087222081436505)
            ·
              refine ⟨10611591915815416561077379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14148789221087222081436505 10611591915815416561077379)
              ·
                refine ⟨15917387873723124841616069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10611591915815416561077379 15917387873723124841616069)
                ·
                  refine ⟨2984510226323085907803013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15917387873723124841616069 2984510226323085907803013)
                  ·
                    refine ⟨559595667435578607713065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2984510226323085907803013 559595667435578607713065)
                    ·
                      rfl

theorem cell22_1634713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 4].length) (baseStart_1634713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634713 prefixEnd_1634713 := by exact prefixLift 1634713
  have htrace : WordTrace (prefixWord ++ tailWord_1634713) baseStart_1634713 baseEnd_1634713 := by
    simpa [prefixWord, tailWord_1634713, baseEnd_1634713] using wordTrace_append hprefix tailTrace_1634713
  have hstable : (prefixWord ++ tailWord_1634713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634713).length < 2 ^ (prefixWord ++ tailWord_1634713).sum := by decide
  have hdescent : baseEnd_1634713 < baseStart_1634713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634745 : List Nat := [1, 2, 1, 4, 3, 1, 4, 6]
def baseStart_1634745 : Nat := 118140960795 + 1634745 * 2 ^ 59
def prefixEnd_1634745 : Nat := 4983230072969 + 3 ^ 40 * 1634745 * 2
def baseEnd_1634745 : Nat := 62178513521060132323663

theorem tailTrace_1634745 : CollatzResearch.WordTrace tailWord_1634745 prefixEnd_1634745 62178513521060132323663 := by
  unfold tailWord_1634745
  simp only [CollatzResearch.WordTrace]
  refine ⟨59624048462605532063481689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39749365641737021375654459 59624048462605532063481689)
  ·
    refine ⟨44718036346954149047611267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59624048462605532063481689 44718036346954149047611267)
    ·
      refine ⟨67077054520431223571416901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44718036346954149047611267 67077054520431223571416901)
      ·
        refine ⟨12576947722580854419640669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67077054520431223571416901 12576947722580854419640669)
        ·
          refine ⟨4716355395967820407365251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12576947722580854419640669 4716355395967820407365251)
          ·
            refine ⟨7074533093951730611047877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4716355395967820407365251 7074533093951730611047877)
            ·
              refine ⟨1326474955115949489571477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7074533093951730611047877 1326474955115949489571477)
              ·
                refine ⟨62178513521060132323663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1326474955115949489571477 62178513521060132323663)
                ·
                  rfl

theorem cell22_1634745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 6].length) (baseStart_1634745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634745 prefixEnd_1634745 := by exact prefixLift 1634745
  have htrace : WordTrace (prefixWord ++ tailWord_1634745) baseStart_1634745 baseEnd_1634745 := by
    simpa [prefixWord, tailWord_1634745, baseEnd_1634745] using wordTrace_append hprefix tailTrace_1634745
  have hstable : (prefixWord ++ tailWord_1634745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634745).length < 2 ^ (prefixWord ++ tailWord_1634745).sum := by decide
  have hdescent : baseEnd_1634745 < baseStart_1634745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634886 : List Nat := [6, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_1634886 : Nat := 118140960795 + 1634886 * 2 ^ 59
def prefixEnd_1634886 : Nat := 4983230072969 + 3 ^ 40 * 1634886 * 2
def baseEnd_1634886 : Nat := 186551629623687941045845

theorem tailTrace_1634886 : CollatzResearch.WordTrace tailWord_1634886 prefixEnd_1634886 186551629623687941045845 := by
  unfold tailWord_1634886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1863412223596709785761391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39752794103396475429576341 1863412223596709785761391)
  ·
    refine ⟨2795118335395064678642087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1863412223596709785761391 2795118335395064678642087)
    ·
      refine ⟨4192677503092597017963131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2795118335395064678642087 4192677503092597017963131)
      ·
        refine ⟨6289016254638895526944697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4192677503092597017963131 6289016254638895526944697)
        ·
          refine ⟨4716762190979171645208523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6289016254638895526944697 4716762190979171645208523)
          ·
            refine ⟨7075143286468757467812785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4716762190979171645208523 7075143286468757467812785)
            ·
              refine ⟨5306357464851568100859589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7075143286468757467812785 5306357464851568100859589)
              ·
                refine ⟨994942024659669018911173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5306357464851568100859589 994942024659669018911173)
                ·
                  refine ⟨186551629623687941045845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 994942024659669018911173 186551629623687941045845)
                  ·
                    rfl

theorem cell22_1634886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_1634886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634886 prefixEnd_1634886 := by exact prefixLift 1634886
  have htrace : WordTrace (prefixWord ++ tailWord_1634886) baseStart_1634886 baseEnd_1634886 := by
    simpa [prefixWord, tailWord_1634886, baseEnd_1634886] using wordTrace_append hprefix tailTrace_1634886
  have hstable : (prefixWord ++ tailWord_1634886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634886).length < 2 ^ (prefixWord ++ tailWord_1634886).sum := by decide
  have hdescent : baseEnd_1634886 < baseStart_1634886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634912 : List Nat := [2, 1, 1, 3, 2, 1, 4, 2, 3, 3]
def baseStart_1634912 : Nat := 118140960795 + 1634912 * 2 ^ 59
def prefixEnd_1634912 : Nat := 4983230072969 + 3 ^ 40 * 1634912 * 2
def baseEnd_1634912 : Nat := 559663789202408421987455

theorem tailTrace_1634912 : CollatzResearch.WordTrace tailWord_1634912 prefixEnd_1634912 559663789202408421987455 := by
  unfold tailWord_1634912
  simp only [CollatzResearch.WordTrace]
  refine ⟨29815069726500259792405495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39753426302000346389873993 29815069726500259792405495)
  ·
    refine ⟨44722604589750389688608243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29815069726500259792405495 44722604589750389688608243)
    ·
      refine ⟨67083906884625584532912365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44722604589750389688608243 67083906884625584532912365)
      ·
        refine ⟨25156465081734594199842137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67083906884625584532912365 25156465081734594199842137)
        ·
          refine ⟨18867348811300945649881603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25156465081734594199842137 18867348811300945649881603)
          ·
            refine ⟨28301023216951418474822405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18867348811300945649881603 28301023216951418474822405)
            ·
              refine ⟨5306441853178390964029201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28301023216951418474822405 5306441853178390964029201)
              ·
                refine ⟨3979831389883793223021901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5306441853178390964029201 3979831389883793223021901)
                ·
                  refine ⟨1492436771206422458633213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3979831389883793223021901 1492436771206422458633213)
                  ·
                    refine ⟨559663789202408421987455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1492436771206422458633213 559663789202408421987455)
                    ·
                      rfl

theorem cell22_1634912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 3, 3].length) (baseStart_1634912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634912 prefixEnd_1634912 := by exact prefixLift 1634912
  have htrace : WordTrace (prefixWord ++ tailWord_1634912) baseStart_1634912 baseEnd_1634912 := by
    simpa [prefixWord, tailWord_1634912, baseEnd_1634912] using wordTrace_append hprefix tailTrace_1634912
  have hstable : (prefixWord ++ tailWord_1634912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634912).length < 2 ^ (prefixWord ++ tailWord_1634912).sum := by decide
  have hdescent : baseEnd_1634912 < baseStart_1634912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634914 : List Nat := [3, 3, 2, 3, 1, 1, 1, 8]
def baseStart_1634914 : Nat := 118140960795 + 1634914 * 2 ^ 59
def prefixEnd_1634914 : Nat := 4983230072969 + 3 ^ 40 * 1634914 * 2
def baseEnd_1634914 : Nat := 62184941538142342604161

theorem tailTrace_1634914 : CollatzResearch.WordTrace tailWord_1634914 prefixEnd_1634914 62184941538142342604161 := by
  unfold tailWord_1634914
  simp only [CollatzResearch.WordTrace]
  refine ⟨14907553099748318481595949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39753474932662182617589197 14907553099748318481595949)
  ·
    refine ⟨5590332412405619430598481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14907553099748318481595949 5590332412405619430598481)
    ·
      refine ⟨4192749309304214572948861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5590332412405619430598481 4192749309304214572948861)
      ·
        refine ⟨1572280990989080464855823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4192749309304214572948861 1572280990989080464855823)
        ·
          refine ⟨2358421486483620697283735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1572280990989080464855823 2358421486483620697283735)
          ·
            refine ⟨3537632229725431045925603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2358421486483620697283735 3537632229725431045925603)
            ·
              refine ⟨5306448344588146568888405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3537632229725431045925603 5306448344588146568888405)
              ·
                refine ⟨62184941538142342604161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5306448344588146568888405 62184941538142342604161)
                ·
                  rfl

theorem cell22_1634914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 8].length) (baseStart_1634914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634914 prefixEnd_1634914 := by exact prefixLift 1634914
  have htrace : WordTrace (prefixWord ++ tailWord_1634914) baseStart_1634914 baseEnd_1634914 := by
    simpa [prefixWord, tailWord_1634914, baseEnd_1634914] using wordTrace_append hprefix tailTrace_1634914
  have hstable : (prefixWord ++ tailWord_1634914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634914).length < 2 ^ (prefixWord ++ tailWord_1634914).sum := by decide
  have hdescent : baseEnd_1634914 < baseStart_1634914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634940 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 4, 5]
def baseStart_1634940 : Nat := 118140960795 + 1634940 * 2 ^ 59
def prefixEnd_1634940 : Nat := 4983230072969 + 3 ^ 40 * 1634940 * 2
def baseEnd_1634940 : Nat := 559673374174625682287369

theorem tailTrace_1634940 : CollatzResearch.WordTrace tailWord_1634940 prefixEnd_1634940 559673374174625682287369 := by
  unfold tailWord_1634940
  simp only [CollatzResearch.WordTrace]
  refine ⟨29815580348449540183415137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39754107131266053577886849 29815580348449540183415137)
  ·
    refine ⟨22361685261337155137561353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29815580348449540183415137 22361685261337155137561353)
    ·
      refine ⟨16771263946002866353171015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22361685261337155137561353 16771263946002866353171015)
      ·
        refine ⟨25156895919004299529756523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16771263946002866353171015 25156895919004299529756523)
        ·
          refine ⟨37735343878506449294634785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25156895919004299529756523 37735343878506449294634785)
          ·
            refine ⟨28301507908879836970976089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37735343878506449294634785 28301507908879836970976089)
            ·
              refine ⟨21226130931659877728232067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28301507908879836970976089 21226130931659877728232067)
              ·
                refine ⟨31839196397489816592348101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21226130931659877728232067 31839196397489816592348101)
                ·
                  refine ⟨5969849324529340611065269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31839196397489816592348101 5969849324529340611065269)
                  ·
                    refine ⟨559673374174625682287369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5969849324529340611065269 559673374174625682287369)
                    ·
                      rfl

theorem cell22_1634940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_1634940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634940 prefixEnd_1634940 := by exact prefixLift 1634940
  have htrace : WordTrace (prefixWord ++ tailWord_1634940) baseStart_1634940 baseEnd_1634940 := by
    simpa [prefixWord, tailWord_1634940, baseEnd_1634940] using wordTrace_append hprefix tailTrace_1634940
  have hstable : (prefixWord ++ tailWord_1634940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634940).length < 2 ^ (prefixWord ++ tailWord_1634940).sum := by decide
  have hdescent : baseEnd_1634940 < baseStart_1634940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1634985 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 3, 5]
def baseStart_1634985 : Nat := 118140960795 + 1634985 * 2 ^ 59
def prefixEnd_1634985 : Nat := 4983230072969 + 3 ^ 40 * 1634985 * 2
def baseEnd_1634985 : Nat := 559688778594260564912231

theorem tailTrace_1634985 : CollatzResearch.WordTrace tailWord_1634985 prefixEnd_1634985 559688778594260564912231 := by
  unfold tailWord_1634985
  simp only [CollatzResearch.WordTrace]
  refine ⟨59632801981736053052218409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39755201321157368701478939 59632801981736053052218409)
  ·
    refine ⟨44724601486302039789163807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59632801981736053052218409 44724601486302039789163807)
    ·
      refine ⟨67086902229453059683745711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44724601486302039789163807 67086902229453059683745711)
      ·
        refine ⟨100630353344179589525618567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67086902229453059683745711 100630353344179589525618567)
        ·
          refine ⟨150945530016269384288427851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100630353344179589525618567 150945530016269384288427851)
          ·
            refine ⟨226418295024404076432641777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150945530016269384288427851 226418295024404076432641777)
            ·
              refine ⟨169813721268303057324481333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226418295024404076432641777 169813721268303057324481333)
              ·
                refine ⟨15920036368903411624170125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169813721268303057324481333 15920036368903411624170125)
                ·
                  refine ⟨5970013638338779359063797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15920036368903411624170125 5970013638338779359063797)
                  ·
                    refine ⟨559688778594260564912231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5970013638338779359063797 559688778594260564912231)
                    ·
                      rfl

theorem cell22_1634985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_1634985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1634985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1634985 prefixEnd_1634985 := by exact prefixLift 1634985
  have htrace : WordTrace (prefixWord ++ tailWord_1634985) baseStart_1634985 baseEnd_1634985 := by
    simpa [prefixWord, tailWord_1634985, baseEnd_1634985] using wordTrace_append hprefix tailTrace_1634985
  have hstable : (prefixWord ++ tailWord_1634985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1634985).length < 2 ^ (prefixWord ++ tailWord_1634985).sum := by decide
  have hdescent : baseEnd_1634985 < baseStart_1634985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1634985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635000 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 5, 6]
def baseStart_1635000 : Nat := 118140960795 + 1635000 * 2 ^ 59
def prefixEnd_1635000 : Nat := 4983230072969 + 3 ^ 40 * 1635000 * 2
def baseEnd_1635000 : Nat := 559693913400805525787185

theorem tailTrace_1635000 : CollatzResearch.WordTrace tailWord_1635000 prefixEnd_1635000 559693913400805525787185 := by
  unfold tailWord_1635000
  simp only [CollatzResearch.WordTrace]
  refine ⟨29816674538340855307007227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39755566051121140409342969 29816674538340855307007227)
  ·
    refine ⟨44725011807511282960510841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29816674538340855307007227 44725011807511282960510841)
    ·
      refine ⟨33543758855633462220383131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44725011807511282960510841 33543758855633462220383131)
      ·
        refine ⟨50315638283450193330574697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33543758855633462220383131 50315638283450193330574697)
        ·
          refine ⟨37736728712587644997931023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50315638283450193330574697 37736728712587644997931023)
          ·
            refine ⟨56605093068881467496896535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37736728712587644997931023 56605093068881467496896535)
            ·
              refine ⟨84907639603322201245344803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56605093068881467496896535 84907639603322201245344803)
              ·
                refine ⟨127361459404983301868017205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84907639603322201245344803 127361459404983301868017205)
                ·
                  refine ⟨11940136819217184550126613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127361459404983301868017205 11940136819217184550126613)
                  ·
                    refine ⟨559693913400805525787185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11940136819217184550126613 559693913400805525787185)
                    ·
                      rfl

theorem cell22_1635000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_1635000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635000 prefixEnd_1635000 := by exact prefixLift 1635000
  have htrace : WordTrace (prefixWord ++ tailWord_1635000) baseStart_1635000 baseEnd_1635000 := by
    simpa [prefixWord, tailWord_1635000, baseEnd_1635000] using wordTrace_append hprefix tailTrace_1635000
  have hstable : (prefixWord ++ tailWord_1635000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635000).length < 2 ^ (prefixWord ++ tailWord_1635000).sum := by decide
  have hdescent : baseEnd_1635000 < baseStart_1635000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635004 : List Nat := [2, 2, 2, 3, 1, 1, 3, 4, 4]
def baseStart_1635004 : Nat := 118140960795 + 1635004 * 2 ^ 59
def prefixEnd_1635004 : Nat := 4983230072969 + 3 ^ 40 * 1635004 * 2
def baseEnd_1635004 : Nat := 186565094227516949562391

theorem tailTrace_1635004 : CollatzResearch.WordTrace tailWord_1635004 prefixEnd_1635004 186565094227516949562391 := by
  unfold tailWord_1635004
  simp only [CollatzResearch.WordTrace]
  refine ⟨29816747484333609648580033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39755663312444812864773377 29816747484333609648580033)
  ·
    refine ⟨22362560613250207236435025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29816747484333609648580033 22362560613250207236435025)
    ·
      refine ⟨16771920459937655427326269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22362560613250207236435025 16771920459937655427326269)
      ·
        refine ⟨6289470172476620785247351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16771920459937655427326269 6289470172476620785247351)
        ·
          refine ⟨9434205258714931177871027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6289470172476620785247351 9434205258714931177871027)
          ·
            refine ⟨14151307888072396766806541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9434205258714931177871027 14151307888072396766806541)
            ·
              refine ⟨5306740458027148787552453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14151307888072396766806541 5306740458027148787552453)
              ·
                refine ⟨995013835880090397666085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5306740458027148787552453 995013835880090397666085)
                ·
                  refine ⟨186565094227516949562391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 995013835880090397666085 186565094227516949562391)
                  ·
                    rfl

theorem cell22_1635004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 4].length) (baseStart_1635004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635004 prefixEnd_1635004 := by exact prefixLift 1635004
  have htrace : WordTrace (prefixWord ++ tailWord_1635004) baseStart_1635004 baseEnd_1635004 := by
    simpa [prefixWord, tailWord_1635004, baseEnd_1635004] using wordTrace_append hprefix tailTrace_1635004
  have hstable : (prefixWord ++ tailWord_1635004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635004).length < 2 ^ (prefixWord ++ tailWord_1635004).sum := by decide
  have hdescent : baseEnd_1635004 < baseStart_1635004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635015 : List Nat := [1, 1, 4, 1, 1, 1, 2, 11]
def baseStart_1635015 : Nat := 118140960795 + 1635015 * 2 ^ 59
def prefixEnd_1635015 : Nat := 4983230072969 + 3 ^ 40 * 1635015 * 2
def baseEnd_1635015 : Nat := 62188783134150054073571

theorem tailTrace_1635015 : CollatzResearch.WordTrace tailWord_1635015 prefixEnd_1635015 62188783134150054073571 := by
  unfold tailWord_1635015
  simp only [CollatzResearch.WordTrace]
  refine ⟨59633896171627368175810499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39755930781084912117206999 59633896171627368175810499)
  ·
    refine ⟨89450844257441052263715749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59633896171627368175810499 89450844257441052263715749)
    ·
      refine ⟨16772033298270197299446703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89450844257441052263715749 16772033298270197299446703)
      ·
        refine ⟨25158049947405295949170055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16772033298270197299446703 25158049947405295949170055)
        ·
          refine ⟨37737074921107943923755083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25158049947405295949170055 37737074921107943923755083)
          ·
            refine ⟨56605612381661915885632625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37737074921107943923755083 56605612381661915885632625)
            ·
              refine ⟨42454209286246436914224469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56605612381661915885632625 42454209286246436914224469)
              ·
                refine ⟨62188783134150054073571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 42454209286246436914224469 62188783134150054073571)
                ·
                  rfl

theorem cell22_1635015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 11].length) (baseStart_1635015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635015 prefixEnd_1635015 := by exact prefixLift 1635015
  have htrace : WordTrace (prefixWord ++ tailWord_1635015) baseStart_1635015 baseEnd_1635015 := by
    simpa [prefixWord, tailWord_1635015, baseEnd_1635015] using wordTrace_append hprefix tailTrace_1635015
  have hstable : (prefixWord ++ tailWord_1635015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635015).length < 2 ^ (prefixWord ++ tailWord_1635015).sum := by decide
  have hdescent : baseEnd_1635015 < baseStart_1635015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635021 : List Nat := [1, 6, 2, 1, 2, 1, 1, 2, 6]
def baseStart_1635021 : Nat := 118140960795 + 1635021 * 2 ^ 59
def prefixEnd_1635021 : Nat := 4983230072969 + 3 ^ 40 * 1635021 * 2
def baseEnd_1635021 : Nat := 186567034043322823670707

theorem tailTrace_1635021 : CollatzResearch.WordTrace tailWord_1635021 prefixEnd_1635021 186567034043322823670707 := by
  unfold tailWord_1635021
  simp only [CollatzResearch.WordTrace]
  refine ⟨59634115009605631200528917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39756076673070420800352611 59634115009605631200528917)
  ·
    refine ⟨2795349141075263962524793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59634115009605631200528917 2795349141075263962524793)
    ·
      refine ⟨2096511855806447971893595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2795349141075263962524793 2096511855806447971893595)
      ·
        refine ⟨3144767783709671957840393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2096511855806447971893595 3144767783709671957840393)
        ·
          refine ⟨2358575837782253968380295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3144767783709671957840393 2358575837782253968380295)
          ·
            refine ⟨3537863756673380952570443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2358575837782253968380295 3537863756673380952570443)
            ·
              refine ⟨5306795635010071428855665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3537863756673380952570443 5306795635010071428855665)
              ·
                refine ⟨3980096726257553571641749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5306795635010071428855665 3980096726257553571641749)
                ·
                  refine ⟨186567034043322823670707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3980096726257553571641749 186567034043322823670707)
                  ·
                    rfl

theorem cell22_1635021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_1635021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635021 prefixEnd_1635021 := by exact prefixLift 1635021
  have htrace : WordTrace (prefixWord ++ tailWord_1635021) baseStart_1635021 baseEnd_1635021 := by
    simpa [prefixWord, tailWord_1635021, baseEnd_1635021] using wordTrace_append hprefix tailTrace_1635021
  have hstable : (prefixWord ++ tailWord_1635021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635021).length < 2 ^ (prefixWord ++ tailWord_1635021).sum := by decide
  have hdescent : baseEnd_1635021 < baseStart_1635021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635064 : List Nat := [2, 1, 2, 1, 1, 2, 6, 1, 3, 3]
def baseStart_1635064 : Nat := 118140960795 + 1635064 * 2 ^ 59
def prefixEnd_1635064 : Nat := 4983230072969 + 3 ^ 40 * 1635064 * 2
def baseEnd_1635064 : Nat := 559715821908730692186989

theorem tailTrace_1635064 : CollatzResearch.WordTrace tailWord_1635064 prefixEnd_1635064 559715821908730692186989 := by
  unfold tailWord_1635064
  simp only [CollatzResearch.WordTrace]
  refine ⟨29817841674224924772172123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39757122232299899696229497 29817841674224924772172123)
  ·
    refine ⟨44726762511337387158258185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29817841674224924772172123 44726762511337387158258185)
    ·
      refine ⟨33545071883503040368693639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44726762511337387158258185 33545071883503040368693639)
      ·
        refine ⟨50317607825254560553040459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33545071883503040368693639 50317607825254560553040459)
        ·
          refine ⟨75476411737881840829560689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50317607825254560553040459 75476411737881840829560689)
          ·
            refine ⟨56607308803411380622170517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75476411737881840829560689 56607308803411380622170517)
            ·
              refine ⟨2653467600159908466664243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56607308803411380622170517 2653467600159908466664243)
              ·
                refine ⟨3980201400239862699996365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2653467600159908466664243 3980201400239862699996365)
                ·
                  refine ⟨1492575525089948512498637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3980201400239862699996365 1492575525089948512498637)
                  ·
                    refine ⟨559715821908730692186989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1492575525089948512498637 559715821908730692186989)
                    ·
                      rfl

theorem cell22_1635064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_1635064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635064 prefixEnd_1635064 := by exact prefixLift 1635064
  have htrace : WordTrace (prefixWord ++ tailWord_1635064) baseStart_1635064 baseEnd_1635064 := by
    simpa [prefixWord, tailWord_1635064, baseEnd_1635064] using wordTrace_append hprefix tailTrace_1635064
  have hstable : (prefixWord ++ tailWord_1635064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635064).length < 2 ^ (prefixWord ++ tailWord_1635064).sum := by decide
  have hdescent : baseEnd_1635064 < baseStart_1635064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635077 : List Nat := [1, 3, 1, 1, 2, 1, 1, 7, 5]
def baseStart_1635077 : Nat := 118140960795 + 1635077 * 2 ^ 59
def prefixEnd_1635077 : Nat := 4983230072969 + 3 ^ 40 * 1635077 * 2
def baseEnd_1635077 : Nat := 186573424024800997203983

theorem tailTrace_1635077 : CollatzResearch.WordTrace tailWord_1635077 prefixEnd_1635077 186573424024800997203983 := by
  unfold tailWord_1635077
  simp only [CollatzResearch.WordTrace]
  refine ⟨59636157497402752764567485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39757438331601835176378323 59636157497402752764567485)
  ·
    refine ⟨22363559061526032286712807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59636157497402752764567485 22363559061526032286712807)
    ·
      refine ⟨33545338592289048430069211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22363559061526032286712807 33545338592289048430069211)
      ·
        refine ⟨50318007888433572645103817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33545338592289048430069211 50318007888433572645103817)
        ·
          refine ⟨37738505916325179483827863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50318007888433572645103817 37738505916325179483827863)
          ·
            refine ⟨56607758874487769225741795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37738505916325179483827863 56607758874487769225741795)
            ·
              refine ⟨84911638311731653838612693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56607758874487769225741795 84911638311731653838612693)
              ·
                refine ⟨1990116522931210636842485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 84911638311731653838612693 1990116522931210636842485)
                ·
                  refine ⟨186573424024800997203983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1990116522931210636842485 186573424024800997203983)
                  ·
                    rfl

theorem cell22_1635077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_1635077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635077 prefixEnd_1635077 := by exact prefixLift 1635077
  have htrace : WordTrace (prefixWord ++ tailWord_1635077) baseStart_1635077 baseEnd_1635077 := by
    simpa [prefixWord, tailWord_1635077, baseEnd_1635077] using wordTrace_append hprefix tailTrace_1635077
  have hstable : (prefixWord ++ tailWord_1635077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635077).length < 2 ^ (prefixWord ++ tailWord_1635077).sum := by decide
  have hdescent : baseEnd_1635077 < baseStart_1635077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635107 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 5, 4]
def baseStart_1635107 : Nat := 118140960795 + 1635107 * 2 ^ 59
def prefixEnd_1635107 : Nat := 4983230072969 + 3 ^ 40 * 1635107 * 2
def baseEnd_1635107 : Nat := 559730541687492913361857

theorem tailTrace_1635107 : CollatzResearch.WordTrace tailWord_1635107 prefixEnd_1635107 559730541687492913361857 := by
  unfold tailWord_1635107
  simp only [CollatzResearch.WordTrace]
  refine ⟨59637251687294067888159575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39758167791529378592106383 59637251687294067888159575)
  ·
    refine ⟨89455877530941101832239363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59637251687294067888159575 89455877530941101832239363)
    ·
      refine ⟨134183816296411652748359045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89455877530941101832239363 134183816296411652748359045)
      ·
        refine ⟨25159465555577184890317321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134183816296411652748359045 25159465555577184890317321)
        ·
          refine ⟨18869599166682888667737991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25159465555577184890317321 18869599166682888667737991)
          ·
            refine ⟨28304398750024333001606987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18869599166682888667737991 28304398750024333001606987)
            ·
              refine ⟨42456598125036499502410481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28304398750024333001606987 42456598125036499502410481)
              ·
                refine ⟨31842448593777374626807861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42456598125036499502410481 31842448593777374626807861)
                ·
                  refine ⟨2985229555666628871263237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31842448593777374626807861 2985229555666628871263237)
                  ·
                    refine ⟨559730541687492913361857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2985229555666628871263237 559730541687492913361857)
                    ·
                      rfl

theorem cell22_1635107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 4].length) (baseStart_1635107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635107 prefixEnd_1635107 := by exact prefixLift 1635107
  have htrace : WordTrace (prefixWord ++ tailWord_1635107) baseStart_1635107 baseEnd_1635107 := by
    simpa [prefixWord, tailWord_1635107, baseEnd_1635107] using wordTrace_append hprefix tailTrace_1635107
  have hstable : (prefixWord ++ tailWord_1635107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635107).length < 2 ^ (prefixWord ++ tailWord_1635107).sum := by decide
  have hdescent : baseEnd_1635107 < baseStart_1635107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635152 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 1, 6]
def baseStart_1635152 : Nat := 118140960795 + 1635152 * 2 ^ 59
def prefixEnd_1635152 : Nat := 4983230072969 + 3 ^ 40 * 1635152 * 2
def baseEnd_1635152 : Nat := 559745946107127795986719

theorem tailTrace_1635152 : CollatzResearch.WordTrace tailWord_1635152 prefixEnd_1635152 559745946107127795986719 := by
  unfold tailWord_1635152
  simp only [CollatzResearch.WordTrace]
  refine ⟨29819446486065520286773855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39759261981420693715698473 29819446486065520286773855)
  ·
    refine ⟨44729169729098280430160783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29819446486065520286773855 44729169729098280430160783)
    ·
      refine ⟨67093754593647420645241175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44729169729098280430160783 67093754593647420645241175)
      ·
        refine ⟨100640631890471130967861763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67093754593647420645241175 100640631890471130967861763)
        ·
          refine ⟨150960947835706696451792645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100640631890471130967861763 150960947835706696451792645)
          ·
            refine ⟨28305177719195005584711121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150960947835706696451792645 28305177719195005584711121)
            ·
              refine ⟨21228883289396254188533341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28305177719195005584711121 21228883289396254188533341)
              ·
                refine ⟨7960831233523595320700003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21228883289396254188533341 7960831233523595320700003)
                ·
                  refine ⟨11941246850285392981050005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7960831233523595320700003 11941246850285392981050005)
                  ·
                    refine ⟨559745946107127795986719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11941246850285392981050005 559745946107127795986719)
                    ·
                      rfl

theorem cell22_1635152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_1635152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635152 prefixEnd_1635152 := by exact prefixLift 1635152
  have htrace : WordTrace (prefixWord ++ tailWord_1635152) baseStart_1635152 baseEnd_1635152 := by
    simpa [prefixWord, tailWord_1635152, baseEnd_1635152] using wordTrace_append hprefix tailTrace_1635152
  have hstable : (prefixWord ++ tailWord_1635152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635152).length < 2 ^ (prefixWord ++ tailWord_1635152).sum := by decide
  have hdescent : baseEnd_1635152 < baseStart_1635152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635154 : List Nat := [3, 2, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_1635154 : Nat := 118140960795 + 1635154 * 2 ^ 59
def prefixEnd_1635154 : Nat := 4983230072969 + 3 ^ 40 * 1635154 * 2
def baseEnd_1635154 : Nat := 559746630748000457436713

theorem tailTrace_1635154 : CollatzResearch.WordTrace tailWord_1635154 prefixEnd_1635154 559746630748000457436713 := by
  unfold tailWord_1635154
  simp only [CollatzResearch.WordTrace]
  refine ⟨14909741479530948728780129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39759310612082529943413677 14909741479530948728780129)
  ·
    refine ⟨11182306109648211546585097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14909741479530948728780129 11182306109648211546585097)
    ·
      refine ⟨8386729582236158659938823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11182306109648211546585097 8386729582236158659938823)
      ·
        refine ⟨12580094373354237989908235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8386729582236158659938823 12580094373354237989908235)
        ·
          refine ⟨18870141560031356984862353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12580094373354237989908235 18870141560031356984862353)
          ·
            refine ⟨14152606170023517738646765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18870141560031356984862353 14152606170023517738646765)
            ·
              refine ⟨5307227313758819151992537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14152606170023517738646765 5307227313758819151992537)
              ·
                refine ⟨3980420485319114363994403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5307227313758819151992537 3980420485319114363994403)
                ·
                  refine ⟨5970630727978671545991605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3980420485319114363994403 5970630727978671545991605)
                  ·
                    refine ⟨559746630748000457436713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5970630727978671545991605 559746630748000457436713)
                    ·
                      rfl

theorem cell22_1635154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_1635154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635154 prefixEnd_1635154 := by exact prefixLift 1635154
  have htrace : WordTrace (prefixWord ++ tailWord_1635154) baseStart_1635154 baseEnd_1635154 := by
    simpa [prefixWord, tailWord_1635154, baseEnd_1635154] using wordTrace_append hprefix tailTrace_1635154
  have hstable : (prefixWord ++ tailWord_1635154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635154).length < 2 ^ (prefixWord ++ tailWord_1635154).sum := by decide
  have hdescent : baseEnd_1635154 < baseStart_1635154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635171 : List Nat := [1, 1, 1, 5, 3, 1, 1, 4, 2, 3]
def baseStart_1635171 : Nat := 118140960795 + 1635171 * 2 ^ 59
def prefixEnd_1635171 : Nat := 4983230072969 + 3 ^ 40 * 1635171 * 2
def baseEnd_1635171 : Nat := 559752450195418079761661

theorem tailTrace_1635171 : CollatzResearch.WordTrace tailWord_1635171 prefixEnd_1635171 559752450195418079761661 := by
  unfold tailWord_1635171
  simp only [CollatzResearch.WordTrace]
  refine ⟨59639585959062206818489367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39759723972708137878992911 59639585959062206818489367)
  ·
    refine ⟨89459378938593310227734051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59639585959062206818489367 89459378938593310227734051)
    ·
      refine ⟨134189068407889965341601077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89459378938593310227734051 134189068407889965341601077)
      ·
        refine ⟨12580225163239684250775101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134189068407889965341601077 12580225163239684250775101)
        ·
          refine ⟨4717584436214881594040663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12580225163239684250775101 4717584436214881594040663)
          ·
            refine ⟨7076376654322322391060995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4717584436214881594040663 7076376654322322391060995)
            ·
              refine ⟨10614564981483483586591493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7076376654322322391060995 10614564981483483586591493)
              ·
                refine ⟨1990230934028153172485905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10614564981483483586591493 1990230934028153172485905)
                ·
                  refine ⟨1492673200521114879364429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1990230934028153172485905 1492673200521114879364429)
                  ·
                    refine ⟨559752450195418079761661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1492673200521114879364429 559752450195418079761661)
                    ·
                      rfl

theorem cell22_1635171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 3].length) (baseStart_1635171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635171 prefixEnd_1635171 := by exact prefixLift 1635171
  have htrace : WordTrace (prefixWord ++ tailWord_1635171) baseStart_1635171 baseEnd_1635171 := by
    simpa [prefixWord, tailWord_1635171, baseEnd_1635171] using wordTrace_append hprefix tailTrace_1635171
  have hstable : (prefixWord ++ tailWord_1635171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635171).length < 2 ^ (prefixWord ++ tailWord_1635171).sum := by decide
  have hdescent : baseEnd_1635171 < baseStart_1635171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635199 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 5, 3]
def baseStart_1635199 : Nat := 118140960795 + 1635199 * 2 ^ 59
def prefixEnd_1635199 : Nat := 4983230072969 + 3 ^ 40 * 1635199 * 2
def baseEnd_1635199 : Nat := 559762035167635340061575

theorem tailTrace_1635199 : CollatzResearch.WordTrace tailWord_1635199 prefixEnd_1635199 559762035167635340061575 := by
  unfold tailWord_1635199
  simp only [CollatzResearch.WordTrace]
  refine ⟨59640607202960767600508651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39760404801973845067005767 59640607202960767600508651)
  ·
    refine ⟨89460910804441151400762977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59640607202960767600508651 89460910804441151400762977)
    ·
      refine ⟨67095683103330863550572233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89460910804441151400762977 67095683103330863550572233)
      ·
        refine ⟨50321762327498147662929175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67095683103330863550572233 50321762327498147662929175)
        ·
          refine ⟨75482643491247221494393763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50321762327498147662929175 75482643491247221494393763)
          ·
            refine ⟨113223965236870832241590645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75482643491247221494393763 113223965236870832241590645)
            ·
              refine ⟨10614746740956640522649123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113223965236870832241590645 10614746740956640522649123)
              ·
                refine ⟨15922120111434960783973685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10614746740956640522649123 15922120111434960783973685)
                ·
                  refine ⟨1492698760447027573497533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15922120111434960783973685 1492698760447027573497533)
                  ·
                    refine ⟨559762035167635340061575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1492698760447027573497533 559762035167635340061575)
                    ·
                      rfl

theorem cell22_1635199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 3].length) (baseStart_1635199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635199 prefixEnd_1635199 := by exact prefixLift 1635199
  have htrace : WordTrace (prefixWord ++ tailWord_1635199) baseStart_1635199 baseEnd_1635199 := by
    simpa [prefixWord, tailWord_1635199, baseEnd_1635199] using wordTrace_append hprefix tailTrace_1635199
  have hstable : (prefixWord ++ tailWord_1635199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635199).length < 2 ^ (prefixWord ++ tailWord_1635199).sum := by decide
  have hdescent : baseEnd_1635199 < baseStart_1635199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635222 : List Nat := [5, 3, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_1635222 : Nat := 118140960795 + 1635222 * 2 ^ 59
def prefixEnd_1635222 : Nat := 4983230072969 + 3 ^ 40 * 1635222 * 2
def baseEnd_1635222 : Nat := 559769908537670946736505

theorem tailTrace_1635222 : CollatzResearch.WordTrace tailWord_1635222 prefixEnd_1635222 559769908537670946736505 := by
  unfold tailWord_1635222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3727590380117340158037245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39760964054584961685730613 3727590380117340158037245)
  ·
    refine ⟨1397846392544002559263967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3727590380117340158037245 1397846392544002559263967)
    ·
      refine ⟨2096769588816003838895951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1397846392544002559263967 2096769588816003838895951)
      ·
        refine ⟨3145154383224005758343927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2096769588816003838895951 3145154383224005758343927)
        ·
          refine ⟨4717731574836008637515891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3145154383224005758343927 4717731574836008637515891)
          ·
            refine ⟨7076597362254012956273837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4717731574836008637515891 7076597362254012956273837)
            ·
              refine ⟨2653724010845254858602689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7076597362254012956273837 2653724010845254858602689)
              ·
                refine ⟨1990293008133941143952017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2653724010845254858602689 1990293008133941143952017)
                ·
                  refine ⟨1492719756100455857964013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1990293008133941143952017 1492719756100455857964013)
                  ·
                    refine ⟨559769908537670946736505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1492719756100455857964013 559769908537670946736505)
                    ·
                      rfl

theorem cell22_1635222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_1635222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635222 prefixEnd_1635222 := by exact prefixLift 1635222
  have htrace : WordTrace (prefixWord ++ tailWord_1635222) baseStart_1635222 baseEnd_1635222 := by
    simpa [prefixWord, tailWord_1635222, baseEnd_1635222] using wordTrace_append hprefix tailTrace_1635222
  have hstable : (prefixWord ++ tailWord_1635222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635222).length < 2 ^ (prefixWord ++ tailWord_1635222).sum := by decide
  have hdescent : baseEnd_1635222 < baseStart_1635222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635229 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 7]
def baseStart_1635229 : Nat := 118140960795 + 1635229 * 2 ^ 59
def prefixEnd_1635229 : Nat := 4983230072969 + 3 ^ 40 * 1635229 * 2
def baseEnd_1635229 : Nat := 186590768260241753937161

theorem tailTrace_1635229 : CollatzResearch.WordTrace tailWord_1635229 prefixEnd_1635229 186590768260241753937161 := by
  unfold tailWord_1635229
  simp only [CollatzResearch.WordTrace]
  refine ⟨59641701392852082724100741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39761134261901388482733827 59641701392852082724100741)
  ·
    refine ⟨11182819011159765510768889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59641701392852082724100741 11182819011159765510768889)
    ·
      refine ⟨8387114258369824133076667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11182819011159765510768889 8387114258369824133076667)
      ·
        refine ⟨12580671387554736199615001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8387114258369824133076667 12580671387554736199615001)
        ·
          refine ⟨9435503540666052149711251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12580671387554736199615001 9435503540666052149711251)
          ·
            refine ⟨14153255310999078224566877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9435503540666052149711251 14153255310999078224566877)
            ·
              refine ⟨5307470741624654334212579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14153255310999078224566877 5307470741624654334212579)
              ·
                refine ⟨7961206112436981501318869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5307470741624654334212579 7961206112436981501318869)
                ·
                  refine ⟨186590768260241753937161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7961206112436981501318869 186590768260241753937161)
                  ·
                    rfl

theorem cell22_1635229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_1635229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635229 prefixEnd_1635229 := by exact prefixLift 1635229
  have htrace : WordTrace (prefixWord ++ tailWord_1635229) baseStart_1635229 baseEnd_1635229 := by
    simpa [prefixWord, tailWord_1635229, baseEnd_1635229] using wordTrace_append hprefix tailTrace_1635229
  have hstable : (prefixWord ++ tailWord_1635229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635229).length < 2 ^ (prefixWord ++ tailWord_1635229).sum := by decide
  have hdescent : baseEnd_1635229 < baseStart_1635229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635233 : List Nat := [1, 2, 3, 4, 1, 2, 2, 1, 3, 3]
def baseStart_1635233 : Nat := 118140960795 + 1635233 * 2 ^ 59
def prefixEnd_1635233 : Nat := 4983230072969 + 3 ^ 40 * 1635233 * 2
def baseEnd_1635233 : Nat := 559773674062470584711471

theorem tailTrace_1635233 : CollatzResearch.WordTrace tailWord_1635233 prefixEnd_1635233 559773674062470584711471 := by
  unfold tailWord_1635233
  simp only [CollatzResearch.WordTrace]
  refine ⟨59641847284837591407246353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39761231523225060938164235 59641847284837591407246353)
  ·
    refine ⟨44731385463628193555434765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59641847284837591407246353 44731385463628193555434765)
    ·
      refine ⟨16774269548860572583288037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44731385463628193555434765 16774269548860572583288037)
      ·
        refine ⟨3145175540411357359366507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16774269548860572583288037 3145175540411357359366507)
        ·
          refine ⟨4717763310617036039049761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3145175540411357359366507 4717763310617036039049761)
          ·
            refine ⟨3538322482962777029287321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4717763310617036039049761 3538322482962777029287321)
            ·
              refine ⟨2653741862222082771965491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3538322482962777029287321 2653741862222082771965491)
              ·
                refine ⟨3980612793333124157948237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2653741862222082771965491 3980612793333124157948237)
                ·
                  refine ⟨1492729797499921559230589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3980612793333124157948237 1492729797499921559230589)
                  ·
                    refine ⟨559773674062470584711471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1492729797499921559230589 559773674062470584711471)
                    ·
                      rfl

theorem cell22_1635233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_1635233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635233 prefixEnd_1635233 := by exact prefixLift 1635233
  have htrace : WordTrace (prefixWord ++ tailWord_1635233) baseStart_1635233 baseEnd_1635233 := by
    simpa [prefixWord, tailWord_1635233, baseEnd_1635233] using wordTrace_append hprefix tailTrace_1635233
  have hstable : (prefixWord ++ tailWord_1635233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635233).length < 2 ^ (prefixWord ++ tailWord_1635233).sum := by decide
  have hdescent : baseEnd_1635233 < baseStart_1635233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635276 : List Nat := [2, 2, 1, 4, 1, 1, 1, 5, 1, 4]
def baseStart_1635276 : Nat := 118140960795 + 1635276 * 2 ^ 59
def prefixEnd_1635276 : Nat := 4983230072969 + 3 ^ 40 * 1635276 * 2
def baseEnd_1635276 : Nat := 559788393841232805886339

theorem tailTrace_1635276 : CollatzResearch.WordTrace tailWord_1635276 prefixEnd_1635276 559788393841232805886339 := by
  unfold tailWord_1635276
  simp only [CollatzResearch.WordTrace]
  refine ⟨29821707811840904875530841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39762277082454539834041121 29821707811840904875530841)
  ·
    refine ⟨22366280858880678656648131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29821707811840904875530841 22366280858880678656648131)
    ·
      refine ⟨33549421288321017984972197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22366280858880678656648131 33549421288321017984972197)
      ·
        refine ⟨6290516491560190872182287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33549421288321017984972197 6290516491560190872182287)
        ·
          refine ⟨9435774737340286308273431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6290516491560190872182287 9435774737340286308273431)
          ·
            refine ⟨14153662106010429462410147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9435774737340286308273431 14153662106010429462410147)
            ·
              refine ⟨21230493159015644193615221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14153662106010429462410147 21230493159015644193615221)
              ·
                refine ⟨1990358733657716643151427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21230493159015644193615221 1990358733657716643151427)
                ·
                  refine ⟨2985538100486574964727141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1990358733657716643151427 2985538100486574964727141)
                  ·
                    refine ⟨559788393841232805886339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2985538100486574964727141 559788393841232805886339)
                    ·
                      rfl

theorem cell22_1635276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_1635276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635276 prefixEnd_1635276 := by exact prefixLift 1635276
  have htrace : WordTrace (prefixWord ++ tailWord_1635276) baseStart_1635276 baseEnd_1635276 := by
    simpa [prefixWord, tailWord_1635276, baseEnd_1635276] using wordTrace_append hprefix tailTrace_1635276
  have hstable : (prefixWord ++ tailWord_1635276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635276).length < 2 ^ (prefixWord ++ tailWord_1635276).sum := by decide
  have hdescent : baseEnd_1635276 < baseStart_1635276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635304 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 3, 6]
def baseStart_1635304 : Nat := 118140960795 + 1635304 * 2 ^ 59
def prefixEnd_1635304 : Nat := 4983230072969 + 3 ^ 40 * 1635304 * 2
def baseEnd_1635304 : Nat := 559797978813450066186253

theorem tailTrace_1635304 : CollatzResearch.WordTrace tailWord_1635304 prefixEnd_1635304 559797978813450066186253 := by
  unfold tailWord_1635304
  simp only [CollatzResearch.WordTrace]
  refine ⟨29822218433790185266540483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39762957911720247022053977 29822218433790185266540483)
  ·
    refine ⟨44733327650685277899810725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29822218433790185266540483 44733327650685277899810725)
    ·
      refine ⟨8387498934503489606214511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44733327650685277899810725 8387498934503489606214511)
      ·
        refine ⟨12581248401755234409321767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8387498934503489606214511 12581248401755234409321767)
        ·
          refine ⟨18871872602632851613982651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12581248401755234409321767 18871872602632851613982651)
          ·
            refine ⟨28307808903949277420973977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18871872602632851613982651 28307808903949277420973977)
            ·
              refine ⟨21230856677961958065730483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28307808903949277420973977 21230856677961958065730483)
              ·
                refine ⟨31846285016942937098595725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21230856677961958065730483 31846285016942937098595725)
                ·
                  refine ⟨11942356881353601411973397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31846285016942937098595725 11942356881353601411973397)
                  ·
                    refine ⟨559797978813450066186253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11942356881353601411973397 559797978813450066186253)
                    ·
                      rfl

theorem cell22_1635304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_1635304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635304 prefixEnd_1635304 := by exact prefixLift 1635304
  have htrace : WordTrace (prefixWord ++ tailWord_1635304) baseStart_1635304 baseEnd_1635304 := by
    simpa [prefixWord, tailWord_1635304, baseEnd_1635304] using wordTrace_append hprefix tailTrace_1635304
  have hstable : (prefixWord ++ tailWord_1635304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635304).length < 2 ^ (prefixWord ++ tailWord_1635304).sum := by decide
  have hdescent : baseEnd_1635304 < baseStart_1635304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635310 : List Nat := [4, 1, 2, 1, 4, 2, 1, 2, 1, 4]
def baseStart_1635310 : Nat := 118140960795 + 1635310 * 2 ^ 59
def prefixEnd_1635310 : Nat := 4983230072969 + 3 ^ 40 * 1635310 * 2
def baseEnd_1635310 : Nat := 559800032736068050536235

theorem tailTrace_1635310 : CollatzResearch.WordTrace tailWord_1635310 prefixEnd_1635310 559800032736068050536235 := by
  unfold tailWord_1635310
  simp only [CollatzResearch.WordTrace]
  refine ⟨7455581963194829194724923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39763103803705755705199589 7455581963194829194724923)
  ·
    refine ⟨11183372944792243792087385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7455581963194829194724923 11183372944792243792087385)
    ·
      refine ⟨8387529708594182844065539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11183372944792243792087385 8387529708594182844065539)
      ·
        refine ⟨12581294562891274266098309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8387529708594182844065539 12581294562891274266098309)
        ·
          refine ⟨2358992730542113924893433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12581294562891274266098309 2358992730542113924893433)
          ·
            refine ⟨1769244547906585443670075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2358992730542113924893433 1769244547906585443670075)
            ·
              refine ⟨2653866821859878165505113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1769244547906585443670075 2653866821859878165505113)
              ·
                refine ⟨1990400116394908624128835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2653866821859878165505113 1990400116394908624128835)
                ·
                  refine ⟨2985600174592362936193253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1990400116394908624128835 2985600174592362936193253)
                  ·
                    refine ⟨559800032736068050536235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2985600174592362936193253 559800032736068050536235)
                    ·
                      rfl

theorem cell22_1635310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_1635310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635310 prefixEnd_1635310 := by exact prefixLift 1635310
  have htrace : WordTrace (prefixWord ++ tailWord_1635310) baseStart_1635310 baseEnd_1635310 := by
    simpa [prefixWord, tailWord_1635310, baseEnd_1635310] using wordTrace_append hprefix tailTrace_1635310
  have hstable : (prefixWord ++ tailWord_1635310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635310).length < 2 ^ (prefixWord ++ tailWord_1635310).sum := by decide
  have hdescent : baseEnd_1635310 < baseStart_1635310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635321 : List Nat := [1, 2, 1, 3, 1, 3, 4, 1, 2, 4]
def baseStart_1635321 : Nat := 118140960795 + 1635321 * 2 ^ 59
def prefixEnd_1635321 : Nat := 4983230072969 + 3 ^ 40 * 1635321 * 2
def baseEnd_1635321 : Nat := 559803798260867688511201

theorem tailTrace_1635321 : CollatzResearch.WordTrace tailWord_1635321 prefixEnd_1635321 559803798260867688511201 := by
  unfold tailWord_1635321
  simp only [CollatzResearch.WordTrace]
  refine ⟨59645056908518782436449817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39763371272345854957633211 59645056908518782436449817)
  ·
    refine ⟨44733792681389086827337363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59645056908518782436449817 44733792681389086827337363)
    ·
      refine ⟨67100689022083630241006045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44733792681389086827337363 67100689022083630241006045)
      ·
        refine ⟨25162758383281361340377267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67100689022083630241006045 25162758383281361340377267)
        ·
          refine ⟨37744137574922042010565901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25162758383281361340377267 37744137574922042010565901)
          ·
            refine ⟨14154051590595765753962213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37744137574922042010565901 14154051590595765753962213)
            ·
              refine ⟨2653884673236706078867915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14154051590595765753962213 2653884673236706078867915)
              ·
                refine ⟨3980827009855059118301873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2653884673236706078867915 3980827009855059118301873)
                ·
                  refine ⟨2985620257391294338726405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3980827009855059118301873 2985620257391294338726405)
                  ·
                    refine ⟨559803798260867688511201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2985620257391294338726405 559803798260867688511201)
                    ·
                      rfl

theorem cell22_1635321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 4].length) (baseStart_1635321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635321 prefixEnd_1635321 := by exact prefixLift 1635321
  have htrace : WordTrace (prefixWord ++ tailWord_1635321) baseStart_1635321 baseEnd_1635321 := by
    simpa [prefixWord, tailWord_1635321, baseEnd_1635321] using wordTrace_append hprefix tailTrace_1635321
  have hstable : (prefixWord ++ tailWord_1635321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635321).length < 2 ^ (prefixWord ++ tailWord_1635321).sum := by decide
  have hdescent : baseEnd_1635321 < baseStart_1635321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635379 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 3, 7]
def baseStart_1635379 : Nat := 118140960795 + 1635379 * 2 ^ 59
def prefixEnd_1635379 : Nat := 4983230072969 + 3 ^ 40 * 1635379 * 2
def baseEnd_1635379 : Nat := 559823652846174870561023

theorem tailTrace_1635379 : CollatzResearch.WordTrace tailWord_1635379 prefixEnd_1635379 559823652846174870561023 := by
  unfold tailWord_1635379
  simp only [CollatzResearch.WordTrace]
  refine ⟨59647172342308658342061191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39764781561539105561374127 59647172342308658342061191)
  ·
    refine ⟨89470758513462987513091787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59647172342308658342061191 89470758513462987513091787)
    ·
      refine ⟨134206137770194481269637681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89470758513462987513091787 134206137770194481269637681)
      ·
        refine ⟨100654603327645860952228261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134206137770194481269637681 100654603327645860952228261)
        ·
          refine ⟨18872738123933598928542799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100654603327645860952228261 18872738123933598928542799)
          ·
            refine ⟨28309107185900398392814199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18872738123933598928542799 28309107185900398392814199)
            ·
              refine ⟨42463660778850597589221299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28309107185900398392814199 42463660778850597589221299)
              ·
                refine ⟨63695491168275896383831949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42463660778850597589221299 63695491168275896383831949)
                ·
                  refine ⟨23885809188103461143936981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63695491168275896383831949 23885809188103461143936981)
                  ·
                    refine ⟨559823652846174870561023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23885809188103461143936981 559823652846174870561023)
                    ·
                      rfl

theorem cell22_1635379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 7].length) (baseStart_1635379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635379 prefixEnd_1635379 := by exact prefixLift 1635379
  have htrace : WordTrace (prefixWord ++ tailWord_1635379) baseStart_1635379 baseEnd_1635379 := by
    simpa [prefixWord, tailWord_1635379, baseEnd_1635379] using wordTrace_append hprefix tailTrace_1635379
  have hstable : (prefixWord ++ tailWord_1635379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635379).length < 2 ^ (prefixWord ++ tailWord_1635379).sum := by decide
  have hdescent : baseEnd_1635379 < baseStart_1635379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635385 : List Nat := [1, 2, 1, 5, 2, 1, 1, 5, 1, 3]
def baseStart_1635385 : Nat := 118140960795 + 1635385 * 2 ^ 59
def prefixEnd_1635385 : Nat := 4983230072969 + 3 ^ 40 * 1635385 * 2
def baseEnd_1635385 : Nat := 559825706768792854911005

theorem tailTrace_1635385 : CollatzResearch.WordTrace tailWord_1635385 prefixEnd_1635385 559825706768792854911005 := by
  unfold tailWord_1635385
  simp only [CollatzResearch.WordTrace]
  refine ⟨59647391180286921366779609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39764927453524614244519739 59647391180286921366779609)
  ·
    refine ⟨44735543385215191025084707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59647391180286921366779609 44735543385215191025084707)
    ·
      refine ⟨67103315077822786537627061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44735543385215191025084707 67103315077822786537627061)
      ·
        refine ⟨6290935788545886237902537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67103315077822786537627061 6290935788545886237902537)
        ·
          refine ⟨4718201841409414678426903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6290935788545886237902537 4718201841409414678426903)
          ·
            refine ⟨7077302762114122017640355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4718201841409414678426903 7077302762114122017640355)
            ·
              refine ⟨10615954143171183026460533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7077302762114122017640355 10615954143171183026460533)
              ·
                refine ⟨995245700922298408730675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10615954143171183026460533 995245700922298408730675)
                ·
                  refine ⟨1492868551383447613096013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 995245700922298408730675 1492868551383447613096013)
                  ·
                    refine ⟨559825706768792854911005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1492868551383447613096013 559825706768792854911005)
                    ·
                      rfl

theorem cell22_1635385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 1, 3].length) (baseStart_1635385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635385 prefixEnd_1635385 := by exact prefixLift 1635385
  have htrace : WordTrace (prefixWord ++ tailWord_1635385) baseStart_1635385 baseEnd_1635385 := by
    simpa [prefixWord, tailWord_1635385, baseEnd_1635385] using wordTrace_append hprefix tailTrace_1635385
  have hstable : (prefixWord ++ tailWord_1635385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635385).length < 2 ^ (prefixWord ++ tailWord_1635385).sum := by decide
  have hdescent : baseEnd_1635385 < baseStart_1635385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635456 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 4, 4]
def baseStart_1635456 : Nat := 118140960795 + 1635456 * 2 ^ 59
def prefixEnd_1635456 : Nat := 4983230072969 + 3 ^ 40 * 1635456 * 2
def baseEnd_1635456 : Nat := 559850011519772336385787

theorem tailTrace_1635456 : CollatzResearch.WordTrace tailWord_1635456 prefixEnd_1635456 559850011519772336385787 := by
  unfold tailWord_1635456
  simp only [CollatzResearch.WordTrace]
  refine ⟨29824990381514850246307111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39766653842019800328409481 29824990381514850246307111)
  ·
    refine ⟨44737485572272275369460667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29824990381514850246307111 44737485572272275369460667)
    ·
      refine ⟨67106228358408413054191001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44737485572272275369460667 67106228358408413054191001)
      ·
        refine ⟨50329671268806309790643251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67106228358408413054191001 50329671268806309790643251)
        ·
          refine ⟨75494506903209464685964877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50329671268806309790643251 75494506903209464685964877)
          ·
            refine ⟨28310440088703549257236829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75494506903209464685964877 28310440088703549257236829)
            ·
              refine ⟨10616415033263830971463811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28310440088703549257236829 10616415033263830971463811)
              ·
                refine ⟨15924622549895746457195717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10616415033263830971463811 15924622549895746457195717)
                ·
                  refine ⟨2985866728105452460724197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15924622549895746457195717 2985866728105452460724197)
                  ·
                    refine ⟨559850011519772336385787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2985866728105452460724197 559850011519772336385787)
                    ·
                      rfl

theorem cell22_1635456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 4, 4].length) (baseStart_1635456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635456 prefixEnd_1635456 := by exact prefixLift 1635456
  have htrace : WordTrace (prefixWord ++ tailWord_1635456) baseStart_1635456 baseEnd_1635456 := by
    simpa [prefixWord, tailWord_1635456, baseEnd_1635456] using wordTrace_append hprefix tailTrace_1635456
  have hstable : (prefixWord ++ tailWord_1635456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635456).length < 2 ^ (prefixWord ++ tailWord_1635456).sum := by decide
  have hdescent : baseEnd_1635456 < baseStart_1635456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635475 : List Nat := [1, 1, 1, 2, 1, 2, 8, 1, 2, 3]
def baseStart_1635475 : Nat := 118140960795 + 1635475 * 2 ^ 59
def prefixEnd_1635475 : Nat := 4983230072969 + 3 ^ 40 * 1635475 * 2
def baseEnd_1635475 : Nat := 559856515608062620160729

theorem tailTrace_1635475 : CollatzResearch.WordTrace tailWord_1635475 prefixEnd_1635475 559856515608062620160729 := by
  unfold tailWord_1635475
  simp only [CollatzResearch.WordTrace]
  refine ⟨59650673749960866737555879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39767115833307244491703919 59650673749960866737555879)
  ·
    refine ⟨89476010624941300106333819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59650673749960866737555879 89476010624941300106333819)
    ·
      refine ⟨134214015937411950159500729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89476010624941300106333819 134214015937411950159500729)
      ·
        refine ⟨100660511953058962619625547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134214015937411950159500729 100660511953058962619625547)
        ·
          refine ⟨150990767929588443929438321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100660511953058962619625547 150990767929588443929438321)
          ·
            refine ⟨113243075947191332947078741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150990767929588443929438321 113243075947191332947078741)
            ·
              refine ⟨1327067296256148432973579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 113243075947191332947078741 1327067296256148432973579)
              ·
                refine ⟨1990600944384222649460369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1327067296256148432973579 1990600944384222649460369)
                ·
                  refine ⟨1492950708288166987095277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1990600944384222649460369 1492950708288166987095277)
                  ·
                    refine ⟨559856515608062620160729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1492950708288166987095277 559856515608062620160729)
                    ·
                      rfl

theorem cell22_1635475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 2, 3].length) (baseStart_1635475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635475 prefixEnd_1635475 := by exact prefixLift 1635475
  have htrace : WordTrace (prefixWord ++ tailWord_1635475) baseStart_1635475 baseEnd_1635475 := by
    simpa [prefixWord, tailWord_1635475, baseEnd_1635475] using wordTrace_append hprefix tailTrace_1635475
  have hstable : (prefixWord ++ tailWord_1635475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635475).length < 2 ^ (prefixWord ++ tailWord_1635475).sum := by decide
  have hdescent : baseEnd_1635475 < baseStart_1635475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635518 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_1635518 : Nat := 118140960795 + 1635518 * 2 ^ 59
def prefixEnd_1635518 : Nat := 4983230072969 + 3 ^ 40 * 1635518 * 2
def baseEnd_1635518 : Nat := 559871235386824841335597

theorem tailTrace_1635518 : CollatzResearch.WordTrace tailWord_1635518 prefixEnd_1635518 559871235386824841335597 := by
  unfold tailWord_1635518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7456530261100635635171401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39768161392536723387580805 7456530261100635635171401)
  ·
    refine ⟨5592397695825476726378551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7456530261100635635171401 5592397695825476726378551)
    ·
      refine ⟨8388596543738215089567827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5592397695825476726378551 8388596543738215089567827)
      ·
        refine ⟨12582894815607322634351741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8388596543738215089567827 12582894815607322634351741)
        ·
          refine ⟨4718585555852745987881903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12582894815607322634351741 4718585555852745987881903)
          ·
            refine ⟨7077878333779118981822855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4718585555852745987881903 7077878333779118981822855)
            ·
              refine ⟨10616817500668678472734283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7077878333779118981822855 10616817500668678472734283)
              ·
                refine ⟨15925226251003017709101425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10616817500668678472734283 15925226251003017709101425)
                ·
                  refine ⟨11943919688252263281826069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15925226251003017709101425 11943919688252263281826069)
                  ·
                    refine ⟨559871235386824841335597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11943919688252263281826069 559871235386824841335597)
                    ·
                      rfl

theorem cell22_1635518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_1635518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635518 prefixEnd_1635518 := by exact prefixLift 1635518
  have htrace : WordTrace (prefixWord ++ tailWord_1635518) baseStart_1635518 baseEnd_1635518 := by
    simpa [prefixWord, tailWord_1635518, baseEnd_1635518] using wordTrace_append hprefix tailTrace_1635518
  have hstable : (prefixWord ++ tailWord_1635518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635518).length < 2 ^ (prefixWord ++ tailWord_1635518).sum := by decide
  have hdescent : baseEnd_1635518 < baseStart_1635518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635567 : List Nat := [1, 1, 2, 1, 8, 1, 1, 2, 5]
def baseStart_1635567 : Nat := 118140960795 + 1635567 * 2 ^ 59
def prefixEnd_1635567 : Nat := 4983230072969 + 3 ^ 40 * 1635567 * 2
def baseEnd_1635567 : Nat := 186629336362735015620149

theorem tailTrace_1635567 : CollatzResearch.WordTrace tailWord_1635567 prefixEnd_1635567 186629336362735015620149 := by
  unfold tailWord_1635567
  simp only [CollatzResearch.WordTrace]
  refine ⟨59654029265627566449904955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39769352843751710966603303 59654029265627566449904955)
  ·
    refine ⟨89481043898441349674857433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59654029265627566449904955 89481043898441349674857433)
    ·
      refine ⟨67110782923831012256143075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89481043898441349674857433 67110782923831012256143075)
      ·
        refine ⟨100666174385746518384214613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67110782923831012256143075 100666174385746518384214613)
        ·
          refine ⟨1179681731082967012315015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 100666174385746518384214613 1179681731082967012315015)
          ·
            refine ⟨1769522596624450518472523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1179681731082967012315015 1769522596624450518472523)
            ·
              refine ⟨2654283894936675777708785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1769522596624450518472523 2654283894936675777708785)
              ·
                refine ⟨1990712921202506833281589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2654283894936675777708785 1990712921202506833281589)
                ·
                  refine ⟨186629336362735015620149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1990712921202506833281589 186629336362735015620149)
                  ·
                    rfl

theorem cell22_1635567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 5].length) (baseStart_1635567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635567 prefixEnd_1635567 := by exact prefixLift 1635567
  have htrace : WordTrace (prefixWord ++ tailWord_1635567) baseStart_1635567 baseEnd_1635567 := by
    simpa [prefixWord, tailWord_1635567, baseEnd_1635567] using wordTrace_append hprefix tailTrace_1635567
  have hstable : (prefixWord ++ tailWord_1635567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635567).length < 2 ^ (prefixWord ++ tailWord_1635567).sum := by decide
  have hdescent : baseEnd_1635567 < baseStart_1635567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635576 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 2, 9]
def baseStart_1635576 : Nat := 118140960795 + 1635576 * 2 ^ 59
def prefixEnd_1635576 : Nat := 4983230072969 + 3 ^ 40 * 1635576 * 2
def baseEnd_1635576 : Nat := 559891089972132023385419

theorem tailTrace_1635576 : CollatzResearch.WordTrace tailWord_1635576 prefixEnd_1635576 559891089972132023385419 := by
  unfold tailWord_1635576
  simp only [CollatzResearch.WordTrace]
  refine ⟨29827178761297480493491291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39769571681729973991321721 29827178761297480493491291)
  ·
    refine ⟨44740768141946220740236937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29827178761297480493491291 44740768141946220740236937)
    ·
      refine ⟨33555576106459665555177703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44740768141946220740236937 33555576106459665555177703)
      ·
        refine ⟨50333364159689498332766555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33555576106459665555177703 50333364159689498332766555)
        ·
          refine ⟨75500046239534247499149833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50333364159689498332766555 75500046239534247499149833)
          ·
            refine ⟨56625034679650685624362375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75500046239534247499149833 56625034679650685624362375)
            ·
              refine ⟨84937552019476028436543563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56625034679650685624362375 84937552019476028436543563)
              ·
                refine ⟨127406328029214042654815345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84937552019476028436543563 127406328029214042654815345)
                ·
                  refine ⟨95554746021910531991111509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127406328029214042654815345 95554746021910531991111509)
                  ·
                    refine ⟨559891089972132023385419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 95554746021910531991111509 559891089972132023385419)
                    ·
                      rfl

theorem cell22_1635576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_1635576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635576 prefixEnd_1635576 := by exact prefixLift 1635576
  have htrace : WordTrace (prefixWord ++ tailWord_1635576) baseStart_1635576 baseEnd_1635576 := by
    simpa [prefixWord, tailWord_1635576, baseEnd_1635576] using wordTrace_append hprefix tailTrace_1635576
  have hstable : (prefixWord ++ tailWord_1635576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635576).length < 2 ^ (prefixWord ++ tailWord_1635576).sum := by decide
  have hdescent : baseEnd_1635576 < baseStart_1635576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635578 : List Nat := [3, 1, 1, 1, 1, 4, 4, 1, 6]
def baseStart_1635578 : Nat := 118140960795 + 1635578 * 2 ^ 59
def prefixEnd_1635578 : Nat := 4983230072969 + 3 ^ 40 * 1635578 * 2
def baseEnd_1635578 : Nat := 186630591537668228278471

theorem tailTrace_1635578 : CollatzResearch.WordTrace tailWord_1635578 prefixEnd_1635578 186630591537668228278471 := by
  unfold tailWord_1635578
  simp only [CollatzResearch.WordTrace]
  refine ⟨14913607617146928832138847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39769620312391810219036925 14913607617146928832138847)
  ·
    refine ⟨22370411425720393248208271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14913607617146928832138847 22370411425720393248208271)
    ·
      refine ⟨33555617138580589872312407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22370411425720393248208271 33555617138580589872312407)
      ·
        refine ⟨50333425707870884808468611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33555617138580589872312407 50333425707870884808468611)
        ·
          refine ⟨75500138561806327212702917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50333425707870884808468611 75500138561806327212702917)
          ·
            refine ⟨14156275980338686352381797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75500138561806327212702917 14156275980338686352381797)
            ·
              refine ⟨2654301746313503691071587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14156275980338686352381797 2654301746313503691071587)
              ·
                refine ⟨3981452619470255536607381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2654301746313503691071587 3981452619470255536607381)
                ·
                  refine ⟨186630591537668228278471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3981452619470255536607381 186630591537668228278471)
                  ·
                    rfl

theorem cell22_1635578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_1635578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635578 prefixEnd_1635578 := by exact prefixLift 1635578
  have htrace : WordTrace (prefixWord ++ tailWord_1635578) baseStart_1635578 baseEnd_1635578 := by
    simpa [prefixWord, tailWord_1635578, baseEnd_1635578] using wordTrace_append hprefix tailTrace_1635578
  have hstable : (prefixWord ++ tailWord_1635578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635578).length < 2 ^ (prefixWord ++ tailWord_1635578).sum := by decide
  have hdescent : baseEnd_1635578 < baseStart_1635578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635608 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 1, 6]
def baseStart_1635608 : Nat := 118140960795 + 1635608 * 2 ^ 59
def prefixEnd_1635608 : Nat := 4983230072969 + 3 ^ 40 * 1635608 * 2
def baseEnd_1635608 : Nat := 559902044226094606585321

theorem tailTrace_1635608 : CollatzResearch.WordTrace tailWord_1635608 prefixEnd_1635608 559902044226094606585321 := by
  unfold tailWord_1635608
  simp only [CollatzResearch.WordTrace]
  refine ⟨29827762329239515226073739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39770349772319353634764985 29827762329239515226073739)
  ·
    refine ⟨44741643493859272839110609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29827762329239515226073739 44741643493859272839110609)
    ·
      refine ⟨33556232620394454629332957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44741643493859272839110609 33556232620394454629332957)
      ·
        refine ⟨12583587232647920485999859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33556232620394454629332957 12583587232647920485999859)
        ·
          refine ⟨18875380848971880728999789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12583587232647920485999859 18875380848971880728999789)
          ·
            refine ⟨7078267818364455273374921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18875380848971880728999789 7078267818364455273374921)
            ·
              refine ⟨5308700863773341455031191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7078267818364455273374921 5308700863773341455031191)
              ·
                refine ⟨7963051295660012182546787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5308700863773341455031191 7963051295660012182546787)
                ·
                  refine ⟨11944576943490018273820181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7963051295660012182546787 11944576943490018273820181)
                  ·
                    refine ⟨559902044226094606585321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11944576943490018273820181 559902044226094606585321)
                    ·
                      rfl

theorem cell22_1635608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_1635608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635608 prefixEnd_1635608 := by exact prefixLift 1635608
  have htrace : WordTrace (prefixWord ++ tailWord_1635608) baseStart_1635608 baseEnd_1635608 := by
    simpa [prefixWord, tailWord_1635608, baseEnd_1635608] using wordTrace_append hprefix tailTrace_1635608
  have hstable : (prefixWord ++ tailWord_1635608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635608).length < 2 ^ (prefixWord ++ tailWord_1635608).sum := by decide
  have hdescent : baseEnd_1635608 < baseStart_1635608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635610 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 4, 3]
def baseStart_1635610 : Nat := 118140960795 + 1635610 * 2 ^ 59
def prefixEnd_1635610 : Nat := 4983230072969 + 3 ^ 40 * 1635610 * 2
def baseEnd_1635610 : Nat := 559902728866967268035315

theorem tailTrace_1635610 : CollatzResearch.WordTrace tailWord_1635610 prefixEnd_1635610 559902728866967268035315 := by
  unfold tailWord_1635610
  simp only [CollatzResearch.WordTrace]
  refine ⟨14913899401117946198430071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39770398402981189862480189 14913899401117946198430071)
  ·
    refine ⟨22370849101676919297645107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14913899401117946198430071 22370849101676919297645107)
    ·
      refine ⟨33556273652515378946467661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22370849101676919297645107 33556273652515378946467661)
      ·
        refine ⟨12583602619693267104925373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33556273652515378946467661 12583602619693267104925373)
        ·
          refine ⟨4718850982384975164347015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12583602619693267104925373 4718850982384975164347015)
          ·
            refine ⟨7078276473577462746520523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4718850982384975164347015 7078276473577462746520523)
            ·
              refine ⟨10617414710366194119780785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7078276473577462746520523 10617414710366194119780785)
              ·
                refine ⟨7963061032774645589835589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10617414710366194119780785 7963061032774645589835589)
                ·
                  refine ⟨1493073943645246048094173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7963061032774645589835589 1493073943645246048094173)
                  ·
                    refine ⟨559902728866967268035315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1493073943645246048094173 559902728866967268035315)
                    ·
                      rfl

theorem cell22_1635610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_1635610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635610 prefixEnd_1635610 := by exact prefixLift 1635610
  have htrace : WordTrace (prefixWord ++ tailWord_1635610) baseStart_1635610 baseEnd_1635610 := by
    simpa [prefixWord, tailWord_1635610, baseEnd_1635610] using wordTrace_append hprefix tailTrace_1635610
  have hstable : (prefixWord ++ tailWord_1635610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635610).length < 2 ^ (prefixWord ++ tailWord_1635610).sum := by decide
  have hdescent : baseEnd_1635610 < baseStart_1635610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635644 : List Nat := [2, 2, 2, 2, 1, 5, 2, 1, 2, 3]
def baseStart_1635644 : Nat := 118140960795 + 1635644 * 2 ^ 59
def prefixEnd_1635644 : Nat := 4983230072969 + 3 ^ 40 * 1635644 * 2
def baseEnd_1635644 : Nat := 559914367761802512685211

theorem tailTrace_1635644 : CollatzResearch.WordTrace tailWord_1635644 prefixEnd_1635644 559914367761802512685211 := by
  unfold tailWord_1635644
  simp only [CollatzResearch.WordTrace]
  refine ⟨29828418843174304300228993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39771225124232405733638657 29828418843174304300228993)
  ·
    refine ⟨22371314132380728225171745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29828418843174304300228993 22371314132380728225171745)
    ·
      refine ⟨16778485599285546168878809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22371314132380728225171745 16778485599285546168878809)
      ·
        refine ⟨12583864199464159626659107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16778485599285546168878809 12583864199464159626659107)
        ·
          refine ⟨18875796299196239439988661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12583864199464159626659107 18875796299196239439988661)
          ·
            refine ⟨1769605903049647447498937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18875796299196239439988661 1769605903049647447498937)
            ·
              refine ⟨1327204427287235585624203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1769605903049647447498937 1327204427287235585624203)
              ·
                refine ⟨1990806640930853378436305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1327204427287235585624203 1990806640930853378436305)
                ·
                  refine ⟨1493104980698140033827229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1990806640930853378436305 1493104980698140033827229)
                  ·
                    refine ⟨559914367761802512685211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1493104980698140033827229 559914367761802512685211)
                    ·
                      rfl

theorem cell22_1635644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_1635644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635644 prefixEnd_1635644 := by exact prefixLift 1635644
  have htrace : WordTrace (prefixWord ++ tailWord_1635644) baseStart_1635644 baseEnd_1635644 := by
    simpa [prefixWord, tailWord_1635644, baseEnd_1635644] using wordTrace_append hprefix tailTrace_1635644
  have hstable : (prefixWord ++ tailWord_1635644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635644).length < 2 ^ (prefixWord ++ tailWord_1635644).sum := by decide
  have hdescent : baseEnd_1635644 < baseStart_1635644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635672 : List Nat := [2, 1, 2, 2, 1, 1, 4, 5, 1, 3]
def baseStart_1635672 : Nat := 118140960795 + 1635672 * 2 ^ 59
def prefixEnd_1635672 : Nat := 4983230072969 + 3 ^ 40 * 1635672 * 2
def baseEnd_1635672 : Nat := 559923952734019772985125

theorem tailTrace_1635672 : CollatzResearch.WordTrace tailWord_1635672 prefixEnd_1635672 559923952734019772985125 := by
  unfold tailWord_1635672
  simp only [CollatzResearch.WordTrace]
  refine ⟨29828929465123584691238635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39771905953498112921651513 29828929465123584691238635)
  ·
    refine ⟨44743394197685377036857953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29828929465123584691238635 44743394197685377036857953)
    ·
      refine ⟨33557545648264032777643465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44743394197685377036857953 33557545648264032777643465)
      ·
        refine ⟨25168159236198024583232599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33557545648264032777643465 25168159236198024583232599)
        ·
          refine ⟨37752238854297036874848899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25168159236198024583232599 37752238854297036874848899)
          ·
            refine ⟨56628358281445555312273349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37752238854297036874848899 56628358281445555312273349)
            ·
              refine ⟨10617817177771041621051253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56628358281445555312273349 10617817177771041621051253)
              ·
                refine ⟨995420360416035151973555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10617817177771041621051253 995420360416035151973555)
                ·
                  refine ⟨1493130540624052727960333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 995420360416035151973555 1493130540624052727960333)
                  ·
                    refine ⟨559923952734019772985125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1493130540624052727960333 559923952734019772985125)
                    ·
                      rfl

theorem cell22_1635672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 1, 3].length) (baseStart_1635672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635672 prefixEnd_1635672 := by exact prefixLift 1635672
  have htrace : WordTrace (prefixWord ++ tailWord_1635672) baseStart_1635672 baseEnd_1635672 := by
    simpa [prefixWord, tailWord_1635672, baseEnd_1635672] using wordTrace_append hprefix tailTrace_1635672
  have hstable : (prefixWord ++ tailWord_1635672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635672).length < 2 ^ (prefixWord ++ tailWord_1635672).sum := by decide
  have hdescent : baseEnd_1635672 < baseStart_1635672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635685 : List Nat := [1, 3, 1, 3, 1, 2, 4, 2, 5]
def baseStart_1635685 : Nat := 118140960795 + 1635685 * 2 ^ 59
def prefixEnd_1635685 : Nat := 4983230072969 + 3 ^ 40 * 1635685 * 2
def baseEnd_1635685 : Nat := 186642800966564024136695

theorem tailTrace_1635685 : CollatzResearch.WordTrace tailWord_1635685 prefixEnd_1635685 186642800966564024136695 := by
  unfold tailWord_1635685
  simp only [CollatzResearch.WordTrace]
  refine ⟨59658333079200072602700509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39772222052800048401800339 59658333079200072602700509)
  ·
    refine ⟨22371874904700027226012691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59658333079200072602700509 22371874904700027226012691)
    ·
      refine ⟨33557812357050040839019037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22371874904700027226012691 33557812357050040839019037)
      ·
        refine ⟨12584179633893765314632139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33557812357050040839019037 12584179633893765314632139)
        ·
          refine ⟨18876269450840647971948209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12584179633893765314632139 18876269450840647971948209)
          ·
            refine ⟨14157202088130485978961157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18876269450840647971948209 14157202088130485978961157)
            ·
              refine ⟨2654475391524466121055217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14157202088130485978961157 2654475391524466121055217)
              ·
                refine ⟨1990856543643349590791413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2654475391524466121055217 1990856543643349590791413)
                ·
                  refine ⟨186642800966564024136695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1990856543643349590791413 186642800966564024136695)
                  ·
                    rfl

theorem cell22_1635685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_1635685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635685 prefixEnd_1635685 := by exact prefixLift 1635685
  have htrace : WordTrace (prefixWord ++ tailWord_1635685) baseStart_1635685 baseEnd_1635685 := by
    simpa [prefixWord, tailWord_1635685, baseEnd_1635685] using wordTrace_append hprefix tailTrace_1635685
  have hstable : (prefixWord ++ tailWord_1635685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635685).length < 2 ^ (prefixWord ++ tailWord_1635685).sum := by decide
  have hdescent : baseEnd_1635685 < baseStart_1635685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635715 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 3, 4]
def baseStart_1635715 : Nat := 118140960795 + 1635715 * 2 ^ 59
def prefixEnd_1635715 : Nat := 4983230072969 + 3 ^ 40 * 1635715 * 2
def baseEnd_1635715 : Nat := 559938672512781994159993

theorem tailTrace_1635715 : CollatzResearch.WordTrace tailWord_1635715 prefixEnd_1635715 559938672512781994159993 := by
  unfold tailWord_1635715
  simp only [CollatzResearch.WordTrace]
  refine ⟨59659427269091387726292599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39772951512727591817528399 59659427269091387726292599)
  ·
    refine ⟨89489140903637081589438899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59659427269091387726292599 89489140903637081589438899)
    ·
      refine ⟨134233711355455622384158349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89489140903637081589438899 134233711355455622384158349)
      ·
        refine ⟨50337641758295858394059381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134233711355455622384158349 50337641758295858394059381)
        ·
          refine ⟨4719153914840236724443067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50337641758295858394059381 4719153914840236724443067)
          ·
            refine ⟨7078730872260355086664601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4719153914840236724443067 7078730872260355086664601)
            ·
              refine ⟨5309048154195266314998451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7078730872260355086664601 5309048154195266314998451)
              ·
                refine ⟨7963572231292899472497677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5309048154195266314998451 7963572231292899472497677)
                ·
                  refine ⟨2986339586734837302186629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7963572231292899472497677 2986339586734837302186629)
                  ·
                    refine ⟨559938672512781994159993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2986339586734837302186629 559938672512781994159993)
                    ·
                      rfl

theorem cell22_1635715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 4].length) (baseStart_1635715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635715 prefixEnd_1635715 := by exact prefixLift 1635715
  have htrace : WordTrace (prefixWord ++ tailWord_1635715) baseStart_1635715 baseEnd_1635715 := by
    simpa [prefixWord, tailWord_1635715, baseEnd_1635715] using wordTrace_append hprefix tailTrace_1635715
  have hstable : (prefixWord ++ tailWord_1635715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635715).length < 2 ^ (prefixWord ++ tailWord_1635715).sum := by decide
  have hdescent : baseEnd_1635715 < baseStart_1635715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635854 : List Nat := [4, 1, 1, 2, 4, 1, 2, 2, 5]
def baseStart_1635854 : Nat := 118140960795 + 1635854 * 2 ^ 59
def prefixEnd_1635854 : Nat := 4983230072969 + 3 ^ 40 * 1635854 * 2
def baseEnd_1635854 : Nat := 186662085017810654978189

theorem tailTrace_1635854 : CollatzResearch.WordTrace tailWord_1635854 prefixEnd_1635854 186662085017810654978189 := by
  unfold tailWord_1635854
  simp only [CollatzResearch.WordTrace]
  refine ⟨7458062126948476808200327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39776331343725209643735077 7458062126948476808200327)
  ·
    refine ⟨11187093190422715212300491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7458062126948476808200327 11187093190422715212300491)
    ·
      refine ⟨16780639785634072818450737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11187093190422715212300491 16780639785634072818450737)
      ·
        refine ⟨12585479839225554613838053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16780639785634072818450737 12585479839225554613838053)
        ·
          refine ⟨2359777469854791490094635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12585479839225554613838053 2359777469854791490094635)
          ·
            refine ⟨3539666204782187235141953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2359777469854791490094635 3539666204782187235141953)
            ·
              refine ⟨2654749653586640426356465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3539666204782187235141953 2654749653586640426356465)
              ·
                refine ⟨1991062240189980319767349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2654749653586640426356465 1991062240189980319767349)
                ·
                  refine ⟨186662085017810654978189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1991062240189980319767349 186662085017810654978189)
                  ·
                    rfl

theorem cell22_1635854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_1635854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635854 prefixEnd_1635854 := by exact prefixLift 1635854
  have htrace : WordTrace (prefixWord ++ tailWord_1635854) baseStart_1635854 baseEnd_1635854 := by
    simpa [prefixWord, tailWord_1635854, baseEnd_1635854] using wordTrace_append hprefix tailTrace_1635854
  have hstable : (prefixWord ++ tailWord_1635854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635854).length < 2 ^ (prefixWord ++ tailWord_1635854).sum := by decide
  have hdescent : baseEnd_1635854 < baseStart_1635854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635882 : List Nat := [3, 1, 4, 1, 1, 1, 3, 2, 6]
def baseStart_1635882 : Nat := 118140960795 + 1635882 * 2 ^ 59
def prefixEnd_1635882 : Nat := 4983230072969 + 3 ^ 40 * 1635882 * 2
def baseEnd_1635882 : Nat := 186665280008549741744827

theorem tailTrace_1635882 : CollatzResearch.WordTrace tailWord_1635882 prefixEnd_1635882 186665280008549741744827 := by
  unfold tailWord_1635882
  simp only [CollatzResearch.WordTrace]
  refine ⟨14916379564871593811905475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39777012172990916831747933 14916379564871593811905475)
  ·
    refine ⟨22374569347307390717858213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14916379564871593811905475 22374569347307390717858213)
    ·
      refine ⟨4195231752620135759598415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22374569347307390717858213 4195231752620135759598415)
      ·
        refine ⟨6292847628930203639397623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4195231752620135759598415 6292847628930203639397623)
        ·
          refine ⟨9439271443395305459096435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6292847628930203639397623 9439271443395305459096435)
          ·
            refine ⟨14158907165092958188644653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9439271443395305459096435 14158907165092958188644653)
            ·
              refine ⟨5309590186909859320741745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14158907165092958188644653 5309590186909859320741745)
              ·
                refine ⟨3982192640182394490556309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5309590186909859320741745 3982192640182394490556309)
                ·
                  refine ⟨186665280008549741744827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3982192640182394490556309 186665280008549741744827)
                  ·
                    rfl

theorem cell22_1635882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_1635882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635882 prefixEnd_1635882 := by exact prefixLift 1635882
  have htrace : WordTrace (prefixWord ++ tailWord_1635882) baseStart_1635882 baseEnd_1635882 := by
    simpa [prefixWord, tailWord_1635882, baseEnd_1635882] using wordTrace_append hprefix tailTrace_1635882
  have hstable : (prefixWord ++ tailWord_1635882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635882).length < 2 ^ (prefixWord ++ tailWord_1635882).sum := by decide
  have hdescent : baseEnd_1635882 < baseStart_1635882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635897 : List Nat := [1, 2, 1, 5, 1, 2, 2, 2, 1, 5]
def baseStart_1635897 : Nat := 118140960795 + 1635897 * 2 ^ 59
def prefixEnd_1635897 : Nat := 4983230072969 + 3 ^ 40 * 1635897 * 2
def baseEnd_1635897 : Nat := 560000974832194186109435

theorem tailTrace_1635897 : CollatzResearch.WordTrace tailWord_1635897 prefixEnd_1635897 560000974832194186109435 := by
  unfold tailWord_1635897
  simp only [CollatzResearch.WordTrace]
  refine ⟨59666065354432032809417945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39777376902954688539611963 59666065354432032809417945)
  ·
    refine ⟨44749549015824024607063459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59666065354432032809417945 44749549015824024607063459)
    ·
      refine ⟨67124323523736036910595189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44749549015824024607063459 67124323523736036910595189)
      ·
        refine ⟨6292905330350253460368299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67124323523736036910595189 6292905330350253460368299)
        ·
          refine ⟨9439357995525380190552449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6292905330350253460368299 9439357995525380190552449)
          ·
            refine ⟨7079518496644035142914337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9439357995525380190552449 7079518496644035142914337)
            ·
              refine ⟨5309638872483026357185753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7079518496644035142914337 5309638872483026357185753)
              ·
                refine ⟨3982229154362269767889315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5309638872483026357185753 3982229154362269767889315)
                ·
                  refine ⟨5973343731543404651833973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3982229154362269767889315 5973343731543404651833973)
                  ·
                    refine ⟨560000974832194186109435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5973343731543404651833973 560000974832194186109435)
                    ·
                      rfl

theorem cell22_1635897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 5].length) (baseStart_1635897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635897 prefixEnd_1635897 := by exact prefixLift 1635897
  have htrace : WordTrace (prefixWord ++ tailWord_1635897) baseStart_1635897 baseEnd_1635897 := by
    simpa [prefixWord, tailWord_1635897, baseEnd_1635897] using wordTrace_append hprefix tailTrace_1635897
  have hstable : (prefixWord ++ tailWord_1635897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635897).length < 2 ^ (prefixWord ++ tailWord_1635897).sum := by decide
  have hdescent : baseEnd_1635897 < baseStart_1635897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1635944 : List Nat := [2, 1, 4, 3, 1, 1, 4, 6]
def baseStart_1635944 : Nat := 118140960795 + 1635944 * 2 ^ 59
def prefixEnd_1635944 : Nat := 4983230072969 + 3 ^ 40 * 1635944 * 2
def baseEnd_1635944 : Nat := 62224118210300192242699

theorem tailTrace_1635944 : CollatzResearch.WordTrace tailWord_1635944 prefixEnd_1635944 62224118210300192242699 := by
  unfold tailWord_1635944
  simp only [CollatzResearch.WordTrace]
  refine ⟨29833889792630879918189443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39778519723507839890919257 29833889792630879918189443)
  ·
    refine ⟨44750834688946319877284165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29833889792630879918189443 44750834688946319877284165)
    ·
      refine ⟨8390781504177434976990781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44750834688946319877284165 8390781504177434976990781)
      ·
        refine ⟨3146543064066538116371543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8390781504177434976990781 3146543064066538116371543)
        ·
          refine ⟨4719814596099807174557315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3146543064066538116371543 4719814596099807174557315)
          ·
            refine ⟨7079721894149710761835973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4719814596099807174557315 7079721894149710761835973)
            ·
              refine ⟨1327447855153070767844245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7079721894149710761835973 1327447855153070767844245)
              ·
                refine ⟨62224118210300192242699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1327447855153070767844245 62224118210300192242699)
                ·
                  rfl

theorem cell22_1635944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 6].length) (baseStart_1635944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1635944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1635944 prefixEnd_1635944 := by exact prefixLift 1635944
  have htrace : WordTrace (prefixWord ++ tailWord_1635944) baseStart_1635944 baseEnd_1635944 := by
    simpa [prefixWord, tailWord_1635944, baseEnd_1635944] using wordTrace_append hprefix tailTrace_1635944
  have hstable : (prefixWord ++ tailWord_1635944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1635944).length < 2 ^ (prefixWord ++ tailWord_1635944).sum := by decide
  have hdescent : baseEnd_1635944 < baseStart_1635944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1635944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636032 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 3, 5]
def baseStart_1636032 : Nat := 118140960795 + 1636032 * 2 ^ 59
def prefixEnd_1636032 : Nat := 4983230072969 + 3 ^ 40 * 1636032 * 2
def baseEnd_1636032 : Nat := 560047188091098833984021

theorem tailTrace_1636032 : CollatzResearch.WordTrace tailWord_1636032 prefixEnd_1636032 560047188091098833984021 := by
  unfold tailWord_1636032
  simp only [CollatzResearch.WordTrace]
  refine ⟨29835494604471475432791175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39780659472628633910388233 29835494604471475432791175)
  ·
    refine ⟨44753241906707213149186763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29835494604471475432791175 44753241906707213149186763)
    ·
      refine ⟨67129862860060819723780145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44753241906707213149186763 67129862860060819723780145)
      ·
        refine ⟨50347397145045614792835109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67129862860060819723780145 50347397145045614792835109)
        ·
          refine ⟨9440136964696052773656583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50347397145045614792835109 9440136964696052773656583)
          ·
            refine ⟨14160205447044079160484875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9440136964696052773656583 14160205447044079160484875)
            ·
              refine ⟨21240308170566118740727313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14160205447044079160484875 21240308170566118740727313)
              ·
                refine ⟨15930231127924589055545485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21240308170566118740727313 15930231127924589055545485)
                ·
                  refine ⟨5973836672971720895829557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15930231127924589055545485 5973836672971720895829557)
                  ·
                    refine ⟨560047188091098833984021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5973836672971720895829557 560047188091098833984021)
                    ·
                      rfl

theorem cell22_1636032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_1636032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636032 prefixEnd_1636032 := by exact prefixLift 1636032
  have htrace : WordTrace (prefixWord ++ tailWord_1636032) baseStart_1636032 baseEnd_1636032 := by
    simpa [prefixWord, tailWord_1636032, baseEnd_1636032] using wordTrace_append hprefix tailTrace_1636032
  have hstable : (prefixWord ++ tailWord_1636032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636032).length < 2 ^ (prefixWord ++ tailWord_1636032).sum := by decide
  have hdescent : baseEnd_1636032 < baseStart_1636032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636038 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_1636038 : Nat := 118140960795 + 1636038 * 2 ^ 59
def prefixEnd_1636038 : Nat := 4983230072969 + 3 ^ 40 * 1636038 * 2
def baseEnd_1636038 : Nat := 560049242013716818334003

theorem tailTrace_1636038 : CollatzResearch.WordTrace tailWord_1636038 prefixEnd_1636038 560049242013716818334003 := by
  unfold tailWord_1636038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1864725251466287934071899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39780805364614142593533845 1864725251466287934071899)
  ·
    refine ⟨2797087877199431901107849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1864725251466287934071899 2797087877199431901107849)
    ·
      refine ⟨2097815907899573925830887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2797087877199431901107849 2097815907899573925830887)
      ·
        refine ⟨3146723861849360888746331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2097815907899573925830887 3146723861849360888746331)
        ·
          refine ⟨4720085792774041333119497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3146723861849360888746331 4720085792774041333119497)
          ·
            refine ⟨3540064344580530999839623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4720085792774041333119497 3540064344580530999839623)
            ·
              refine ⟨5310096516870796499759435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3540064344580530999839623 5310096516870796499759435)
              ·
                refine ⟨7965144775306194749639153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5310096516870796499759435 7965144775306194749639153)
                ·
                  refine ⟨5973858581479646062229365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7965144775306194749639153 5973858581479646062229365)
                  ·
                    refine ⟨560049242013716818334003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5973858581479646062229365 560049242013716818334003)
                    ·
                      rfl

theorem cell22_1636038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_1636038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636038 prefixEnd_1636038 := by exact prefixLift 1636038
  have htrace : WordTrace (prefixWord ++ tailWord_1636038) baseStart_1636038 baseEnd_1636038 := by
    simpa [prefixWord, tailWord_1636038, baseEnd_1636038] using wordTrace_append hprefix tailTrace_1636038
  have hstable : (prefixWord ++ tailWord_1636038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636038).length < 2 ^ (prefixWord ++ tailWord_1636038).sum := by decide
  have hdescent : baseEnd_1636038 < baseStart_1636038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636047 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 4, 4]
def baseStart_1636047 : Nat := 118140960795 + 1636047 * 2 ^ 59
def prefixEnd_1636047 : Nat := 4983230072969 + 3 ^ 40 * 1636047 * 2
def baseEnd_1636047 : Nat := 560052322897643794858975

theorem tailTrace_1636047 : CollatzResearch.WordTrace tailWord_1636047 prefixEnd_1636047 560052322897643794858975 := by
  unfold tailWord_1636047
  simp only [CollatzResearch.WordTrace]
  refine ⟨59671536303888608427378395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39781024202592405618252263 59671536303888608427378395)
  ·
    refine ⟨89507304455832912641067593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59671536303888608427378395 89507304455832912641067593)
    ·
      refine ⟨67130478341874684480800695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89507304455832912641067593 67130478341874684480800695)
      ·
        refine ⟨100695717512812026721201043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67130478341874684480800695 100695717512812026721201043)
        ·
          refine ⟨151043576269218040081801565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100695717512812026721201043 151043576269218040081801565)
          ·
            refine ⟨56641341100956765030675587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151043576269218040081801565 56641341100956765030675587)
            ·
              refine ⟨84962011651435147546013381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56641341100956765030675587 84962011651435147546013381)
              ·
                refine ⟨15930377184644090164877509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84962011651435147546013381 15930377184644090164877509)
                ·
                  refine ⟨2986945722120766905914533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15930377184644090164877509 2986945722120766905914533)
                  ·
                    refine ⟨560052322897643794858975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2986945722120766905914533 560052322897643794858975)
                    ·
                      rfl

theorem cell22_1636047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 4].length) (baseStart_1636047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636047 prefixEnd_1636047 := by exact prefixLift 1636047
  have htrace : WordTrace (prefixWord ++ tailWord_1636047) baseStart_1636047 baseEnd_1636047 := by
    simpa [prefixWord, tailWord_1636047, baseEnd_1636047] using wordTrace_append hprefix tailTrace_1636047
  have hstable : (prefixWord ++ tailWord_1636047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636047).length < 2 ^ (prefixWord ++ tailWord_1636047).sum := by decide
  have hdescent : baseEnd_1636047 < baseStart_1636047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636049 : List Nat := [1, 2, 2, 1, 2, 5, 2, 1, 1, 5]
def baseStart_1636049 : Nat := 118140960795 + 1636049 * 2 ^ 59
def prefixEnd_1636049 : Nat := 4983230072969 + 3 ^ 40 * 1636049 * 2
def baseEnd_1636049 : Nat := 560053007538516456308969

theorem tailTrace_1636049 : CollatzResearch.WordTrace tailWord_1636049 prefixEnd_1636049 560053007538516456308969 := by
  unfold tailWord_1636049
  simp only [CollatzResearch.WordTrace]
  refine ⟨59671609249881362768951201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39781072833254241845967467 59671609249881362768951201)
  ·
    refine ⟨44753706937411022076713401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59671609249881362768951201 44753706937411022076713401)
    ·
      refine ⟨33565280203058266557535051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44753706937411022076713401 33565280203058266557535051)
      ·
        refine ⟨50347920304587399836302577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33565280203058266557535051 50347920304587399836302577)
        ·
          refine ⟨37760940228440549877226933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50347920304587399836302577 37760940228440549877226933)
          ·
            refine ⟨3540088146416301550990025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37760940228440549877226933 3540088146416301550990025)
            ·
              refine ⟨2655066109812226163242519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3540088146416301550990025 2655066109812226163242519)
              ·
                refine ⟨3982599164718339244863779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2655066109812226163242519 3982599164718339244863779)
                ·
                  refine ⟨5973898747077508867295669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3982599164718339244863779 5973898747077508867295669)
                  ·
                    refine ⟨560053007538516456308969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5973898747077508867295669 560053007538516456308969)
                    ·
                      rfl

theorem cell22_1636049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_1636049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636049 prefixEnd_1636049 := by exact prefixLift 1636049
  have htrace : WordTrace (prefixWord ++ tailWord_1636049) baseStart_1636049 baseEnd_1636049 := by
    simpa [prefixWord, tailWord_1636049, baseEnd_1636049] using wordTrace_append hprefix tailTrace_1636049
  have hstable : (prefixWord ++ tailWord_1636049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636049).length < 2 ^ (prefixWord ++ tailWord_1636049).sum := by decide
  have hdescent : baseEnd_1636049 < baseStart_1636049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636064 : List Nat := [2, 1, 1, 3, 1, 2, 5, 1, 2, 4]
def baseStart_1636064 : Nat := 118140960795 + 1636064 * 2 ^ 59
def prefixEnd_1636064 : Nat := 4983230072969 + 3 ^ 40 * 1636064 * 2
def baseEnd_1636064 : Nat := 560058142345061417183923

theorem tailTrace_1636064 : CollatzResearch.WordTrace tailWord_1636064 prefixEnd_1636064 560058142345061417183923 := by
  unfold tailWord_1636064
  simp only [CollatzResearch.WordTrace]
  refine ⟨29836078172413510165373623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39781437563218013553831497 29836078172413510165373623)
  ·
    refine ⟨44754117258620265248060435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29836078172413510165373623 44754117258620265248060435)
    ·
      refine ⟨67131175887930397872090653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44754117258620265248060435 67131175887930397872090653)
      ·
        refine ⟨25174190957973899202033995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67131175887930397872090653 25174190957973899202033995)
        ·
          refine ⟨37761286436960848803050993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25174190957973899202033995 37761286436960848803050993)
          ·
            refine ⟨28320964827720636602288245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37761286436960848803050993 28320964827720636602288245)
            ·
              refine ⟨2655090452598809681464523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28320964827720636602288245 2655090452598809681464523)
              ·
                refine ⟨3982635678898214522196785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2655090452598809681464523 3982635678898214522196785)
                ·
                  refine ⟨2986976759173660891647589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3982635678898214522196785 2986976759173660891647589)
                  ·
                    refine ⟨560058142345061417183923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2986976759173660891647589 560058142345061417183923)
                    ·
                      rfl

theorem cell22_1636064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 2, 4].length) (baseStart_1636064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636064 prefixEnd_1636064 := by exact prefixLift 1636064
  have htrace : WordTrace (prefixWord ++ tailWord_1636064) baseStart_1636064 baseEnd_1636064 := by
    simpa [prefixWord, tailWord_1636064, baseEnd_1636064] using wordTrace_append hprefix tailTrace_1636064
  have hstable : (prefixWord ++ tailWord_1636064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636064).length < 2 ^ (prefixWord ++ tailWord_1636064).sum := by decide
  have hdescent : baseEnd_1636064 < baseStart_1636064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636145 : List Nat := [1, 2, 2, 3, 2, 3, 3, 2, 1, 3]
def baseStart_1636145 : Nat := 118140960795 + 1636145 * 2 ^ 59
def prefixEnd_1636145 : Nat := 4983230072969 + 3 ^ 40 * 1636145 * 2
def baseEnd_1636145 : Nat := 560085870300404205908675

theorem tailTrace_1636145 : CollatzResearch.WordTrace tailWord_1636145 prefixEnd_1636145 560085870300404205908675 := by
  unfold tailWord_1636145
  simp only [CollatzResearch.WordTrace]
  refine ⟨59675110657533571164445889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39783407105022380776297259 59675110657533571164445889)
  ·
    refine ⟨44756332993150178373334417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59675110657533571164445889 44756332993150178373334417)
    ·
      refine ⟨33567249744862633780000813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44756332993150178373334417 33567249744862633780000813)
      ·
        refine ⟨12587718654323487667500305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33567249744862633780000813 12587718654323487667500305)
        ·
          refine ⟨9440788990742615750625229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12587718654323487667500305 9440788990742615750625229)
          ·
            refine ⟨3540295871528480906484461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9440788990742615750625229 3540295871528480906484461)
            ·
              refine ⟨1327610951823180339931673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3540295871528480906484461 1327610951823180339931673)
              ·
                refine ⟨995708213867385254948755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1327610951823180339931673 995708213867385254948755)
                ·
                  refine ⟨1493562320801077882423133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 995708213867385254948755 1493562320801077882423133)
                  ·
                    refine ⟨560085870300404205908675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1493562320801077882423133 560085870300404205908675)
                    ·
                      rfl

theorem cell22_1636145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 1, 3].length) (baseStart_1636145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636145 prefixEnd_1636145 := by exact prefixLift 1636145
  have htrace : WordTrace (prefixWord ++ tailWord_1636145) baseStart_1636145 baseEnd_1636145 := by
    simpa [prefixWord, tailWord_1636145, baseEnd_1636145] using wordTrace_append hprefix tailTrace_1636145
  have hstable : (prefixWord ++ tailWord_1636145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636145).length < 2 ^ (prefixWord ++ tailWord_1636145).sum := by decide
  have hdescent : baseEnd_1636145 < baseStart_1636145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636158 : List Nat := [4, 2, 1, 2, 2, 1, 4, 1, 5]
def baseStart_1636158 : Nat := 118140960795 + 1636158 * 2 ^ 59
def prefixEnd_1636158 : Nat := 4983230072969 + 3 ^ 40 * 1636158 * 2
def baseEnd_1636158 : Nat := 186696773488692168444545

theorem tailTrace_1636158 : CollatzResearch.WordTrace tailWord_1636158 prefixEnd_1636158 186696773488692168444545 := by
  unfold tailWord_1636158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7459448100810809298083641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39783723204324316256446085 7459448100810809298083641)
  ·
    refine ⟨5594586075608106973562731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7459448100810809298083641 5594586075608106973562731)
    ·
      refine ⟨8391879113412160460344097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5594586075608106973562731 8391879113412160460344097)
      ·
        refine ⟨6293909335059120345258073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8391879113412160460344097 6293909335059120345258073)
        ·
          refine ⟨4720432001294340258943555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6293909335059120345258073 4720432001294340258943555)
          ·
            refine ⟨7080648001941510388415333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4720432001294340258943555 7080648001941510388415333)
            ·
              refine ⟨1327621500364033197827875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7080648001941510388415333 1327621500364033197827875)
              ·
                refine ⟨1991432250546049796741813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1327621500364033197827875 1991432250546049796741813)
                ·
                  refine ⟨186696773488692168444545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1991432250546049796741813 186696773488692168444545)
                  ·
                    rfl

theorem cell22_1636158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_1636158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636158 prefixEnd_1636158 := by exact prefixLift 1636158
  have htrace : WordTrace (prefixWord ++ tailWord_1636158) baseStart_1636158 baseEnd_1636158 := by
    simpa [prefixWord, tailWord_1636158, baseEnd_1636158] using wordTrace_append hprefix tailTrace_1636158
  have hstable : (prefixWord ++ tailWord_1636158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636158).length < 2 ^ (prefixWord ++ tailWord_1636158).sum := by decide
  have hdescent : baseEnd_1636158 < baseStart_1636158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636186 : List Nat := [3, 1, 1, 2, 1, 3, 2, 5, 4]
def baseStart_1636186 : Nat := 118140960795 + 1636186 * 2 ^ 59
def prefixEnd_1636186 : Nat := 4983230072969 + 3 ^ 40 * 1636186 * 2
def baseEnd_1636186 : Nat := 186699968479431255211183

theorem tailTrace_1636186 : CollatzResearch.WordTrace tailWord_1636186 prefixEnd_1636186 186699968479431255211183 := by
  unfold tailWord_1636186
  simp only [CollatzResearch.WordTrace]
  refine ⟨14919151512596258791672103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39784404033590023444458941 14919151512596258791672103)
  ·
    refine ⟨22378727268894388187508155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14919151512596258791672103 22378727268894388187508155)
    ·
      refine ⟨33568090903341582281262233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22378727268894388187508155 33568090903341582281262233)
      ·
        refine ⟨25176068177506186710946675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33568090903341582281262233 25176068177506186710946675)
        ·
          refine ⟨37764102266259280066420013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25176068177506186710946675 37764102266259280066420013)
          ·
            refine ⟨14161538349847230024907505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37764102266259280066420013 14161538349847230024907505)
            ·
              refine ⟨10621153762385422518680629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14161538349847230024907505 10621153762385422518680629)
              ·
                refine ⟨995733165223633361126309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10621153762385422518680629 995733165223633361126309)
                ·
                  refine ⟨186699968479431255211183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 995733165223633361126309 186699968479431255211183)
                  ·
                    rfl

theorem cell22_1636186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 4].length) (baseStart_1636186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636186 prefixEnd_1636186 := by exact prefixLift 1636186
  have htrace : WordTrace (prefixWord ++ tailWord_1636186) baseStart_1636186 baseEnd_1636186 := by
    simpa [prefixWord, tailWord_1636186, baseEnd_1636186] using wordTrace_append hprefix tailTrace_1636186
  have hstable : (prefixWord ++ tailWord_1636186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636186).length < 2 ^ (prefixWord ++ tailWord_1636186).sum := by decide
  have hdescent : baseEnd_1636186 < baseStart_1636186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636263 : List Nat := [1, 1, 6, 1, 2, 1, 1, 3, 3, 3]
def baseStart_1636263 : Nat := 118140960795 + 1636263 * 2 ^ 59
def prefixEnd_1636263 : Nat := 4983230072969 + 3 ^ 40 * 1636263 * 2
def baseEnd_1636263 : Nat := 560126264111891231458313

theorem tailTrace_1636263 : CollatzResearch.WordTrace tailWord_1636263 prefixEnd_1636263 560126264111891231458313 := by
  unfold tailWord_1636263
  simp only [CollatzResearch.WordTrace]
  refine ⟨59679414471106077317241443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39786276314070718211494295 59679414471106077317241443)
  ·
    refine ⟨89519121706659115975862165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59679414471106077317241443 89519121706659115975862165)
    ·
      refine ⟨4196208829999646061368539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89519121706659115975862165 4196208829999646061368539)
      ·
        refine ⟨6294313244999469092052809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4196208829999646061368539 6294313244999469092052809)
        ·
          refine ⟨4720734933749601819039607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6294313244999469092052809 4720734933749601819039607)
          ·
            refine ⟨7081102400624402728559411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4720734933749601819039607 7081102400624402728559411)
            ·
              refine ⟨10621653600936604092839117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7081102400624402728559411 10621653600936604092839117)
              ·
                refine ⟨3983120100351226534814669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10621653600936604092839117 3983120100351226534814669)
                ·
                  refine ⟨1493670037631709950555501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3983120100351226534814669 1493670037631709950555501)
                  ·
                    refine ⟨560126264111891231458313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1493670037631709950555501 560126264111891231458313)
                    ·
                      rfl

theorem cell22_1636263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_1636263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636263 prefixEnd_1636263 := by exact prefixLift 1636263
  have htrace : WordTrace (prefixWord ++ tailWord_1636263) baseStart_1636263 baseEnd_1636263 := by
    simpa [prefixWord, tailWord_1636263, baseEnd_1636263] using wordTrace_append hprefix tailTrace_1636263
  have hstable : (prefixWord ++ tailWord_1636263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636263).length < 2 ^ (prefixWord ++ tailWord_1636263).sum := by decide
  have hdescent : baseEnd_1636263 < baseStart_1636263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636304 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 8]
def baseStart_1636304 : Nat := 118140960795 + 1636304 * 2 ^ 59
def prefixEnd_1636304 : Nat := 4983230072969 + 3 ^ 40 * 1636304 * 2
def baseEnd_1636304 : Nat := 186713433083260263727729

theorem tailTrace_1636304 : CollatzResearch.WordTrace tailWord_1636304 prefixEnd_1636304 186713433083260263727729 := by
  unfold tailWord_1636304
  simp only [CollatzResearch.WordTrace]
  refine ⟨29840454931978770659741983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39787273242638360879655977 29840454931978770659741983)
  ·
    refine ⟨44760682397968155989612975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29840454931978770659741983 44760682397968155989612975)
    ·
      refine ⟨67141023596952233984419463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44760682397968155989612975 67141023596952233984419463)
      ·
        refine ⟨100711535395428350976629195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67141023596952233984419463 100711535395428350976629195)
        ·
          refine ⟨151067303093142526464943793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100711535395428350976629195 151067303093142526464943793)
          ·
            refine ⟨113300477319856894848707845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151067303093142526464943793 113300477319856894848707845)
            ·
              refine ⟨21243839497473167784132721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113300477319856894848707845 21243839497473167784132721)
              ·
                refine ⟨15932879623104875838099541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21243839497473167784132721 15932879623104875838099541)
                ·
                  refine ⟨186713433083260263727729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15932879623104875838099541 186713433083260263727729)
                  ·
                    rfl

theorem cell22_1636304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 8].length) (baseStart_1636304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636304 prefixEnd_1636304 := by exact prefixLift 1636304
  have htrace : WordTrace (prefixWord ++ tailWord_1636304) baseStart_1636304 baseEnd_1636304 := by
    simpa [prefixWord, tailWord_1636304, baseEnd_1636304] using wordTrace_append hprefix tailTrace_1636304
  have hstable : (prefixWord ++ tailWord_1636304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636304).length < 2 ^ (prefixWord ++ tailWord_1636304).sum := by decide
  have hdescent : baseEnd_1636304 < baseStart_1636304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636321 : List Nat := [1, 2, 3, 1, 2, 1, 5, 1, 6]
def baseStart_1636321 : Nat := 118140960795 + 1636321 * 2 ^ 59
def prefixEnd_1636321 : Nat := 4983230072969 + 3 ^ 40 * 1636321 * 2
def baseEnd_1636321 : Nat := 186715372899066137836045

theorem tailTrace_1636321 : CollatzResearch.WordTrace tailWord_1636321 prefixEnd_1636321 186715372899066137836045 := by
  unfold tailWord_1636321
  simp only [CollatzResearch.WordTrace]
  refine ⟨59681529904895953222852817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39787686603263968815235211 59681529904895953222852817)
  ·
    refine ⟨44761147428671964917139613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59681529904895953222852817 44761147428671964917139613)
    ·
      refine ⟨16785430285751986843927355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44761147428671964917139613 16785430285751986843927355)
      ·
        refine ⟨25178145428627980265891033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16785430285751986843927355 25178145428627980265891033)
        ·
          refine ⟨18883609071470985199418275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25178145428627980265891033 18883609071470985199418275)
          ·
            refine ⟨28325413607206477799127413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18883609071470985199418275 28325413607206477799127413)
            ·
              refine ⟨2655507525675607293668195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28325413607206477799127413 2655507525675607293668195)
              ·
                refine ⟨3983261288513410940502293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2655507525675607293668195 3983261288513410940502293)
                ·
                  refine ⟨186715372899066137836045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3983261288513410940502293 186715372899066137836045)
                  ·
                    rfl

theorem cell22_1636321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 6].length) (baseStart_1636321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636321 prefixEnd_1636321 := by exact prefixLift 1636321
  have htrace : WordTrace (prefixWord ++ tailWord_1636321) baseStart_1636321 baseEnd_1636321 := by
    simpa [prefixWord, tailWord_1636321, baseEnd_1636321] using wordTrace_append hprefix tailTrace_1636321
  have hstable : (prefixWord ++ tailWord_1636321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636321).length < 2 ^ (prefixWord ++ tailWord_1636321).sum := by decide
  have hdescent : baseEnd_1636321 < baseStart_1636321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636327 : List Nat := [1, 1, 5, 2, 4, 1, 2, 1, 5]
def baseStart_1636327 : Nat := 118140960795 + 1636327 * 2 ^ 59
def prefixEnd_1636327 : Nat := 4983230072969 + 3 ^ 40 * 1636327 * 2
def baseEnd_1636327 : Nat := 186716057539938799286039

theorem tailTrace_1636327 : CollatzResearch.WordTrace tailWord_1636327 prefixEnd_1636327 186716057539938799286039 := by
  unfold tailWord_1636327
  simp only [CollatzResearch.WordTrace]
  refine ⟨59681748742874216247571235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39787832495249477498380823 59681748742874216247571235)
  ·
    refine ⟨89522623114311324371356853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59681748742874216247571235 89522623114311324371356853)
    ·
      refine ⟨8392745916966686659814705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89522623114311324371356853 8392745916966686659814705)
      ·
        refine ⟨6294559437725014994861029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8392745916966686659814705 6294559437725014994861029)
        ·
          refine ⟨1180229894573440311536443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6294559437725014994861029 1180229894573440311536443)
          ·
            refine ⟨1770344841860160467304665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180229894573440311536443 1770344841860160467304665)
            ·
              refine ⟨1327758631395120350478499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1770344841860160467304665 1327758631395120350478499)
              ·
                refine ⟨1991637947092680525717749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1327758631395120350478499 1991637947092680525717749)
                ·
                  refine ⟨186716057539938799286039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1991637947092680525717749 186716057539938799286039)
                  ·
                    rfl

theorem cell22_1636327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 5].length) (baseStart_1636327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636327 prefixEnd_1636327 := by exact prefixLift 1636327
  have htrace : WordTrace (prefixWord ++ tailWord_1636327) baseStart_1636327 baseEnd_1636327 := by
    simpa [prefixWord, tailWord_1636327, baseEnd_1636327] using wordTrace_append hprefix tailTrace_1636327
  have hstable : (prefixWord ++ tailWord_1636327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636327).length < 2 ^ (prefixWord ++ tailWord_1636327).sum := by decide
  have hdescent : baseEnd_1636327 < baseStart_1636327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636365 : List Nat := [1, 7, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_1636365 : Nat := 118140960795 + 1636365 * 2 ^ 59
def prefixEnd_1636365 : Nat := 4983230072969 + 3 ^ 40 * 1636365 * 2
def baseEnd_1636365 : Nat := 560161180796396965408001

theorem tailTrace_1636365 : CollatzResearch.WordTrace tailWord_1636365 prefixEnd_1636365 560161180796396965408001 := by
  unfold tailWord_1636365
  simp only [CollatzResearch.WordTrace]
  refine ⟨59683134716736548737454549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39788756477824365824969699 59683134716736548737454549)
  ·
    refine ⟨1398823469923512861034091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 59683134716736548737454549 1398823469923512861034091)
    ·
      refine ⟨2098235204885269291551137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1398823469923512861034091 2098235204885269291551137)
      ·
        refine ⟨1573676403663951968663353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2098235204885269291551137 1573676403663951968663353)
        ·
          refine ⟨1180257302747963976497515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1573676403663951968663353 1180257302747963976497515)
          ·
            refine ⟨1770385954121945964746273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180257302747963976497515 1770385954121945964746273)
            ·
              refine ⟨1327789465591459473559705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1770385954121945964746273 1327789465591459473559705)
              ·
                refine ⟨995842099193594605169779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1327789465591459473559705 995842099193594605169779)
                ·
                  refine ⟨1493763148790391907754669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 995842099193594605169779 1493763148790391907754669)
                  ·
                    refine ⟨560161180796396965408001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1493763148790391907754669 560161180796396965408001)
                    ·
                      rfl

theorem cell22_1636365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_1636365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636365 prefixEnd_1636365 := by exact prefixLift 1636365
  have htrace : WordTrace (prefixWord ++ tailWord_1636365) baseStart_1636365 baseEnd_1636365 := by
    simpa [prefixWord, tailWord_1636365, baseEnd_1636365] using wordTrace_append hprefix tailTrace_1636365
  have hstable : (prefixWord ++ tailWord_1636365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636365).length < 2 ^ (prefixWord ++ tailWord_1636365).sum := by decide
  have hdescent : baseEnd_1636365 < baseStart_1636365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636415 : List Nat := [1, 1, 2, 2, 3, 1, 3, 5, 1, 3]
def baseStart_1636415 : Nat := 118140960795 + 1636415 * 2 ^ 59
def prefixEnd_1636415 : Nat := 4983230072969 + 3 ^ 40 * 1636415 * 2
def baseEnd_1636415 : Nat := 560178296818213501657847

theorem tailTrace_1636415 : CollatzResearch.WordTrace tailWord_1636415 prefixEnd_1636415 560178296818213501657847 := by
  unfold tailWord_1636415
  simp only [CollatzResearch.WordTrace]
  refine ⟨59684958366555407276774699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39789972244370271517849799 59684958366555407276774699)
  ·
    refine ⟨89527437549833110915162049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59684958366555407276774699 89527437549833110915162049)
    ·
      refine ⟨67145578162374833186371537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89527437549833110915162049 67145578162374833186371537)
      ·
        refine ⟨50359183621781124889778653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67145578162374833186371537 50359183621781124889778653)
        ·
          refine ⟨18884693858167921833666995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50359183621781124889778653 18884693858167921833666995)
          ·
            refine ⟨28327040787251882750500493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18884693858167921833666995 28327040787251882750500493)
            ·
              refine ⟨10622640295219456031437685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28327040787251882750500493 10622640295219456031437685)
              ·
                refine ⟨995872527676824002947283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10622640295219456031437685 995872527676824002947283)
                ·
                  refine ⟨1493808791515236004420925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 995872527676824002947283 1493808791515236004420925)
                  ·
                    refine ⟨560178296818213501657847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1493808791515236004420925 560178296818213501657847)
                    ·
                      rfl

theorem cell22_1636415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 1, 3].length) (baseStart_1636415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636415 prefixEnd_1636415 := by exact prefixLift 1636415
  have htrace : WordTrace (prefixWord ++ tailWord_1636415) baseStart_1636415 baseEnd_1636415 := by
    simpa [prefixWord, tailWord_1636415, baseEnd_1636415] using wordTrace_append hprefix tailTrace_1636415
  have hstable : (prefixWord ++ tailWord_1636415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636415).length < 2 ^ (prefixWord ++ tailWord_1636415).sum := by decide
  have hdescent : baseEnd_1636415 < baseStart_1636415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636428 : List Nat := [2, 2, 1, 3, 1, 1, 5, 2, 5]
def baseStart_1636428 : Nat := 118140960795 + 1636428 * 2 ^ 59
def prefixEnd_1636428 : Nat := 4983230072969 + 3 ^ 40 * 1636428 * 2
def baseEnd_1636428 : Nat := 186727582327961933694269

theorem tailTrace_1636428 : CollatzResearch.WordTrace tailWord_1636428 prefixEnd_1636428 186727582327961933694269 := by
  unfold tailWord_1636428
  simp only [CollatzResearch.WordTrace]
  refine ⟨29842716257754155248498969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39790288343672206997998625 29842716257754155248498969)
  ·
    refine ⟨22382037193315616436374227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29842716257754155248498969 22382037193315616436374227)
    ·
      refine ⟨33573055789973424654561341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22382037193315616436374227 33573055789973424654561341)
      ·
        refine ⟨12589895921240034245460503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33573055789973424654561341 12589895921240034245460503)
        ·
          refine ⟨18884843881860051368190755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12589895921240034245460503 18884843881860051368190755)
          ·
            refine ⟨28327265822790077052286133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18884843881860051368190755 28327265822790077052286133)
            ·
              refine ⟨2655681170886569723651825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28327265822790077052286133 2655681170886569723651825)
              ·
                refine ⟨1991760878164927292738869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2655681170886569723651825 1991760878164927292738869)
                ·
                  refine ⟨186727582327961933694269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1991760878164927292738869 186727582327961933694269)
                  ·
                    rfl

theorem cell22_1636428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_1636428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636428 prefixEnd_1636428 := by exact prefixLift 1636428
  have htrace : WordTrace (prefixWord ++ tailWord_1636428) baseStart_1636428 baseEnd_1636428 := by
    simpa [prefixWord, tailWord_1636428, baseEnd_1636428] using wordTrace_append hprefix tailTrace_1636428
  have hstable : (prefixWord ++ tailWord_1636428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636428).length < 2 ^ (prefixWord ++ tailWord_1636428).sum := by decide
  have hdescent : baseEnd_1636428 < baseStart_1636428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636490 : List Nat := [3, 1, 2, 3, 1, 4, 1, 1, 6]
def baseStart_1636490 : Nat := 118140960795 + 1636490 * 2 ^ 59
def prefixEnd_1636490 : Nat := 4983230072969 + 3 ^ 40 * 1636490 * 2
def baseEnd_1636490 : Nat := 186734656950312768677539

theorem tailTrace_1636490 : CollatzResearch.WordTrace tailWord_1636490 prefixEnd_1636490 186734656950312768677539 := by
  unfold tailWord_1636490
  simp only [CollatzResearch.WordTrace]
  refine ⟨14921923460320923771438731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39791795894189130057169949 14921923460320923771438731)
  ·
    refine ⟨22382885190481385657158097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14921923460320923771438731 22382885190481385657158097)
    ·
      refine ⟨16787163892861039242868573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22382885190481385657158097 16787163892861039242868573)
      ·
        refine ⟨6295186459822889716075715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16787163892861039242868573 6295186459822889716075715)
        ·
          refine ⟨9442779689734334574113573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6295186459822889716075715 9442779689734334574113573)
          ·
            refine ⟨1770521191825187732646295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9442779689734334574113573 1770521191825187732646295)
            ·
              refine ⟨2655781787737781598969443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1770521191825187732646295 2655781787737781598969443)
              ·
                refine ⟨3983672681606672398454165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2655781787737781598969443 3983672681606672398454165)
                ·
                  refine ⟨186734656950312768677539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3983672681606672398454165 186734656950312768677539)
                  ·
                    rfl

theorem cell22_1636490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_1636490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636490 prefixEnd_1636490 := by exact prefixLift 1636490
  have htrace : WordTrace (prefixWord ++ tailWord_1636490) baseStart_1636490 baseEnd_1636490 := by
    simpa [prefixWord, tailWord_1636490, baseEnd_1636490] using wordTrace_append hprefix tailTrace_1636490
  have hstable : (prefixWord ++ tailWord_1636490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636490).length < 2 ^ (prefixWord ++ tailWord_1636490).sum := by decide
  have hdescent : baseEnd_1636490 < baseStart_1636490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636522 : List Nat := [3, 1, 5, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1636522 : Nat := 118140960795 + 1636522 * 2 ^ 59
def prefixEnd_1636522 : Nat := 4983230072969 + 3 ^ 40 * 1636522 * 2
def baseEnd_1636522 : Nat := 560214925104900889232519

theorem tailTrace_1636522 : CollatzResearch.WordTrace tailWord_1636522 prefixEnd_1636522 560214925104900889232519 := by
  unfold tailWord_1636522
  simp only [CollatzResearch.WordTrace]
  refine ⟨14922215244291941137729955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39792573984778509700613213 14922215244291941137729955)
  ·
    refine ⟨22383322866437911706594933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14922215244291941137729955 22383322866437911706594933)
    ·
      refine ⟨2098436518728554222493275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22383322866437911706594933 2098436518728554222493275)
      ·
        refine ⟨3147654778092831333739913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2098436518728554222493275 3147654778092831333739913)
        ·
          refine ⟨2360741083569623500304935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3147654778092831333739913 2360741083569623500304935)
          ·
            refine ⟨3541111625354435250457403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2360741083569623500304935 3541111625354435250457403)
            ·
              refine ⟨5311667438031652875686105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3541111625354435250457403 5311667438031652875686105)
              ·
                refine ⟨3983750578523739656764579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5311667438031652875686105 3983750578523739656764579)
                ·
                  refine ⟨5975625867785609485146869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3983750578523739656764579 5975625867785609485146869)
                  ·
                    refine ⟨560214925104900889232519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5975625867785609485146869 560214925104900889232519)
                    ·
                      rfl

theorem cell22_1636522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1636522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636522 prefixEnd_1636522 := by exact prefixLift 1636522
  have htrace : WordTrace (prefixWord ++ tailWord_1636522) baseStart_1636522 baseEnd_1636522 := by
    simpa [prefixWord, tailWord_1636522, baseEnd_1636522] using wordTrace_append hprefix tailTrace_1636522
  have hstable : (prefixWord ++ tailWord_1636522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636522).length < 2 ^ (prefixWord ++ tailWord_1636522).sum := by decide
  have hdescent : baseEnd_1636522 < baseStart_1636522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636526 : List Nat := [4, 1, 4, 2, 1, 1, 3, 1, 1, 4]
def baseStart_1636526 : Nat := 118140960795 + 1636526 * 2 ^ 59
def prefixEnd_1636526 : Nat := 4983230072969 + 3 ^ 40 * 1636526 * 2
def baseEnd_1636526 : Nat := 560216294386646212132507

theorem tailTrace_1636526 : CollatzResearch.WordTrace tailWord_1636526 prefixEnd_1636526 560216294386646212132507 := by
  unfold tailWord_1636526
  simp only [CollatzResearch.WordTrace]
  refine ⟨7461125858644159154258179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39792671246102182156043621 7461125858644159154258179)
  ·
    refine ⟨11191688787966238731387269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7461125858644159154258179 11191688787966238731387269)
    ·
      refine ⟨2098441647743669762135113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11191688787966238731387269 2098441647743669762135113)
      ·
        refine ⟨1573831235807752321601335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2098441647743669762135113 1573831235807752321601335)
        ·
          refine ⟨2360746853711628482402003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1573831235807752321601335 2360746853711628482402003)
          ·
            refine ⟨3541120280567442723603005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2360746853711628482402003 3541120280567442723603005)
            ·
              refine ⟨1327920105212791021351127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3541120280567442723603005 1327920105212791021351127)
              ·
                refine ⟨1991880157819186532026691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1327920105212791021351127 1991880157819186532026691)
                ·
                  refine ⟨2987820236728779798040037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1991880157819186532026691 2987820236728779798040037)
                  ·
                    refine ⟨560216294386646212132507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2987820236728779798040037 560216294386646212132507)
                    ·
                      rfl

theorem cell22_1636526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_1636526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636526 prefixEnd_1636526 := by exact prefixLift 1636526
  have htrace : WordTrace (prefixWord ++ tailWord_1636526) baseStart_1636526 baseEnd_1636526 := by
    simpa [prefixWord, tailWord_1636526, baseEnd_1636526] using wordTrace_append hprefix tailTrace_1636526
  have hstable : (prefixWord ++ tailWord_1636526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636526).length < 2 ^ (prefixWord ++ tailWord_1636526).sum := by decide
  have hdescent : baseEnd_1636526 < baseStart_1636526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636584 : List Nat := [2, 1, 4, 1, 2, 3, 2, 3, 1, 3]
def baseStart_1636584 : Nat := 118140960795 + 1636584 * 2 ^ 59
def prefixEnd_1636584 : Nat := 4983230072969 + 3 ^ 40 * 1636584 * 2
def baseEnd_1636584 : Nat := 560236148971953394182329

theorem tailTrace_1636584 : CollatzResearch.WordTrace tailWord_1636584 prefixEnd_1636584 560236148971953394182329 := by
  unfold tailWord_1636584
  simp only [CollatzResearch.WordTrace]
  refine ⟨29845561151471574569838403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39794081535295432759784537 29845561151471574569838403)
  ·
    refine ⟨44768341727207361854757605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29845561151471574569838403 44768341727207361854757605)
    ·
      refine ⟨8394064073851380347767051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44768341727207361854757605 8394064073851380347767051)
      ·
        refine ⟨12591096110777070521650577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8394064073851380347767051 12591096110777070521650577)
        ·
          refine ⟨9443322083082802891237933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12591096110777070521650577 9443322083082802891237933)
          ·
            refine ⟨3541245781156051084214225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9443322083082802891237933 3541245781156051084214225)
            ·
              refine ⟨2655934335867038313160669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3541245781156051084214225 2655934335867038313160669)
              ·
                refine ⟨995975375950139367435251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2655934335867038313160669 995975375950139367435251)
                ·
                  refine ⟨1493963063925209051152877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 995975375950139367435251 1493963063925209051152877)
                  ·
                    refine ⟨560236148971953394182329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1493963063925209051152877 560236148971953394182329)
                    ·
                      rfl

theorem cell22_1636584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_1636584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636584 prefixEnd_1636584 := by exact prefixLift 1636584
  have htrace : WordTrace (prefixWord ++ tailWord_1636584) baseStart_1636584 baseEnd_1636584 := by
    simpa [prefixWord, tailWord_1636584, baseEnd_1636584] using wordTrace_append hprefix tailTrace_1636584
  have hstable : (prefixWord ++ tailWord_1636584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636584).length < 2 ^ (prefixWord ++ tailWord_1636584).sum := by decide
  have hdescent : baseEnd_1636584 < baseStart_1636584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636608 : List Nat := [2, 1, 1, 2, 1, 1, 5, 3, 6]
def baseStart_1636608 : Nat := 118140960795 + 1636608 * 2 ^ 59
def prefixEnd_1636608 : Nat := 4983230072969 + 3 ^ 40 * 1636608 * 2
def baseEnd_1636608 : Nat := 186748121554141777194085

theorem tailTrace_1636608 : CollatzResearch.WordTrace tailWord_1636608 prefixEnd_1636608 186748121554141777194085 := by
  unfold tailWord_1636608
  simp only [CollatzResearch.WordTrace]
  refine ⟨29845998827428100619275239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39794665103237467492366985 29845998827428100619275239)
  ·
    refine ⟨44768998241142150928912859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29845998827428100619275239 44768998241142150928912859)
    ·
      refine ⟨67153497361713226393369289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44768998241142150928912859 67153497361713226393369289)
      ·
        refine ⟨50365123021284919795026967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67153497361713226393369289 50365123021284919795026967)
        ·
          refine ⟨75547684531927379692540451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50365123021284919795026967 75547684531927379692540451)
          ·
            refine ⟨113321526797891069538810677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75547684531927379692540451 113321526797891069538810677)
            ·
              refine ⟨10623893137302287769263501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113321526797891069538810677 10623893137302287769263501)
              ·
                refine ⟨3983959926488357913473813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10623893137302287769263501 3983959926488357913473813)
                ·
                  refine ⟨186748121554141777194085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3983959926488357913473813 186748121554141777194085)
                  ·
                    rfl

theorem cell22_1636608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 6].length) (baseStart_1636608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636608 prefixEnd_1636608 := by exact prefixLift 1636608
  have htrace : WordTrace (prefixWord ++ tailWord_1636608) baseStart_1636608 baseEnd_1636608 := by
    simpa [prefixWord, tailWord_1636608, baseEnd_1636608] using wordTrace_append hprefix tailTrace_1636608
  have hstable : (prefixWord ++ tailWord_1636608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636608).length < 2 ^ (prefixWord ++ tailWord_1636608).sum := by decide
  have hdescent : baseEnd_1636608 < baseStart_1636608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636670 : List Nat := [4, 2, 1, 2, 1, 2, 1, 9]
def baseStart_1636670 : Nat := 118140960795 + 1636670 * 2 ^ 59
def prefixEnd_1636670 : Nat := 4983230072969 + 3 ^ 40 * 1636670 * 2
def baseEnd_1636670 : Nat := 62251732058830870725785

theorem tailTrace_1636670 : CollatzResearch.WordTrace tailWord_1636670 prefixEnd_1636670 62251732058830870725785 := by
  unfold tailWord_1636670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7461782372578948228413433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39796172653754390551538309 7461782372578948228413433)
  ·
    refine ⟨5596336779434211171310075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7461782372578948228413433 5596336779434211171310075)
    ·
      refine ⟨8394505169151316756965113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5596336779434211171310075 8394505169151316756965113)
      ·
        refine ⟨6295878876863487567723835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8394505169151316756965113 6295878876863487567723835)
        ·
          refine ⟨9443818315295231351585753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6295878876863487567723835 9443818315295231351585753)
          ·
            refine ⟨7082863736471423513689315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9443818315295231351585753 7082863736471423513689315)
            ·
              refine ⟨10624295604707135270533973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7082863736471423513689315 10624295604707135270533973)
              ·
                refine ⟨62251732058830870725785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10624295604707135270533973 62251732058830870725785)
                ·
                  rfl

theorem cell22_1636670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_1636670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636670 prefixEnd_1636670 := by exact prefixLift 1636670
  have htrace : WordTrace (prefixWord ++ tailWord_1636670) baseStart_1636670 baseEnd_1636670 := by
    simpa [prefixWord, tailWord_1636670, baseEnd_1636670] using wordTrace_append hprefix tailTrace_1636670
  have hstable : (prefixWord ++ tailWord_1636670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636670).length < 2 ^ (prefixWord ++ tailWord_1636670).sum := by decide
  have hdescent : baseEnd_1636670 < baseStart_1636670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636683 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 4, 6]
def baseStart_1636683 : Nat := 118140960795 + 1636683 * 2 ^ 59
def prefixEnd_1636683 : Nat := 4983230072969 + 3 ^ 40 * 1636683 * 2
def baseEnd_1636683 : Nat := 560270038695150135957025

theorem tailTrace_1636683 : CollatzResearch.WordTrace tailWord_1636683 prefixEnd_1636683 560270038695150135957025 := by
  unfold tailWord_1636683
  simp only [CollatzResearch.WordTrace]
  refine ⟨59694733129584489047530703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39796488753056326031687135 59694733129584489047530703)
  ·
    refine ⟨89542099694376733571296055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59694733129584489047530703 89542099694376733571296055)
    ·
      refine ⟨134313149541565100356944083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89542099694376733571296055 134313149541565100356944083)
      ·
        refine ⟨201469724312347650535416125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134313149541565100356944083 201469724312347650535416125)
        ·
          refine ⟨75551146617130368950781047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201469724312347650535416125 75551146617130368950781047)
          ·
            refine ⟨113326719925695553426171571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75551146617130368950781047 113326719925695553426171571)
            ·
              refine ⟨169990079888543330139257357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113326719925695553426171571 169990079888543330139257357)
              ·
                refine ⟨63746279958203748802221509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169990079888543330139257357 63746279958203748802221509)
                ·
                  refine ⟨11952427492163202900416533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63746279958203748802221509 11952427492163202900416533)
                  ·
                    refine ⟨560270038695150135957025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11952427492163202900416533 560270038695150135957025)
                    ·
                      rfl

theorem cell22_1636683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 6].length) (baseStart_1636683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636683 prefixEnd_1636683 := by exact prefixLift 1636683
  have htrace : WordTrace (prefixWord ++ tailWord_1636683) baseStart_1636683 baseEnd_1636683 := by
    simpa [prefixWord, tailWord_1636683, baseEnd_1636683] using wordTrace_append hprefix tailTrace_1636683
  have hstable : (prefixWord ++ tailWord_1636683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636683).length < 2 ^ (prefixWord ++ tailWord_1636683).sum := by decide
  have hdescent : baseEnd_1636683 < baseStart_1636683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636766 : List Nat := [4, 3, 1, 2, 1, 3, 1, 2, 5]
def baseStart_1636766 : Nat := 118140960795 + 1636766 * 2 ^ 59
def prefixEnd_1636766 : Nat := 4983230072969 + 3 ^ 40 * 1636766 * 2
def baseEnd_1636766 : Nat := 186766150430455195377257

theorem tailTrace_1636766 : CollatzResearch.WordTrace tailWord_1636766 prefixEnd_1636766 186766150430455195377257 := by
  unfold tailWord_1636766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7462220048535474277850269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39798506925522529481868101 7462220048535474277850269)
  ·
    refine ⟨2798332518200802854193851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7462220048535474277850269 2798332518200802854193851)
    ·
      refine ⟨4197498777301204281290777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2798332518200802854193851 4197498777301204281290777)
      ·
        refine ⟨3148124082975903210968083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4197498777301204281290777 3148124082975903210968083)
        ·
          refine ⟨4722186124463854816452125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3148124082975903210968083 4722186124463854816452125)
          ·
            refine ⟨1770819796673945556169547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4722186124463854816452125 1770819796673945556169547)
            ·
              refine ⟨2656229695010918334254321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1770819796673945556169547 2656229695010918334254321)
              ·
                refine ⟨1992172271258188750690741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2656229695010918334254321 1992172271258188750690741)
                ·
                  refine ⟨186766150430455195377257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1992172271258188750690741 186766150430455195377257)
                  ·
                    rfl

theorem cell22_1636766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_1636766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636766 prefixEnd_1636766 := by exact prefixLift 1636766
  have htrace : WordTrace (prefixWord ++ tailWord_1636766) baseStart_1636766 baseEnd_1636766 := by
    simpa [prefixWord, tailWord_1636766, baseEnd_1636766] using wordTrace_append hprefix tailTrace_1636766
  have hstable : (prefixWord ++ tailWord_1636766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636766).length < 2 ^ (prefixWord ++ tailWord_1636766).sum := by decide
  have hdescent : baseEnd_1636766 < baseStart_1636766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636854 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_1636854 : Nat := 118140960795 + 1636854 * 2 ^ 59
def prefixEnd_1636854 : Nat := 4983230072969 + 3 ^ 40 * 1636854 * 2
def baseEnd_1636854 : Nat := 560328575489762689931501

theorem tailTrace_1636854 : CollatzResearch.WordTrace tailWord_1636854 prefixEnd_1636854 560328575489762689931501 := by
  unfold tailWord_1636854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3731310625747811578250351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39800646674643323501337077 3731310625747811578250351)
  ·
    refine ⟨5596965938621717367375527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3731310625747811578250351 5596965938621717367375527)
    ·
      refine ⟨8395448907932576051063291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5596965938621717367375527 8395448907932576051063291)
      ·
        refine ⟨12593173361898864076594937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8395448907932576051063291 12593173361898864076594937)
        ·
          refine ⟨9444880021424148057446203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12593173361898864076594937 9444880021424148057446203)
          ·
            refine ⟨14167320032136222086169305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9444880021424148057446203 14167320032136222086169305)
            ·
              refine ⟨10625490024102166564626979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14167320032136222086169305 10625490024102166564626979)
              ·
                refine ⟨15938235036153249846940469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10625490024102166564626979 15938235036153249846940469)
                ·
                  refine ⟨1494209534639367173150669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15938235036153249846940469 1494209534639367173150669)
                  ·
                    refine ⟨560328575489762689931501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1494209534639367173150669 560328575489762689931501)
                    ·
                      rfl

theorem cell22_1636854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_1636854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636854 prefixEnd_1636854 := by exact prefixLift 1636854
  have htrace : WordTrace (prefixWord ++ tailWord_1636854) baseStart_1636854 baseEnd_1636854 := by
    simpa [prefixWord, tailWord_1636854, baseEnd_1636854] using wordTrace_append hprefix tailTrace_1636854
  have hstable : (prefixWord ++ tailWord_1636854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636854).length < 2 ^ (prefixWord ++ tailWord_1636854).sum := by decide
  have hdescent : baseEnd_1636854 < baseStart_1636854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636880 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 4, 8]
def baseStart_1636880 : Nat := 118140960795 + 1636880 * 2 ^ 59
def prefixEnd_1636880 : Nat := 4983230072969 + 3 ^ 40 * 1636880 * 2
def baseEnd_1636880 : Nat := 560337475821107288781421

theorem tailTrace_1636880 : CollatzResearch.WordTrace tailWord_1636880 prefixEnd_1636880 560337475821107288781421 := by
  unfold tailWord_1636880
  simp only [CollatzResearch.WordTrace]
  refine ⟨29850959154935395846226047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39801278873247194461634729 29850959154935395846226047)
  ·
    refine ⟨44776438732403093769339071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29850959154935395846226047 44776438732403093769339071)
    ·
      refine ⟨67164658098604640654008607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44776438732403093769339071 67164658098604640654008607)
      ·
        refine ⟨100746987147906960981012911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67164658098604640654008607 100746987147906960981012911)
        ·
          refine ⟨151120480721860441471519367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100746987147906960981012911 151120480721860441471519367)
          ·
            refine ⟨226680721082790662207279051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151120480721860441471519367 226680721082790662207279051)
            ·
              refine ⟨340021081624185993310918577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226680721082790662207279051 340021081624185993310918577)
              ·
                refine ⟨255015811218139494983188933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340021081624185993310918577 255015811218139494983188933)
                ·
                  refine ⟨47815464603401155309347925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 255015811218139494983188933 47815464603401155309347925)
                  ·
                    refine ⟨560337475821107288781421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47815464603401155309347925 560337475821107288781421)
                    ·
                      rfl

theorem cell22_1636880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_1636880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636880 prefixEnd_1636880 := by exact prefixLift 1636880
  have htrace : WordTrace (prefixWord ++ tailWord_1636880) baseStart_1636880 baseEnd_1636880 := by
    simpa [prefixWord, tailWord_1636880, baseEnd_1636880] using wordTrace_append hprefix tailTrace_1636880
  have hstable : (prefixWord ++ tailWord_1636880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636880).length < 2 ^ (prefixWord ++ tailWord_1636880).sum := by decide
  have hdescent : baseEnd_1636880 < baseStart_1636880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636888 : List Nat := [2, 1, 2, 3, 3, 1, 4, 2, 1, 3]
def baseStart_1636888 : Nat := 118140960795 + 1636888 * 2 ^ 59
def prefixEnd_1636888 : Nat := 4983230072969 + 3 ^ 40 * 1636888 * 2
def baseEnd_1636888 : Nat := 560340214384597934581397

theorem tailTrace_1636888 : CollatzResearch.WordTrace tailWord_1636888 prefixEnd_1636888 560340214384597934581397 := by
  unfold tailWord_1636888
  simp only [CollatzResearch.WordTrace]
  refine ⟨29851105046920904529371659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39801473395894539372495545 29851105046920904529371659)
  ·
    refine ⟨44776657570381356794057489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29851105046920904529371659 44776657570381356794057489)
    ·
      refine ⟨33582493177786017595543117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44776657570381356794057489 33582493177786017595543117)
      ·
        refine ⟨12593434941669756598328669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33582493177786017595543117 12593434941669756598328669)
        ·
          refine ⟨4722538103126158724373251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12593434941669756598328669 4722538103126158724373251)
          ·
            refine ⟨7083807154689238086559877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4722538103126158724373251 7083807154689238086559877)
            ·
              refine ⟨1328213841504232141229977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7083807154689238086559877 1328213841504232141229977)
              ·
                refine ⟨996160381128174105922483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1328213841504232141229977 996160381128174105922483)
                ·
                  refine ⟨1494240571692261158883725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 996160381128174105922483 1494240571692261158883725)
                  ·
                    refine ⟨560340214384597934581397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1494240571692261158883725 560340214384597934581397)
                    ·
                      rfl

theorem cell22_1636888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 1, 3].length) (baseStart_1636888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636888 prefixEnd_1636888 := by exact prefixLift 1636888
  have htrace : WordTrace (prefixWord ++ tailWord_1636888) baseStart_1636888 baseEnd_1636888 := by
    simpa [prefixWord, tailWord_1636888, baseEnd_1636888] using wordTrace_append hprefix tailTrace_1636888
  have hstable : (prefixWord ++ tailWord_1636888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636888).length < 2 ^ (prefixWord ++ tailWord_1636888).sum := by decide
  have hdescent : baseEnd_1636888 < baseStart_1636888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636897 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 5, 4]
def baseStart_1636897 : Nat := 118140960795 + 1636897 * 2 ^ 59
def prefixEnd_1636897 : Nat := 4983230072969 + 3 ^ 40 * 1636897 * 2
def baseEnd_1636897 : Nat := 560343295268524911106369

theorem tailTrace_1636897 : CollatzResearch.WordTrace tailWord_1636897 prefixEnd_1636897 560343295268524911106369 := by
  unfold tailWord_1636897
  simp only [CollatzResearch.WordTrace]
  refine ⟨59702538350809203595820945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39801692233872802397213963 59702538350809203595820945)
  ·
    refine ⟨44776903763106902696865709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59702538350809203595820945 44776903763106902696865709)
    ·
      refine ⟨16791338911165088511324641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44776903763106902696865709 16791338911165088511324641)
      ·
        refine ⟨12593504183373816383493481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16791338911165088511324641 12593504183373816383493481)
        ·
          refine ⟨9445128137530362287620111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12593504183373816383493481 9445128137530362287620111)
          ·
            refine ⟨14167692206295543431430167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9445128137530362287620111 14167692206295543431430167)
            ·
              refine ⟨21251538309443315147145251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14167692206295543431430167 21251538309443315147145251)
              ·
                refine ⟨31877307464164972720717877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21251538309443315147145251 31877307464164972720717877)
                ·
                  refine ⟨2988497574765466192567301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31877307464164972720717877 2988497574765466192567301)
                  ·
                    refine ⟨560343295268524911106369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2988497574765466192567301 560343295268524911106369)
                    ·
                      rfl

theorem cell22_1636897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_1636897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636897 prefixEnd_1636897 := by exact prefixLift 1636897
  have htrace : WordTrace (prefixWord ++ tailWord_1636897) baseStart_1636897 baseEnd_1636897 := by
    simpa [prefixWord, tailWord_1636897, baseEnd_1636897] using wordTrace_append hprefix tailTrace_1636897
  have hstable : (prefixWord ++ tailWord_1636897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636897).length < 2 ^ (prefixWord ++ tailWord_1636897).sum := by decide
  have hdescent : baseEnd_1636897 < baseStart_1636897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636927 : List Nat := [1, 1, 2, 2, 3, 2, 1, 4, 1, 5]
def baseStart_1636927 : Nat := 118140960795 + 1636927 * 2 ^ 59
def prefixEnd_1636927 : Nat := 4983230072969 + 3 ^ 40 * 1636927 * 2
def baseEnd_1636927 : Nat := 560353564881614832856277

theorem tailTrace_1636927 : CollatzResearch.WordTrace tailWord_1636927 prefixEnd_1636927 560353564881614832856277 := by
  unfold tailWord_1636927
  simp only [CollatzResearch.WordTrace]
  refine ⟨59703632540700518719413035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39802421693800345812942023 59703632540700518719413035)
  ·
    refine ⟨89555448811050778079119553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59703632540700518719413035 89555448811050778079119553)
    ·
      refine ⟨67166586608288083559339665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89555448811050778079119553 67166586608288083559339665)
      ·
        refine ⟨50374939956216062669504749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67166586608288083559339665 50374939956216062669504749)
        ·
          refine ⟨18890602483581023501064281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50374939956216062669504749 18890602483581023501064281)
          ·
            refine ⟨14167951862685767625798211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18890602483581023501064281 14167951862685767625798211)
            ·
              refine ⟨21251927794028651438697317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14167951862685767625798211 21251927794028651438697317)
              ·
                refine ⟨3984736461380372144755747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21251927794028651438697317 3984736461380372144755747)
                ·
                  refine ⟨5977104692070558217133621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3984736461380372144755747 5977104692070558217133621)
                  ·
                    refine ⟨560353564881614832856277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5977104692070558217133621 560353564881614832856277)
                    ·
                      rfl

theorem cell22_1636927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 5].length) (baseStart_1636927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636927 prefixEnd_1636927 := by exact prefixLift 1636927
  have htrace : WordTrace (prefixWord ++ tailWord_1636927) baseStart_1636927 baseEnd_1636927 := by
    simpa [prefixWord, tailWord_1636927, baseEnd_1636927] using wordTrace_append hprefix tailTrace_1636927
  have hstable : (prefixWord ++ tailWord_1636927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636927).length < 2 ^ (prefixWord ++ tailWord_1636927).sum := by decide
  have hdescent : baseEnd_1636927 < baseStart_1636927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636944 : List Nat := [2, 1, 1, 1, 1, 3, 2, 6, 2, 3]
def baseStart_1636944 : Nat := 118140960795 + 1636944 * 2 ^ 59
def prefixEnd_1636944 : Nat := 4983230072969 + 3 ^ 40 * 1636944 * 2
def baseEnd_1636944 : Nat := 560359384329032455181225

theorem tailTrace_1636944 : CollatzResearch.WordTrace tailWord_1636944 prefixEnd_1636944 560359384329032455181225 := by
  unfold tailWord_1636944
  simp only [CollatzResearch.WordTrace]
  refine ⟨29852126290819465311390943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39802835054425953748521257 29852126290819465311390943)
  ·
    refine ⟨44778189436229197967086415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29852126290819465311390943 44778189436229197967086415)
    ·
      refine ⟨67167284154343796950629623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44778189436229197967086415 67167284154343796950629623)
      ·
        refine ⟨100750926231515695425944435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67167284154343796950629623 100750926231515695425944435)
        ·
          refine ⟨151126389347273543138916653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100750926231515695425944435 151126389347273543138916653)
          ·
            refine ⟨56672396005227578677093745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151126389347273543138916653 56672396005227578677093745)
            ·
              refine ⟨42504297003920684007820309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56672396005227578677093745 42504297003920684007820309)
              ·
                refine ⟨1992388922058782062866577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42504297003920684007820309 1992388922058782062866577)
                ·
                  refine ⟨1494291691544086547149933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1992388922058782062866577 1494291691544086547149933)
                  ·
                    refine ⟨560359384329032455181225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1494291691544086547149933 560359384329032455181225)
                    ·
                      rfl

theorem cell22_1636944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 2, 3].length) (baseStart_1636944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636944 prefixEnd_1636944 := by exact prefixLift 1636944
  have htrace : WordTrace (prefixWord ++ tailWord_1636944) baseStart_1636944 baseEnd_1636944 := by
    simpa [prefixWord, tailWord_1636944, baseEnd_1636944] using wordTrace_append hprefix tailTrace_1636944
  have hstable : (prefixWord ++ tailWord_1636944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636944).length < 2 ^ (prefixWord ++ tailWord_1636944).sum := by decide
  have hdescent : baseEnd_1636944 < baseStart_1636944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1636974 : List Nat := [4, 1, 2, 2, 2, 2, 1, 8]
def baseStart_1636974 : Nat := 118140960795 + 1636974 * 2 ^ 59
def prefixEnd_1636974 : Nat := 4983230072969 + 3 ^ 40 * 1636974 * 2
def baseEnd_1636974 : Nat := 62263294882458041881237

theorem tailTrace_1636974 : CollatzResearch.WordTrace tailWord_1636974 prefixEnd_1636974 62263294882458041881237 := by
  unfold tailWord_1636974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7463168346441280718296747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39803564514353497164249317 7463168346441280718296747)
  ·
    refine ⟨11194752519661921077445121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7463168346441280718296747 11194752519661921077445121)
    ·
      refine ⟨8396064389746440808083841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11194752519661921077445121 8396064389746440808083841)
      ·
        refine ⟨6297048292309830606062881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8396064389746440808083841 6297048292309830606062881)
        ·
          refine ⟨4722786219232372954547161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6297048292309830606062881 4722786219232372954547161)
          ·
            refine ⟨3542089664424279715910371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4722786219232372954547161 3542089664424279715910371)
            ·
              refine ⟨5313134496636419573865557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3542089664424279715910371 5313134496636419573865557)
              ·
                refine ⟨62263294882458041881237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5313134496636419573865557 62263294882458041881237)
                ·
                  rfl

theorem cell22_1636974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_1636974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1636974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1636974 prefixEnd_1636974 := by exact prefixLift 1636974
  have htrace : WordTrace (prefixWord ++ tailWord_1636974) baseStart_1636974 baseEnd_1636974 := by
    simpa [prefixWord, tailWord_1636974, baseEnd_1636974] using wordTrace_append hprefix tailTrace_1636974
  have hstable : (prefixWord ++ tailWord_1636974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1636974).length < 2 ^ (prefixWord ++ tailWord_1636974).sum := by decide
  have hdescent : baseEnd_1636974 < baseStart_1636974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1636974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637017 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 1, 7]
def baseStart_1637017 : Nat := 118140960795 + 1637017 * 2 ^ 59
def prefixEnd_1637017 : Nat := 4983230072969 + 3 ^ 40 * 1637017 * 2
def baseEnd_1637017 : Nat := 560384373720884598106001

theorem tailTrace_1637017 : CollatzResearch.WordTrace tailWord_1637017 prefixEnd_1637017 560384373720884598106001 := by
  unfold tailWord_1637017
  simp only [CollatzResearch.WordTrace]
  refine ⟨59706915110374464090189305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39804610073582976060126203 59706915110374464090189305)
  ·
    refine ⟨44780186332780848067641979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59706915110374464090189305 44780186332780848067641979)
    ·
      refine ⟨67170279499171272101462969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44780186332780848067641979 67170279499171272101462969)
      ·
        refine ⟨50377709624378454076097227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67170279499171272101462969 50377709624378454076097227)
        ·
          refine ⟨75566564436567681114145841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50377709624378454076097227 75566564436567681114145841)
          ·
            refine ⟨56674923327425760835609381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75566564436567681114145841 56674923327425760835609381)
            ·
              refine ⟨10626548123892330156676759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56674923327425760835609381 10626548123892330156676759)
              ·
                refine ⟨15939822185838495235015139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10626548123892330156676759 15939822185838495235015139)
                ·
                  refine ⟨23909733278757742852522709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15939822185838495235015139 23909733278757742852522709)
                  ·
                    refine ⟨560384373720884598106001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23909733278757742852522709 560384373720884598106001)
                    ·
                      rfl

theorem cell22_1637017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_1637017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637017 prefixEnd_1637017 := by exact prefixLift 1637017
  have htrace : WordTrace (prefixWord ++ tailWord_1637017) baseStart_1637017 baseEnd_1637017 := by
    simpa [prefixWord, tailWord_1637017, baseEnd_1637017] using wordTrace_append hprefix tailTrace_1637017
  have hstable : (prefixWord ++ tailWord_1637017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637017).length < 2 ^ (prefixWord ++ tailWord_1637017).sum := by decide
  have hdescent : baseEnd_1637017 < baseStart_1637017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637057 : List Nat := [1, 2, 6, 2, 1, 1, 1, 4, 1, 3]
def baseStart_1637057 : Nat := 118140960795 + 1637057 * 2 ^ 59
def prefixEnd_1637057 : Nat := 4983230072969 + 3 ^ 40 * 1637057 * 2
def baseEnd_1637057 : Nat := 560398066538337827105879

theorem tailTrace_1637057 : CollatzResearch.WordTrace tailWord_1637057 prefixEnd_1637057 560398066538337827105879 := by
  unfold tailWord_1637057
  simp only [CollatzResearch.WordTrace]
  refine ⟨59708374030229550921645425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39805582686819700614430283 59708374030229550921645425)
  ·
    refine ⟨44781280522672163191234069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59708374030229550921645425 44781280522672163191234069)
    ·
      refine ⟨2099122524500257649589097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44781280522672163191234069 2099122524500257649589097)
      ·
        refine ⟨1574341893375193237191823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2099122524500257649589097 1574341893375193237191823)
        ·
          refine ⟨2361512840062789855787735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1574341893375193237191823 2361512840062789855787735)
          ·
            refine ⟨3542269260094184783681603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2361512840062789855787735 3542269260094184783681603)
            ·
              refine ⟨5313403890141277175522405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3542269260094184783681603 5313403890141277175522405)
              ·
                refine ⟨996263229401489470410451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5313403890141277175522405 996263229401489470410451)
                ·
                  refine ⟨1494394844102234205615677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 996263229401489470410451 1494394844102234205615677)
                  ·
                    refine ⟨560398066538337827105879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1494394844102234205615677 560398066538337827105879)
                    ·
                      rfl

theorem cell22_1637057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_1637057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637057 prefixEnd_1637057 := by exact prefixLift 1637057
  have htrace : WordTrace (prefixWord ++ tailWord_1637057) baseStart_1637057 baseEnd_1637057 := by
    simpa [prefixWord, tailWord_1637057, baseEnd_1637057] using wordTrace_append hprefix tailTrace_1637057
  have hstable : (prefixWord ++ tailWord_1637057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637057).length < 2 ^ (prefixWord ++ tailWord_1637057).sum := by decide
  have hdescent : baseEnd_1637057 < baseStart_1637057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637079 : List Nat := [1, 1, 3, 2, 1, 4, 1, 3, 1, 5]
def baseStart_1637079 : Nat := 118140960795 + 1637079 * 2 ^ 59
def prefixEnd_1637079 : Nat := 4983230072969 + 3 ^ 40 * 1637079 * 2
def baseEnd_1637079 : Nat := 560405597587937103055811

theorem tailTrace_1637079 : CollatzResearch.WordTrace tailWord_1637079 prefixEnd_1637079 560405597587937103055811 := by
  unfold tailWord_1637079
  simp only [CollatzResearch.WordTrace]
  refine ⟨59709176436149848678946291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39806117624099899119297527 59709176436149848678946291)
  ·
    refine ⟨89563764654224773018419437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59709176436149848678946291 89563764654224773018419437)
    ·
      refine ⟨33586411745334289881907289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89563764654224773018419437 33586411745334289881907289)
      ·
        refine ⟨25189808809000717411430467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33586411745334289881907289 25189808809000717411430467)
        ·
          refine ⟨37784713213501076117145701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25189808809000717411430467 37784713213501076117145701)
          ·
            refine ⟨7084633727531451771964819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37784713213501076117145701 7084633727531451771964819)
            ·
              refine ⟨10626950591297177657947229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7084633727531451771964819 10626950591297177657947229)
              ·
                refine ⟨3985106471736441621730211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10626950591297177657947229 3985106471736441621730211)
                ·
                  refine ⟨5977659707604662432595317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3985106471736441621730211 5977659707604662432595317)
                  ·
                    refine ⟨560405597587937103055811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5977659707604662432595317 560405597587937103055811)
                    ·
                      rfl

theorem cell22_1637079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_1637079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637079 prefixEnd_1637079 := by exact prefixLift 1637079
  have htrace : WordTrace (prefixWord ++ tailWord_1637079) baseStart_1637079 baseEnd_1637079 := by
    simpa [prefixWord, tailWord_1637079, baseEnd_1637079] using wordTrace_append hprefix tailTrace_1637079
  have hstable : (prefixWord ++ tailWord_1637079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637079).length < 2 ^ (prefixWord ++ tailWord_1637079).sum := by decide
  have hdescent : baseEnd_1637079 < baseStart_1637079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637141 : List Nat := [1, 3, 2, 1, 2, 2, 1, 4, 3, 3]
def baseStart_1637141 : Nat := 118140960795 + 1637141 * 2 ^ 59
def prefixEnd_1637141 : Nat := 4983230072969 + 3 ^ 40 * 1637141 * 2
def baseEnd_1637141 : Nat := 560426821454989608005621

theorem tailTrace_1637141 : CollatzResearch.WordTrace tailWord_1637141 prefixEnd_1637141 560426821454989608005621 := by
  unfold tailWord_1637141
  simp only [CollatzResearch.WordTrace]
  refine ⟨59711437761925233267703277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39807625174616822178468851 59711437761925233267703277)
  ·
    refine ⟨22391789160721962475388729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59711437761925233267703277 22391789160721962475388729)
    ·
      refine ⟨16793841870541471856541547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22391789160721962475388729 16793841870541471856541547)
      ·
        refine ⟨25190762805812207784812321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16793841870541471856541547 25190762805812207784812321)
        ·
          refine ⟨18893072104359155838609241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25190762805812207784812321 18893072104359155838609241)
          ·
            refine ⟨14169804078269366878956931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18893072104359155838609241 14169804078269366878956931)
            ·
              refine ⟨21254706117404050318435397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14169804078269366878956931 21254706117404050318435397)
              ·
                refine ⟨3985257397013259434706637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21254706117404050318435397 3985257397013259434706637)
                ·
                  refine ⟨1494471523879972288014989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3985257397013259434706637 1494471523879972288014989)
                  ·
                    refine ⟨560426821454989608005621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1494471523879972288014989 560426821454989608005621)
                    ·
                      rfl

theorem cell22_1637141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_1637141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637141 prefixEnd_1637141 := by exact prefixLift 1637141
  have htrace : WordTrace (prefixWord ++ tailWord_1637141) baseStart_1637141 baseEnd_1637141 := by
    simpa [prefixWord, tailWord_1637141, baseEnd_1637141] using wordTrace_append hprefix tailTrace_1637141
  have hstable : (prefixWord ++ tailWord_1637141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637141).length < 2 ^ (prefixWord ++ tailWord_1637141).sum := by decide
  have hdescent : baseEnd_1637141 < baseStart_1637141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637143 : List Nat := [1, 1, 3, 4, 3, 2, 2, 6]
def baseStart_1637143 : Nat := 118140960795 + 1637143 * 2 ^ 59
def prefixEnd_1637143 : Nat := 4983230072969 + 3 ^ 40 * 1637143 * 2
def baseEnd_1637143 : Nat := 62269722899540252161735

theorem tailTrace_1637143 : CollatzResearch.WordTrace tailWord_1637143 prefixEnd_1637143 62269722899540252161735 := by
  unfold tailWord_1637143
  simp only [CollatzResearch.WordTrace]
  refine ⟨59711510707917987609276083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39807673805278658406184055 59711510707917987609276083)
  ·
    refine ⟨89567266061876981413914125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59711510707917987609276083 89567266061876981413914125)
    ·
      refine ⟨33587724773203868030217797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89567266061876981413914125 33587724773203868030217797)
      ·
        refine ⟨6297698394975725255665837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33587724773203868030217797 6297698394975725255665837)
        ·
          refine ⟨2361636898115896970874689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6297698394975725255665837 2361636898115896970874689)
          ·
            refine ⟨1771227673586922728156017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2361636898115896970874689 1771227673586922728156017)
            ·
              refine ⟨1328420755190192046117013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1771227673586922728156017 1328420755190192046117013)
              ·
                refine ⟨62269722899540252161735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1328420755190192046117013 62269722899540252161735)
                ·
                  rfl

theorem cell22_1637143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 6].length) (baseStart_1637143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637143 prefixEnd_1637143 := by exact prefixLift 1637143
  have htrace : WordTrace (prefixWord ++ tailWord_1637143) baseStart_1637143 baseEnd_1637143 := by
    simpa [prefixWord, tailWord_1637143, baseEnd_1637143] using wordTrace_append hprefix tailTrace_1637143
  have hstable : (prefixWord ++ tailWord_1637143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637143).length < 2 ^ (prefixWord ++ tailWord_1637143).sum := by decide
  have hdescent : baseEnd_1637143 < baseStart_1637143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637175 : List Nat := [1, 1, 3, 1, 2, 1, 7, 2, 1, 3]
def baseStart_1637175 : Nat := 118140960795 + 1637175 * 2 ^ 59
def prefixEnd_1637175 : Nat := 4983230072969 + 3 ^ 40 * 1637175 * 2
def baseEnd_1637175 : Nat := 560438460349824852655517

theorem tailTrace_1637175 : CollatzResearch.WordTrace tailWord_1637175 prefixEnd_1637175 560438460349824852655517 := by
  unfold tailWord_1637175
  simp only [CollatzResearch.WordTrace]
  refine ⟨59712677843802057074440979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39808451895868038049627319 59712677843802057074440979)
  ·
    refine ⟨89569016765703085611661469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59712677843802057074440979 89569016765703085611661469)
    ·
      refine ⟨33588381287138657104373051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89569016765703085611661469 33588381287138657104373051)
      ·
        refine ⟨50382571930707985656559577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33588381287138657104373051 50382571930707985656559577)
        ·
          refine ⟨37786928948030989242419683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50382571930707985656559577 37786928948030989242419683)
          ·
            refine ⟨56680393422046483863629525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37786928948030989242419683 56680393422046483863629525)
            ·
              refine ⟨1328446720829214465553817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 56680393422046483863629525 1328446720829214465553817)
              ·
                refine ⟨996335040621910849165363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1328446720829214465553817 996335040621910849165363)
                ·
                  refine ⟨1494502560932866273748045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 996335040621910849165363 1494502560932866273748045)
                  ·
                    refine ⟨560438460349824852655517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1494502560932866273748045 560438460349824852655517)
                    ·
                      rfl

theorem cell22_1637175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 1, 3].length) (baseStart_1637175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637175 prefixEnd_1637175 := by exact prefixLift 1637175
  have htrace : WordTrace (prefixWord ++ tailWord_1637175) baseStart_1637175 baseEnd_1637175 := by
    simpa [prefixWord, tailWord_1637175, baseEnd_1637175] using wordTrace_append hprefix tailTrace_1637175
  have hstable : (prefixWord ++ tailWord_1637175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637175).length < 2 ^ (prefixWord ++ tailWord_1637175).sum := by decide
  have hdescent : baseEnd_1637175 < baseStart_1637175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637231 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 4, 3]
def baseStart_1637231 : Nat := 118140960795 + 1637231 * 2 ^ 59
def prefixEnd_1637231 : Nat := 4983230072969 + 3 ^ 40 * 1637231 * 2
def baseEnd_1637231 : Nat := 560457630294259373255345

theorem tailTrace_1637231 : CollatzResearch.WordTrace tailWord_1637231 prefixEnd_1637231 560457630294259373255345 := by
  unfold tailWord_1637231
  simp only [CollatzResearch.WordTrace]
  refine ⟨59714720331599178638479547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39809813554399452425653031 59714720331599178638479547)
  ·
    refine ⟨89572080497398767957719321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59714720331599178638479547 89572080497398767957719321)
    ·
      refine ⟨67179060373049075968289491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89572080497398767957719321 67179060373049075968289491)
      ·
        refine ⟨100768590559573613952434237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67179060373049075968289491 100768590559573613952434237)
        ·
          refine ⟨37788221459840105232162839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100768590559573613952434237 37788221459840105232162839)
          ·
            refine ⟨56682332189760157848244259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37788221459840105232162839 56682332189760157848244259)
            ·
              refine ⟨85023498284640236772366389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56682332189760157848244259 85023498284640236772366389)
              ·
                refine ⟨7970952964185022197409349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85023498284640236772366389 7970952964185022197409349)
                ·
                  refine ⟨1494553680784691662014253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7970952964185022197409349 1494553680784691662014253)
                  ·
                    refine ⟨560457630294259373255345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1494553680784691662014253 560457630294259373255345)
                    ·
                      rfl

theorem cell22_1637231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 3].length) (baseStart_1637231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637231 prefixEnd_1637231 := by exact prefixLift 1637231
  have htrace : WordTrace (prefixWord ++ tailWord_1637231) baseStart_1637231 baseEnd_1637231 := by
    simpa [prefixWord, tailWord_1637231, baseEnd_1637231] using wordTrace_append hprefix tailTrace_1637231
  have hstable : (prefixWord ++ tailWord_1637231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637231).length < 2 ^ (prefixWord ++ tailWord_1637231).sum := by decide
  have hdescent : baseEnd_1637231 < baseStart_1637231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637233 : List Nat := [1, 2, 2, 2, 1, 5, 1, 4, 4]
def baseStart_1637233 : Nat := 118140960795 + 1637233 * 2 ^ 59
def prefixEnd_1637233 : Nat := 4983230072969 + 3 ^ 40 * 1637233 * 2
def baseEnd_1637233 : Nat := 186819438311710678235113

theorem tailTrace_1637233 : CollatzResearch.WordTrace tailWord_1637233 prefixEnd_1637233 186819438311710678235113 := by
  unfold tailWord_1637233
  simp only [CollatzResearch.WordTrace]
  refine ⟨59714793277591932980052353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39809862185061288653368235 59714793277591932980052353)
  ·
    refine ⟨44786094958193949735039265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59714793277591932980052353 44786094958193949735039265)
    ·
      refine ⟨33589571218645462301279449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44786094958193949735039265 33589571218645462301279449)
      ·
        refine ⟨25192178413984096725959587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33589571218645462301279449 25192178413984096725959587)
        ·
          refine ⟨37788267620976145088939381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25192178413984096725959587 37788267620976145088939381)
          ·
            refine ⟨3542650089466513602088067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37788267620976145088939381 3542650089466513602088067)
            ·
              refine ⟨5313975134199770403132101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3542650089466513602088067 5313975134199770403132101)
              ·
                refine ⟨996370337662456950587269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5313975134199770403132101 996370337662456950587269)
                ·
                  refine ⟨186819438311710678235113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 996370337662456950587269 186819438311710678235113)
                  ·
                    rfl

theorem cell22_1637233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 4].length) (baseStart_1637233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637233 prefixEnd_1637233 := by exact prefixLift 1637233
  have htrace : WordTrace (prefixWord ++ tailWord_1637233) baseStart_1637233 baseEnd_1637233 := by
    simpa [prefixWord, tailWord_1637233, baseEnd_1637233] using wordTrace_append hprefix tailTrace_1637233
  have hstable : (prefixWord ++ tailWord_1637233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637233).length < 2 ^ (prefixWord ++ tailWord_1637233).sum := by decide
  have hdescent : baseEnd_1637233 < baseStart_1637233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637282 : List Nat := [3, 3, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_1637282 : Nat := 118140960795 + 1637282 * 2 ^ 59
def prefixEnd_1637282 : Nat := 4983230072969 + 3 ^ 40 * 1637282 * 2
def baseEnd_1637282 : Nat := 560475088636512240230189

theorem tailTrace_1637282 : CollatzResearch.WordTrace tailWord_1637282 prefixEnd_1637282 560475088636512240230189 := by
  unfold tailWord_1637282
  simp only [CollatzResearch.WordTrace]
  refine ⟨14929145113603603587146525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39811053636276276232390733 14929145113603603587146525)
  ·
    refine ⟨5598429417601351345179947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14929145113603603587146525 5598429417601351345179947)
    ·
      refine ⟨8397644126402027017769921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5598429417601351345179947 8397644126402027017769921)
      ·
        refine ⟨6298233094801520263327441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8397644126402027017769921 6298233094801520263327441)
        ·
          refine ⟨4723674821101140197495581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6298233094801520263327441 4723674821101140197495581)
          ·
            refine ⟨1771378057912927574060843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4723674821101140197495581 1771378057912927574060843)
            ·
              refine ⟨2657067086869391361091265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1771378057912927574060843 2657067086869391361091265)
              ·
                refine ⟨1992800315152043520818449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2657067086869391361091265 1992800315152043520818449)
                ·
                  refine ⟨1494600236364032640613837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1992800315152043520818449 1494600236364032640613837)
                  ·
                    refine ⟨560475088636512240230189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1494600236364032640613837 560475088636512240230189)
                    ·
                      rfl

theorem cell22_1637282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_1637282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637282 prefixEnd_1637282 := by exact prefixLift 1637282
  have htrace : WordTrace (prefixWord ++ tailWord_1637282) baseStart_1637282 baseEnd_1637282 := by
    simpa [prefixWord, tailWord_1637282, baseEnd_1637282] using wordTrace_append hprefix tailTrace_1637282
  have hstable : (prefixWord ++ tailWord_1637282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637282).length < 2 ^ (prefixWord ++ tailWord_1637282).sum := by decide
  have hdescent : baseEnd_1637282 < baseStart_1637282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637318 : List Nat := [6, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_1637318 : Nat := 118140960795 + 1637318 * 2 ^ 59
def prefixEnd_1637318 : Nat := 4983230072969 + 3 ^ 40 * 1637318 * 2
def baseEnd_1637318 : Nat := 186829137390740048776693

theorem tailTrace_1637318 : CollatzResearch.WordTrace tailWord_1637318 prefixEnd_1637318 186829137390740048776693 := by
  unfold tailWord_1637318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1866184171321374765528019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39811928988189328331264405 1866184171321374765528019)
  ·
    refine ⟨2799276256982062148292029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1866184171321374765528019 2799276256982062148292029)
    ·
      refine ⟨1049728596368273305609511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2799276256982062148292029 1049728596368273305609511)
      ·
        refine ⟨1574592894552409958414267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1049728596368273305609511 1574592894552409958414267)
        ·
          refine ⟨2361889341828614937621401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1574592894552409958414267 2361889341828614937621401)
          ·
            refine ⟨1771417006371461203216051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2361889341828614937621401 1771417006371461203216051)
            ·
              refine ⟨2657125509557191804824077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1771417006371461203216051 2657125509557191804824077)
              ·
                refine ⟨996422066083946926809029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2657125509557191804824077 996422066083946926809029)
                ·
                  refine ⟨186829137390740048776693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 996422066083946926809029 186829137390740048776693)
                  ·
                    rfl

theorem cell22_1637318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_1637318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637318 prefixEnd_1637318 := by exact prefixLift 1637318
  have htrace : WordTrace (prefixWord ++ tailWord_1637318) baseStart_1637318 baseEnd_1637318 := by
    simpa [prefixWord, tailWord_1637318, baseEnd_1637318] using wordTrace_append hprefix tailTrace_1637318
  have hstable : (prefixWord ++ tailWord_1637318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637318).length < 2 ^ (prefixWord ++ tailWord_1637318).sum := by decide
  have hdescent : baseEnd_1637318 < baseStart_1637318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637327 : List Nat := [1, 1, 2, 1, 1, 8, 1, 3, 1, 3]
def baseStart_1637327 : Nat := 118140960795 + 1637327 * 2 ^ 59
def prefixEnd_1637327 : Nat := 4983230072969 + 3 ^ 40 * 1637327 * 2
def baseEnd_1637327 : Nat := 560490493056147122855051

theorem tailTrace_1637327 : CollatzResearch.WordTrace tailWord_1637327 prefixEnd_1637327 560490493056147122855051 := by
  unfold tailWord_1637327
  simp only [CollatzResearch.WordTrace]
  refine ⟨59718221739251387033974235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39812147826167591355982823 59718221739251387033974235)
  ·
    refine ⟨89577332608877080550961353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59718221739251387033974235 89577332608877080550961353)
    ·
      refine ⟨67182999456657810413221015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89577332608877080550961353 67182999456657810413221015)
      ·
        refine ⟨100774499184986715619831523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67182999456657810413221015 100774499184986715619831523)
        ·
          refine ⟨151161748777480073429747285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100774499184986715619831523 151161748777480073429747285)
          ·
            refine ⟨1771426743486094610504851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 151161748777480073429747285 1771426743486094610504851)
            ·
              refine ⟨2657140115229141915757277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1771426743486094610504851 2657140115229141915757277)
              ·
                refine ⟨996427543210928218408979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2657140115229141915757277 996427543210928218408979)
                ·
                  refine ⟨1494641314816392327613469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 996427543210928218408979 1494641314816392327613469)
                  ·
                    refine ⟨560490493056147122855051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1494641314816392327613469 560490493056147122855051)
                    ·
                      rfl

theorem cell22_1637327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 1, 3].length) (baseStart_1637327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637327 prefixEnd_1637327 := by exact prefixLift 1637327
  have htrace : WordTrace (prefixWord ++ tailWord_1637327) baseStart_1637327 baseEnd_1637327 := by
    simpa [prefixWord, tailWord_1637327, baseEnd_1637327] using wordTrace_append hprefix tailTrace_1637327
  have hstable : (prefixWord ++ tailWord_1637327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637327).length < 2 ^ (prefixWord ++ tailWord_1637327).sum := by decide
  have hdescent : baseEnd_1637327 < baseStart_1637327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637383 : List Nat := [1, 1, 4, 3, 1, 1, 3, 2, 1, 5]
def baseStart_1637383 : Nat := 118140960795 + 1637383 * 2 ^ 59
def prefixEnd_1637383 : Nat := 4983230072969 + 3 ^ 40 * 1637383 * 2
def baseEnd_1637383 : Nat := 560509663000581643454879

theorem tailTrace_1637383 : CollatzResearch.WordTrace tailWord_1637383 prefixEnd_1637383 560509663000581643454879 := by
  unfold tailWord_1637383
  simp only [CollatzResearch.WordTrace]
  refine ⟨59720264227048508598012803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39813509484699005732008535 59720264227048508598012803)
  ·
    refine ⟨89580396340572762897019205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59720264227048508598012803 89580396340572762897019205)
    ·
      refine ⟨16796324313857393043191101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89580396340572762897019205 16796324313857393043191101)
      ·
        refine ⟨6298621617696522391196663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16796324313857393043191101 6298621617696522391196663)
        ·
          refine ⟨9447932426544783586794995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6298621617696522391196663 9447932426544783586794995)
          ·
            refine ⟨14171898639817175380192493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9447932426544783586794995 14171898639817175380192493)
            ·
              refine ⟨5314461989931440767572185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14171898639817175380192493 5314461989931440767572185)
              ·
                refine ⟨3985846492448580575679139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5314461989931440767572185 3985846492448580575679139)
                ·
                  refine ⟨5978769738672870863518709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3985846492448580575679139 5978769738672870863518709)
                  ·
                    refine ⟨560509663000581643454879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5978769738672870863518709 560509663000581643454879)
                    ·
                      rfl

theorem cell22_1637383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_1637383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637383 prefixEnd_1637383 := by exact prefixLift 1637383
  have htrace : WordTrace (prefixWord ++ tailWord_1637383) baseStart_1637383 baseEnd_1637383 := by
    simpa [prefixWord, tailWord_1637383, baseEnd_1637383] using wordTrace_append hprefix tailTrace_1637383
  have hstable : (prefixWord ++ tailWord_1637383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637383).length < 2 ^ (prefixWord ++ tailWord_1637383).sum := by decide
  have hdescent : baseEnd_1637383 < baseStart_1637383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637400 : List Nat := [2, 1, 2, 3, 2, 2, 1, 4, 2, 3]
def baseStart_1637400 : Nat := 118140960795 + 1637400 * 2 ^ 59
def prefixEnd_1637400 : Nat := 4983230072969 + 3 ^ 40 * 1637400 * 2
def baseEnd_1637400 : Nat := 560515482447999265779827

theorem tailTrace_1637400 : CollatzResearch.WordTrace tailWord_1637400 prefixEnd_1637400 560515482447999265779827 := by
  unfold tailWord_1637400
  simp only [CollatzResearch.WordTrace]
  refine ⟨29860442133993460250690827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39813922845324613667587769 29860442133993460250690827)
  ·
    refine ⟨44790663200990190376036241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29860442133993460250690827 44790663200990190376036241)
    ·
      refine ⟨33592997400742642782027181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44790663200990190376036241 33592997400742642782027181)
      ·
        refine ⟨12597374025278491043260193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33592997400742642782027181 12597374025278491043260193)
        ·
          refine ⟨9448030518958868282445145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12597374025278491043260193 9448030518958868282445145)
          ·
            refine ⟨7086022889219151211833859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9448030518958868282445145 7086022889219151211833859)
            ·
              refine ⟨10629034333828726817750789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7086022889219151211833859 10629034333828726817750789)
              ·
                refine ⟨1992943937592886278328273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10629034333828726817750789 1992943937592886278328273)
                ·
                  refine ⟨1494707953194664708746205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1992943937592886278328273 1494707953194664708746205)
                  ·
                    refine ⟨560515482447999265779827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1494707953194664708746205 560515482447999265779827)
                    ·
                      rfl

theorem cell22_1637400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_1637400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637400 prefixEnd_1637400 := by exact prefixLift 1637400
  have htrace : WordTrace (prefixWord ++ tailWord_1637400) baseStart_1637400 baseEnd_1637400 := by
    simpa [prefixWord, tailWord_1637400, baseEnd_1637400] using wordTrace_append hprefix tailTrace_1637400
  have hstable : (prefixWord ++ tailWord_1637400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637400).length < 2 ^ (prefixWord ++ tailWord_1637400).sum := by decide
  have hdescent : baseEnd_1637400 < baseStart_1637400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637473 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 2, 5]
def baseStart_1637473 : Nat := 118140960795 + 1637473 * 2 ^ 59
def prefixEnd_1637473 : Nat := 4983230072969 + 3 ^ 40 * 1637473 * 2
def baseEnd_1637473 : Nat := 560540471839851408704603

theorem tailTrace_1637473 : CollatzResearch.WordTrace tailWord_1637473 prefixEnd_1637473 560540471839851408704603 := by
  unfold tailWord_1637473
  simp only [CollatzResearch.WordTrace]
  refine ⟨59723546796722453968789073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39815697864481635979192715 59723546796722453968789073)
  ·
    refine ⟨44792660097541840476591805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59723546796722453968789073 44792660097541840476591805)
    ·
      refine ⟨16797247536578190178721927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44792660097541840476591805 16797247536578190178721927)
      ·
        refine ⟨25195871304867285268082891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16797247536578190178721927 25195871304867285268082891)
        ·
          refine ⟨37793806957300927902124337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25195871304867285268082891 37793806957300927902124337)
          ·
            refine ⟨28345355217975695926593253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37793806957300927902124337 28345355217975695926593253)
            ·
              refine ⟨5314754103370442986236235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28345355217975695926593253 5314754103370442986236235)
              ·
                refine ⟨7972131155055664479354353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5314754103370442986236235 7972131155055664479354353)
                ·
                  refine ⟨5979098366291748359515765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7972131155055664479354353 5979098366291748359515765)
                  ·
                    refine ⟨560540471839851408704603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5979098366291748359515765 560540471839851408704603)
                    ·
                      rfl

theorem cell22_1637473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_1637473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637473 prefixEnd_1637473 := by exact prefixLift 1637473
  have htrace : WordTrace (prefixWord ++ tailWord_1637473) baseStart_1637473 baseEnd_1637473 := by
    simpa [prefixWord, tailWord_1637473, baseEnd_1637473] using wordTrace_append hprefix tailTrace_1637473
  have hstable : (prefixWord ++ tailWord_1637473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637473).length < 2 ^ (prefixWord ++ tailWord_1637473).sum := by decide
  have hdescent : baseEnd_1637473 < baseStart_1637473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637569 : List Nat := [1, 2, 6, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1637569 : Nat := 118140960795 + 1637569 * 2 ^ 59
def prefixEnd_1637569 : Nat := 4983230072969 + 3 ^ 40 * 1637569 * 2
def baseEnd_1637569 : Nat := 560573334601739158304309

theorem tailTrace_1637569 : CollatzResearch.WordTrace tailWord_1637569 prefixEnd_1637569 560573334601739158304309 := by
  unfold tailWord_1637569
  simp only [CollatzResearch.WordTrace]
  refine ⟨59727048204374662364283761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39818032136249774909522507 59727048204374662364283761)
  ·
    refine ⟨44795286153280996773212821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59727048204374662364283761 44795286153280996773212821)
    ·
      refine ⟨2099779038435046723744351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44795286153280996773212821 2099779038435046723744351)
      ·
        refine ⟨3149668557652570085616527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2099779038435046723744351 3149668557652570085616527)
        ·
          refine ⟨4724502836478855128424791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3149668557652570085616527 4724502836478855128424791)
          ·
            refine ⟨7086754254718282692637187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4724502836478855128424791 7086754254718282692637187)
            ·
              refine ⟨10630131382077424038955781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7086754254718282692637187 10630131382077424038955781)
              ·
                refine ⟨1993149634139517007304209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10630131382077424038955781 1993149634139517007304209)
                ·
                  refine ⟨1494862225604637755478157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1993149634139517007304209 1494862225604637755478157)
                  ·
                    refine ⟨560573334601739158304309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1494862225604637755478157 560573334601739158304309)
                    ·
                      rfl

theorem cell22_1637569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1637569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637569 prefixEnd_1637569 := by exact prefixLift 1637569
  have htrace : WordTrace (prefixWord ++ tailWord_1637569) baseStart_1637569 baseEnd_1637569 := by
    simpa [prefixWord, tailWord_1637569, baseEnd_1637569] using wordTrace_append hprefix tailTrace_1637569
  have hstable : (prefixWord ++ tailWord_1637569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637569).length < 2 ^ (prefixWord ++ tailWord_1637569).sum := by decide
  have hdescent : baseEnd_1637569 < baseStart_1637569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637582 : List Nat := [4, 1, 1, 1, 5, 2, 1, 7]
def baseStart_1637582 : Nat := 118140960795 + 1637582 * 2 ^ 59
def prefixEnd_1637582 : Nat := 4983230072969 + 3 ^ 40 * 1637582 * 2
def baseEnd_1637582 : Nat := 62286420529712384192141

theorem tailTrace_1637582 : CollatzResearch.WordTrace tailWord_1637582 prefixEnd_1637582 62286420529712384192141 := by
  unfold tailWord_1637582
  simp only [CollatzResearch.WordTrace]
  refine ⟨7465940294165945698063375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39818348235551710389671333 7465940294165945698063375)
  ·
    refine ⟨11198910441248918547095063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7465940294165945698063375 11198910441248918547095063)
    ·
      refine ⟨16798365661873377820642595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11198910441248918547095063 16798365661873377820642595)
      ·
        refine ⟨25197548492810066730963893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16798365661873377820642595 25197548492810066730963893)
        ·
          refine ⟨2362270171200943756027865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25197548492810066730963893 2362270171200943756027865)
          ·
            refine ⟨1771702628400707817020899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2362270171200943756027865 1771702628400707817020899)
            ·
              refine ⟨2657553942601061725531349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1771702628400707817020899 2657553942601061725531349)
              ·
                refine ⟨62286420529712384192141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2657553942601061725531349 62286420529712384192141)
                ·
                  rfl

theorem cell22_1637582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_1637582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637582 prefixEnd_1637582 := by exact prefixLift 1637582
  have htrace : WordTrace (prefixWord ++ tailWord_1637582) baseStart_1637582 baseEnd_1637582 := by
    simpa [prefixWord, tailWord_1637582, baseEnd_1637582] using wordTrace_append hprefix tailTrace_1637582
  have hstable : (prefixWord ++ tailWord_1637582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637582).length < 2 ^ (prefixWord ++ tailWord_1637582).sum := by decide
  have hdescent : baseEnd_1637582 < baseStart_1637582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637593 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 9]
def baseStart_1637593 : Nat := 118140960795 + 1637593 * 2 ^ 59
def prefixEnd_1637593 : Nat := 4983230072969 + 3 ^ 40 * 1637593 * 2
def baseEnd_1637593 : Nat := 186860516764070365234745

theorem tailTrace_1637593 : CollatzResearch.WordTrace tailWord_1637593 prefixEnd_1637593 186860516764070365234745 := by
  unfold tailWord_1637593
  simp only [CollatzResearch.WordTrace]
  refine ⟨59727923556287714463157433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39818615704191809642104955 59727923556287714463157433)
  ·
    refine ⟨44795942667215785847368075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59727923556287714463157433 44795942667215785847368075)
    ·
      refine ⟨67193914000823678771052113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44795942667215785847368075 67193914000823678771052113)
      ·
        refine ⟨50395435500617759078289085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67193914000823678771052113 50395435500617759078289085)
        ·
          refine ⟨18898288312731659654358407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50395435500617759078289085 18898288312731659654358407)
          ·
            refine ⟨28347432469097489481537611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18898288312731659654358407 28347432469097489481537611)
            ·
              refine ⟨42521148703646234222306417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28347432469097489481537611 42521148703646234222306417)
              ·
                refine ⟨31890861527734675666729813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42521148703646234222306417 31890861527734675666729813)
                ·
                  refine ⟨186860516764070365234745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31890861527734675666729813 186860516764070365234745)
                  ·
                    rfl

theorem cell22_1637593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 9].length) (baseStart_1637593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637593 prefixEnd_1637593 := by exact prefixLift 1637593
  have htrace : WordTrace (prefixWord ++ tailWord_1637593) baseStart_1637593 baseEnd_1637593 := by
    simpa [prefixWord, tailWord_1637593, baseEnd_1637593] using wordTrace_append hprefix tailTrace_1637593
  have hstable : (prefixWord ++ tailWord_1637593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637593).length < 2 ^ (prefixWord ++ tailWord_1637593).sum := by decide
  have hdescent : baseEnd_1637593 < baseStart_1637593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637614 : List Nat := [4, 1, 2, 1, 1, 1, 3, 5, 1, 3]
def baseStart_1637614 : Nat := 118140960795 + 1637614 * 2 ^ 59
def prefixEnd_1637614 : Nat := 4983230072969 + 3 ^ 40 * 1637614 * 2
def baseEnd_1637614 : Nat := 560588739021374040929171

theorem tailTrace_1637614 : CollatzResearch.WordTrace tailWord_1637614 prefixEnd_1637614 560588739021374040929171 := by
  unfold tailWord_1637614
  simp only [CollatzResearch.WordTrace]
  refine ⟨7466086186151454381208987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39819126326141090033114597 7466086186151454381208987)
  ·
    refine ⟨11199129279227181571813481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7466086186151454381208987 11199129279227181571813481)
    ·
      refine ⟨8399346959420386178860111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11199129279227181571813481 8399346959420386178860111)
      ·
        refine ⟨12599020439130579268290167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8399346959420386178860111 12599020439130579268290167)
        ·
          refine ⟨18898530658695868902435251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12599020439130579268290167 18898530658695868902435251)
          ·
            refine ⟨28347795988043803353652877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18898530658695868902435251 28347795988043803353652877)
            ·
              refine ⟨10630423495516426257619829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28347795988043803353652877 10630423495516426257619829)
              ·
                refine ⟨996602202704664961651859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10630423495516426257619829 996602202704664961651859)
                ·
                  refine ⟨1494903304056997442477789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 996602202704664961651859 1494903304056997442477789)
                  ·
                    refine ⟨560588739021374040929171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1494903304056997442477789 560588739021374040929171)
                    ·
                      rfl

theorem cell22_1637614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_1637614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637614 prefixEnd_1637614 := by exact prefixLift 1637614
  have htrace : WordTrace (prefixWord ++ tailWord_1637614) baseStart_1637614 baseEnd_1637614 := by
    simpa [prefixWord, tailWord_1637614, baseEnd_1637614] using wordTrace_append hprefix tailTrace_1637614
  have hstable : (prefixWord ++ tailWord_1637614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637614).length < 2 ^ (prefixWord ++ tailWord_1637614).sum := by decide
  have hdescent : baseEnd_1637614 < baseStart_1637614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637620 : List Nat := [2, 6, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_1637620 : Nat := 118140960795 + 1637620 * 2 ^ 59
def prefixEnd_1637620 : Nat := 4983230072969 + 3 ^ 40 * 1637620 * 2
def baseEnd_1637620 : Nat := 560590792943992025279153

theorem tailTrace_1637620 : CollatzResearch.WordTrace tailWord_1637620 prefixEnd_1637620 560590792943992025279153 := by
  unfold tailWord_1637620
  simp only [CollatzResearch.WordTrace]
  refine ⟨29864454163594949037195157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39819272218126598716260209 29864454163594949037195157)
  ·
    refine ⟨1399896288918513236118523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29864454163594949037195157 1399896288918513236118523)
    ·
      refine ⟨2099844433377769854177785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1399896288918513236118523 2099844433377769854177785)
      ·
        refine ⟨1574883325033327390633339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2099844433377769854177785 1574883325033327390633339)
        ·
          refine ⟨2362324987549991085950009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1574883325033327390633339 2362324987549991085950009)
          ·
            refine ⟨1771743740662493314462507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2362324987549991085950009 1771743740662493314462507)
            ·
              refine ⟨2657615610993739971693761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1771743740662493314462507 2657615610993739971693761)
              ·
                refine ⟨1993211708245304978770321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2657615610993739971693761 1993211708245304978770321)
                ·
                  refine ⟨1494908781183978734077741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1993211708245304978770321 1494908781183978734077741)
                  ·
                    refine ⟨560590792943992025279153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1494908781183978734077741 560590792943992025279153)
                    ·
                      rfl

theorem cell22_1637620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_1637620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637620 prefixEnd_1637620 := by exact prefixLift 1637620
  have htrace : WordTrace (prefixWord ++ tailWord_1637620) baseStart_1637620 baseEnd_1637620 := by
    simpa [prefixWord, tailWord_1637620, baseEnd_1637620] using wordTrace_append hprefix tailTrace_1637620
  have hstable : (prefixWord ++ tailWord_1637620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637620).length < 2 ^ (prefixWord ++ tailWord_1637620).sum := by decide
  have hdescent : baseEnd_1637620 < baseStart_1637620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637655 : List Nat := [1, 1, 3, 4, 1, 1, 1, 4, 6]
def baseStart_1637655 : Nat := 118140960795 + 1637655 * 2 ^ 59
def prefixEnd_1637655 : Nat := 4983230072969 + 3 ^ 40 * 1637655 * 2
def baseEnd_1637655 : Nat := 186867591386421200218015

theorem tailTrace_1637655 : CollatzResearch.WordTrace tailWord_1637655 prefixEnd_1637655 186867591386421200218015 := by
  unfold tailWord_1637655
  simp only [CollatzResearch.WordTrace]
  refine ⟨59730184882063099051914419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39820123254708732701276279 59730184882063099051914419)
  ·
    refine ⟨89595277323094648577871629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59730184882063099051914419 89595277323094648577871629)
    ·
      refine ⟨33598228996160493216701861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89595277323094648577871629 33598228996160493216701861)
      ·
        refine ⟨6299667936780092478131599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33598228996160493216701861 6299667936780092478131599)
        ·
          refine ⟨9449501905170138717197399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6299667936780092478131599 9449501905170138717197399)
          ·
            refine ⟨14174252857755208075796099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9449501905170138717197399 14174252857755208075796099)
            ·
              refine ⟨21261379286632812113694149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14174252857755208075796099 21261379286632812113694149)
              ·
                refine ⟨3986508616243652271317653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21261379286632812113694149 3986508616243652271317653)
                ·
                  refine ⟨186867591386421200218015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3986508616243652271317653 186867591386421200218015)
                  ·
                    rfl

theorem cell22_1637655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 6].length) (baseStart_1637655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637655 prefixEnd_1637655 := by exact prefixLift 1637655
  have htrace : WordTrace (prefixWord ++ tailWord_1637655) baseStart_1637655 baseEnd_1637655 := by
    simpa [prefixWord, tailWord_1637655, baseEnd_1637655] using wordTrace_append hprefix tailTrace_1637655
  have hstable : (prefixWord ++ tailWord_1637655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637655).length < 2 ^ (prefixWord ++ tailWord_1637655).sum := by decide
  have hdescent : baseEnd_1637655 < baseStart_1637655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637674 : List Nat := [3, 1, 4, 2, 1, 1, 2, 3, 1, 4]
def baseStart_1637674 : Nat := 118140960795 + 1637674 * 2 ^ 59
def prefixEnd_1637674 : Nat := 4983230072969 + 3 ^ 40 * 1637674 * 2
def baseEnd_1637674 : Nat := 560609278247553884428987

theorem tailTrace_1637674 : CollatzResearch.WordTrace tailWord_1637674 prefixEnd_1637674 560609278247553884428987 := by
  unfold tailWord_1637674
  simp only [CollatzResearch.WordTrace]
  refine ⟨14932719467248566324214019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39820585245996176864570717 14932719467248566324214019)
  ·
    refine ⟨22399079200872849486321029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14932719467248566324214019 22399079200872849486321029)
    ·
      refine ⟨4199827350163659278685193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22399079200872849486321029 4199827350163659278685193)
      ·
        refine ⟨3149870512622744459013895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4199827350163659278685193 3149870512622744459013895)
        ·
          refine ⟨4724805768934116688520843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3149870512622744459013895 4724805768934116688520843)
          ·
            refine ⟨7087208653401175032781265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4724805768934116688520843 7087208653401175032781265)
            ·
              refine ⟨5315406490050881274585949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7087208653401175032781265 5315406490050881274585949)
              ·
                refine ⟨1993277433769080477969731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5315406490050881274585949 1993277433769080477969731)
                ·
                  refine ⟨2989916150653620716954597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1993277433769080477969731 2989916150653620716954597)
                  ·
                    refine ⟨560609278247553884428987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2989916150653620716954597 560609278247553884428987)
                    ·
                      rfl

theorem cell22_1637674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_1637674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637674 prefixEnd_1637674 := by exact prefixLift 1637674
  have htrace : WordTrace (prefixWord ++ tailWord_1637674) baseStart_1637674 baseEnd_1637674 := by
    simpa [prefixWord, tailWord_1637674, baseEnd_1637674] using wordTrace_append hprefix tailTrace_1637674
  have hstable : (prefixWord ++ tailWord_1637674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637674).length < 2 ^ (prefixWord ++ tailWord_1637674).sum := by decide
  have hdescent : baseEnd_1637674 < baseStart_1637674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637689 : List Nat := [1, 2, 1, 6, 2, 2, 1, 1, 6]
def baseStart_1637689 : Nat := 118140960795 + 1637689 * 2 ^ 59
def prefixEnd_1637689 : Nat := 4983230072969 + 3 ^ 40 * 1637689 * 2
def baseEnd_1637689 : Nat := 186871471018032948434647

theorem tailTrace_1637689 : CollatzResearch.WordTrace tailWord_1637689 prefixEnd_1637689 186871471018032948434647 := by
  unfold tailWord_1637689
  simp only [CollatzResearch.WordTrace]
  refine ⟨59731424963939922858652121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39820949975959948572434747 59731424963939922858652121)
  ·
    refine ⟨44798568722954942143989091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59731424963939922858652121 44798568722954942143989091)
    ·
      refine ⟨67197853084432413215983637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44798568722954942143989091 67197853084432413215983637)
      ·
        refine ⟨3149899363332769369499233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67197853084432413215983637 3149899363332769369499233)
        ·
          refine ⟨2362424522499577027124425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3149899363332769369499233 2362424522499577027124425)
          ·
            refine ⟨1771818391874682770343319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2362424522499577027124425 1771818391874682770343319)
            ·
              refine ⟨2657727587812024155514979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1771818391874682770343319 2657727587812024155514979)
              ·
                refine ⟨3986591381718036233272469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2657727587812024155514979 3986591381718036233272469)
                ·
                  refine ⟨186871471018032948434647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3986591381718036233272469 186871471018032948434647)
                  ·
                    rfl

theorem cell22_1637689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 6].length) (baseStart_1637689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637689 prefixEnd_1637689 := by exact prefixLift 1637689
  have htrace : WordTrace (prefixWord ++ tailWord_1637689) baseStart_1637689 baseEnd_1637689 := by
    simpa [prefixWord, tailWord_1637689, baseEnd_1637689] using wordTrace_append hprefix tailTrace_1637689
  have hstable : (prefixWord ++ tailWord_1637689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637689).length < 2 ^ (prefixWord ++ tailWord_1637689).sum := by decide
  have hdescent : baseEnd_1637689 < baseStart_1637689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637725 : List Nat := [1, 4, 5, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1637725 : Nat := 118140960795 + 1637725 * 2 ^ 59
def prefixEnd_1637725 : Nat := 4983230072969 + 3 ^ 40 * 1637725 * 2
def baseEnd_1637725 : Nat := 560626736589806751403831

theorem tailTrace_1637725 : CollatzResearch.WordTrace tailWord_1637725 prefixEnd_1637725 560626736589806751403831 := by
  unfold tailWord_1637725
  simp only [CollatzResearch.WordTrace]
  refine ⟨59732737991809501006962629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39821825327873000671308419 59732737991809501006962629)
  ·
    refine ⟨11199888373464281438805493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59732737991809501006962629 11199888373464281438805493)
    ·
      refine ⟨1049989535012276384888015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11199888373464281438805493 1049989535012276384888015)
      ·
        refine ⟨1574984302518414577332023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1049989535012276384888015 1574984302518414577332023)
        ·
          refine ⟨2362476453777621865998035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1574984302518414577332023 2362476453777621865998035)
          ·
            refine ⟨3543714680666432798997053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2362476453777621865998035 3543714680666432798997053)
            ·
              refine ⟨1328893005249912299623895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3543714680666432798997053 1328893005249912299623895)
              ·
                refine ⟨1993339507874868449435843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1328893005249912299623895 1993339507874868449435843)
                ·
                  refine ⟨2990009261812302674153765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1993339507874868449435843 2990009261812302674153765)
                  ·
                    refine ⟨560626736589806751403831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2990009261812302674153765 560626736589806751403831)
                    ·
                      rfl

theorem cell22_1637725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1637725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637725 prefixEnd_1637725 := by exact prefixLift 1637725
  have htrace : WordTrace (prefixWord ++ tailWord_1637725) baseStart_1637725 baseEnd_1637725 := by
    simpa [prefixWord, tailWord_1637725, baseEnd_1637725] using wordTrace_append hprefix tailTrace_1637725
  have hstable : (prefixWord ++ tailWord_1637725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637725).length < 2 ^ (prefixWord ++ tailWord_1637725).sum := by decide
  have hdescent : baseEnd_1637725 < baseStart_1637725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637745 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 7]
def baseStart_1637745 : Nat := 118140960795 + 1637745 * 2 ^ 59
def prefixEnd_1637745 : Nat := 4983230072969 + 3 ^ 40 * 1637745 * 2
def baseEnd_1637745 : Nat := 186877860999511121967923

theorem tailTrace_1637745 : CollatzResearch.WordTrace tailWord_1637745 prefixEnd_1637745 186877860999511121967923 := by
  unfold tailWord_1637745
  simp only [CollatzResearch.WordTrace]
  refine ⟨59733467451737044422690689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39822311634491362948460459 59733467451737044422690689)
  ·
    refine ⟨44800100588802783317018017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59733467451737044422690689 44800100588802783317018017)
    ·
      refine ⟨33600075441602087487763513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44800100588802783317018017 33600075441602087487763513)
      ·
        refine ⟨25200056581201565615822635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33600075441602087487763513 25200056581201565615822635)
        ·
          refine ⟨37800084871802348423733953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25200056581201565615822635 37800084871802348423733953)
          ·
            refine ⟨28350063653851761317800465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37800084871802348423733953 28350063653851761317800465)
            ·
              refine ⟨21262547740388820988350349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28350063653851761317800465 21262547740388820988350349)
              ·
                refine ⟨7973455402645807870631381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21262547740388820988350349 7973455402645807870631381)
                ·
                  refine ⟨186877860999511121967923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7973455402645807870631381 186877860999511121967923)
                  ·
                    rfl

theorem cell22_1637745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 7].length) (baseStart_1637745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637745 prefixEnd_1637745 := by exact prefixLift 1637745
  have htrace : WordTrace (prefixWord ++ tailWord_1637745) baseStart_1637745 baseEnd_1637745 := by
    simpa [prefixWord, tailWord_1637745, baseEnd_1637745] using wordTrace_append hprefix tailTrace_1637745
  have hstable : (prefixWord ++ tailWord_1637745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637745).length < 2 ^ (prefixWord ++ tailWord_1637745).sum := by decide
  have hdescent : baseEnd_1637745 < baseStart_1637745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637873 : List Nat := [1, 2, 2, 2, 3, 4, 2, 1, 2, 3]
def baseStart_1637873 : Nat := 118140960795 + 1637873 * 2 ^ 59
def prefixEnd_1637873 : Nat := 4983230072969 + 3 ^ 40 * 1637873 * 2
def baseEnd_1637873 : Nat := 560677400014383698703377

theorem tailTrace_1637873 : CollatzResearch.WordTrace tailWord_1637873 prefixEnd_1637873 560677400014383698703377 := by
  unfold tailWord_1637873
  simp only [CollatzResearch.WordTrace]
  refine ⟨59738135995273322283350273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39825423996848881522233515 59738135995273322283350273)
  ·
    refine ⟨44803601996454991712512705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59738135995273322283350273 44803601996454991712512705)
    ·
      refine ⟨33602701497341243784384529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44803601996454991712512705 33602701497341243784384529)
      ·
        refine ⟨25202026123005932838288397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33602701497341243784384529 25202026123005932838288397)
        ·
          refine ⟨9450759796127224814358149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25202026123005932838288397 9450759796127224814358149)
          ·
            refine ⟨1772017461773854652692153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9450759796127224814358149 1772017461773854652692153)
            ·
              refine ⟨1329013096330390989519115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1772017461773854652692153 1329013096330390989519115)
              ·
                refine ⟨1993519644495586484278673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1329013096330390989519115 1993519644495586484278673)
                ·
                  refine ⟨1495139733371689863209005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1993519644495586484278673 1495139733371689863209005)
                  ·
                    refine ⟨560677400014383698703377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1495139733371689863209005 560677400014383698703377)
                    ·
                      rfl

theorem cell22_1637873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 2, 3].length) (baseStart_1637873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637873 prefixEnd_1637873 := by exact prefixLift 1637873
  have htrace : WordTrace (prefixWord ++ tailWord_1637873) baseStart_1637873 baseEnd_1637873 := by
    simpa [prefixWord, tailWord_1637873, baseEnd_1637873] using wordTrace_append hprefix tailTrace_1637873
  have hstable : (prefixWord ++ tailWord_1637873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637873).length < 2 ^ (prefixWord ++ tailWord_1637873).sum := by decide
  have hdescent : baseEnd_1637873 < baseStart_1637873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637884 : List Nat := [2, 2, 2, 1, 2, 1, 2, 4, 3, 3]
def baseStart_1637884 : Nat := 118140960795 + 1637884 * 2 ^ 59
def prefixEnd_1637884 : Nat := 4983230072969 + 3 ^ 40 * 1637884 * 2
def baseEnd_1637884 : Nat := 560681165539183336678343

theorem tailTrace_1637884 : CollatzResearch.WordTrace tailWord_1637884 prefixEnd_1637884 560681165539183336678343 := by
  unfold tailWord_1637884
  simp only [CollatzResearch.WordTrace]
  refine ⟨29869268599116735581000353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39825691465488980774667137 29869268599116735581000353)
  ·
    refine ⟨22401951449337551685750265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29869268599116735581000353 22401951449337551685750265)
    ·
      refine ⟨16801463587003163764312699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22401951449337551685750265 16801463587003163764312699)
      ·
        refine ⟨25202195380504745646469049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16801463587003163764312699 25202195380504745646469049)
        ·
          refine ⟨18901646535378559234851787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25202195380504745646469049 18901646535378559234851787)
          ·
            refine ⟨28352469803067838852277681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18901646535378559234851787 28352469803067838852277681)
            ·
              refine ⟨21264352352300879139208261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28352469803067838852277681 21264352352300879139208261)
              ·
                refine ⟨3987066066056414838601549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21264352352300879139208261 3987066066056414838601549)
                ·
                  refine ⟨1495149774771155564475581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3987066066056414838601549 1495149774771155564475581)
                  ·
                    refine ⟨560681165539183336678343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1495149774771155564475581 560681165539183336678343)
                    ·
                      rfl

theorem cell22_1637884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_1637884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637884 prefixEnd_1637884 := by exact prefixLift 1637884
  have htrace : WordTrace (prefixWord ++ tailWord_1637884) baseStart_1637884 baseEnd_1637884 := by
    simpa [prefixWord, tailWord_1637884, baseEnd_1637884] using wordTrace_append hprefix tailTrace_1637884
  have hstable : (prefixWord ++ tailWord_1637884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637884).length < 2 ^ (prefixWord ++ tailWord_1637884).sum := by decide
  have hdescent : baseEnd_1637884 < baseStart_1637884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637944 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 3, 4]
def baseStart_1637944 : Nat := 118140960795 + 1637944 * 2 ^ 59
def prefixEnd_1637944 : Nat := 4983230072969 + 3 ^ 40 * 1637944 * 2
def baseEnd_1637944 : Nat := 560701704765363180178159

theorem tailTrace_1637944 : CollatzResearch.WordTrace tailWord_1637944 prefixEnd_1637944 560701704765363180178159 := by
  unfold tailWord_1637944
  simp only [CollatzResearch.WordTrace]
  refine ⟨29870362789008050704592443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39827150385344067606123257 29870362789008050704592443)
  ·
    refine ⟨44805544183512076056888665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29870362789008050704592443 44805544183512076056888665)
    ·
      refine ⟨33604158137634057042666499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44805544183512076056888665 33604158137634057042666499)
      ·
        refine ⟨50406237206451085563999749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33604158137634057042666499 50406237206451085563999749)
        ·
          refine ⟨9451169476209578543249953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50406237206451085563999749 9451169476209578543249953)
          ·
            refine ⟨7088377107157183907437465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9451169476209578543249953 7088377107157183907437465)
            ·
              refine ⟨5316282830367887930578099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7088377107157183907437465 5316282830367887930578099)
              ·
                refine ⟨7974424245551831895867149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5316282830367887930578099 7974424245551831895867149)
                ·
                  refine ⟨2990409092081936960950181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7974424245551831895867149 2990409092081936960950181)
                  ·
                    refine ⟨560701704765363180178159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2990409092081936960950181 560701704765363180178159)
                    ·
                      rfl

theorem cell22_1637944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_1637944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637944 prefixEnd_1637944 := by exact prefixLift 1637944
  have htrace : WordTrace (prefixWord ++ tailWord_1637944) baseStart_1637944 baseEnd_1637944 := by
    simpa [prefixWord, tailWord_1637944, baseEnd_1637944] using wordTrace_append hprefix tailTrace_1637944
  have hstable : (prefixWord ++ tailWord_1637944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637944).length < 2 ^ (prefixWord ++ tailWord_1637944).sum := by decide
  have hdescent : baseEnd_1637944 < baseStart_1637944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637965 : List Nat := [1, 6, 1, 1, 4, 1, 1, 2, 5]
def baseStart_1637965 : Nat := 118140960795 + 1637965 * 2 ^ 59
def prefixEnd_1637965 : Nat := 4983230072969 + 3 ^ 40 * 1637965 * 2
def baseEnd_1637965 : Nat := 186902964498175375134365

theorem tailTrace_1637965 : CollatzResearch.WordTrace tailWord_1637965 prefixEnd_1637965 186902964498175375134365 := by
  unfold tailWord_1637965
  simp only [CollatzResearch.WordTrace]
  refine ⟨59741491510940021995699349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39827661007293347997132899 59741491510940021995699349)
  ·
    refine ⟨2800382414575313531048407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59741491510940021995699349 2800382414575313531048407)
    ·
      refine ⟨4200573621862970296572611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2800382414575313531048407 4200573621862970296572611)
      ·
        refine ⟨6300860432794455444858917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4200573621862970296572611 6300860432794455444858917)
        ·
          refine ⟨1181411331148960395911047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6300860432794455444858917 1181411331148960395911047)
          ·
            refine ⟨1772116996723440593866571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1181411331148960395911047 1772116996723440593866571)
            ·
              refine ⟨2658175495085160890799857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1772116996723440593866571 2658175495085160890799857)
              ·
                refine ⟨1993631621313870668099893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2658175495085160890799857 1993631621313870668099893)
                ·
                  refine ⟨186902964498175375134365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1993631621313870668099893 186902964498175375134365)
                  ·
                    rfl

theorem cell22_1637965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_1637965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637965 prefixEnd_1637965 := by exact prefixLift 1637965
  have htrace : WordTrace (prefixWord ++ tailWord_1637965) baseStart_1637965 baseEnd_1637965 := by
    simpa [prefixWord, tailWord_1637965, baseEnd_1637965] using wordTrace_append hprefix tailTrace_1637965
  have hstable : (prefixWord ++ tailWord_1637965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637965).length < 2 ^ (prefixWord ++ tailWord_1637965).sum := by decide
  have hdescent : baseEnd_1637965 < baseStart_1637965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637989 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 1, 6]
def baseStart_1637989 : Nat := 118140960795 + 1637989 * 2 ^ 59
def prefixEnd_1637989 : Nat := 4983230072969 + 3 ^ 40 * 1637989 * 2
def baseEnd_1637989 : Nat := 560717109184998062803021

theorem tailTrace_1637989 : CollatzResearch.WordTrace tailWord_1637989 prefixEnd_1637989 560717109184998062803021 := by
  unfold tailWord_1637989
  simp only [CollatzResearch.WordTrace]
  refine ⟨59742366862853074094573021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39828244575235382729715347 59742366862853074094573021)
  ·
    refine ⟨22403387573569902785464883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59742366862853074094573021 22403387573569902785464883)
    ·
      refine ⟨33605081360354854178197325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22403387573569902785464883 33605081360354854178197325)
      ·
        refine ⟨12601905510133070316823997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33605081360354854178197325 12601905510133070316823997)
        ·
          refine ⟨4725714566299901368808999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12601905510133070316823997 4725714566299901368808999)
          ·
            refine ⟨7088571849449852053213499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4725714566299901368808999 7088571849449852053213499)
            ·
              refine ⟨10632857774174778079820249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7088571849449852053213499 10632857774174778079820249)
              ·
                refine ⟨7974643330631083559865187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10632857774174778079820249 7974643330631083559865187)
                ·
                  refine ⟨11961964995946625339797781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7974643330631083559865187 11961964995946625339797781)
                  ·
                    refine ⟨560717109184998062803021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11961964995946625339797781 560717109184998062803021)
                    ·
                      rfl

theorem cell22_1637989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_1637989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637989 prefixEnd_1637989 := by exact prefixLift 1637989
  have htrace : WordTrace (prefixWord ++ tailWord_1637989) baseStart_1637989 baseEnd_1637989 := by
    simpa [prefixWord, tailWord_1637989, baseEnd_1637989] using wordTrace_append hprefix tailTrace_1637989
  have hstable : (prefixWord ++ tailWord_1637989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637989).length < 2 ^ (prefixWord ++ tailWord_1637989).sum := by decide
  have hdescent : baseEnd_1637989 < baseStart_1637989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1637991 : List Nat := [1, 1, 5, 1, 1, 1, 2, 5, 2, 3]
def baseStart_1637991 : Nat := 118140960795 + 1637991 * 2 ^ 59
def prefixEnd_1637991 : Nat := 4983230072969 + 3 ^ 40 * 1637991 * 2
def baseEnd_1637991 : Nat := 560717793825870724253015

theorem tailTrace_1637991 : CollatzResearch.WordTrace tailWord_1637991 prefixEnd_1637991 560717793825870724253015 := by
  unfold tailWord_1637991
  simp only [CollatzResearch.WordTrace]
  refine ⟨59742439808845828436145827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39828293205897218957430551 59742439808845828436145827)
  ·
    refine ⟨89613659713268742654218741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59742439808845828436145827 89613659713268742654218741)
    ·
      refine ⟨8401280598118944623833007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89613659713268742654218741 8401280598118944623833007)
      ·
        refine ⟨12601920897178416935749511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8401280598118944623833007 12601920897178416935749511)
        ·
          refine ⟨18902881345767625403624267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12601920897178416935749511 18902881345767625403624267)
          ·
            refine ⟨28354322018651438105436401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18902881345767625403624267 28354322018651438105436401)
            ·
              refine ⟨21265741513988578579077301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28354322018651438105436401 21265741513988578579077301)
              ·
                refine ⟨1993663266936429241788497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21265741513988578579077301 1993663266936429241788497)
                ·
                  refine ⟨1495247450202321931341373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1993663266936429241788497 1495247450202321931341373)
                  ·
                    refine ⟨560717793825870724253015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1495247450202321931341373 560717793825870724253015)
                    ·
                      rfl

theorem cell22_1637991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_1637991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1637991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1637991 prefixEnd_1637991 := by exact prefixLift 1637991
  have htrace : WordTrace (prefixWord ++ tailWord_1637991) baseStart_1637991 baseEnd_1637991 := by
    simpa [prefixWord, tailWord_1637991, baseEnd_1637991] using wordTrace_append hprefix tailTrace_1637991
  have hstable : (prefixWord ++ tailWord_1637991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1637991).length < 2 ^ (prefixWord ++ tailWord_1637991).sum := by decide
  have hdescent : baseEnd_1637991 < baseStart_1637991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1637991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638006 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_1638006 : Nat := 118140960795 + 1638006 * 2 ^ 59
def prefixEnd_1638006 : Nat := 4983230072969 + 3 ^ 40 * 1638006 * 2
def baseEnd_1638006 : Nat := 560722928632415685127969

theorem tailTrace_1638006 : CollatzResearch.WordTrace tailWord_1638006 prefixEnd_1638006 560722928632415685127969 := by
  unfold tailWord_1638006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3733936681486967874871367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39828657935860990665294581 3733936681486967874871367)
  ·
    refine ⟨5600905022230451812307051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3733936681486967874871367 5600905022230451812307051)
    ·
      refine ⟨8401357533345677718460577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5600905022230451812307051 8401357533345677718460577)
      ·
        refine ⟨6301018150009258288845433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8401357533345677718460577 6301018150009258288845433)
        ·
          refine ⟨4725763612506943716634075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6301018150009258288845433 4725763612506943716634075)
          ·
            refine ⟨7088645418760415574951113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4725763612506943716634075 7088645418760415574951113)
            ·
              refine ⟨5316484064070311681213335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7088645418760415574951113 5316484064070311681213335)
              ·
                refine ⟨7974726096105467521820003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5316484064070311681213335 7974726096105467521820003)
                ·
                  refine ⟨11962089144158201282730005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7974726096105467521820003 11962089144158201282730005)
                  ·
                    refine ⟨560722928632415685127969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11962089144158201282730005 560722928632415685127969)
                    ·
                      rfl

theorem cell22_1638006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_1638006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1638006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1638006 prefixEnd_1638006 := by exact prefixLift 1638006
  have htrace : WordTrace (prefixWord ++ tailWord_1638006) baseStart_1638006 baseEnd_1638006 := by
    simpa [prefixWord, tailWord_1638006, baseEnd_1638006] using wordTrace_append hprefix tailTrace_1638006
  have hstable : (prefixWord ++ tailWord_1638006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638006).length < 2 ^ (prefixWord ++ tailWord_1638006).sum := by decide
  have hdescent : baseEnd_1638006 < baseStart_1638006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638126 : List Nat := [4, 1, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_1638126 : Nat := 118140960795 + 1638126 * 2 ^ 59
def prefixEnd_1638126 : Nat := 4983230072969 + 3 ^ 40 * 1638126 * 2
def baseEnd_1638126 : Nat := 560764007084775372127601

theorem tailTrace_1638126 : CollatzResearch.WordTrace tailWord_1638126 prefixEnd_1638126 560764007084775372127601 := by
  unfold tailWord_1638126
  simp only [CollatzResearch.WordTrace]
  refine ⟨7468420457919593311538779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39831575775571164328206821 7468420457919593311538779)
  ·
    refine ⟨11202630686879389967308169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7468420457919593311538779 11202630686879389967308169)
    ·
      refine ⟨8401973015159542475481127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11202630686879389967308169 8401973015159542475481127)
      ·
        refine ⟨12602959522739313713221691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8401973015159542475481127 12602959522739313713221691)
        ·
          refine ⟨18904439284108970569832537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12602959522739313713221691 18904439284108970569832537)
          ·
            refine ⟨14178329463081727927374403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18904439284108970569832537 14178329463081727927374403)
            ·
              refine ⟨21267494194622591891061605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14178329463081727927374403 21267494194622591891061605)
              ·
                refine ⟨3987655161491735979574051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21267494194622591891061605 3987655161491735979574051)
                ·
                  refine ⟨5981482742237603969361077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3987655161491735979574051 5981482742237603969361077)
                  ·
                    refine ⟨560764007084775372127601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5981482742237603969361077 560764007084775372127601)
                    ·
                      rfl

theorem cell22_1638126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_1638126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1638126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1638126 prefixEnd_1638126 := by exact prefixLift 1638126
  have htrace : WordTrace (prefixWord ++ tailWord_1638126) baseStart_1638126 baseEnd_1638126 := by
    simpa [prefixWord, tailWord_1638126, baseEnd_1638126] using wordTrace_append hprefix tailTrace_1638126
  have hstable : (prefixWord ++ tailWord_1638126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638126).length < 2 ^ (prefixWord ++ tailWord_1638126).sum := by decide
  have hdescent : baseEnd_1638126 < baseStart_1638126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638143 : List Nat := [1, 1, 2, 2, 1, 3, 5, 2, 2, 3]
def baseStart_1638143 : Nat := 118140960795 + 1638143 * 2 ^ 59
def prefixEnd_1638143 : Nat := 4983230072969 + 3 ^ 40 * 1638143 * 2
def baseEnd_1638143 : Nat := 560769826532192994452549

theorem tailTrace_1638143 : CollatzResearch.WordTrace tailWord_1638143 prefixEnd_1638143 560769826532192994452549 := by
  unfold tailWord_1638143
  simp only [CollatzResearch.WordTrace]
  refine ⟨59747983704295158395679083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39831989136196772263786055 59747983704295158395679083)
  ·
    refine ⟨89621975556442737593518625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59747983704295158395679083 89621975556442737593518625)
    ·
      refine ⟨67216481667332053195138969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89621975556442737593518625 67216481667332053195138969)
      ·
        refine ⟨50412361250499039896354227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67216481667332053195138969 50412361250499039896354227)
        ·
          refine ⟨75618541875748559844531341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50412361250499039896354227 75618541875748559844531341)
          ·
            refine ⟨28356953203405709941699253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75618541875748559844531341 28356953203405709941699253)
            ·
              refine ⟨2658464362819285307034305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28356953203405709941699253 2658464362819285307034305)
              ·
                refine ⟨1993848272114463980275729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2658464362819285307034305 1993848272114463980275729)
                ·
                  refine ⟨1495386204085847985206797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1993848272114463980275729 1495386204085847985206797)
                  ·
                    refine ⟨560769826532192994452549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1495386204085847985206797 560769826532192994452549)
                    ·
                      rfl

theorem cell22_1638143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 3].length) (baseStart_1638143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1638143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1638143 prefixEnd_1638143 := by exact prefixLift 1638143
  have htrace : WordTrace (prefixWord ++ tailWord_1638143) baseStart_1638143 baseEnd_1638143 := by
    simpa [prefixWord, tailWord_1638143, baseEnd_1638143] using wordTrace_append hprefix tailTrace_1638143
  have hstable : (prefixWord ++ tailWord_1638143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638143).length < 2 ^ (prefixWord ++ tailWord_1638143).sum := by decide
  have hdescent : baseEnd_1638143 < baseStart_1638143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638164 : List Nat := [2, 4, 4, 1, 1, 1, 2, 2, 1, 4]
def baseStart_1638164 : Nat := 118140960795 + 1638164 * 2 ^ 59
def prefixEnd_1638164 : Nat := 4983230072969 + 3 ^ 40 * 1638164 * 2
def baseEnd_1638164 : Nat := 560777015261355939677485

theorem tailTrace_1638164 : CollatzResearch.WordTrace tailWord_1638164 prefixEnd_1638164 560777015261355939677485 := by
  unfold tailWord_1638164
  simp only [CollatzResearch.WordTrace]
  refine ⟨29874374818609539491096773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39832499758146052654795697 29874374818609539491096773)
  ·
    refine ⟨5601445278489288654580645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29874374818609539491096773 5601445278489288654580645)
    ·
      refine ⟨1050270989716741622733871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5601445278489288654580645 1050270989716741622733871)
      ·
        refine ⟨1575406484575112434100807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1050270989716741622733871 1575406484575112434100807)
        ·
          refine ⟨2363109726862668651151211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1575406484575112434100807 2363109726862668651151211)
          ·
            refine ⟨3544664590294002976726817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2363109726862668651151211 3544664590294002976726817)
            ·
              refine ⟨2658498442720502232545113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3544664590294002976726817 2658498442720502232545113)
              ·
                refine ⟨1993873832040376674408835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2658498442720502232545113 1993873832040376674408835)
                ·
                  refine ⟨2990810748060565011613253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1993873832040376674408835 2990810748060565011613253)
                  ·
                    refine ⟨560777015261355939677485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2990810748060565011613253 560777015261355939677485)
                    ·
                      rfl

theorem cell22_1638164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_1638164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1638164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1638164 prefixEnd_1638164 := by exact prefixLift 1638164
  have htrace : WordTrace (prefixWord ++ tailWord_1638164) baseStart_1638164 baseEnd_1638164 := by
    simpa [prefixWord, tailWord_1638164, baseEnd_1638164] using wordTrace_append hprefix tailTrace_1638164
  have hstable : (prefixWord ++ tailWord_1638164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638164).length < 2 ^ (prefixWord ++ tailWord_1638164).sum := by decide
  have hdescent : baseEnd_1638164 < baseStart_1638164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638169 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 3, 8]
def baseStart_1638169 : Nat := 118140960795 + 1638169 * 2 ^ 59
def prefixEnd_1638169 : Nat := 4983230072969 + 3 ^ 40 * 1638169 * 2
def baseEnd_1638169 : Nat := 560778726863537593302469

theorem tailTrace_1638169 : CollatzResearch.WordTrace tailWord_1638169 prefixEnd_1638169 560778726863537593302469 := by
  unfold tailWord_1638169
  simp only [CollatzResearch.WordTrace]
  refine ⟨59748932002200964836125561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39832621334800643224083707 59748932002200964836125561)
  ·
    refine ⟨44811699001650723627094171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59748932002200964836125561 44811699001650723627094171)
    ·
      refine ⟨67217548502476085440641257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44811699001650723627094171 67217548502476085440641257)
      ·
        refine ⟨50413161376857064080480943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67217548502476085440641257 50413161376857064080480943)
        ·
          refine ⟨75619742065285596120721415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50413161376857064080480943 75619742065285596120721415)
          ·
            refine ⟨113429613097928394181082123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75619742065285596120721415 113429613097928394181082123)
            ·
              refine ⟨170144419646892591271623185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113429613097928394181082123 170144419646892591271623185)
              ·
                refine ⟨127608314735169443453717389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170144419646892591271623185 127608314735169443453717389)
                ·
                  refine ⟨47853118025688541295144021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127608314735169443453717389 47853118025688541295144021)
                  ·
                    refine ⟨560778726863537593302469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47853118025688541295144021 560778726863537593302469)
                    ·
                      rfl

theorem cell22_1638169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_1638169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1638169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1638169 prefixEnd_1638169 := by exact prefixLift 1638169
  have htrace : WordTrace (prefixWord ++ tailWord_1638169) baseStart_1638169 baseEnd_1638169 := by
    simpa [prefixWord, tailWord_1638169, baseEnd_1638169] using wordTrace_append hprefix tailTrace_1638169
  have hstable : (prefixWord ++ tailWord_1638169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638169).length < 2 ^ (prefixWord ++ tailWord_1638169).sum := by decide
  have hdescent : baseEnd_1638169 < baseStart_1638169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638190 : List Nat := [4, 1, 3, 2, 3, 1, 8]
def baseStart_1638190 : Nat := 118140960795 + 1638190 * 2 ^ 59
def prefixEnd_1638190 : Nat := 4983230072969 + 3 ^ 40 * 1638190 * 2
def baseEnd_1638190 : Nat := 20769848725655575501015

theorem tailTrace_1638190 : CollatzResearch.WordTrace tailWord_1638190 prefixEnd_1638190 20769848725655575501015 := by
  unfold tailWord_1638190
  simp only [CollatzResearch.WordTrace]
  refine ⟨7468712241890610677830003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39833131956749923615093349 7468712241890610677830003)
  ·
    refine ⟨11203068362835916016745005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7468712241890610677830003 11203068362835916016745005)
    ·
      refine ⟨4201150636063468506279377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11203068362835916016745005 4201150636063468506279377)
      ·
        refine ⟨3150862977047601379709533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4201150636063468506279377 3150862977047601379709533)
        ·
          refine ⟨1181573616392850517391075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3150862977047601379709533 1181573616392850517391075)
          ·
            refine ⟨1772360424589275776086613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1181573616392850517391075 1772360424589275776086613)
            ·
              refine ⟨20769848725655575501015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1772360424589275776086613 20769848725655575501015)
              ·
                rfl

theorem cell22_1638190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 8].length) (baseStart_1638190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1638190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1638190 prefixEnd_1638190 := by exact prefixLift 1638190
  have htrace : WordTrace (prefixWord ++ tailWord_1638190) baseStart_1638190 baseEnd_1638190 := by
    simpa [prefixWord, tailWord_1638190, baseEnd_1638190] using wordTrace_append hprefix tailTrace_1638190
  have hstable : (prefixWord ++ tailWord_1638190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638190).length < 2 ^ (prefixWord ++ tailWord_1638190).sum := by decide
  have hdescent : baseEnd_1638190 < baseStart_1638190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638205 : List Nat := [1, 4, 1, 4, 1, 1, 3, 1, 3, 3]
def baseStart_1638205 : Nat := 118140960795 + 1638205 * 2 ^ 59
def prefixEnd_1638205 : Nat := 4983230072969 + 3 ^ 40 * 1638205 * 2
def baseEnd_1638205 : Nat := 560791050399245499402359

theorem tailTrace_1638205 : CollatzResearch.WordTrace tailWord_1638205 prefixEnd_1638205 560791050399245499402359 := by
  unfold tailWord_1638205
  simp only [CollatzResearch.WordTrace]
  refine ⟨59750245030070542984436069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39833496686713695322957379 59750245030070542984436069)
  ·
    refine ⟨11203170943138226809581763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59750245030070542984436069 11203170943138226809581763)
    ·
      refine ⟨16804756414707340214372645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11203170943138226809581763 16804756414707340214372645)
      ·
        refine ⟨3150891827757626290194871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16804756414707340214372645 3150891827757626290194871)
        ·
          refine ⟨4726337741636439435292307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3150891827757626290194871 4726337741636439435292307)
          ·
            refine ⟨7089506612454659152938461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4726337741636439435292307 7089506612454659152938461)
            ·
              refine ⟨2658564979670497182351923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7089506612454659152938461 2658564979670497182351923)
              ·
                refine ⟨3987847469505745773527885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2658564979670497182351923 3987847469505745773527885)
                ·
                  refine ⟨1495442801064654665072957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3987847469505745773527885 1495442801064654665072957)
                  ·
                    refine ⟨560791050399245499402359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1495442801064654665072957 560791050399245499402359)
                    ·
                      rfl

theorem cell22_1638205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_1638205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1638205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1638205 prefixEnd_1638205 := by exact prefixLift 1638205
  have htrace : WordTrace (prefixWord ++ tailWord_1638205) baseStart_1638205 baseEnd_1638205 := by
    simpa [prefixWord, tailWord_1638205, baseEnd_1638205] using wordTrace_append hprefix tailTrace_1638205
  have hstable : (prefixWord ++ tailWord_1638205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638205).length < 2 ^ (prefixWord ++ tailWord_1638205).sum := by decide
  have hdescent : baseEnd_1638205 < baseStart_1638205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638383 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 3, 4]
def baseStart_1638383 : Nat := 118140960795 + 1638383 * 2 ^ 59
def prefixEnd_1638383 : Nat := 4983230072969 + 3 ^ 40 * 1638383 * 2
def baseEnd_1638383 : Nat := 560851983436912368451813

theorem tailTrace_1638383 : CollatzResearch.WordTrace tailWord_1638383 prefixEnd_1638383 560851983436912368451813 := by
  unfold tailWord_1638383
  simp only [CollatzResearch.WordTrace]
  refine ⟨59756737223425679384415803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39837824815617119589610535 59756737223425679384415803)
  ·
    refine ⟨89635105835138519076623705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59756737223425679384415803 89635105835138519076623705)
    ·
      refine ⟨67226329376353889307467779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89635105835138519076623705 67226329376353889307467779)
      ·
        refine ⟨100839494064530833961201669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67226329376353889307467779 100839494064530833961201669)
        ·
          refine ⟨18907405137099531367725313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100839494064530833961201669 18907405137099531367725313)
          ·
            refine ⟨14180553852824648525793985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18907405137099531367725313 14180553852824648525793985)
            ·
              refine ⟨10635415389618486394345489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14180553852824648525793985 10635415389618486394345489)
              ·
                refine ⟨7976561542213864795759117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10635415389618486394345489 7976561542213864795759117)
                ·
                  refine ⟨2991210578330199298409669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7976561542213864795759117 2991210578330199298409669)
                  ·
                    refine ⟨560851983436912368451813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2991210578330199298409669 560851983436912368451813)
                    ·
                      rfl

theorem cell22_1638383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 4].length) (baseStart_1638383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1638383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1638383 prefixEnd_1638383 := by exact prefixLift 1638383
  have htrace : WordTrace (prefixWord ++ tailWord_1638383) baseStart_1638383 baseEnd_1638383 := by
    simpa [prefixWord, tailWord_1638383, baseEnd_1638383] using wordTrace_append hprefix tailTrace_1638383
  have hstable : (prefixWord ++ tailWord_1638383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638383).length < 2 ^ (prefixWord ++ tailWord_1638383).sum := by decide
  have hdescent : baseEnd_1638383 < baseStart_1638383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638460 : List Nat := [2, 2, 2, 2, 2, 1, 5, 6]
def baseStart_1638460 : Nat := 118140960795 + 1638460 * 2 ^ 59
def prefixEnd_1638460 : Nat := 4983230072969 + 3 ^ 40 * 1638460 * 2
def baseEnd_1638460 : Nat := 62319815790056648252953

theorem tailTrace_1638460 : CollatzResearch.WordTrace tailWord_1638460 prefixEnd_1638460 62319815790056648252953 := by
  unfold tailWord_1638460
  simp only [CollatzResearch.WordTrace]
  refine ⟨29879772822073360767484417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39839697096097814356645889 29879772822073360767484417)
  ·
    refine ⟨22409829616555020575613313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29879772822073360767484417 22409829616555020575613313)
    ·
      refine ⟨16807372212416265431709985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22409829616555020575613313 16807372212416265431709985)
      ·
        refine ⟨12605529159312199073782489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16807372212416265431709985 12605529159312199073782489)
        ·
          refine ⟨9454146869484149305336867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12605529159312199073782489 9454146869484149305336867)
          ·
            refine ⟨14181220304226223958005301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9454146869484149305336867 14181220304226223958005301)
            ·
              refine ⟨1329489403521208496062997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14181220304226223958005301 1329489403521208496062997)
              ·
                refine ⟨62319815790056648252953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1329489403521208496062997 62319815790056648252953)
                ·
                  rfl

theorem cell22_1638460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 6].length) (baseStart_1638460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1638460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1638460 prefixEnd_1638460 := by exact prefixLift 1638460
  have htrace : WordTrace (prefixWord ++ tailWord_1638460) baseStart_1638460 baseEnd_1638460 := by
    simpa [prefixWord, tailWord_1638460, baseEnd_1638460] using wordTrace_append hprefix tailTrace_1638460
  have hstable : (prefixWord ++ tailWord_1638460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638460).length < 2 ^ (prefixWord ++ tailWord_1638460).sum := by decide
  have hdescent : baseEnd_1638460 < baseStart_1638460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638462 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_1638462 : Nat := 118140960795 + 1638462 * 2 ^ 59
def prefixEnd_1638462 : Nat := 4983230072969 + 3 ^ 40 * 1638462 * 2
def baseEnd_1638462 : Nat := 560879026751382495726571

theorem tailTrace_1638462 : CollatzResearch.WordTrace tailWord_1638462 prefixEnd_1638462 560879026751382495726571 := by
  unfold tailWord_1638462
  simp only [CollatzResearch.WordTrace]
  refine ⟨7469952323767434484567705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39839745726759650584361093 7469952323767434484567705)
  ·
    refine ⟨5602464242825575863425779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7469952323767434484567705 5602464242825575863425779)
    ·
      refine ⟨8403696364238363795138669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5602464242825575863425779 8403696364238363795138669)
      ·
        refine ⟨3151386136589386423177001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8403696364238363795138669 3151386136589386423177001)
        ·
          refine ⟨2363539602442039817382751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3151386136589386423177001 2363539602442039817382751)
          ·
            refine ⟨3545309403663059726074127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2363539602442039817382751 3545309403663059726074127)
            ·
              refine ⟨5317964105494589589111191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3545309403663059726074127 5317964105494589589111191)
              ·
                refine ⟨7976946158241884383666787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5317964105494589589111191 7976946158241884383666787)
                ·
                  refine ⟨11965419237362826575500181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7976946158241884383666787 11965419237362826575500181)
                  ·
                    refine ⟨560879026751382495726571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11965419237362826575500181 560879026751382495726571)
                    ·
                      rfl

theorem cell22_1638462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_1638462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1638462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1638462 prefixEnd_1638462 := by exact prefixLift 1638462
  have htrace : WordTrace (prefixWord ++ tailWord_1638462) baseStart_1638462 baseEnd_1638462 := by
    simpa [prefixWord, tailWord_1638462, baseEnd_1638462] using wordTrace_append hprefix tailTrace_1638462
  have hstable : (prefixWord ++ tailWord_1638462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638462).length < 2 ^ (prefixWord ++ tailWord_1638462).sum := by decide
  have hdescent : baseEnd_1638462 < baseStart_1638462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638492 : List Nat := [2, 2, 4, 1, 1, 2, 1, 3, 3, 3]
def baseStart_1638492 : Nat := 118140960795 + 1638492 * 2 ^ 59
def prefixEnd_1638492 : Nat := 4983230072969 + 3 ^ 40 * 1638492 * 2
def baseEnd_1638492 : Nat := 560889296364472417476479

theorem tailTrace_1638492 : CollatzResearch.WordTrace tailWord_1638492 prefixEnd_1638492 560889296364472417476479 := by
  unfold tailWord_1638492
  simp only [CollatzResearch.WordTrace]
  refine ⟨29880356390015395500066865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39840475186687194000089153 29880356390015395500066865)
  ·
    refine ⟨22410267292511546625050149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29880356390015395500066865 22410267292511546625050149)
    ·
      refine ⟨4201925117345914992196903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22410267292511546625050149 4201925117345914992196903)
      ·
        refine ⟨6302887676018872488295355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4201925117345914992196903 6302887676018872488295355)
        ·
          refine ⟨9454331514028308732443033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6302887676018872488295355 9454331514028308732443033)
          ·
            refine ⟨7090748635521231549332275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9454331514028308732443033 7090748635521231549332275)
            ·
              refine ⟨10636122953281847323998413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7090748635521231549332275 10636122953281847323998413)
              ·
                refine ⟨3988546107480692746499405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10636122953281847323998413 3988546107480692746499405)
                ·
                  refine ⟨1495704790305259779937277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3988546107480692746499405 1495704790305259779937277)
                  ·
                    refine ⟨560889296364472417476479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1495704790305259779937277 560889296364472417476479)
                    ·
                      rfl

theorem cell22_1638492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_1638492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1638492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1638492 prefixEnd_1638492 := by exact prefixLift 1638492
  have htrace : WordTrace (prefixWord ++ tailWord_1638492) baseStart_1638492 baseEnd_1638492 := by
    simpa [prefixWord, tailWord_1638492, baseEnd_1638492] using wordTrace_append hprefix tailTrace_1638492
  have hstable : (prefixWord ++ tailWord_1638492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638492).length < 2 ^ (prefixWord ++ tailWord_1638492).sum := by decide
  have hdescent : baseEnd_1638492 < baseStart_1638492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638565 : List Nat := [1, 3, 1, 2, 1, 3, 2, 3, 1, 5]
def baseStart_1638565 : Nat := 118140960795 + 1638565 * 2 ^ 59
def prefixEnd_1638565 : Nat := 4983230072969 + 3 ^ 40 * 1638565 * 2
def baseEnd_1638565 : Nat := 560914285756324560401255

theorem tailTrace_1638565 : CollatzResearch.WordTrace tailWord_1638565 prefixEnd_1638565 560914285756324560401255 := by
  unfold tailWord_1638565
  simp only [CollatzResearch.WordTrace]
  refine ⟨59763375308766324467541149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39842250205844216311694099 59763375308766324467541149)
  ·
    refine ⟨22411265740787371675327931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59763375308766324467541149 22411265740787371675327931)
    ·
      refine ⟨33616898611181057512991897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22411265740787371675327931 33616898611181057512991897)
      ·
        refine ⟨25212673958385793134743923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33616898611181057512991897 25212673958385793134743923)
        ·
          refine ⟨37819010937578689702115885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25212673958385793134743923 37819010937578689702115885)
          ·
            refine ⟨14182129101592008638293457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37819010937578689702115885 14182129101592008638293457)
            ·
              refine ⟨10636596826194006478720093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14182129101592008638293457 10636596826194006478720093)
              ·
                refine ⟨3988723809822752429520035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10636596826194006478720093 3988723809822752429520035)
                ·
                  refine ⟨5983085714734128644280053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3988723809822752429520035 5983085714734128644280053)
                  ·
                    refine ⟨560914285756324560401255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5983085714734128644280053 560914285756324560401255)
                    ·
                      rfl

theorem cell22_1638565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_1638565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1638565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1638565 prefixEnd_1638565 := by exact prefixLift 1638565
  have htrace : WordTrace (prefixWord ++ tailWord_1638565) baseStart_1638565 baseEnd_1638565 := by
    simpa [prefixWord, tailWord_1638565, baseEnd_1638565] using wordTrace_append hprefix tailTrace_1638565
  have hstable : (prefixWord ++ tailWord_1638565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638565).length < 2 ^ (prefixWord ++ tailWord_1638565).sum := by decide
  have hdescent : baseEnd_1638565 < baseStart_1638565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638625 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 2, 6]
def baseStart_1638625 : Nat := 118140960795 + 1638625 * 2 ^ 59
def prefixEnd_1638625 : Nat := 4983230072969 + 3 ^ 40 * 1638625 * 2
def baseEnd_1638625 : Nat := 560934824982504403901071

theorem tailTrace_1638625 : CollatzResearch.WordTrace tailWord_1638625 prefixEnd_1638625 560934824982504403901071 := by
  unfold tailWord_1638625
  simp only [CollatzResearch.WordTrace]
  refine ⟨59765563688548954714725329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39843709125699303143150219 59765563688548954714725329)
  ·
    refine ⟨44824172766411716036043997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59765563688548954714725329 44824172766411716036043997)
    ·
      refine ⟨16809064787404393513516499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44824172766411716036043997 16809064787404393513516499)
      ·
        refine ⟨25213597181106590270274749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16809064787404393513516499 25213597181106590270274749)
        ·
          refine ⟨9455098942914971351353031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25213597181106590270274749 9455098942914971351353031)
          ·
            refine ⟨14182648414372457027029547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9455098942914971351353031 14182648414372457027029547)
            ·
              refine ⟨21273972621558685540544321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14182648414372457027029547 21273972621558685540544321)
              ·
                refine ⟨15955479466169014155408241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21273972621558685540544321 15955479466169014155408241)
                ·
                  refine ⟨11966609599626760616556181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15955479466169014155408241 11966609599626760616556181)
                  ·
                    refine ⟨560934824982504403901071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11966609599626760616556181 560934824982504403901071)
                    ·
                      rfl

theorem cell22_1638625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_1638625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1638625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1638625 prefixEnd_1638625 := by exact prefixLift 1638625
  have htrace : WordTrace (prefixWord ++ tailWord_1638625) baseStart_1638625 baseEnd_1638625 := by
    simpa [prefixWord, tailWord_1638625, baseEnd_1638625] using wordTrace_append hprefix tailTrace_1638625
  have hstable : (prefixWord ++ tailWord_1638625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638625).length < 2 ^ (prefixWord ++ tailWord_1638625).sum := by decide
  have hdescent : baseEnd_1638625 < baseStart_1638625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638655 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 4, 5]
def baseStart_1638655 : Nat := 118140960795 + 1638655 * 2 ^ 59
def prefixEnd_1638655 : Nat := 4983230072969 + 3 ^ 40 * 1638655 * 2
def baseEnd_1638655 : Nat := 560945094595594325650979

theorem tailTrace_1638655 : CollatzResearch.WordTrace tailWord_1638655 prefixEnd_1638655 560945094595594325650979 := by
  unfold tailWord_1638655
  simp only [CollatzResearch.WordTrace]
  refine ⟨59766657878440269838317419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39844438585626846558878279 59766657878440269838317419)
  ·
    refine ⟨89649986817660404757476129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59766657878440269838317419 89649986817660404757476129)
    ·
      refine ⟨67237490113245303568107097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89649986817660404757476129 67237490113245303568107097)
      ·
        refine ⟨50428117584933977676080323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67237490113245303568107097 50428117584933977676080323)
        ·
          refine ⟨75642176377400966514120485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50428117584933977676080323 75642176377400966514120485)
          ·
            refine ⟨14182908070762681221397591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75642176377400966514120485 14182908070762681221397591)
            ·
              refine ⟨21274362106144021832096387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14182908070762681221397591 21274362106144021832096387)
              ·
                refine ⟨31911543159216032748144581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21274362106144021832096387 31911543159216032748144581)
                ·
                  refine ⟨5983414342353006140277109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31911543159216032748144581 5983414342353006140277109)
                  ·
                    refine ⟨560945094595594325650979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5983414342353006140277109 560945094595594325650979)
                    ·
                      rfl

theorem cell22_1638655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_1638655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1638655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1638655 prefixEnd_1638655 := by exact prefixLift 1638655
  have htrace : WordTrace (prefixWord ++ tailWord_1638655) baseStart_1638655 baseEnd_1638655 := by
    simpa [prefixWord, tailWord_1638655, baseEnd_1638655] using wordTrace_append hprefix tailTrace_1638655
  have hstable : (prefixWord ++ tailWord_1638655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638655).length < 2 ^ (prefixWord ++ tailWord_1638655).sum := by decide
  have hdescent : baseEnd_1638655 < baseStart_1638655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638732 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 4, 4]
def baseStart_1638732 : Nat := 118140960795 + 1638732 * 2 ^ 59
def prefixEnd_1638732 : Nat := 4983230072969 + 3 ^ 40 * 1638732 * 2
def baseEnd_1638732 : Nat := 560971453269191791475743

theorem tailTrace_1638732 : CollatzResearch.WordTrace tailWord_1638732 prefixEnd_1638732 560971453269191791475743 := by
  unfold tailWord_1638732
  simp only [CollatzResearch.WordTrace]
  refine ⟨29884733149580655994435225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39846310866107541325913633 29884733149580655994435225)
  ·
    refine ⟨22413549862185491995826419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29884733149580655994435225 22413549862185491995826419)
    ·
      refine ⟨33620324793278237993739629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22413549862185491995826419 33620324793278237993739629)
      ·
        refine ⟨12607621797479339247652361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33620324793278237993739629 12607621797479339247652361)
        ·
          refine ⟨9455716348109504435739271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12607621797479339247652361 9455716348109504435739271)
          ·
            refine ⟨14183574522164256653608907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9455716348109504435739271 14183574522164256653608907)
            ·
              refine ⟨21275361783246384980413361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14183574522164256653608907 21275361783246384980413361)
              ·
                refine ⟨15956521337434788735310021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21275361783246384980413361 15956521337434788735310021)
                ·
                  refine ⟨2991847750769022887870629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15956521337434788735310021 2991847750769022887870629)
                  ·
                    refine ⟨560971453269191791475743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2991847750769022887870629 560971453269191791475743)
                    ·
                      rfl

theorem cell22_1638732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_1638732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1638732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1638732 prefixEnd_1638732 := by exact prefixLift 1638732
  have htrace : WordTrace (prefixWord ++ tailWord_1638732) baseStart_1638732 baseEnd_1638732 := by
    simpa [prefixWord, tailWord_1638732, baseEnd_1638732] using wordTrace_append hprefix tailTrace_1638732
  have hstable : (prefixWord ++ tailWord_1638732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638732).length < 2 ^ (prefixWord ++ tailWord_1638732).sum := by decide
  have hdescent : baseEnd_1638732 < baseStart_1638732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638856 : List Nat := [2, 1, 3, 1, 3, 3, 2, 2, 1, 4]
def baseStart_1638856 : Nat := 118140960795 + 1638856 * 2 ^ 59
def prefixEnd_1638856 : Nat := 4983230072969 + 3 ^ 40 * 1638856 * 2
def baseEnd_1638856 : Nat := 561013901003296801375363

theorem tailTrace_1638856 : CollatzResearch.WordTrace tailWord_1638856 prefixEnd_1638856 561013901003296801375363 := by
  unfold tailWord_1638856
  simp only [CollatzResearch.WordTrace]
  refine ⟨29886994475356040583192211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39849325967141387444256281 29886994475356040583192211)
  ·
    refine ⟨44830491713034060874788317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29886994475356040583192211 44830491713034060874788317)
    ·
      refine ⟨16811434392387772828045619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44830491713034060874788317 16811434392387772828045619)
      ·
        refine ⟨25217151588581659242068429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16811434392387772828045619 25217151588581659242068429)
        ·
          refine ⟨9456431845718122215775661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25217151588581659242068429 9456431845718122215775661)
          ·
            refine ⟨3546161942144295830915873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9456431845718122215775661 3546161942144295830915873)
            ·
              refine ⟨2659621456608221873186905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3546161942144295830915873 2659621456608221873186905)
              ·
                refine ⟨1994716092456166404890179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2659621456608221873186905 1994716092456166404890179)
                ·
                  refine ⟨2992074138684249607335269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1994716092456166404890179 2992074138684249607335269)
                  ·
                    refine ⟨561013901003296801375363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2992074138684249607335269 561013901003296801375363)
                    ·
                      rfl

theorem cell22_1638856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_1638856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1638856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1638856 prefixEnd_1638856 := by exact prefixLift 1638856
  have htrace : WordTrace (prefixWord ++ tailWord_1638856) baseStart_1638856 baseEnd_1638856 := by
    simpa [prefixWord, tailWord_1638856, baseEnd_1638856] using wordTrace_append hprefix tailTrace_1638856
  have hstable : (prefixWord ++ tailWord_1638856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638856).length < 2 ^ (prefixWord ++ tailWord_1638856).sum := by decide
  have hdescent : baseEnd_1638856 < baseStart_1638856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638888 : List Nat := [2, 1, 4, 1, 1, 4, 3, 2, 4]
def baseStart_1638888 : Nat := 118140960795 + 1638888 * 2 ^ 59
def prefixEnd_1638888 : Nat := 4983230072969 + 3 ^ 40 * 1638888 * 2
def baseEnd_1638888 : Nat := 187008285085753128191755

theorem tailTrace_1638888 : CollatzResearch.WordTrace tailWord_1638888 prefixEnd_1638888 187008285085753128191755 := by
  unfold tailWord_1638888
  simp only [CollatzResearch.WordTrace]
  refine ⟨29887578043298075315774659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39850104057730767087699545 29887578043298075315774659)
  ·
    refine ⟨44831367064947112973661989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29887578043298075315774659 44831367064947112973661989)
    ·
      refine ⟨8405881324677583682561623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44831367064947112973661989 8405881324677583682561623)
      ·
        refine ⟨12608821987016375523842435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8405881324677583682561623 12608821987016375523842435)
        ·
          refine ⟨18913232980524563285763653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12608821987016375523842435 18913232980524563285763653)
          ·
            refine ⟨3546231183848355616080685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18913232980524563285763653 3546231183848355616080685)
            ·
              refine ⟨1329836693943133356030257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3546231183848355616080685 1329836693943133356030257)
              ·
                refine ⟨997377520457350017022693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1329836693943133356030257 997377520457350017022693)
                ·
                  refine ⟨187008285085753128191755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 997377520457350017022693 187008285085753128191755)
                  ·
                    rfl

theorem cell22_1638888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 4].length) (baseStart_1638888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1638888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1638888 prefixEnd_1638888 := by exact prefixLift 1638888
  have htrace : WordTrace (prefixWord ++ tailWord_1638888) baseStart_1638888 baseEnd_1638888 := by
    simpa [prefixWord, tailWord_1638888, baseEnd_1638888] using wordTrace_append hprefix tailTrace_1638888
  have hstable : (prefixWord ++ tailWord_1638888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638888).length < 2 ^ (prefixWord ++ tailWord_1638888).sum := by decide
  have hdescent : baseEnd_1638888 < baseStart_1638888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638982 : List Nat := [6, 1, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_1638982 : Nat := 118140960795 + 1638982 * 2 ^ 59
def prefixEnd_1638982 : Nat := 4983230072969 + 3 ^ 40 * 1638982 * 2
def baseEnd_1638982 : Nat := 561057033378274472724977

theorem tailTrace_1638982 : CollatzResearch.WordTrace tailWord_1638982 prefixEnd_1638982 561057033378274472724977 := by
  unfold tailWord_1638982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1868080767132987646420975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39852389698837069790314133 1868080767132987646420975)
  ·
    refine ⟨2802121150699481469631463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1868080767132987646420975 2802121150699481469631463)
    ·
      refine ⟨4203181726049222204447195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2802121150699481469631463 4203181726049222204447195)
      ·
        refine ⟨6304772589073833306670793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4203181726049222204447195 6304772589073833306670793)
        ·
          refine ⟨4728579441805374980003095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6304772589073833306670793 4728579441805374980003095)
          ·
            refine ⟨7092869162708062470004643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4728579441805374980003095 7092869162708062470004643)
            ·
              refine ⟨10639303744062093705006965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7092869162708062470004643 10639303744062093705006965)
              ·
                refine ⟨997434726005821284844403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10639303744062093705006965 997434726005821284844403)
                ·
                  refine ⟨1496152089008731927266605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997434726005821284844403 1496152089008731927266605)
                  ·
                    refine ⟨561057033378274472724977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1496152089008731927266605 561057033378274472724977)
                    ·
                      rfl

theorem cell22_1638982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_1638982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1638982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1638982 prefixEnd_1638982 := by exact prefixLift 1638982
  have htrace : WordTrace (prefixWord ++ tailWord_1638982) baseStart_1638982 baseEnd_1638982 := by
    simpa [prefixWord, tailWord_1638982, baseEnd_1638982] using wordTrace_append hprefix tailTrace_1638982
  have hstable : (prefixWord ++ tailWord_1638982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638982).length < 2 ^ (prefixWord ++ tailWord_1638982).sum := by decide
  have hdescent : baseEnd_1638982 < baseStart_1638982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639019 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 6, 4]
def baseStart_1639019 : Nat := 118140960795 + 1639019 * 2 ^ 59
def prefixEnd_1639019 : Nat := 4983230072969 + 3 ^ 40 * 1639019 * 2
def baseEnd_1639019 : Nat := 561069699234418709549863

theorem tailTrace_1639019 : CollatzResearch.WordTrace tailWord_1639019 prefixEnd_1639019 561069699234418709549863 := by
  unfold tailWord_1639019
  simp only [CollatzResearch.WordTrace]
  refine ⟨59779934049121560004568111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39853289366081040003045407 59779934049121560004568111)
  ·
    refine ⟨89669901073682340006852167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59779934049121560004568111 89669901073682340006852167)
    ·
      refine ⟨134504851610523510010278251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89669901073682340006852167 134504851610523510010278251)
      ·
        refine ⟨201757277415785265015417377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134504851610523510010278251 201757277415785265015417377)
        ·
          refine ⟨151317958061838948761563033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201757277415785265015417377 151317958061838948761563033)
          ·
            refine ⟨113488468546379211571172275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151317958061838948761563033 113488468546379211571172275)
            ·
              refine ⟨170232702819568817356758413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113488468546379211571172275 170232702819568817356758413)
              ·
                refine ⟨63837263557338306508784405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170232702819568817356758413 63837263557338306508784405)
                ·
                  refine ⟨2992371729250233117599269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63837263557338306508784405 2992371729250233117599269)
                  ·
                    refine ⟨561069699234418709549863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2992371729250233117599269 561069699234418709549863)
                    ·
                      rfl

theorem cell22_1639019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 4].length) (baseStart_1639019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639019 prefixEnd_1639019 := by exact prefixLift 1639019
  have htrace : WordTrace (prefixWord ++ tailWord_1639019) baseStart_1639019 baseEnd_1639019 := by
    simpa [prefixWord, tailWord_1639019, baseEnd_1639019] using wordTrace_append hprefix tailTrace_1639019
  have hstable : (prefixWord ++ tailWord_1639019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639019).length < 2 ^ (prefixWord ++ tailWord_1639019).sum := by decide
  have hdescent : baseEnd_1639019 < baseStart_1639019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639072 : List Nat := [2, 1, 1, 4, 4, 2, 2, 1, 2, 3]
def baseStart_1639072 : Nat := 118140960795 + 1639072 * 2 ^ 59
def prefixEnd_1639072 : Nat := 4983230072969 + 3 ^ 40 * 1639072 * 2
def baseEnd_1639072 : Nat := 561087842217544237974701

theorem tailTrace_1639072 : CollatzResearch.WordTrace tailWord_1639072 prefixEnd_1639072 561087842217544237974701 := by
  unfold tailWord_1639072
  simp only [CollatzResearch.WordTrace]
  refine ⟨29890933558964775028123735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39854578078619700037498313 29890933558964775028123735)
  ·
    refine ⟨44836400338447162542185603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29890933558964775028123735 44836400338447162542185603)
    ·
      refine ⟨67254600507670743813278405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44836400338447162542185603 67254600507670743813278405)
      ·
        refine ⟨12610237595188264464989701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67254600507670743813278405 12610237595188264464989701)
        ·
          refine ⟨2364419549097799587185569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12610237595188264464989701 2364419549097799587185569)
          ·
            refine ⟨1773314661823349690389177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2364419549097799587185569 1773314661823349690389177)
            ·
              refine ⟨1329985996367512267791883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1773314661823349690389177 1329985996367512267791883)
              ·
                refine ⟨1994978994551268401687825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1329985996367512267791883 1994978994551268401687825)
                ·
                  refine ⟨1496234245913451301265869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1994978994551268401687825 1496234245913451301265869)
                  ·
                    refine ⟨561087842217544237974701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1496234245913451301265869 561087842217544237974701)
                    ·
                      rfl

theorem cell22_1639072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 2, 3].length) (baseStart_1639072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639072 prefixEnd_1639072 := by exact prefixLift 1639072
  have htrace : WordTrace (prefixWord ++ tailWord_1639072) baseStart_1639072 baseEnd_1639072 := by
    simpa [prefixWord, tailWord_1639072, baseEnd_1639072] using wordTrace_append hprefix tailTrace_1639072
  have hstable : (prefixWord ++ tailWord_1639072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639072).length < 2 ^ (prefixWord ++ tailWord_1639072).sum := by decide
  have hdescent : baseEnd_1639072 < baseStart_1639072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639100 : List Nat := [2, 2, 2, 3, 1, 1, 2, 5, 1, 3]
def baseStart_1639100 : Nat := 118140960795 + 1639100 * 2 ^ 59
def prefixEnd_1639100 : Nat := 4983230072969 + 3 ^ 40 * 1639100 * 2
def baseEnd_1639100 : Nat := 561097427189761498274615

theorem tailTrace_1639100 : CollatzResearch.WordTrace tailWord_1639100 prefixEnd_1639100 561097427189761498274615 := by
  unfold tailWord_1639100
  simp only [CollatzResearch.WordTrace]
  refine ⟨29891444180914055419133377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39855258907885407225511169 29891444180914055419133377)
  ·
    refine ⟨22418583135685541564350033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29891444180914055419133377 22418583135685541564350033)
    ·
      refine ⟨16813937351764156173262525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22418583135685541564350033 16813937351764156173262525)
      ·
        refine ⟨6305226506911558564973447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16813937351764156173262525 6305226506911558564973447)
        ·
          refine ⟨9457839760367337847460171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6305226506911558564973447 9457839760367337847460171)
          ·
            refine ⟨14186759640551006771190257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9457839760367337847460171 14186759640551006771190257)
            ·
              refine ⟨10640069730413255078392693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14186759640551006771190257 10640069730413255078392693)
              ·
                refine ⟨997506537226242663599315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10640069730413255078392693 997506537226242663599315)
                ·
                  refine ⟨1496259805839363995398973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997506537226242663599315 1496259805839363995398973)
                  ·
                    refine ⟨561097427189761498274615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1496259805839363995398973 561097427189761498274615)
                    ·
                      rfl

theorem cell22_1639100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_1639100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639100 prefixEnd_1639100 := by exact prefixLift 1639100
  have htrace : WordTrace (prefixWord ++ tailWord_1639100) baseStart_1639100 baseEnd_1639100 := by
    simpa [prefixWord, tailWord_1639100, baseEnd_1639100] using wordTrace_append hprefix tailTrace_1639100
  have hstable : (prefixWord ++ tailWord_1639100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639100).length < 2 ^ (prefixWord ++ tailWord_1639100).sum := by decide
  have hdescent : baseEnd_1639100 < baseStart_1639100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639141 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 8]
def baseStart_1639141 : Nat := 118140960795 + 1639141 * 2 ^ 59
def prefixEnd_1639141 : Nat := 4983230072969 + 3 ^ 40 * 1639141 * 2
def baseEnd_1639141 : Nat := 187037154109217019333163

theorem tailTrace_1639141 : CollatzResearch.WordTrace tailWord_1639141 prefixEnd_1639141 187037154109217019333163 := by
  unfold tailWord_1639141
  simp only [CollatzResearch.WordTrace]
  refine ⟨59784383754679574840509277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39856255836453049893672851 59784383754679574840509277)
  ·
    refine ⟨22419143908004840565190979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59784383754679574840509277 22419143908004840565190979)
    ·
      refine ⟨33628715862007260847786469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22419143908004840565190979 33628715862007260847786469)
      ·
        refine ⟨6305384224126361408959963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33628715862007260847786469 6305384224126361408959963)
        ·
          refine ⟨9458076336189542113439945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6305384224126361408959963 9458076336189542113439945)
          ·
            refine ⟨7093557252142156585079959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9458076336189542113439945 7093557252142156585079959)
            ·
              refine ⟨10640335878213234877619939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7093557252142156585079959 10640335878213234877619939)
              ·
                refine ⟨15960503817319852316429909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10640335878213234877619939 15960503817319852316429909)
                ·
                  refine ⟨187037154109217019333163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15960503817319852316429909 187037154109217019333163)
                  ·
                    rfl

theorem cell22_1639141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_1639141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639141 prefixEnd_1639141 := by exact prefixLift 1639141
  have htrace : WordTrace (prefixWord ++ tailWord_1639141) baseStart_1639141 baseEnd_1639141 := by
    simpa [prefixWord, tailWord_1639141, baseEnd_1639141] using wordTrace_append hprefix tailTrace_1639141
  have hstable : (prefixWord ++ tailWord_1639141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639141).length < 2 ^ (prefixWord ++ tailWord_1639141).sum := by decide
  have hdescent : baseEnd_1639141 < baseStart_1639141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639171 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 4, 4]
def baseStart_1639171 : Nat := 118140960795 + 1639171 * 2 ^ 59
def prefixEnd_1639171 : Nat := 4983230072969 + 3 ^ 40 * 1639171 * 2
def baseEnd_1639171 : Nat := 561121731940740979749397

theorem tailTrace_1639171 : CollatzResearch.WordTrace tailWord_1639171 prefixEnd_1639171 561121731940740979749397 := by
  unfold tailWord_1639171
  simp only [CollatzResearch.WordTrace]
  refine ⟨59785477944570889964101367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39856985296380593309400911 59785477944570889964101367)
  ·
    refine ⟨89678216916856334946152051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59785477944570889964101367 89678216916856334946152051)
    ·
      refine ⟨134517325375284502419228077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89678216916856334946152051 134517325375284502419228077)
      ·
        refine ⟨50443997015731688407210529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134517325375284502419228077 50443997015731688407210529)
        ·
          refine ⟨37832997761798766305407897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50443997015731688407210529 37832997761798766305407897)
          ·
            refine ⟨28374748321349074729055923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37832997761798766305407897 28374748321349074729055923)
            ·
              refine ⟨42562122482023612093583885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28374748321349074729055923 42562122482023612093583885)
              ·
                refine ⟨15960795930758854535093957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42562122482023612093583885 15960795930758854535093957)
                ·
                  refine ⟨2992649237017285225330117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15960795930758854535093957 2992649237017285225330117)
                  ·
                    refine ⟨561121731940740979749397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2992649237017285225330117 561121731940740979749397)
                    ·
                      rfl

theorem cell22_1639171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 4].length) (baseStart_1639171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639171 prefixEnd_1639171 := by exact prefixLift 1639171
  have htrace : WordTrace (prefixWord ++ tailWord_1639171) baseStart_1639171 baseEnd_1639171 := by
    simpa [prefixWord, tailWord_1639171, baseEnd_1639171] using wordTrace_append hprefix tailTrace_1639171
  have hstable : (prefixWord ++ tailWord_1639171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639171).length < 2 ^ (prefixWord ++ tailWord_1639171).sum := by decide
  have hdescent : baseEnd_1639171 < baseStart_1639171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639175 : List Nat := [1, 1, 4, 4, 1, 1, 2, 4, 4]
def baseStart_1639175 : Nat := 118140960795 + 1639175 * 2 ^ 59
def prefixEnd_1639175 : Nat := 4983230072969 + 3 ^ 40 * 1639175 * 2
def baseEnd_1639175 : Nat := 187041033740828767549795

theorem tailTrace_1639175 : CollatzResearch.WordTrace tailWord_1639175 prefixEnd_1639175 187041033740828767549795 := by
  unfold tailWord_1639175
  simp only [CollatzResearch.WordTrace]
  refine ⟨59785623836556398647246979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39857082557704265764831319 59785623836556398647246979)
  ·
    refine ⟨89678435754834597970870469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59785623836556398647246979 89678435754834597970870469)
    ·
      refine ⟨16814706704031487119538213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89678435754834597970870469 16814706704031487119538213)
      ·
        refine ⟨3152757507005903834913415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16814706704031487119538213 3152757507005903834913415)
        ·
          refine ⟨4729136260508855752370123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3152757507005903834913415 4729136260508855752370123)
          ·
            refine ⟨7093704390763283628555185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4729136260508855752370123 7093704390763283628555185)
            ·
              refine ⟨5320278293072462721416389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7093704390763283628555185 5320278293072462721416389)
              ·
                refine ⟨997552179951086760265573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5320278293072462721416389 997552179951086760265573)
                ·
                  refine ⟨187041033740828767549795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 997552179951086760265573 187041033740828767549795)
                  ·
                    rfl

theorem cell22_1639175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 4].length) (baseStart_1639175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639175 prefixEnd_1639175 := by exact prefixLift 1639175
  have htrace : WordTrace (prefixWord ++ tailWord_1639175) baseStart_1639175 baseEnd_1639175 := by
    simpa [prefixWord, tailWord_1639175, baseEnd_1639175] using wordTrace_append hprefix tailTrace_1639175
  have hstable : (prefixWord ++ tailWord_1639175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639175).length < 2 ^ (prefixWord ++ tailWord_1639175).sum := by decide
  have hdescent : baseEnd_1639175 < baseStart_1639175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639201 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 2, 7]
def baseStart_1639201 : Nat := 118140960795 + 1639201 * 2 ^ 59
def prefixEnd_1639201 : Nat := 4983230072969 + 3 ^ 40 * 1639201 * 2
def baseEnd_1639201 : Nat := 561132001553830901499305

theorem tailTrace_1639201 : CollatzResearch.WordTrace tailWord_1639201 prefixEnd_1639201 561132001553830901499305 := by
  unfold tailWord_1639201
  simp only [CollatzResearch.WordTrace]
  refine ⟨59786572134462205087693457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39857714756308136725128971 59786572134462205087693457)
  ·
    refine ⟨44839929100846653815770093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59786572134462205087693457 44839929100846653815770093)
    ·
      refine ⟨16814973412817495180913785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44839929100846653815770093 16814973412817495180913785)
      ·
        refine ⟨12611230059613121385685339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16814973412817495180913785 12611230059613121385685339)
        ·
          refine ⟨18916845089419682078528009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12611230059613121385685339 18916845089419682078528009)
          ·
            refine ⟨14187633817064761558896007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18916845089419682078528009 14187633817064761558896007)
            ·
              refine ⟨21281450725597142338344011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14187633817064761558896007 21281450725597142338344011)
              ·
                refine ⟨31922176088395713507516017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21281450725597142338344011 31922176088395713507516017)
                ·
                  refine ⟨23941632066296785130637013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31922176088395713507516017 23941632066296785130637013)
                  ·
                    refine ⟨561132001553830901499305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23941632066296785130637013 561132001553830901499305)
                    ·
                      rfl

theorem cell22_1639201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_1639201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639201 prefixEnd_1639201 := by exact prefixLift 1639201
  have htrace : WordTrace (prefixWord ++ tailWord_1639201) baseStart_1639201 baseEnd_1639201 := by
    simpa [prefixWord, tailWord_1639201, baseEnd_1639201] using wordTrace_append hprefix tailTrace_1639201
  have hstable : (prefixWord ++ tailWord_1639201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639201).length < 2 ^ (prefixWord ++ tailWord_1639201).sum := by decide
  have hdescent : baseEnd_1639201 < baseStart_1639201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639220 : List Nat := [2, 5, 1, 1, 3, 2, 8]
def baseStart_1639220 : Nat := 118140960795 + 1639220 * 2 ^ 59
def prefixEnd_1639220 : Nat := 4983230072969 + 3 ^ 40 * 1639220 * 2
def baseEnd_1639220 : Nat := 20782907616374858713861

theorem tailTrace_1639220 : CollatzResearch.WordTrace tailWord_1639220 prefixEnd_1639220 20782907616374858713861 := by
  unfold tailWord_1639220
  simp only [CollatzResearch.WordTrace]
  refine ⟨29893632560696685666317557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39858176747595580888423409 29893632560696685666317557)
  ·
    refine ⟨2802528052565314281217271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29893632560696685666317557 2802528052565314281217271)
    ·
      refine ⟨4203792078847971421825907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2802528052565314281217271 4203792078847971421825907)
      ·
        refine ⟨6305688118271957132738861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4203792078847971421825907 6305688118271957132738861)
        ·
          refine ⟨2364633044351983924777073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6305688118271957132738861 2364633044351983924777073)
          ·
            refine ⟨1773474783263987943582805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2364633044351983924777073 1773474783263987943582805)
            ·
              refine ⟨20782907616374858713861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1773474783263987943582805 20782907616374858713861)
              ·
                rfl

theorem cell22_1639220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 8].length) (baseStart_1639220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639220 prefixEnd_1639220 := by exact prefixLift 1639220
  have htrace : WordTrace (prefixWord ++ tailWord_1639220) baseStart_1639220 baseEnd_1639220 := by
    simpa [prefixWord, tailWord_1639220, baseEnd_1639220] using wordTrace_append hprefix tailTrace_1639220
  have hstable : (prefixWord ++ tailWord_1639220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639220).length < 2 ^ (prefixWord ++ tailWord_1639220).sum := by decide
  have hdescent : baseEnd_1639220 < baseStart_1639220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639222 : List Nat := [5, 1, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_1639222 : Nat := 118140960795 + 1639222 * 2 ^ 59
def prefixEnd_1639222 : Nat := 4983230072969 + 3 ^ 40 * 1639222 * 2
def baseEnd_1639222 : Nat := 561139190282993846724241

theorem tailTrace_1639222 : CollatzResearch.WordTrace tailWord_1639222 prefixEnd_1639222 561139190282993846724241 := by
  unfold tailWord_1639222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3736708629211632854637995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39858225378257417116138613 3736708629211632854637995)
  ·
    refine ⟨5605062943817449281956993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3736708629211632854637995 5605062943817449281956993)
    ·
      refine ⟨4203797207863086961467745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5605062943817449281956993 4203797207863086961467745)
      ·
        refine ⟨3152847905897315221100809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4203797207863086961467745 3152847905897315221100809)
        ·
          refine ⟨2364635929422986415825607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3152847905897315221100809 2364635929422986415825607)
          ·
            refine ⟨3546953894134479623738411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2364635929422986415825607 3546953894134479623738411)
            ·
              refine ⟨5320430841201719435607617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3546953894134479623738411 5320430841201719435607617)
              ·
                refine ⟨3990323130901289576705713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5320430841201719435607617 3990323130901289576705713)
                ·
                  refine ⟨2992742348175967182529285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3990323130901289576705713 2992742348175967182529285)
                  ·
                    refine ⟨561139190282993846724241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2992742348175967182529285 561139190282993846724241)
                    ·
                      rfl

theorem cell22_1639222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_1639222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639222 prefixEnd_1639222 := by exact prefixLift 1639222
  have htrace : WordTrace (prefixWord ++ tailWord_1639222) baseStart_1639222 baseEnd_1639222 := by
    simpa [prefixWord, tailWord_1639222, baseEnd_1639222] using wordTrace_append hprefix tailTrace_1639222
  have hstable : (prefixWord ++ tailWord_1639222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639222).length < 2 ^ (prefixWord ++ tailWord_1639222).sum := by decide
  have hdescent : baseEnd_1639222 < baseStart_1639222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639286 : List Nat := [5, 1, 1, 3, 1, 1, 4, 2, 1, 3]
def baseStart_1639286 : Nat := 118140960795 + 1639286 * 2 ^ 59
def prefixEnd_1639286 : Nat := 4983230072969 + 3 ^ 40 * 1639286 * 2
def baseEnd_1639286 : Nat := 561161098790919013124045

theorem tailTrace_1639286 : CollatzResearch.WordTrace tailWord_1639286 prefixEnd_1639286 561161098790919013124045 := by
  unfold tailWord_1639286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3736854521197141537783607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39859781559436176403025141 3736854521197141537783607)
  ·
    refine ⟨5605281781795712306675411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3736854521197141537783607 5605281781795712306675411)
    ·
      refine ⟨8407922672693568460013117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5605281781795712306675411 8407922672693568460013117)
      ·
        refine ⟨3152971002260088172504919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8407922672693568460013117 3152971002260088172504919)
        ·
          refine ⟨4729456503390132258757379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3152971002260088172504919 4729456503390132258757379)
          ·
            refine ⟨7094184755085198388136069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4729456503390132258757379 7094184755085198388136069)
            ·
              refine ⟨1330159641578474697775513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7094184755085198388136069 1330159641578474697775513)
              ·
                refine ⟨997619731183856023331635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1330159641578474697775513 997619731183856023331635)
                ·
                  refine ⟨1496429596775784034997453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997619731183856023331635 1496429596775784034997453)
                  ·
                    refine ⟨561161098790919013124045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1496429596775784034997453 561161098790919013124045)
                    ·
                      rfl

theorem cell22_1639286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_1639286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639286 prefixEnd_1639286 := by exact prefixLift 1639286
  have htrace : WordTrace (prefixWord ++ tailWord_1639286) baseStart_1639286 baseEnd_1639286 := by
    simpa [prefixWord, tailWord_1639286, baseEnd_1639286] using wordTrace_append hprefix tailTrace_1639286
  have hstable : (prefixWord ++ tailWord_1639286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639286).length < 2 ^ (prefixWord ++ tailWord_1639286).sum := by decide
  have hdescent : baseEnd_1639286 < baseStart_1639286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639308 : List Nat := [2, 2, 1, 2, 1, 2, 3, 3, 1, 5]
def baseStart_1639308 : Nat := 118140960795 + 1639308 * 2 ^ 59
def prefixEnd_1639308 : Nat := 4983230072969 + 3 ^ 40 * 1639308 * 2
def baseEnd_1639308 : Nat := 561168629840518289073977

theorem tailTrace_1639308 : CollatzResearch.WordTrace tailWord_1639308 prefixEnd_1639308 561168629840518289073977 := by
  unfold tailWord_1639308
  simp only [CollatzResearch.WordTrace]
  refine ⟨29895237372537281180919289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39860316496716374907892385 29895237372537281180919289)
  ·
    refine ⟨22421428029402960885689467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29895237372537281180919289 22421428029402960885689467)
    ·
      refine ⟨33632142044104441328534201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22421428029402960885689467 33632142044104441328534201)
      ·
        refine ⟨25224106533078330996400651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33632142044104441328534201 25224106533078330996400651)
        ·
          refine ⟨37836159799617496494600977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25224106533078330996400651 37836159799617496494600977)
          ·
            refine ⟨28377119849713122370950733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37836159799617496494600977 28377119849713122370950733)
            ·
              refine ⟨10641419943642420889106525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28377119849713122370950733 10641419943642420889106525)
              ·
                refine ⟨3990532478865907833414947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10641419943642420889106525 3990532478865907833414947)
                ·
                  refine ⟨5985798718298861750122421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3990532478865907833414947 5985798718298861750122421)
                  ·
                    refine ⟨561168629840518289073977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5985798718298861750122421 561168629840518289073977)
                    ·
                      rfl

theorem cell22_1639308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_1639308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639308 prefixEnd_1639308 := by exact prefixLift 1639308
  have htrace : WordTrace (prefixWord ++ tailWord_1639308) baseStart_1639308 baseEnd_1639308 := by
    simpa [prefixWord, tailWord_1639308, baseEnd_1639308] using wordTrace_append hprefix tailTrace_1639308
  have hstable : (prefixWord ++ tailWord_1639308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639308).length < 2 ^ (prefixWord ++ tailWord_1639308).sum := by decide
  have hdescent : baseEnd_1639308 < baseStart_1639308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639325 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 4, 3]
def baseStart_1639325 : Nat := 118140960795 + 1639325 * 2 ^ 59
def prefixEnd_1639325 : Nat := 4983230072969 + 3 ^ 40 * 1639325 * 2
def baseEnd_1639325 : Nat := 561174449287935911398925

theorem tailTrace_1639325 : CollatzResearch.WordTrace tailWord_1639325 prefixEnd_1639325 561174449287935911398925 := by
  unfold tailWord_1639325
  simp only [CollatzResearch.WordTrace]
  refine ⟨59791094786012974265207429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39860729857341982843471619 59791094786012974265207429)
  ·
    refine ⟨11210830272377432674726393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59791094786012974265207429 11210830272377432674726393)
    ·
      refine ⟨8408122704283074506044795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11210830272377432674726393 8408122704283074506044795)
      ·
        refine ⟨12612184056424611759067193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8408122704283074506044795 12612184056424611759067193)
        ·
          refine ⟨9459138042318458819300395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12612184056424611759067193 9459138042318458819300395)
          ·
            refine ⟨14188707063477688228950593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9459138042318458819300395 14188707063477688228950593)
            ·
              refine ⟨10641530297608266171712945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14188707063477688228950593 10641530297608266171712945)
              ·
                refine ⟨7981147723206199628784709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10641530297608266171712945 7981147723206199628784709)
                ·
                  refine ⟨1496465198101162430397133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7981147723206199628784709 1496465198101162430397133)
                  ·
                    refine ⟨561174449287935911398925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1496465198101162430397133 561174449287935911398925)
                    ·
                      rfl

theorem cell22_1639325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_1639325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639325 prefixEnd_1639325 := by exact prefixLift 1639325
  have htrace : WordTrace (prefixWord ++ tailWord_1639325) baseStart_1639325 baseEnd_1639325 := by
    simpa [prefixWord, tailWord_1639325, baseEnd_1639325] using wordTrace_append hprefix tailTrace_1639325
  have hstable : (prefixWord ++ tailWord_1639325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639325).length < 2 ^ (prefixWord ++ tailWord_1639325).sum := by decide
  have hdescent : baseEnd_1639325 < baseStart_1639325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639327 : List Nat := [1, 1, 2, 5, 2, 2, 2, 3, 4]
def baseStart_1639327 : Nat := 118140960795 + 1639327 * 2 ^ 59
def prefixEnd_1639327 : Nat := 4983230072969 + 3 ^ 40 * 1639327 * 2
def baseEnd_1639327 : Nat := 187058377976269524282973

theorem tailTrace_1639327 : CollatzResearch.WordTrace tailWord_1639327 prefixEnd_1639327 187058377976269524282973 := by
  unfold tailWord_1639327
  simp only [CollatzResearch.WordTrace]
  refine ⟨59791167732005728606780235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39860778488003819071186823 59791167732005728606780235)
  ·
    refine ⟨89686751598008592910170353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59791167732005728606780235 89686751598008592910170353)
    ·
      refine ⟨67265063698506444682627765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89686751598008592910170353 67265063698506444682627765)
      ·
        refine ⟨6306099721734979188996353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67265063698506444682627765 6306099721734979188996353)
        ·
          refine ⟨4729574791301234391747265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6306099721734979188996353 4729574791301234391747265)
          ·
            refine ⟨3547181093475925793810449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4729574791301234391747265 3547181093475925793810449)
            ·
              refine ⟨2660385820106944345357837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3547181093475925793810449 2660385820106944345357837)
              ·
                refine ⟨997644682540104129509189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2660385820106944345357837 997644682540104129509189)
                ·
                  refine ⟨187058377976269524282973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 997644682540104129509189 187058377976269524282973)
                  ·
                    rfl

theorem cell22_1639327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 4].length) (baseStart_1639327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639327 prefixEnd_1639327 := by exact prefixLift 1639327
  have htrace : WordTrace (prefixWord ++ tailWord_1639327) baseStart_1639327 baseEnd_1639327 := by
    simpa [prefixWord, tailWord_1639327, baseEnd_1639327] using wordTrace_append hprefix tailTrace_1639327
  have hstable : (prefixWord ++ tailWord_1639327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639327).length < 2 ^ (prefixWord ++ tailWord_1639327).sum := by decide
  have hdescent : baseEnd_1639327 < baseStart_1639327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639329 : List Nat := [1, 2, 3, 4, 1, 3, 2, 1, 1, 4]
def baseStart_1639329 : Nat := 118140960795 + 1639329 * 2 ^ 59
def prefixEnd_1639329 : Nat := 4983230072969 + 3 ^ 40 * 1639329 * 2
def baseEnd_1639329 : Nat := 561175818569681234298913

theorem tailTrace_1639329 : CollatzResearch.WordTrace tailWord_1639329 prefixEnd_1639329 561175818569681234298913 := by
  unfold tailWord_1639329
  simp only [CollatzResearch.WordTrace]
  refine ⟨59791240677998482948353041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39860827118665655298902027 59791240677998482948353041)
  ·
    refine ⟨44843430508498862211264781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59791240677998482948353041 44843430508498862211264781)
    ·
      refine ⟨16816286440687073329224293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44843430508498862211264781 16816286440687073329224293)
      ·
        refine ⟨3153053707628826249229555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16816286440687073329224293 3153053707628826249229555)
        ·
          refine ⟨4729580561443239373844333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3153053707628826249229555 4729580561443239373844333)
          ·
            refine ⟨1773592710541214765191625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4729580561443239373844333 1773592710541214765191625)
            ·
              refine ⟨1330194532905911073893719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1773592710541214765191625 1330194532905911073893719)
              ·
                refine ⟨1995291799358866610840579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330194532905911073893719 1995291799358866610840579)
                ·
                  refine ⟨2992937699038299916260869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1995291799358866610840579 2992937699038299916260869)
                  ·
                    refine ⟨561175818569681234298913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2992937699038299916260869 561175818569681234298913)
                    ·
                      rfl

theorem cell22_1639329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_1639329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639329 prefixEnd_1639329 := by exact prefixLift 1639329
  have htrace : WordTrace (prefixWord ++ tailWord_1639329) baseStart_1639329 baseEnd_1639329 := by
    simpa [prefixWord, tailWord_1639329, baseEnd_1639329] using wordTrace_append hprefix tailTrace_1639329
  have hstable : (prefixWord ++ tailWord_1639329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639329).length < 2 ^ (prefixWord ++ tailWord_1639329).sum := by decide
  have hdescent : baseEnd_1639329 < baseStart_1639329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639494 : List Nat := [6, 1, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_1639494 : Nat := 118140960795 + 1639494 * 2 ^ 59
def prefixEnd_1639494 : Nat := 4983230072969 + 3 ^ 40 * 1639494 * 2
def baseEnd_1639494 : Nat := 561232301441675803923407

theorem tailTrace_1639494 : CollatzResearch.WordTrace tailWord_1639494 prefixEnd_1639494 561232301441675803923407 := by
  unfold tailWord_1639494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1868664335075022379003423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39864839148267144085406357 1868664335075022379003423)
  ·
    refine ⟨2802996502612533568505135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1868664335075022379003423 2802996502612533568505135)
    ·
      refine ⟨4204494753918800352757703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2802996502612533568505135 4204494753918800352757703)
      ·
        refine ⟨6306742130878200529136555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4204494753918800352757703 6306742130878200529136555)
        ·
          refine ⟨9460113196317300793704833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6306742130878200529136555 9460113196317300793704833)
          ·
            refine ⟨7095084897237975595278625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9460113196317300793704833 7095084897237975595278625)
            ·
              refine ⟨5321313672928481696458969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7095084897237975595278625 5321313672928481696458969)
              ·
                refine ⟨3990985254696361272344227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5321313672928481696458969 3990985254696361272344227)
                ·
                  refine ⟨5986477882044541908516341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3990985254696361272344227 5986477882044541908516341)
                  ·
                    refine ⟨561232301441675803923407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5986477882044541908516341 561232301441675803923407)
                    ·
                      rfl

theorem cell22_1639494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_1639494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639494 prefixEnd_1639494 := by exact prefixLift 1639494
  have htrace : WordTrace (prefixWord ++ tailWord_1639494) baseStart_1639494 baseEnd_1639494 := by
    simpa [prefixWord, tailWord_1639494, baseEnd_1639494] using wordTrace_append hprefix tailTrace_1639494
  have hstable : (prefixWord ++ tailWord_1639494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639494).length < 2 ^ (prefixWord ++ tailWord_1639494).sum := by decide
  have hdescent : baseEnd_1639494 < baseStart_1639494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639528 : List Nat := [2, 1, 4, 4, 1, 1, 3, 1, 2, 3]
def baseStart_1639528 : Nat := 118140960795 + 1639528 * 2 ^ 59
def prefixEnd_1639528 : Nat := 4983230072969 + 3 ^ 40 * 1639528 * 2
def baseEnd_1639528 : Nat := 561243940336511048573303

theorem tailTrace_1639528 : CollatzResearch.WordTrace tailWord_1639528 prefixEnd_1639528 561243940336511048573303 := by
  unfold tailWord_1639528
  simp only [CollatzResearch.WordTrace]
  refine ⟨29899249402138769967423619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39865665869518359956564825 29899249402138769967423619)
  ·
    refine ⟨44848874103208154951135429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29899249402138769967423619 44848874103208154951135429)
    ·
      refine ⟨8409163894351529053337893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44848874103208154951135429 8409163894351529053337893)
      ·
        refine ⟨1576718230190911697500855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8409163894351529053337893 1576718230190911697500855)
        ·
          refine ⟨2365077345286367546251283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1576718230190911697500855 2365077345286367546251283)
          ·
            refine ⟨3547616017929551319376925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2365077345286367546251283 3547616017929551319376925)
            ·
              refine ⟨1330356006723581744766347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3547616017929551319376925 1330356006723581744766347)
              ·
                refine ⟨1995534010085372617149521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330356006723581744766347 1995534010085372617149521)
                ·
                  refine ⟨1496650507564029462862141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1995534010085372617149521 1496650507564029462862141)
                  ·
                    refine ⟨561243940336511048573303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1496650507564029462862141 561243940336511048573303)
                    ·
                      rfl

theorem cell22_1639528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_1639528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639528 prefixEnd_1639528 := by exact prefixLift 1639528
  have htrace : WordTrace (prefixWord ++ tailWord_1639528) baseStart_1639528 baseEnd_1639528 := by
    simpa [prefixWord, tailWord_1639528, baseEnd_1639528] using wordTrace_append hprefix tailTrace_1639528
  have hstable : (prefixWord ++ tailWord_1639528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639528).length < 2 ^ (prefixWord ++ tailWord_1639528).sum := by decide
  have hdescent : baseEnd_1639528 < baseStart_1639528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639541 : List Nat := [1, 3, 4, 3, 1, 2, 2, 6]
def baseStart_1639541 : Nat := 118140960795 + 1639541 * 2 ^ 59
def prefixEnd_1639541 : Nat := 4983230072969 + 3 ^ 40 * 1639541 * 2
def baseEnd_1639541 : Nat := 62360932278020371999807

theorem tailTrace_1639541 : CollatzResearch.WordTrace tailWord_1639541 prefixEnd_1639541 62360932278020371999807 := by
  unfold tailWord_1639541
  simp only [CollatzResearch.WordTrace]
  refine ⟨59798972953230443155070477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39865981968820295436713651 59798972953230443155070477)
  ·
    refine ⟨22424614857461416183151429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59798972953230443155070477 22424614857461416183151429)
    ·
      refine ⟨4204615285774015534340893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22424614857461416183151429 4204615285774015534340893)
      ·
        refine ⟨1576730732165255825377835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4204615285774015534340893 1576730732165255825377835)
        ·
          refine ⟨2365096098247883738066753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1576730732165255825377835 2365096098247883738066753)
          ·
            refine ⟨1773822073685912803550065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2365096098247883738066753 1773822073685912803550065)
            ·
              refine ⟨1330366555264434602662549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1773822073685912803550065 1330366555264434602662549)
              ·
                refine ⟨62360932278020371999807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1330366555264434602662549 62360932278020371999807)
                ·
                  rfl

theorem cell22_1639541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 6].length) (baseStart_1639541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639541 prefixEnd_1639541 := by exact prefixLift 1639541
  have htrace : WordTrace (prefixWord ++ tailWord_1639541) baseStart_1639541 baseEnd_1639541 := by
    simpa [prefixWord, tailWord_1639541, baseEnd_1639541] using wordTrace_append hprefix tailTrace_1639541
  have hstable : (prefixWord ++ tailWord_1639541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639541).length < 2 ^ (prefixWord ++ tailWord_1639541).sum := by decide
  have hdescent : baseEnd_1639541 < baseStart_1639541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639556 : List Nat := [2, 3, 2, 1, 2, 2, 3, 3, 1, 3]
def baseStart_1639556 : Nat := 118140960795 + 1639556 * 2 ^ 59
def prefixEnd_1639556 : Nat := 4983230072969 + 3 ^ 40 * 1639556 * 2
def baseEnd_1639556 : Nat := 561253525308728308873217

theorem tailTrace_1639556 : CollatzResearch.WordTrace tailWord_1639556 prefixEnd_1639556 561253525308728308873217 := by
  unfold tailWord_1639556
  simp only [CollatzResearch.WordTrace]
  refine ⟨29899760024088050358433261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39866346698784067144577681 29899760024088050358433261)
  ·
    refine ⟨11212410009033018884412473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29899760024088050358433261 11212410009033018884412473)
    ·
      refine ⟨8409307506774764163309355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11212410009033018884412473 8409307506774764163309355)
      ·
        refine ⟨12613961260162146244964033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8409307506774764163309355 12613961260162146244964033)
        ·
          refine ⟨9460470945121609683723025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12613961260162146244964033 9460470945121609683723025)
          ·
            refine ⟨7095353208841207262792269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9460470945121609683723025 7095353208841207262792269)
            ·
              refine ⟨2660757453315452723547101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7095353208841207262792269 2660757453315452723547101)
              ·
                refine ⟨997784044993294771330163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2660757453315452723547101 997784044993294771330163)
                ·
                  refine ⟨1496676067489942156995245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997784044993294771330163 1496676067489942156995245)
                  ·
                    refine ⟨561253525308728308873217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1496676067489942156995245 561253525308728308873217)
                    ·
                      rfl

theorem cell22_1639556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_1639556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639556 prefixEnd_1639556 := by exact prefixLift 1639556
  have htrace : WordTrace (prefixWord ++ tailWord_1639556) baseStart_1639556 baseEnd_1639556 := by
    simpa [prefixWord, tailWord_1639556, baseEnd_1639556] using wordTrace_append hprefix tailTrace_1639556
  have hstable : (prefixWord ++ tailWord_1639556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639556).length < 2 ^ (prefixWord ++ tailWord_1639556).sum := by decide
  have hdescent : baseEnd_1639556 < baseStart_1639556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639612 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 3, 5]
def baseStart_1639612 : Nat := 118140960795 + 1639612 * 2 ^ 59
def prefixEnd_1639612 : Nat := 4983230072969 + 3 ^ 40 * 1639612 * 2
def baseEnd_1639612 : Nat := 561272695253162829473045

theorem tailTrace_1639612 : CollatzResearch.WordTrace tailWord_1639612 prefixEnd_1639612 561272695253162829473045 := by
  unfold tailWord_1639612
  simp only [CollatzResearch.WordTrace]
  refine ⟨29900781267986611140452545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39867708357315481520603393 29900781267986611140452545)
  ·
    refine ⟨22425585950989958355339409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29900781267986611140452545 22425585950989958355339409)
    ·
      refine ⟨16819189463242468766504557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22425585950989958355339409 16819189463242468766504557)
      ·
        refine ⟨6307196048715925787439209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16819189463242468766504557 6307196048715925787439209)
        ·
          refine ⟨4730397036536944340579407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6307196048715925787439209 4730397036536944340579407)
          ·
            refine ⟨7095595554805416510869111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4730397036536944340579407 7095595554805416510869111)
            ·
              refine ⟨10643393332208124766303667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7095595554805416510869111 10643393332208124766303667)
              ·
                refine ⟨15965089998312187149455501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10643393332208124766303667 15965089998312187149455501)
                ·
                  refine ⟨5986908749367070181045813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15965089998312187149455501 5986908749367070181045813)
                  ·
                    refine ⟨561272695253162829473045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5986908749367070181045813 561272695253162829473045)
                    ·
                      rfl

theorem cell22_1639612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_1639612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639612 prefixEnd_1639612 := by exact prefixLift 1639612
  have htrace : WordTrace (prefixWord ++ tailWord_1639612) baseStart_1639612 baseEnd_1639612 := by
    simpa [prefixWord, tailWord_1639612, baseEnd_1639612] using wordTrace_append hprefix tailTrace_1639612
  have hstable : (prefixWord ++ tailWord_1639612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639612).length < 2 ^ (prefixWord ++ tailWord_1639612).sum := by decide
  have hdescent : baseEnd_1639612 < baseStart_1639612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639616 : List Nat := [2, 1, 1, 2, 6, 1, 3, 1, 1, 4]
def baseStart_1639616 : Nat := 118140960795 + 1639616 * 2 ^ 59
def prefixEnd_1639616 : Nat := 4983230072969 + 3 ^ 40 * 1639616 * 2
def baseEnd_1639616 : Nat := 561274064534908152373033

theorem tailTrace_1639616 : CollatzResearch.WordTrace tailWord_1639616 prefixEnd_1639616 561274064534908152373033 := by
  unfold tailWord_1639616
  simp only [CollatzResearch.WordTrace]
  refine ⟨29900854213979365482025351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39867805618639153976033801 29900854213979365482025351)
  ·
    refine ⟨44851281320969048223038027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29900854213979365482025351 44851281320969048223038027)
    ·
      refine ⟨67276921981453572334557041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44851281320969048223038027 67276921981453572334557041)
      ·
        refine ⟨50457691486090179250917781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67276921981453572334557041 50457691486090179250917781)
        ·
          refine ⟨2365204288410477152386771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50457691486090179250917781 2365204288410477152386771)
          ·
            refine ⟨3547806432615715728580157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2365204288410477152386771 3547806432615715728580157)
            ·
              refine ⟨1330427412230893398217559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3547806432615715728580157 1330427412230893398217559)
              ·
                refine ⟨1995641118346340097326339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330427412230893398217559 1995641118346340097326339)
                ·
                  refine ⟨2993461677519510145989509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1995641118346340097326339 2993461677519510145989509)
                  ·
                    refine ⟨561274064534908152373033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2993461677519510145989509 561274064534908152373033)
                    ·
                      rfl

theorem cell22_1639616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 1, 4].length) (baseStart_1639616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639616 prefixEnd_1639616 := by exact prefixLift 1639616
  have htrace : WordTrace (prefixWord ++ tailWord_1639616) baseStart_1639616 baseEnd_1639616 := by
    simpa [prefixWord, tailWord_1639616, baseEnd_1639616] using wordTrace_append hprefix tailTrace_1639616
  have hstable : (prefixWord ++ tailWord_1639616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639616).length < 2 ^ (prefixWord ++ tailWord_1639616).sum := by decide
  have hdescent : baseEnd_1639616 < baseStart_1639616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639661 : List Nat := [1, 5, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_1639661 : Nat := 118140960795 + 1639661 * 2 ^ 59
def prefixEnd_1639661 : Nat := 4983230072969 + 3 ^ 40 * 1639661 * 2
def baseEnd_1639661 : Nat := 561289468954543034997895

theorem tailTrace_1639661 : CollatzResearch.WordTrace tailWord_1639661 prefixEnd_1639661 561289468954543034997895 := by
  unfold tailWord_1639661
  simp only [CollatzResearch.WordTrace]
  refine ⟨59803349712795703649438837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39868899808530469099625891 59803349712795703649438837)
  ·
    refine ⟨5606564035574597217134891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59803349712795703649438837 5606564035574597217134891)
    ·
      refine ⟨8409846053361895825702337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5606564035574597217134891 8409846053361895825702337)
      ·
        refine ⟨6307384540021421869276753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8409846053361895825702337 6307384540021421869276753)
        ·
          refine ⟨4730538405016066401957565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6307384540021421869276753 4730538405016066401957565)
          ·
            refine ⟨1773951901881024900734087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4730538405016066401957565 1773951901881024900734087)
            ·
              refine ⟨2660927852821537351101131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1773951901881024900734087 2660927852821537351101131)
              ·
                refine ⟨3991391779232306026651697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2660927852821537351101131 3991391779232306026651697)
                ·
                  refine ⟨2993543834424229519988773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3991391779232306026651697 2993543834424229519988773)
                  ·
                    refine ⟨561289468954543034997895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2993543834424229519988773 561289468954543034997895)
                    ·
                      rfl

theorem cell22_1639661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_1639661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639661 prefixEnd_1639661 := by exact prefixLift 1639661
  have htrace : WordTrace (prefixWord ++ tailWord_1639661) baseStart_1639661 baseEnd_1639661 := by
    simpa [prefixWord, tailWord_1639661, baseEnd_1639661] using wordTrace_append hprefix tailTrace_1639661
  have hstable : (prefixWord ++ tailWord_1639661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639661).length < 2 ^ (prefixWord ++ tailWord_1639661).sum := by decide
  have hdescent : baseEnd_1639661 < baseStart_1639661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639691 : List Nat := [1, 1, 1, 1, 5, 3, 2, 4, 1, 3]
def baseStart_1639691 : Nat := 118140960795 + 1639691 * 2 ^ 59
def prefixEnd_1639691 : Nat := 4983230072969 + 3 ^ 40 * 1639691 * 2
def baseEnd_1639691 : Nat := 561299738567632956747803

theorem tailTrace_1639691 : CollatzResearch.WordTrace tailWord_1639691 prefixEnd_1639691 561299738567632956747803 := by
  unfold tailWord_1639691
  simp only [CollatzResearch.WordTrace]
  refine ⟨59804443902687018773030927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39869629268458012515353951 59804443902687018773030927)
  ·
    refine ⟨89706665854030528159546391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59804443902687018773030927 89706665854030528159546391)
    ·
      refine ⟨134559998781045792239319587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89706665854030528159546391 134559998781045792239319587)
      ·
        refine ⟨201839998171568688358979381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134559998781045792239319587 201839998171568688358979381)
        ·
          refine ⟨18922499828584564533654317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201839998171568688358979381 18922499828584564533654317)
          ·
            refine ⟨7095937435719211700120369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18922499828584564533654317 7095937435719211700120369)
            ·
              refine ⟨5321953076789408775090277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7095937435719211700120369 5321953076789408775090277)
              ·
                refine ⟨997866201898014145329427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5321953076789408775090277 997866201898014145329427)
                ·
                  refine ⟨1496799302847021217994141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997866201898014145329427 1496799302847021217994141)
                  ·
                    refine ⟨561299738567632956747803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1496799302847021217994141 561299738567632956747803)
                    ·
                      rfl

theorem cell22_1639691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 1, 3].length) (baseStart_1639691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639691 prefixEnd_1639691 := by exact prefixLift 1639691
  have htrace : WordTrace (prefixWord ++ tailWord_1639691) baseStart_1639691 baseEnd_1639691 := by
    simpa [prefixWord, tailWord_1639691, baseEnd_1639691] using wordTrace_append hprefix tailTrace_1639691
  have hstable : (prefixWord ++ tailWord_1639691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639691).length < 2 ^ (prefixWord ++ tailWord_1639691).sum := by decide
  have hdescent : baseEnd_1639691 < baseStart_1639691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639710 : List Nat := [4, 3, 2, 1, 3, 1, 2, 6]
def baseStart_1639710 : Nat := 118140960795 + 1639710 * 2 ^ 59
def prefixEnd_1639710 : Nat := 4983230072969 + 3 ^ 40 * 1639710 * 2
def baseEnd_1639710 : Nat := 62367360295102582280305

theorem tailTrace_1639710 : CollatzResearch.WordTrace tailWord_1639710 prefixEnd_1639710 62367360295102582280305 := by
  unfold tailWord_1639710
  simp only [CollatzResearch.WordTrace]
  refine ⟨7475642111202273127246573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39870091259745456678648389 7475642111202273127246573)
  ·
    refine ⟨2803365791700852422717465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7475642111202273127246573 2803365791700852422717465)
    ·
      refine ⟨2102524343775639317038099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2803365791700852422717465 2102524343775639317038099)
      ·
        refine ⟨3153786515663458975557149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2102524343775639317038099 3153786515663458975557149)
        ·
          refine ⟨1182669943373797115833931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3153786515663458975557149 1182669943373797115833931)
          ·
            refine ⟨1774004915060695673750897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1182669943373797115833931 1774004915060695673750897)
            ·
              refine ⟨1330503686295521755313173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1774004915060695673750897 1330503686295521755313173)
              ·
                refine ⟨62367360295102582280305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1330503686295521755313173 62367360295102582280305)
                ·
                  rfl

theorem cell22_1639710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_1639710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639710 prefixEnd_1639710 := by exact prefixLift 1639710
  have htrace : WordTrace (prefixWord ++ tailWord_1639710) baseStart_1639710 baseEnd_1639710 := by
    simpa [prefixWord, tailWord_1639710, baseEnd_1639710] using wordTrace_append hprefix tailTrace_1639710
  have hstable : (prefixWord ++ tailWord_1639710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639710).length < 2 ^ (prefixWord ++ tailWord_1639710).sum := by decide
  have hdescent : baseEnd_1639710 < baseStart_1639710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639725 : List Nat := [1, 5, 3, 1, 1, 1, 3, 3, 1, 3]
def baseStart_1639725 : Nat := 118140960795 + 1639725 * 2 ^ 59
def prefixEnd_1639725 : Nat := 4983230072969 + 3 ^ 40 * 1639725 * 2
def baseEnd_1639725 : Nat := 561311377462468201397699

theorem tailTrace_1639725 : CollatzResearch.WordTrace tailWord_1639725 prefixEnd_1639725 561311377462468201397699 := by
  unfold tailWord_1639725
  simp only [CollatzResearch.WordTrace]
  refine ⟨59805683984563842579768629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39870455989709228386512419 59805683984563842579768629)
  ·
    refine ⟨5606782873552860241853309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59805683984563842579768629 5606782873552860241853309)
    ·
      refine ⟨2102543577582322590694991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5606782873552860241853309 2102543577582322590694991)
      ·
        refine ⟨3153815366373483886042487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2102543577582322590694991 3153815366373483886042487)
        ·
          refine ⟨4730723049560225829063731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3153815366373483886042487 4730723049560225829063731)
          ·
            refine ⟨7096084574340338743595597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4730723049560225829063731 7096084574340338743595597)
            ·
              refine ⟨2661031715377627028848349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7096084574340338743595597 2661031715377627028848349)
              ·
                refine ⟨997886893266610135818131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2661031715377627028848349 997886893266610135818131)
                ·
                  refine ⟨1496830339899915203727197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997886893266610135818131 1496830339899915203727197)
                  ·
                    refine ⟨561311377462468201397699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1496830339899915203727197 561311377462468201397699)
                    ·
                      rfl

theorem cell22_1639725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_1639725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639725 prefixEnd_1639725 := by exact prefixLift 1639725
  have htrace : WordTrace (prefixWord ++ tailWord_1639725) baseStart_1639725 baseEnd_1639725 := by
    simpa [prefixWord, tailWord_1639725, baseEnd_1639725] using wordTrace_append hprefix tailTrace_1639725
  have hstable : (prefixWord ++ tailWord_1639725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639725).length < 2 ^ (prefixWord ++ tailWord_1639725).sum := by decide
  have hdescent : baseEnd_1639725 < baseStart_1639725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639749 : List Nat := [1, 3, 1, 1, 1, 2, 1, 8, 4]
def baseStart_1639749 : Nat := 118140960795 + 1639749 * 2 ^ 59
def prefixEnd_1639749 : Nat := 4983230072969 + 3 ^ 40 * 1639749 * 2
def baseEnd_1639749 : Nat := 187106531050980046265875

theorem tailTrace_1639749 : CollatzResearch.WordTrace tailWord_1639749 prefixEnd_1639749 187106531050980046265875 := by
  unfold tailWord_1639749
  simp only [CollatzResearch.WordTrace]
  refine ⟨59806559336476894678642301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39871039557651263119094867 59806559336476894678642301)
  ·
    refine ⟨22427459751178835504490863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59806559336476894678642301 22427459751178835504490863)
    ·
      refine ⟨33641189626768253256736295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22427459751178835504490863 33641189626768253256736295)
      ·
        refine ⟨50461784440152379885104443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33641189626768253256736295 50461784440152379885104443)
        ·
          refine ⟨75692676660228569827656665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50461784440152379885104443 75692676660228569827656665)
          ·
            refine ⟨56769507495171427370742499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75692676660228569827656665 56769507495171427370742499)
            ·
              refine ⟨85154261242757141056113749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56769507495171427370742499 85154261242757141056113749)
              ·
                refine ⟨997901498938560246751333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 85154261242757141056113749 997901498938560246751333)
                ·
                  refine ⟨187106531050980046265875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 997901498938560246751333 187106531050980046265875)
                  ·
                    rfl

theorem cell22_1639749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 4].length) (baseStart_1639749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639749 prefixEnd_1639749 := by exact prefixLift 1639749
  have htrace : WordTrace (prefixWord ++ tailWord_1639749) baseStart_1639749 baseEnd_1639749 := by
    simpa [prefixWord, tailWord_1639749, baseEnd_1639749] using wordTrace_append hprefix tailTrace_1639749
  have hstable : (prefixWord ++ tailWord_1639749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639749).length < 2 ^ (prefixWord ++ tailWord_1639749).sum := by decide
  have hdescent : baseEnd_1639749 < baseStart_1639749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639764 : List Nat := [2, 4, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_1639764 : Nat := 118140960795 + 1639764 * 2 ^ 59
def prefixEnd_1639764 : Nat := 4983230072969 + 3 ^ 40 * 1639764 * 2
def baseEnd_1639764 : Nat := 561324727959485099672579

theorem tailTrace_1639764 : CollatzResearch.WordTrace tailWord_1639764 prefixEnd_1639764 561324727959485099672579 := by
  unfold tailWord_1639764
  simp only [CollatzResearch.WordTrace]
  refine ⟨29903553215711276120219173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39871404287615034826958897 29903553215711276120219173)
  ·
    refine ⟨5606916227945864272541095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29903553215711276120219173 5606916227945864272541095)
    ·
      refine ⟨8410374341918796408811643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5606916227945864272541095 8410374341918796408811643)
      ·
        refine ⟨12615561512878194613217465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8410374341918796408811643 12615561512878194613217465)
        ·
          refine ⟨9461671134658645959913099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12615561512878194613217465 9461671134658645959913099)
          ·
            refine ⟨14192506701987968939869649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9461671134658645959913099 14192506701987968939869649)
            ·
              refine ⟨10644380026490976704902237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14192506701987968939869649 10644380026490976704902237)
              ·
                refine ⟨3991642509934116264338339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10644380026490976704902237 3991642509934116264338339)
                ·
                  refine ⟨5987463764901174396507509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3991642509934116264338339 5987463764901174396507509)
                  ·
                    refine ⟨561324727959485099672579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5987463764901174396507509 561324727959485099672579)
                    ·
                      rfl

theorem cell22_1639764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_1639764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639764 prefixEnd_1639764 := by exact prefixLift 1639764
  have htrace : WordTrace (prefixWord ++ tailWord_1639764) baseStart_1639764 baseEnd_1639764 := by
    simpa [prefixWord, tailWord_1639764, baseEnd_1639764] using wordTrace_append hprefix tailTrace_1639764
  have hstable : (prefixWord ++ tailWord_1639764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639764).length < 2 ^ (prefixWord ++ tailWord_1639764).sum := by decide
  have hdescent : baseEnd_1639764 < baseStart_1639764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639779 : List Nat := [1, 1, 1, 5, 2, 2, 1, 3, 2, 4]
def baseStart_1639779 : Nat := 118140960795 + 1639779 * 2 ^ 59
def prefixEnd_1639779 : Nat := 4983230072969 + 3 ^ 40 * 1639779 * 2
def baseEnd_1639779 : Nat := 561329862766030060547533

theorem tailTrace_1639779 : CollatzResearch.WordTrace tailWord_1639779 prefixEnd_1639779 561329862766030060547533 := by
  unfold tailWord_1639779
  simp only [CollatzResearch.WordTrace]
  refine ⟨59807653526368209802234391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39871769017578806534822927 59807653526368209802234391)
  ·
    refine ⟨89711480289552314703351587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59807653526368209802234391 89711480289552314703351587)
    ·
      refine ⟨134567220434328472055027381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89711480289552314703351587 134567220434328472055027381)
      ·
        refine ⟨12615676915718294255158817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134567220434328472055027381 12615676915718294255158817)
        ·
          refine ⟨9461757686788720691369113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12615676915718294255158817 9461757686788720691369113)
          ·
            refine ⟨7096318265091540518526835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9461757686788720691369113 7096318265091540518526835)
            ·
              refine ⟨10644477397637310777790253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7096318265091540518526835 10644477397637310777790253)
              ·
                refine ⟨3991679024113991541671345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10644477397637310777790253 3991679024113991541671345)
                ·
                  refine ⟨2993759268085493656253509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3991679024113991541671345 2993759268085493656253509)
                  ·
                    refine ⟨561329862766030060547533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2993759268085493656253509 561329862766030060547533)
                    ·
                      rfl

theorem cell22_1639779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 4].length) (baseStart_1639779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639779 prefixEnd_1639779 := by exact prefixLift 1639779
  have htrace : WordTrace (prefixWord ++ tailWord_1639779) baseStart_1639779 baseEnd_1639779 := by
    simpa [prefixWord, tailWord_1639779, baseEnd_1639779] using wordTrace_append hprefix tailTrace_1639779
  have hstable : (prefixWord ++ tailWord_1639779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639779).length < 2 ^ (prefixWord ++ tailWord_1639779).sum := by decide
  have hdescent : baseEnd_1639779 < baseStart_1639779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639843 : List Nat := [1, 1, 1, 4, 1, 3, 4, 3, 1, 3]
def baseStart_1639843 : Nat := 118140960795 + 1639843 * 2 ^ 59
def prefixEnd_1639843 : Nat := 4983230072969 + 3 ^ 40 * 1639843 * 2
def baseEnd_1639843 : Nat := 561351771273955226947337

theorem tailTrace_1639843 : CollatzResearch.WordTrace tailWord_1639843 prefixEnd_1639843 561351771273955226947337 := by
  unfold tailWord_1639843
  simp only [CollatzResearch.WordTrace]
  refine ⟨59809987798136348732564183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39873325198757565821709455 59809987798136348732564183)
  ·
    refine ⟨89714981697204523098846275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59809987798136348732564183 89714981697204523098846275)
    ·
      refine ⟨134572472545806784648269413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89714981697204523098846275 134572472545806784648269413)
      ·
        refine ⟨25232338602338772121550515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134572472545806784648269413 25232338602338772121550515)
        ·
          refine ⟨37848507903508158182325773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25232338602338772121550515 37848507903508158182325773)
          ·
            refine ⟨14193190463815559318372165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37848507903508158182325773 14193190463815559318372165)
            ·
              refine ⟨2661223211965417372194781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14193190463815559318372165 2661223211965417372194781)
              ·
                refine ⟨997958704487031514573043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2661223211965417372194781 997958704487031514573043)
                ·
                  refine ⟨1496938056730547271859565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997958704487031514573043 1496938056730547271859565)
                  ·
                    refine ⟨561351771273955226947337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1496938056730547271859565 561351771273955226947337)
                    ·
                      rfl

theorem cell22_1639843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 1, 3].length) (baseStart_1639843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639843 prefixEnd_1639843 := by exact prefixLift 1639843
  have htrace : WordTrace (prefixWord ++ tailWord_1639843) baseStart_1639843 baseEnd_1639843 := by
    simpa [prefixWord, tailWord_1639843, baseEnd_1639843] using wordTrace_append hprefix tailTrace_1639843
  have hstable : (prefixWord ++ tailWord_1639843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639843).length < 2 ^ (prefixWord ++ tailWord_1639843).sum := by decide
  have hdescent : baseEnd_1639843 < baseStart_1639843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639886 : List Nat := [4, 1, 1, 1, 2, 1, 3, 4, 1, 4]
def baseStart_1639886 : Nat := 118140960795 + 1639886 * 2 ^ 59
def prefixEnd_1639886 : Nat := 4983230072969 + 3 ^ 40 * 1639886 * 2
def baseEnd_1639886 : Nat := 561366491052717448122205

theorem tailTrace_1639886 : CollatzResearch.WordTrace tailWord_1639886 prefixEnd_1639886 561366491052717448122205 := by
  unfold tailWord_1639886
  simp only [CollatzResearch.WordTrace]
  refine ⟨7476444517122570884547439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39874370757987044717586341 7476444517122570884547439)
  ·
    refine ⟨11214666775683856326821159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7476444517122570884547439 11214666775683856326821159)
    ·
      refine ⟨16822000163525784490231739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11214666775683856326821159 16822000163525784490231739)
      ·
        refine ⟨25233000245288676735347609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16822000163525784490231739 25233000245288676735347609)
        ·
          refine ⟨18924750183966507551510707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25233000245288676735347609 18924750183966507551510707)
          ·
            refine ⟨28387125275949761327266061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18924750183966507551510707 28387125275949761327266061)
            ·
              refine ⟨10645171978481160497724773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28387125275949761327266061 10645171978481160497724773)
              ·
                refine ⟨1995969745965217593323395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10645171978481160497724773 1995969745965217593323395)
                ·
                  refine ⟨2993954618947826389985093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1995969745965217593323395 2993954618947826389985093)
                  ·
                    refine ⟨561366491052717448122205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2993954618947826389985093 561366491052717448122205)
                    ·
                      rfl

theorem cell22_1639886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_1639886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639886 prefixEnd_1639886 := by exact prefixLift 1639886
  have htrace : WordTrace (prefixWord ++ tailWord_1639886) baseStart_1639886 baseEnd_1639886 := by
    simpa [prefixWord, tailWord_1639886, baseEnd_1639886] using wordTrace_append hprefix tailTrace_1639886
  have hstable : (prefixWord ++ tailWord_1639886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639886).length < 2 ^ (prefixWord ++ tailWord_1639886).sum := by decide
  have hdescent : baseEnd_1639886 < baseStart_1639886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639933 : List Nat := [1, 4, 1, 1, 1, 5, 1, 3, 2, 3]
def baseStart_1639933 : Nat := 118140960795 + 1639933 * 2 ^ 59
def prefixEnd_1639933 : Nat := 4983230072969 + 3 ^ 40 * 1639933 * 2
def baseEnd_1639933 : Nat := 561382580113224992197061

theorem tailTrace_1639933 : CollatzResearch.WordTrace tailWord_1639933 prefixEnd_1639933 561382580113224992197061 := by
  unfold tailWord_1639933
  simp only [CollatzResearch.WordTrace]
  refine ⟨59813270367810294103340453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39875513578540196068893635 59813270367810294103340453)
  ·
    refine ⟨11214988193964430144376335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59813270367810294103340453 11214988193964430144376335)
    ·
      refine ⟨16822482290946645216564503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11214988193964430144376335 16822482290946645216564503)
      ·
        refine ⟨25233723436419967824846755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16822482290946645216564503 25233723436419967824846755)
        ·
          refine ⟨37850585154629951737270133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25233723436419967824846755 37850585154629951737270133)
          ·
            refine ⟨3548492358246557975369075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37850585154629951737270133 3548492358246557975369075)
            ·
              refine ⟨5322738537369836963053613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3548492358246557975369075 5322738537369836963053613)
              ·
                refine ⟨1996026951513688861145105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5322738537369836963053613 1996026951513688861145105)
                ·
                  refine ⟨1497020213635266645858829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1996026951513688861145105 1497020213635266645858829)
                  ·
                    refine ⟨561382580113224992197061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1497020213635266645858829 561382580113224992197061)
                    ·
                      rfl

theorem cell22_1639933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_1639933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639933 prefixEnd_1639933 := by exact prefixLift 1639933
  have htrace : WordTrace (prefixWord ++ tailWord_1639933) baseStart_1639933 baseEnd_1639933 := by
    simpa [prefixWord, tailWord_1639933, baseEnd_1639933] using wordTrace_append hprefix tailTrace_1639933
  have hstable : (prefixWord ++ tailWord_1639933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639933).length < 2 ^ (prefixWord ++ tailWord_1639933).sum := by decide
  have hdescent : baseEnd_1639933 < baseStart_1639933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639944 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 2, 7]
def baseStart_1639944 : Nat := 118140960795 + 1639944 * 2 ^ 59
def prefixEnd_1639944 : Nat := 4983230072969 + 3 ^ 40 * 1639944 * 2
def baseEnd_1639944 : Nat := 561386345638024630172027

theorem tailTrace_1639944 : CollatzResearch.WordTrace tailWord_1639944 prefixEnd_1639944 561386345638024630172027 := by
  unfold tailWord_1639944
  simp only [CollatzResearch.WordTrace]
  refine ⟨29906835785385221490995443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39875781047180295321327257 29906835785385221490995443)
  ·
    refine ⟨44860253678077832236493165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29906835785385221490995443 44860253678077832236493165)
    ·
      refine ⟨16822595129279187088684937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44860253678077832236493165 16822595129279187088684937)
      ·
        refine ⟨12616946346959390316513703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16822595129279187088684937 12616946346959390316513703)
        ·
          refine ⟨18925419520439085474770555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12616946346959390316513703 18925419520439085474770555)
          ·
            refine ⟨28388129280658628212155833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18925419520439085474770555 28388129280658628212155833)
            ·
              refine ⟨21291096960493971159116875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28388129280658628212155833 21291096960493971159116875)
              ·
                refine ⟨31936645440740956738675313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21291096960493971159116875 31936645440740956738675313)
                ·
                  refine ⟨23952484080555717554006485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31936645440740956738675313 23952484080555717554006485)
                  ·
                    refine ⟨561386345638024630172027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23952484080555717554006485 561386345638024630172027)
                    ·
                      rfl

theorem cell22_1639944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_1639944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639944 prefixEnd_1639944 := by exact prefixLift 1639944
  have htrace : WordTrace (prefixWord ++ tailWord_1639944) baseStart_1639944 baseEnd_1639944 := by
    simpa [prefixWord, tailWord_1639944, baseEnd_1639944] using wordTrace_append hprefix tailTrace_1639944
  have hstable : (prefixWord ++ tailWord_1639944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639944).length < 2 ^ (prefixWord ++ tailWord_1639944).sum := by decide
  have hdescent : baseEnd_1639944 < baseStart_1639944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639948 : List Nat := [2, 2, 1, 2, 5, 1, 2, 1, 2, 4]
def baseStart_1639948 : Nat := 118140960795 + 1639948 * 2 ^ 59
def prefixEnd_1639948 : Nat := 4983230072969 + 3 ^ 40 * 1639948 * 2
def baseEnd_1639948 : Nat := 561387714919769953072015

theorem tailTrace_1639948 : CollatzResearch.WordTrace tailWord_1639948 prefixEnd_1639948 561387714919769953072015 := by
  unfold tailWord_1639948
  simp only [CollatzResearch.WordTrace]
  refine ⟨29906908731377975832568249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39875878308503967776757665 29906908731377975832568249)
  ·
    refine ⟨22430181548533481874426187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29906908731377975832568249 22430181548533481874426187)
    ·
      refine ⟨33645272322800222811639281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22430181548533481874426187 33645272322800222811639281)
      ·
        refine ⟨25233954242100167108729461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33645272322800222811639281 25233954242100167108729461)
        ·
          refine ⟨2365683210196890666443387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25233954242100167108729461 2365683210196890666443387)
          ·
            refine ⟨3548524815295335999665081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2365683210196890666443387 3548524815295335999665081)
            ·
              refine ⟨2661393611471501999748811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3548524815295335999665081 2661393611471501999748811)
              ·
                refine ⟨3992090417207252999623217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2661393611471501999748811 3992090417207252999623217)
                ·
                  refine ⟨2994067812905439749717413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3992090417207252999623217 2994067812905439749717413)
                  ·
                    refine ⟨561387714919769953072015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2994067812905439749717413 561387714919769953072015)
                    ·
                      rfl

theorem cell22_1639948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_1639948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639948 prefixEnd_1639948 := by exact prefixLift 1639948
  have htrace : WordTrace (prefixWord ++ tailWord_1639948) baseStart_1639948 baseEnd_1639948 := by
    simpa [prefixWord, tailWord_1639948, baseEnd_1639948] using wordTrace_append hprefix tailTrace_1639948
  have hstable : (prefixWord ++ tailWord_1639948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639948).length < 2 ^ (prefixWord ++ tailWord_1639948).sum := by decide
  have hdescent : baseEnd_1639948 < baseStart_1639948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639978 : List Nat := [3, 1, 4, 1, 1, 1, 2, 3, 3, 3]
def baseStart_1639978 : Nat := 118140960795 + 1639978 * 2 ^ 59
def prefixEnd_1639978 : Nat := 4983230072969 + 3 ^ 40 * 1639978 * 2
def baseEnd_1639978 : Nat := 561397984532859874821923

theorem tailTrace_1639978 : CollatzResearch.WordTrace tailWord_1639978 prefixEnd_1639978 561397984532859874821923 := by
  unfold tailWord_1639978
  simp only [CollatzResearch.WordTrace]
  refine ⟨14953727913161816697182147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39876607768431511192485725 14953727913161816697182147)
  ·
    refine ⟨22430591869742725045773221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14953727913161816697182147 22430591869742725045773221)
    ·
      refine ⟨4205735975576760946082479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22430591869742725045773221 4205735975576760946082479)
      ·
        refine ⟨6308603963365141419123719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4205735975576760946082479 6308603963365141419123719)
        ·
          refine ⟨9462905945047712128685579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6308603963365141419123719 9462905945047712128685579)
          ·
            refine ⟨14194358917571568193028369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9462905945047712128685579 14194358917571568193028369)
            ·
              refine ⟨10645769188178676144771277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14194358917571568193028369 10645769188178676144771277)
              ·
                refine ⟨3992163445567003554289229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10645769188178676144771277 3992163445567003554289229)
                ·
                  refine ⟨1497061292087626332858461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3992163445567003554289229 1497061292087626332858461)
                  ·
                    refine ⟨561397984532859874821923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1497061292087626332858461 561397984532859874821923)
                    ·
                      rfl

theorem cell22_1639978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_1639978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639978 prefixEnd_1639978 := by exact prefixLift 1639978
  have htrace : WordTrace (prefixWord ++ tailWord_1639978) baseStart_1639978 baseEnd_1639978 := by
    simpa [prefixWord, tailWord_1639978, baseEnd_1639978] using wordTrace_append hprefix tailTrace_1639978
  have hstable : (prefixWord ++ tailWord_1639978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639978).length < 2 ^ (prefixWord ++ tailWord_1639978).sum := by decide
  have hdescent : baseEnd_1639978 < baseStart_1639978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639991 : List Nat := [1, 1, 3, 1, 2, 4, 2, 3, 5]
def baseStart_1639991 : Nat := 118140960795 + 1639991 * 2 ^ 59
def prefixEnd_1639991 : Nat := 4983230072969 + 3 ^ 40 * 1639991 * 2
def baseEnd_1639991 : Nat := 187134144899510724748961

theorem tailTrace_1639991 : CollatzResearch.WordTrace tailWord_1639991 prefixEnd_1639991 187134144899510724748961 := by
  unfold tailWord_1639991
  simp only [CollatzResearch.WordTrace]
  refine ⟨59815385801600170008951827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39876923867733446672634551 59815385801600170008951827)
  ·
    refine ⟨89723078702400255013427741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59815385801600170008951827 89723078702400255013427741)
    ·
      refine ⟨33646154513400095630035403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89723078702400255013427741 33646154513400095630035403)
      ·
        refine ⟨50469231770100143445053105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33646154513400095630035403 50469231770100143445053105)
        ·
          refine ⟨37851923827575107583789829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50469231770100143445053105 37851923827575107583789829)
          ·
            refine ⟨7097235717670332671960593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37851923827575107583789829 7097235717670332671960593)
            ·
              refine ⟨5322926788252749503970445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7097235717670332671960593 5322926788252749503970445)
              ·
                refine ⟨1996097545594781063988917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5322926788252749503970445 1996097545594781063988917)
                ·
                  refine ⟨187134144899510724748961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1996097545594781063988917 187134144899510724748961)
                  ·
                    rfl

theorem cell22_1639991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 5].length) (baseStart_1639991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1639991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1639991 prefixEnd_1639991 := by exact prefixLift 1639991
  have htrace : WordTrace (prefixWord ++ tailWord_1639991) baseStart_1639991 baseEnd_1639991 := by
    simpa [prefixWord, tailWord_1639991, baseEnd_1639991] using wordTrace_append hprefix tailTrace_1639991
  have hstable : (prefixWord ++ tailWord_1639991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639991).length < 2 ^ (prefixWord ++ tailWord_1639991).sum := by decide
  have hdescent : baseEnd_1639991 < baseStart_1639991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640036 : List Nat := [2, 3, 1, 1, 2, 3, 1, 3, 6]
def baseStart_1640036 : Nat := 118140960795 + 1640036 * 2 ^ 59
def prefixEnd_1640036 : Nat := 4983230072969 + 3 ^ 40 * 1640036 * 2
def baseEnd_1640036 : Nat := 187139279706055685623915

theorem tailTrace_1640036 : CollatzResearch.WordTrace tailWord_1640036 prefixEnd_1640036 187139279706055685623915 := by
  unfold tailWord_1640036
  simp only [CollatzResearch.WordTrace]
  refine ⟨29908513543218571347169981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39878018057624761796226641 29908513543218571347169981)
  ·
    refine ⟨11215692578706964255188743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29908513543218571347169981 11215692578706964255188743)
    ·
      refine ⟨16823538868060446382783115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11215692578706964255188743 16823538868060446382783115)
      ·
        refine ⟨25235308302090669574174673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16823538868060446382783115 25235308302090669574174673)
        ·
          refine ⟨18926481226568002180631005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25235308302090669574174673 18926481226568002180631005)
          ·
            refine ⟨7097430459963000817736627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18926481226568002180631005 7097430459963000817736627)
            ·
              refine ⟨10646145689944501226604941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7097430459963000817736627 10646145689944501226604941)
              ·
                refine ⟨3992304633729187959976853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10646145689944501226604941 3992304633729187959976853)
                ·
                  refine ⟨187139279706055685623915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3992304633729187959976853 187139279706055685623915)
                  ·
                    rfl

theorem cell22_1640036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_1640036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640036 prefixEnd_1640036 := by exact prefixLift 1640036
  have htrace : WordTrace (prefixWord ++ tailWord_1640036) baseStart_1640036 baseEnd_1640036 := by
    simpa [prefixWord, tailWord_1640036, baseEnd_1640036] using wordTrace_append hprefix tailTrace_1640036
  have hstable : (prefixWord ++ tailWord_1640036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640036).length < 2 ^ (prefixWord ++ tailWord_1640036).sum := by decide
  have hdescent : baseEnd_1640036 < baseStart_1640036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640053 : List Nat := [1, 3, 4, 2, 1, 1, 2, 2, 6]
def baseStart_1640053 : Nat := 118140960795 + 1640053 * 2 ^ 59
def prefixEnd_1640053 : Nat := 4983230072969 + 3 ^ 40 * 1640053 * 2
def baseEnd_1640053 : Nat := 187141219521861559732231

theorem tailTrace_1640053 : CollatzResearch.WordTrace tailWord_1640053 prefixEnd_1640053 187141219521861559732231 := by
  unfold tailWord_1640053
  simp only [CollatzResearch.WordTrace]
  refine ⟨59817647127375554597708813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39878431418250369731805875 59817647127375554597708813)
  ·
    refine ⟨22431617672765832974140805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59817647127375554597708813 22431617672765832974140805)
    ·
      refine ⟨4205928313643593682651401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22431617672765832974140805 4205928313643593682651401)
      ·
        refine ⟨3154446235232695261988551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4205928313643593682651401 3154446235232695261988551)
        ·
          refine ⟨4731669352849042892982827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3154446235232695261988551 4731669352849042892982827)
          ·
            refine ⟨7097504029273564339474241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4731669352849042892982827 7097504029273564339474241)
            ·
              refine ⟨5323128021955173254605681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7097504029273564339474241 5323128021955173254605681)
              ·
                refine ⟨3992346016466379940954261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5323128021955173254605681 3992346016466379940954261)
                ·
                  refine ⟨187141219521861559732231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3992346016466379940954261 187141219521861559732231)
                  ·
                    rfl

theorem cell22_1640053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_1640053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640053 prefixEnd_1640053 := by exact prefixLift 1640053
  have htrace : WordTrace (prefixWord ++ tailWord_1640053) baseStart_1640053 baseEnd_1640053 := by
    simpa [prefixWord, tailWord_1640053, baseEnd_1640053] using wordTrace_append hprefix tailTrace_1640053
  have hstable : (prefixWord ++ tailWord_1640053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640053).length < 2 ^ (prefixWord ++ tailWord_1640053).sum := by decide
  have hdescent : baseEnd_1640053 < baseStart_1640053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640171 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 8]
def baseStart_1640171 : Nat := 118140960795 + 1640171 * 2 ^ 59
def prefixEnd_1640171 : Nat := 4983230072969 + 3 ^ 40 * 1640171 * 2
def baseEnd_1640171 : Nat := 187154684125690568248777

theorem tailTrace_1640171 : CollatzResearch.WordTrace tailWord_1640171 prefixEnd_1640171 187154684125690568248777 := by
  unfold tailWord_1640171
  simp only [CollatzResearch.WordTrace]
  refine ⟨59821950940948060750504367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39881300627298707167002911 59821950940948060750504367)
  ·
    refine ⟨89732926411422091125756551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59821950940948060750504367 89732926411422091125756551)
    ·
      refine ⟨134599389617133136688634827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89732926411422091125756551 134599389617133136688634827)
      ·
        refine ⟨201899084425699705032952241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134599389617133136688634827 201899084425699705032952241)
        ·
          refine ⟨151424313319274778774714181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201899084425699705032952241 151424313319274778774714181)
          ·
            refine ⟨28392058747364021020258909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151424313319274778774714181 28392058747364021020258909)
            ·
              refine ⟨10647022030261507882597091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28392058747364021020258909 10647022030261507882597091)
              ·
                refine ⟨15970533045392261823895637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10647022030261507882597091 15970533045392261823895637)
                ·
                  refine ⟨187154684125690568248777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15970533045392261823895637 187154684125690568248777)
                  ·
                    rfl

theorem cell22_1640171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 8].length) (baseStart_1640171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640171 prefixEnd_1640171 := by exact prefixLift 1640171
  have htrace : WordTrace (prefixWord ++ tailWord_1640171) baseStart_1640171 baseEnd_1640171 := by
    simpa [prefixWord, tailWord_1640171, baseEnd_1640171] using wordTrace_append hprefix tailTrace_1640171
  have hstable : (prefixWord ++ tailWord_1640171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640171).length < 2 ^ (prefixWord ++ tailWord_1640171).sum := by decide
  have hdescent : baseEnd_1640171 < baseStart_1640171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640218 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 1, 6]
def baseStart_1640218 : Nat := 118140960795 + 1640218 * 2 ^ 59
def prefixEnd_1640218 : Nat := 4983230072969 + 3 ^ 40 * 1640218 * 2
def baseEnd_1640218 : Nat := 561480141437579248821187

theorem tailTrace_1640218 : CollatzResearch.WordTrace tailWord_1640218 prefixEnd_1640218 561480141437579248821187 := by
  unfold tailWord_1640218
  simp only [CollatzResearch.WordTrace]
  refine ⟨14955916292944446944366327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39882443447851858518310205 14955916292944446944366327)
  ·
    refine ⟨22433874439416670416549491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14955916292944446944366327 22433874439416670416549491)
    ·
      refine ⟨33650811659125005624824237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22433874439416670416549491 33650811659125005624824237)
      ·
        refine ⟨12619054372171877109309089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33650811659125005624824237 12619054372171877109309089)
        ·
          refine ⟨9464290779128907831981817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12619054372171877109309089 9464290779128907831981817)
          ·
            refine ⟨7098218084346680873986363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9464290779128907831981817 7098218084346680873986363)
            ·
              refine ⟨10647327126520021310979545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7098218084346680873986363 10647327126520021310979545)
              ·
                refine ⟨7985495344890015983234659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10647327126520021310979545 7985495344890015983234659)
                ·
                  refine ⟨11978243017335023974851989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7985495344890015983234659 11978243017335023974851989)
                  ·
                    refine ⟨561480141437579248821187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11978243017335023974851989 561480141437579248821187)
                    ·
                      rfl

theorem cell22_1640218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_1640218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640218 prefixEnd_1640218 := by exact prefixLift 1640218
  have htrace : WordTrace (prefixWord ++ tailWord_1640218) baseStart_1640218 baseEnd_1640218 := by
    simpa [prefixWord, tailWord_1640218, baseEnd_1640218] using wordTrace_append hprefix tailTrace_1640218
  have hstable : (prefixWord ++ tailWord_1640218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640218).length < 2 ^ (prefixWord ++ tailWord_1640218).sum := by decide
  have hdescent : baseEnd_1640218 < baseStart_1640218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640293 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 4, 5]
def baseStart_1640293 : Nat := 118140960795 + 1640293 * 2 ^ 59
def prefixEnd_1640293 : Nat := 4983230072969 + 3 ^ 40 * 1640293 * 2
def baseEnd_1640293 : Nat := 561505815470304053195957

theorem tailTrace_1640293 : CollatzResearch.WordTrace tailWord_1640293 prefixEnd_1640293 561505815470304053195957 := by
  unfold tailWord_1640293
  simp only [CollatzResearch.WordTrace]
  refine ⟨59826400646506075586445533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39884267097670717057630355 59826400646506075586445533)
  ·
    refine ⟨22434900242439778344917075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59826400646506075586445533 22434900242439778344917075)
    ·
      refine ⟨33652350363659667517375613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22434900242439778344917075 33652350363659667517375613)
      ·
        refine ⟨12619631386372375319015855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33652350363659667517375613 12619631386372375319015855)
        ·
          refine ⟨18929447079558562978523783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12619631386372375319015855 18929447079558562978523783)
          ·
            refine ⟨28394170619337844467785675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18929447079558562978523783 28394170619337844467785675)
            ·
              refine ⟨42591255929006766701678513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28394170619337844467785675 42591255929006766701678513)
              ·
                refine ⟨31943441946755075026258885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42591255929006766701678513 31943441946755075026258885)
                ·
                  refine ⟨5989395365016576567423541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31943441946755075026258885 5989395365016576567423541)
                  ·
                    refine ⟨561505815470304053195957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5989395365016576567423541 561505815470304053195957)
                    ·
                      rfl

theorem cell22_1640293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_1640293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640293 prefixEnd_1640293 := by exact prefixLift 1640293
  have htrace : WordTrace (prefixWord ++ tailWord_1640293) baseStart_1640293 baseEnd_1640293 := by
    simpa [prefixWord, tailWord_1640293, baseEnd_1640293] using wordTrace_append hprefix tailTrace_1640293
  have hstable : (prefixWord ++ tailWord_1640293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640293).length < 2 ^ (prefixWord ++ tailWord_1640293).sum := by decide
  have hdescent : baseEnd_1640293 < baseStart_1640293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640340 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 8]
def baseStart_1640340 : Nat := 118140960795 + 1640340 * 2 ^ 59
def prefixEnd_1640340 : Nat := 4983230072969 + 3 ^ 40 * 1640340 * 2
def baseEnd_1640340 : Nat := 187173968176937199090271

theorem tailTrace_1640340 : CollatzResearch.WordTrace tailWord_1640340 prefixEnd_1640340 187173968176937199090271 := by
  unfold tailWord_1640340
  simp only [CollatzResearch.WordTrace]
  refine ⟨29914057438667901306703237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39885409918223868408937649 29914057438667901306703237)
  ·
    refine ⟨5608885769750231495006857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29914057438667901306703237 5608885769750231495006857)
    ·
      refine ⟨4206664327312673621255143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5608885769750231495006857 4206664327312673621255143)
      ·
        refine ⟨6309996490969010431882715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4206664327312673621255143 6309996490969010431882715)
        ·
          refine ⟨9464994736453515647824073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6309996490969010431882715 9464994736453515647824073)
          ·
            refine ⟨7098746052340136735868055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9464994736453515647824073 7098746052340136735868055)
            ·
              refine ⟨10648119078510205103802083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7098746052340136735868055 10648119078510205103802083)
              ·
                refine ⟨15972178617765307655703125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10648119078510205103802083 15972178617765307655703125)
                ·
                  refine ⟨187173968176937199090271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15972178617765307655703125 187173968176937199090271)
                  ·
                    rfl

theorem cell22_1640340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_1640340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640340 prefixEnd_1640340 := by exact prefixLift 1640340
  have htrace : WordTrace (prefixWord ++ tailWord_1640340) baseStart_1640340 baseEnd_1640340 := by
    simpa [prefixWord, tailWord_1640340, baseEnd_1640340] using wordTrace_append hprefix tailTrace_1640340
  have hstable : (prefixWord ++ tailWord_1640340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640340).length < 2 ^ (prefixWord ++ tailWord_1640340).sum := by decide
  have hdescent : baseEnd_1640340 < baseStart_1640340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640355 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 4, 3]
def baseStart_1640355 : Nat := 118140960795 + 1640355 * 2 ^ 59
def prefixEnd_1640355 : Nat := 4983230072969 + 3 ^ 40 * 1640355 * 2
def baseEnd_1640355 : Nat := 561527039337356558145767

theorem tailTrace_1640355 : CollatzResearch.WordTrace tailWord_1640355 prefixEnd_1640355 561527039337356558145767 := by
  unfold tailWord_1640355
  simp only [CollatzResearch.WordTrace]
  refine ⟨59828661972281460175202519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39885774648187640116801679 59828661972281460175202519)
  ·
    refine ⟨89742992958422190262803779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59828661972281460175202519 89742992958422190262803779)
    ·
      refine ⟨134614489437633285394205669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89742992958422190262803779 134614489437633285394205669)
      ·
        refine ⟨25240216769556241011413563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134614489437633285394205669 25240216769556241011413563)
        ·
          refine ⟨37860325154334361517120345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25240216769556241011413563 37860325154334361517120345)
          ·
            refine ⟨28395243865750771137840259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37860325154334361517120345 28395243865750771137840259)
            ·
              refine ⟨42592865798626156706760389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28395243865750771137840259 42592865798626156706760389)
              ·
                refine ⟨7986162337242404382517573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42592865798626156706760389 7986162337242404382517573)
                ·
                  refine ⟨1497405438232950821722045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7986162337242404382517573 1497405438232950821722045)
                  ·
                    refine ⟨561527039337356558145767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1497405438232950821722045 561527039337356558145767)
                    ·
                      rfl

theorem cell22_1640355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 3].length) (baseStart_1640355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640355 prefixEnd_1640355 := by exact prefixLift 1640355
  have htrace : WordTrace (prefixWord ++ tailWord_1640355) baseStart_1640355 baseEnd_1640355 := by
    simpa [prefixWord, tailWord_1640355, baseEnd_1640355] using wordTrace_append hprefix tailTrace_1640355
  have hstable : (prefixWord ++ tailWord_1640355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640355).length < 2 ^ (prefixWord ++ tailWord_1640355).sum := by decide
  have hdescent : baseEnd_1640355 < baseStart_1640355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640359 : List Nat := [1, 1, 6, 1, 2, 1, 4, 1, 1, 4]
def baseStart_1640359 : Nat := 118140960795 + 1640359 * 2 ^ 59
def prefixEnd_1640359 : Nat := 4983230072969 + 3 ^ 40 * 1640359 * 2
def baseEnd_1640359 : Nat := 561528408619101881045755

theorem tailTrace_1640359 : CollatzResearch.WordTrace tailWord_1640359 prefixEnd_1640359 561528408619101881045755 := by
  unfold tailWord_1640359
  simp only [CollatzResearch.WordTrace]
  refine ⟨59828807864266968858348131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39885871909511312572232087 59828807864266968858348131)
  ·
    refine ⟨89743211796400453287522197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59828807864266968858348131 89743211796400453287522197)
    ·
      refine ⟨4206713052956271247852603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89743211796400453287522197 4206713052956271247852603)
      ·
        refine ⟨6310069579434406871778905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4206713052956271247852603 6310069579434406871778905)
        ·
          refine ⟨4732552184575805153834179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6310069579434406871778905 4732552184575805153834179)
          ·
            refine ⟨7098828276863707730751269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4732552184575805153834179 7098828276863707730751269)
            ·
              refine ⟨1331030301911945199515863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7098828276863707730751269 1331030301911945199515863)
              ·
                refine ⟨1996545452867917799273795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1331030301911945199515863 1996545452867917799273795)
                ·
                  refine ⟨2994818179301876698910693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1996545452867917799273795 2994818179301876698910693)
                  ·
                    refine ⟨561528408619101881045755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2994818179301876698910693 561528408619101881045755)
                    ·
                      rfl

theorem cell22_1640359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_1640359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640359 prefixEnd_1640359 := by exact prefixLift 1640359
  have htrace : WordTrace (prefixWord ++ tailWord_1640359) baseStart_1640359 baseEnd_1640359 := by
    simpa [prefixWord, tailWord_1640359, baseEnd_1640359] using wordTrace_append hprefix tailTrace_1640359
  have hstable : (prefixWord ++ tailWord_1640359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640359).length < 2 ^ (prefixWord ++ tailWord_1640359).sum := by decide
  have hdescent : baseEnd_1640359 < baseStart_1640359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640370 : List Nat := [3, 2, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_1640370 : Nat := 118140960795 + 1640370 * 2 ^ 59
def prefixEnd_1640370 : Nat := 4983230072969 + 3 ^ 40 * 1640370 * 2
def baseEnd_1640370 : Nat := 561532174143901519020721

theorem tailTrace_1640370 : CollatzResearch.WordTrace tailWord_1640370 prefixEnd_1640370 561532174143901519020721 := by
  unfold tailWord_1640370
  simp only [CollatzResearch.WordTrace]
  refine ⟨14957302266806779434249641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39886139378151411824665709 14957302266806779434249641)
  ·
    refine ⟨11217976700105084575687231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14957302266806779434249641 11217976700105084575687231)
    ·
      refine ⟨16826965050157626863530847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11217976700105084575687231 16826965050157626863530847)
      ·
        refine ⟨25240447575236440295296271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16826965050157626863530847 25240447575236440295296271)
        ·
          refine ⟨37860671362854660442944407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25240447575236440295296271 37860671362854660442944407)
          ·
            refine ⟨56791007044281990664416611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37860671362854660442944407 56791007044281990664416611)
            ·
              refine ⟨85186510566422985996624917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56791007044281990664416611 85186510566422985996624917)
              ·
                refine ⟨3993117682801077468591793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85186510566422985996624917 3993117682801077468591793)
                ·
                  refine ⟨2994838262100808101443845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3993117682801077468591793 2994838262100808101443845)
                  ·
                    refine ⟨561532174143901519020721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2994838262100808101443845 561532174143901519020721)
                    ·
                      rfl

theorem cell22_1640370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_1640370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640370 prefixEnd_1640370 := by exact prefixLift 1640370
  have htrace : WordTrace (prefixWord ++ tailWord_1640370) baseStart_1640370 baseEnd_1640370 := by
    simpa [prefixWord, tailWord_1640370, baseEnd_1640370] using wordTrace_append hprefix tailTrace_1640370
  have hstable : (prefixWord ++ tailWord_1640370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640370).length < 2 ^ (prefixWord ++ tailWord_1640370).sum := by decide
  have hdescent : baseEnd_1640370 < baseStart_1640370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640402 : List Nat := [3, 2, 2, 3, 2, 1, 1, 8]
def baseStart_1640402 : Nat := 118140960795 + 1640402 * 2 ^ 59
def prefixEnd_1640402 : Nat := 4983230072969 + 3 ^ 40 * 1640402 * 2
def baseEnd_1640402 : Nat := 62393680933096011357847

theorem tailTrace_1640402 : CollatzResearch.WordTrace tailWord_1640402 prefixEnd_1640402 62393680933096011357847 := by
  unfold tailWord_1640402
  simp only [CollatzResearch.WordTrace]
  refine ⟨14957594050777796800540865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39886917468740791468108973 14957594050777796800540865)
  ·
    refine ⟨11218195538083347600405649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14957594050777796800540865 11218195538083347600405649)
    ·
      refine ⟨8413646653562510700304237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11218195538083347600405649 8413646653562510700304237)
      ·
        refine ⟨3155117495085941512614089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8413646653562510700304237 3155117495085941512614089)
        ·
          refine ⟨2366338121314456134460567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3155117495085941512614089 2366338121314456134460567)
          ·
            refine ⟨3549507181971684201690851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2366338121314456134460567 3549507181971684201690851)
            ·
              refine ⟨5324260772957526302536277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3549507181971684201690851 5324260772957526302536277)
              ·
                refine ⟨62393680933096011357847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5324260772957526302536277 62393680933096011357847)
                ·
                  rfl

theorem cell22_1640402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 8].length) (baseStart_1640402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640402 prefixEnd_1640402 := by exact prefixLift 1640402
  have htrace : WordTrace (prefixWord ++ tailWord_1640402) baseStart_1640402 baseEnd_1640402 := by
    simpa [prefixWord, tailWord_1640402, baseEnd_1640402] using wordTrace_append hprefix tailTrace_1640402
  have hstable : (prefixWord ++ tailWord_1640402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640402).length < 2 ^ (prefixWord ++ tailWord_1640402).sum := by decide
  have hdescent : baseEnd_1640402 < baseStart_1640402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640445 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_1640445 : Nat := 118140960795 + 1640445 * 2 ^ 59
def prefixEnd_1640445 : Nat := 4983230072969 + 3 ^ 40 * 1640445 * 2
def baseEnd_1640445 : Nat := 561557848176626323395491

theorem tailTrace_1640445 : CollatzResearch.WordTrace tailWord_1640445 prefixEnd_1640445 561557848176626323395491 := by
  unfold tailWord_1640445
  simp only [CollatzResearch.WordTrace]
  refine ⟨59831944541955405545978789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39887963027970270363985859 59831944541955405545978789)
  ·
    refine ⟨11218489601616638539871023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59831944541955405545978789 11218489601616638539871023)
    ·
      refine ⟨16827734402424957809806535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11218489601616638539871023 16827734402424957809806535)
      ·
        refine ⟨25241601603637436714709803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16827734402424957809806535 25241601603637436714709803)
        ·
          refine ⟨37862402405456155072064705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25241601603637436714709803 37862402405456155072064705)
          ·
            refine ⟨28396801804092116304048529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37862402405456155072064705 28396801804092116304048529)
            ·
              refine ⟨21297601353069087228036397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28396801804092116304048529 21297601353069087228036397)
              ·
                refine ⟨7986600507400907710513649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21297601353069087228036397 7986600507400907710513649)
                ·
                  refine ⟨5989950380550680782885237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7986600507400907710513649 5989950380550680782885237)
                  ·
                    refine ⟨561557848176626323395491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5989950380550680782885237 561557848176626323395491)
                    ·
                      rfl

theorem cell22_1640445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_1640445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640445 prefixEnd_1640445 := by exact prefixLift 1640445
  have htrace : WordTrace (prefixWord ++ tailWord_1640445) baseStart_1640445 baseEnd_1640445 := by
    simpa [prefixWord, tailWord_1640445, baseEnd_1640445] using wordTrace_append hprefix tailTrace_1640445
  have hstable : (prefixWord ++ tailWord_1640445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640445).length < 2 ^ (prefixWord ++ tailWord_1640445).sum := by decide
  have hdescent : baseEnd_1640445 < baseStart_1640445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640541 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 4, 3]
def baseStart_1640541 : Nat := 118140960795 + 1640541 * 2 ^ 59
def prefixEnd_1640541 : Nat := 4983230072969 + 3 ^ 40 * 1640541 * 2
def baseEnd_1640541 : Nat := 561590710938514072995197

theorem tailTrace_1640541 : CollatzResearch.WordTrace tailWord_1640541 prefixEnd_1640541 561590710938514072995197 := by
  unfold tailWord_1640541
  simp only [CollatzResearch.WordTrace]
  refine ⟨59835445949607613941473477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39890297299738409294315651 59835445949607613941473477)
  ·
    refine ⟨11219146115551427614026277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59835445949607613941473477 11219146115551427614026277)
    ·
      refine ⟨2103589896665892677629927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11219146115551427614026277 2103589896665892677629927)
      ·
        refine ⟨3155384844998839016444891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2103589896665892677629927 3155384844998839016444891)
        ·
          refine ⟨4733077267498258524667337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3155384844998839016444891 4733077267498258524667337)
          ·
            refine ⟨3549807950623693893500503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4733077267498258524667337 3549807950623693893500503)
            ·
              refine ⟨5324711925935540840250755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3549807950623693893500503 5324711925935540840250755)
              ·
                refine ⟨7987067888903311260376133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5324711925935540840250755 7987067888903311260376133)
                ·
                  refine ⟨1497575229169370861320525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7987067888903311260376133 1497575229169370861320525)
                  ·
                    refine ⟨561590710938514072995197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1497575229169370861320525 561590710938514072995197)
                    ·
                      rfl

theorem cell22_1640541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_1640541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640541 prefixEnd_1640541 := by exact prefixLift 1640541
  have htrace : WordTrace (prefixWord ++ tailWord_1640541) baseStart_1640541 baseEnd_1640541 := by
    simpa [prefixWord, tailWord_1640541, baseEnd_1640541] using wordTrace_append hprefix tailTrace_1640541
  have hstable : (prefixWord ++ tailWord_1640541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640541).length < 2 ^ (prefixWord ++ tailWord_1640541).sum := by decide
  have hdescent : baseEnd_1640541 < baseStart_1640541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640569 : List Nat := [1, 2, 1, 3, 4, 1, 2, 2, 3, 3]
def baseStart_1640569 : Nat := 118140960795 + 1640569 * 2 ^ 59
def prefixEnd_1640569 : Nat := 4983230072969 + 3 ^ 40 * 1640569 * 2
def baseEnd_1640569 : Nat := 561600295910731333295111

theorem tailTrace_1640569 : CollatzResearch.WordTrace tailWord_1640569 prefixEnd_1640569 561600295910731333295111 := by
  unfold tailWord_1640569
  simp only [CollatzResearch.WordTrace]
  refine ⟨59836467193506174723492761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39890978129004116482328507 59836467193506174723492761)
  ·
    refine ⟨44877350395129631042619571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59836467193506174723492761 44877350395129631042619571)
    ·
      refine ⟨67316025592694446563929357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44877350395129631042619571 67316025592694446563929357)
      ·
        refine ⟨25243509597260417461473509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67316025592694446563929357 25243509597260417461473509)
        ·
          refine ⟨4733158049486328274026283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25243509597260417461473509 4733158049486328274026283)
          ·
            refine ⟨7099737074229492411039425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4733158049486328274026283 7099737074229492411039425)
            ·
              refine ⟨5324802805672119308279569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7099737074229492411039425 5324802805672119308279569)
              ·
                refine ⟨3993602104254089481209677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5324802805672119308279569 3993602104254089481209677)
                ·
                  refine ⟨1497600789095283555453629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3993602104254089481209677 1497600789095283555453629)
                  ·
                    refine ⟨561600295910731333295111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1497600789095283555453629 561600295910731333295111)
                    ·
                      rfl

theorem cell22_1640569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 3].length) (baseStart_1640569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640569 prefixEnd_1640569 := by exact prefixLift 1640569
  have htrace : WordTrace (prefixWord ++ tailWord_1640569) baseStart_1640569 baseEnd_1640569 := by
    simpa [prefixWord, tailWord_1640569, baseEnd_1640569] using wordTrace_append hprefix tailTrace_1640569
  have hstable : (prefixWord ++ tailWord_1640569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640569).length < 2 ^ (prefixWord ++ tailWord_1640569).sum := by decide
  have hdescent : baseEnd_1640569 < baseStart_1640569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640721 : List Nat := [1, 2, 2, 1, 1, 6, 2, 1, 3, 3]
def baseStart_1640721 : Nat := 118140960795 + 1640721 * 2 ^ 59
def prefixEnd_1640721 : Nat := 4983230072969 + 3 ^ 40 * 1640721 * 2
def baseEnd_1640721 : Nat := 561652328617053603494645

theorem tailTrace_1640721 : CollatzResearch.WordTrace tailWord_1640721 prefixEnd_1640721 561652328617053603494645 := by
  unfold tailWord_1640721
  simp only [CollatzResearch.WordTrace]
  refine ⟨59842011088955504683026017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39894674059303669788684011 59842011088955504683026017)
  ·
    refine ⟨44881508316716628512269513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59842011088955504683026017 44881508316716628512269513)
    ·
      refine ⟨33661131237537471384202135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44881508316716628512269513 33661131237537471384202135)
      ·
        refine ⟨50491696856306207076303203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33661131237537471384202135 50491696856306207076303203)
        ·
          refine ⟨75737545284459310614454805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50491696856306207076303203 75737545284459310614454805)
          ·
            refine ⟨3550197435209030185052569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75737545284459310614454805 3550197435209030185052569)
            ·
              refine ⟨2662648076406772638789427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3550197435209030185052569 2662648076406772638789427)
              ·
                refine ⟨3993972114610158958184141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2662648076406772638789427 3993972114610158958184141)
                ·
                  refine ⟨1497739542978809609319053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3993972114610158958184141 1497739542978809609319053)
                  ·
                    refine ⟨561652328617053603494645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1497739542978809609319053 561652328617053603494645)
                    ·
                      rfl

theorem cell22_1640721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_1640721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640721 prefixEnd_1640721 := by exact prefixLift 1640721
  have htrace : WordTrace (prefixWord ++ tailWord_1640721) baseStart_1640721 baseEnd_1640721 := by
    simpa [prefixWord, tailWord_1640721, baseEnd_1640721] using wordTrace_append hprefix tailTrace_1640721
  have hstable : (prefixWord ++ tailWord_1640721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640721).length < 2 ^ (prefixWord ++ tailWord_1640721).sum := by decide
  have hdescent : baseEnd_1640721 < baseStart_1640721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640772 : List Nat := [2, 3, 4, 1, 3, 1, 1, 1, 3, 3]
def baseStart_1640772 : Nat := 118140960795 + 1640772 * 2 ^ 59
def prefixEnd_1640772 : Nat := 4983230072969 + 3 ^ 40 * 1640772 * 2
def baseEnd_1640772 : Nat := 561669786959306470469489

theorem tailTrace_1640772 : CollatzResearch.WordTrace tailWord_1640772 prefixEnd_1640772 561669786959306470469489 := by
  unfold tailWord_1640772
  simp only [CollatzResearch.WordTrace]
  refine ⟨29921935605885370196566285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39895914141180493595421713 29921935605885370196566285)
  ·
    refine ⟨11220725852207013823712357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29921935605885370196566285 11220725852207013823712357)
    ·
      refine ⟨2103886097288815091946067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11220725852207013823712357 2103886097288815091946067)
      ·
        refine ⟨3155829145933222637919101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2103886097288815091946067 3155829145933222637919101)
        ·
          refine ⟨1183435929724958489219663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3155829145933222637919101 1183435929724958489219663)
          ·
            refine ⟨1775153894587437733829495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1183435929724958489219663 1775153894587437733829495)
            ·
              refine ⟨2662730841881156600744243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1775153894587437733829495 2662730841881156600744243)
              ·
                refine ⟨3994096262821734901116365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2662730841881156600744243 3994096262821734901116365)
                ·
                  refine ⟨1497786098558150587918637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3994096262821734901116365 1497786098558150587918637)
                  ·
                    refine ⟨561669786959306470469489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1497786098558150587918637 561669786959306470469489)
                    ·
                      rfl

theorem cell22_1640772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_1640772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640772 prefixEnd_1640772 := by exact prefixLift 1640772
  have htrace : WordTrace (prefixWord ++ tailWord_1640772) baseStart_1640772 baseEnd_1640772 := by
    simpa [prefixWord, tailWord_1640772, baseEnd_1640772] using wordTrace_append hprefix tailTrace_1640772
  have hstable : (prefixWord ++ tailWord_1640772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640772).length < 2 ^ (prefixWord ++ tailWord_1640772).sum := by decide
  have hdescent : baseEnd_1640772 < baseStart_1640772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640794 : List Nat := [3, 1, 1, 2, 1, 2, 1, 5, 1, 5]
def baseStart_1640794 : Nat := 118140960795 + 1640794 * 2 ^ 59
def prefixEnd_1640794 : Nat := 4983230072969 + 3 ^ 40 * 1640794 * 2
def baseEnd_1640794 : Nat := 561677318008905746419421

theorem tailTrace_1640794 : CollatzResearch.WordTrace tailWord_1640794 prefixEnd_1640794 561677318008905746419421 := by
  unfold tailWord_1640794
  simp only [CollatzResearch.WordTrace]
  refine ⟨14961168404422759537608359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39896449078460692100288957 14961168404422759537608359)
  ·
    refine ⟨22441752606634139306412539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14961168404422759537608359 22441752606634139306412539)
    ·
      refine ⟨33662628909951208959618809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22441752606634139306412539 33662628909951208959618809)
      ·
        refine ⟨25246971682463406719714107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33662628909951208959618809 25246971682463406719714107)
        ·
          refine ⟨37870457523695110079571161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25246971682463406719714107 37870457523695110079571161)
          ·
            refine ⟨28402843142771332559678371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37870457523695110079571161 28402843142771332559678371)
            ·
              refine ⟨42604264714156998839517557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28402843142771332559678371 42604264714156998839517557)
              ·
                refine ⟨3994149816952218641204771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42604264714156998839517557 3994149816952218641204771)
                ·
                  refine ⟨5991224725428327961807157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3994149816952218641204771 5991224725428327961807157)
                  ·
                    refine ⟨561677318008905746419421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5991224725428327961807157 561677318008905746419421)
                    ·
                      rfl

theorem cell22_1640794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_1640794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640794 prefixEnd_1640794 := by exact prefixLift 1640794
  have htrace : WordTrace (prefixWord ++ tailWord_1640794) baseStart_1640794 baseEnd_1640794 := by
    simpa [prefixWord, tailWord_1640794, baseEnd_1640794] using wordTrace_append hprefix tailTrace_1640794
  have hstable : (prefixWord ++ tailWord_1640794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640794).length < 2 ^ (prefixWord ++ tailWord_1640794).sum := by decide
  have hdescent : baseEnd_1640794 < baseStart_1640794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640841 : List Nat := [1, 2, 1, 1, 6, 3, 1, 7]
def baseStart_1640841 : Nat := 118140960795 + 1640841 * 2 ^ 59
def prefixEnd_1640841 : Nat := 4983230072969 + 3 ^ 40 * 1640841 * 2
def baseEnd_1640841 : Nat := 62410378563268143388253

theorem tailTrace_1640841 : CollatzResearch.WordTrace tailWord_1640841 prefixEnd_1640841 62410378563268143388253 := by
  unfold tailWord_1640841
  simp only [CollatzResearch.WordTrace]
  refine ⟨59846387848520765177394377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39897591899013843451596251 59846387848520765177394377)
  ·
    refine ⟨44884790886390573883045783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59846387848520765177394377 44884790886390573883045783)
    ·
      refine ⟨67327186329585860824568675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44884790886390573883045783 67327186329585860824568675)
      ·
        refine ⟨100990779494378791236853013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67327186329585860824568675 100990779494378791236853013)
        ·
          refine ⟨4733942788799005839227485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 100990779494378791236853013 4733942788799005839227485)
          ·
            refine ⟨1775228545799627189710307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4733942788799005839227485 1775228545799627189710307)
            ·
              refine ⟨2662842818699440784565461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1775228545799627189710307 2662842818699440784565461)
              ·
                refine ⟨62410378563268143388253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2662842818699440784565461 62410378563268143388253)
                ·
                  rfl

theorem cell22_1640841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 7].length) (baseStart_1640841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640841 prefixEnd_1640841 := by exact prefixLift 1640841
  have htrace : WordTrace (prefixWord ++ tailWord_1640841) baseStart_1640841 baseEnd_1640841 := by
    simpa [prefixWord, tailWord_1640841, baseEnd_1640841] using wordTrace_append hprefix tailTrace_1640841
  have hstable : (prefixWord ++ tailWord_1640841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640841).length < 2 ^ (prefixWord ++ tailWord_1640841).sum := by decide
  have hdescent : baseEnd_1640841 < baseStart_1640841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640869 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 7]
def baseStart_1640869 : Nat := 118140960795 + 1640869 * 2 ^ 59
def prefixEnd_1640869 : Nat := 4983230072969 + 3 ^ 40 * 1640869 * 2
def baseEnd_1640869 : Nat := 187234330680543516931397

theorem tailTrace_1640869 : CollatzResearch.WordTrace tailWord_1640869 prefixEnd_1640869 187234330680543516931397 := by
  unfold tailWord_1640869
  simp only [CollatzResearch.WordTrace]
  refine ⟨59847409092419325959413661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39898272728279550639609107 59847409092419325959413661)
  ·
    refine ⟨22442778409657247234780123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59847409092419325959413661 22442778409657247234780123)
    ·
      refine ⟨33664167614485870852170185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22442778409657247234780123 33664167614485870852170185)
      ·
        refine ⟨25248125710864403139127639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33664167614485870852170185 25248125710864403139127639)
        ·
          refine ⟨37872188566296604708691459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25248125710864403139127639 37872188566296604708691459)
          ·
            refine ⟨56808282849444907063037189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37872188566296604708691459 56808282849444907063037189)
            ·
              refine ⟨10651553034270920074319473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56808282849444907063037189 10651553034270920074319473)
              ·
                refine ⟨7988664775703190055739605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10651553034270920074319473 7988664775703190055739605)
                ·
                  refine ⟨187234330680543516931397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7988664775703190055739605 187234330680543516931397)
                  ·
                    rfl

theorem cell22_1640869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_1640869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640869 prefixEnd_1640869 := by exact prefixLift 1640869
  have htrace : WordTrace (prefixWord ++ tailWord_1640869) baseStart_1640869 baseEnd_1640869 := by
    simpa [prefixWord, tailWord_1640869, baseEnd_1640869] using wordTrace_append hprefix tailTrace_1640869
  have hstable : (prefixWord ++ tailWord_1640869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640869).length < 2 ^ (prefixWord ++ tailWord_1640869).sum := by decide
  have hdescent : baseEnd_1640869 < baseStart_1640869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640903 : List Nat := [1, 1, 4, 1, 1, 5, 3, 1, 5]
def baseStart_1640903 : Nat := 118140960795 + 1640903 * 2 ^ 59
def prefixEnd_1640903 : Nat := 4983230072969 + 3 ^ 40 * 1640903 * 2
def baseEnd_1640903 : Nat := 187238210312155265148029

theorem tailTrace_1640903 : CollatzResearch.WordTrace tailWord_1640903 prefixEnd_1640903 187238210312155265148029 := by
  unfold tailWord_1640903
  simp only [CollatzResearch.WordTrace]
  refine ⟨59848649174296149766151363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39899099449530766510767575 59848649174296149766151363)
  ·
    refine ⟨89772973761444224649227045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59848649174296149766151363 89772973761444224649227045)
    ·
      refine ⟨16832432580270792121730071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89772973761444224649227045 16832432580270792121730071)
      ·
        refine ⟨25248648870406188182595107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16832432580270792121730071 25248648870406188182595107)
        ·
          refine ⟨37872973305609282273892661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25248648870406188182595107 37872973305609282273892661)
          ·
            refine ⟨3550591247400870213177437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37872973305609282273892661 3550591247400870213177437)
            ·
              refine ⟨1331471717775326329941539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3550591247400870213177437 1331471717775326329941539)
              ·
                refine ⟨1997207576662989494912309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1331471717775326329941539 1997207576662989494912309)
                ·
                  refine ⟨187238210312155265148029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1997207576662989494912309 187238210312155265148029)
                  ·
                    rfl

theorem cell22_1640903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 5].length) (baseStart_1640903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640903 prefixEnd_1640903 := by exact prefixLift 1640903
  have htrace : WordTrace (prefixWord ++ tailWord_1640903) baseStart_1640903 baseEnd_1640903 := by
    simpa [prefixWord, tailWord_1640903, baseEnd_1640903] using wordTrace_append hprefix tailTrace_1640903
  have hstable : (prefixWord ++ tailWord_1640903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640903).length < 2 ^ (prefixWord ++ tailWord_1640903).sum := by decide
  have hdescent : baseEnd_1640903 < baseStart_1640903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640963 : List Nat := [1, 1, 1, 3, 2, 1, 5, 3, 2, 3]
def baseStart_1640963 : Nat := 118140960795 + 1640963 * 2 ^ 59
def prefixEnd_1640963 : Nat := 4983230072969 + 3 ^ 40 * 1640963 * 2
def baseEnd_1640963 : Nat := 561735170162645638943903

theorem tailTrace_1640963 : CollatzResearch.WordTrace tailWord_1640963 prefixEnd_1640963 561735170162645638943903 := by
  unfold tailWord_1640963
  simp only [CollatzResearch.WordTrace]
  refine ⟨59850837554078780013335543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39900558369385853342223695 59850837554078780013335543)
  ·
    refine ⟨89776256331118170020003315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59850837554078780013335543 89776256331118170020003315)
    ·
      refine ⟨134664384496677255030004973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89776256331118170020003315 134664384496677255030004973)
      ·
        refine ⟨50499144186253970636251865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134664384496677255030004973 50499144186253970636251865)
        ·
          refine ⟨37874358139690477977188899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50499144186253970636251865 37874358139690477977188899)
          ·
            refine ⟨56811537209535716965783349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37874358139690477977188899 56811537209535716965783349)
            ·
              refine ⟨5326081613393973465542189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56811537209535716965783349 5326081613393973465542189)
              ·
                refine ⟨1997280605022740049578321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5326081613393973465542189 1997280605022740049578321)
                ·
                  refine ⟨1497960453767055037183741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1997280605022740049578321 1497960453767055037183741)
                  ·
                    refine ⟨561735170162645638943903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1497960453767055037183741 561735170162645638943903)
                    ·
                      rfl

theorem cell22_1640963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 3].length) (baseStart_1640963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640963 prefixEnd_1640963 := by exact prefixLift 1640963
  have htrace : WordTrace (prefixWord ++ tailWord_1640963) baseStart_1640963 baseEnd_1640963 := by
    simpa [prefixWord, tailWord_1640963, baseEnd_1640963] using wordTrace_append hprefix tailTrace_1640963
  have hstable : (prefixWord ++ tailWord_1640963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640963).length < 2 ^ (prefixWord ++ tailWord_1640963).sum := by decide
  have hdescent : baseEnd_1640963 < baseStart_1640963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640967 : List Nat := [1, 1, 4, 3, 4, 1, 1, 2, 1, 4]
def baseStart_1640967 : Nat := 118140960795 + 1640967 * 2 ^ 59
def prefixEnd_1640967 : Nat := 4983230072969 + 3 ^ 40 * 1640967 * 2
def baseEnd_1640967 : Nat := 561736539444390961843891

theorem tailTrace_1640967 : CollatzResearch.WordTrace tailWord_1640967 prefixEnd_1640967 561736539444390961843891 := by
  unfold tailWord_1640967
  simp only [CollatzResearch.WordTrace]
  refine ⟨59850983446064288696481155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39900655630709525797654103 59850983446064288696481155)
  ·
    refine ⟨89776475169096433044721733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59850983446064288696481155 89776475169096433044721733)
    ·
      refine ⟨16833089094205581195885325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89776475169096433044721733 16833089094205581195885325)
      ·
        refine ⟨6312408410327092948456997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16833089094205581195885325 6312408410327092948456997)
        ·
          refine ⟨1183576576936329927835687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6312408410327092948456997 1183576576936329927835687)
          ·
            refine ⟨1775364865404494891753531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1183576576936329927835687 1775364865404494891753531)
            ·
              refine ⟨2663047298106742337630297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1775364865404494891753531 2663047298106742337630297)
              ·
                refine ⟨1997285473580056753222723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2663047298106742337630297 1997285473580056753222723)
                ·
                  refine ⟨2995928210370085129834085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1997285473580056753222723 2995928210370085129834085)
                  ·
                    refine ⟨561736539444390961843891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2995928210370085129834085 561736539444390961843891)
                    ·
                      rfl

theorem cell22_1640967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_1640967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640967 prefixEnd_1640967 := by exact prefixLift 1640967
  have htrace : WordTrace (prefixWord ++ tailWord_1640967) baseStart_1640967 baseEnd_1640967 := by
    simpa [prefixWord, tailWord_1640967, baseEnd_1640967] using wordTrace_append hprefix tailTrace_1640967
  have hstable : (prefixWord ++ tailWord_1640967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640967).length < 2 ^ (prefixWord ++ tailWord_1640967).sum := by decide
  have hdescent : baseEnd_1640967 < baseStart_1640967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640980 : List Nat := [2, 4, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1640980 : Nat := 118140960795 + 1640980 * 2 ^ 59
def prefixEnd_1640980 : Nat := 4983230072969 + 3 ^ 40 * 1640980 * 2
def baseEnd_1640980 : Nat := 561740989610063261268851

theorem tailTrace_1640980 : CollatzResearch.WordTrace tailWord_1640980 prefixEnd_1640980 561740989610063261268851 := by
  unfold tailWord_1640980
  simp only [CollatzResearch.WordTrace]
  refine ⟨29925728797508595958352197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39900971730011461277802929 29925728797508595958352197)
  ·
    refine ⟨5611074149532861742191037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29925728797508595958352197 5611074149532861742191037)
    ·
      refine ⟨2104152806074823153321639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5611074149532861742191037 2104152806074823153321639)
      ·
        refine ⟨3156229209112234729982459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2104152806074823153321639 3156229209112234729982459)
        ·
          refine ⟨4734343813668352094973689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3156229209112234729982459 4734343813668352094973689)
          ·
            refine ⟨3550757860251264071230267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4734343813668352094973689 3550757860251264071230267)
            ·
              refine ⟨5326136790376896106845401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3550757860251264071230267 5326136790376896106845401)
              ·
                refine ⟨3994602592782672080134051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5326136790376896106845401 3994602592782672080134051)
                ·
                  refine ⟨5991903889174008120201077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3994602592782672080134051 5991903889174008120201077)
                  ·
                    refine ⟨561740989610063261268851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5991903889174008120201077 561740989610063261268851)
                    ·
                      rfl

theorem cell22_1640980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1640980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1640980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1640980 prefixEnd_1640980 := by exact prefixLift 1640980
  have htrace : WordTrace (prefixWord ++ tailWord_1640980) baseStart_1640980 baseEnd_1640980 := by
    simpa [prefixWord, tailWord_1640980, baseEnd_1640980] using wordTrace_append hprefix tailTrace_1640980
  have hstable : (prefixWord ++ tailWord_1640980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640980).length < 2 ^ (prefixWord ++ tailWord_1640980).sum := by decide
  have hdescent : baseEnd_1640980 < baseStart_1640980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641025 : List Nat := [1, 2, 5, 1, 1, 3, 1, 2, 3, 3]
def baseStart_1641025 : Nat := 118140960795 + 1641025 * 2 ^ 59
def prefixEnd_1641025 : Nat := 4983230072969 + 3 ^ 40 * 1641025 * 2
def baseEnd_1641025 : Nat := 561756394029698143893713

theorem tailTrace_1641025 : CollatzResearch.WordTrace tailWord_1641025 prefixEnd_1641025 561756394029698143893713 := by
  unfold tailWord_1641025
  simp only [CollatzResearch.WordTrace]
  refine ⟨59853098879854164602092529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39902065919902776401395019 59853098879854164602092529)
  ·
    refine ⟨44889824159890623451569397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59853098879854164602092529 44889824159890623451569397)
    ·
      refine ⟨4208421014989745948584631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44889824159890623451569397 4208421014989745948584631)
      ·
        refine ⟨6312631522484618922876947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4208421014989745948584631 6312631522484618922876947)
        ·
          refine ⟨9468947283726928384315421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6312631522484618922876947 9468947283726928384315421)
          ·
            refine ⟨3550855231397598144118283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9468947283726928384315421 3550855231397598144118283)
            ·
              refine ⟨5326282847096397216177425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3550855231397598144118283 5326282847096397216177425)
              ·
                refine ⟨3994712135322297912133069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5326282847096397216177425 3994712135322297912133069)
                ·
                  refine ⟨1498017050745861717049901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3994712135322297912133069 1498017050745861717049901)
                  ·
                    refine ⟨561756394029698143893713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1498017050745861717049901 561756394029698143893713)
                    ·
                      rfl

theorem cell22_1641025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_1641025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641025 prefixEnd_1641025 := by exact prefixLift 1641025
  have htrace : WordTrace (prefixWord ++ tailWord_1641025) baseStart_1641025 baseEnd_1641025 := by
    simpa [prefixWord, tailWord_1641025, baseEnd_1641025] using wordTrace_append hprefix tailTrace_1641025
  have hstable : (prefixWord ++ tailWord_1641025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641025).length < 2 ^ (prefixWord ++ tailWord_1641025).sum := by decide
  have hdescent : baseEnd_1641025 < baseStart_1641025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641036 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 1, 7]
def baseStart_1641036 : Nat := 118140960795 + 1641036 * 2 ^ 59
def prefixEnd_1641036 : Nat := 4983230072969 + 3 ^ 40 * 1641036 * 2
def baseEnd_1641036 : Nat := 561760159554497781868679

theorem tailTrace_1641036 : CollatzResearch.WordTrace tailWord_1641036 prefixEnd_1641036 561760159554497781868679 := by
  unfold tailWord_1641036
  simp only [CollatzResearch.WordTrace]
  refine ⟨29926750041407156740371481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39902333388542875653828641 29926750041407156740371481)
  ·
    refine ⟨22445062531055367555278611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29926750041407156740371481 22445062531055367555278611)
    ·
      refine ⟨33667593796583051332917917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22445062531055367555278611 33667593796583051332917917)
      ·
        refine ⟨12625347673718644249844219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33667593796583051332917917 12625347673718644249844219)
        ·
          refine ⟨18938021510577966374766329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12625347673718644249844219 18938021510577966374766329)
          ·
            refine ⟨14203516132933474781074747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18938021510577966374766329 14203516132933474781074747)
            ·
              refine ⟨21305274199400212171612121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14203516132933474781074747 21305274199400212171612121)
              ·
                refine ⟨15978955649550159128709091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21305274199400212171612121 15978955649550159128709091)
                ·
                  refine ⟨23968433474325238693063637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15978955649550159128709091 23968433474325238693063637)
                  ·
                    refine ⟨561760159554497781868679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23968433474325238693063637 561760159554497781868679)
                    ·
                      rfl

theorem cell22_1641036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_1641036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641036 prefixEnd_1641036 := by exact prefixLift 1641036
  have htrace : WordTrace (prefixWord ++ tailWord_1641036) baseStart_1641036 baseEnd_1641036 := by
    simpa [prefixWord, tailWord_1641036, baseEnd_1641036] using wordTrace_append hprefix tailTrace_1641036
  have hstable : (prefixWord ++ tailWord_1641036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641036).length < 2 ^ (prefixWord ++ tailWord_1641036).sum := by decide
  have hdescent : baseEnd_1641036 < baseStart_1641036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641042 : List Nat := [3, 2, 2, 1, 2, 1, 4, 3, 1, 3]
def baseStart_1641042 : Nat := 118140960795 + 1641042 * 2 ^ 59
def prefixEnd_1641042 : Nat := 4983230072969 + 3 ^ 40 * 1641042 * 2
def baseEnd_1641042 : Nat := 561762213477115766218661

theorem tailTrace_1641042 : CollatzResearch.WordTrace tailWord_1641042 prefixEnd_1641042 561762213477115766218661 := by
  unfold tailWord_1641042
  simp only [CollatzResearch.WordTrace]
  refine ⟨14963429730198144126365345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39902479280528384336974253 14963429730198144126365345)
  ·
    refine ⟨11222572297648608094774009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14963429730198144126365345 11222572297648608094774009)
    ·
      refine ⟨8416929223236456071080507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11222572297648608094774009 8416929223236456071080507)
      ·
        refine ⟨12625393834854684106620761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8416929223236456071080507 12625393834854684106620761)
        ·
          refine ⟨9469045376141013079965571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12625393834854684106620761 9469045376141013079965571)
          ·
            refine ⟨14203568064211519619948357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9469045376141013079965571 14203568064211519619948357)
            ·
              refine ⟨2663169012039659928740317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14203568064211519619948357 2663169012039659928740317)
              ·
                refine ⟨998688379514872473277619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2663169012039659928740317 998688379514872473277619)
                ·
                  refine ⟨1498032569272308709916429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 998688379514872473277619 1498032569272308709916429)
                  ·
                    refine ⟨561762213477115766218661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1498032569272308709916429 561762213477115766218661)
                    ·
                      rfl

theorem cell22_1641042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_1641042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641042 prefixEnd_1641042 := by exact prefixLift 1641042
  have htrace : WordTrace (prefixWord ++ tailWord_1641042) baseStart_1641042 baseEnd_1641042 := by
    simpa [prefixWord, tailWord_1641042, baseEnd_1641042] using wordTrace_append hprefix tailTrace_1641042
  have hstable : (prefixWord ++ tailWord_1641042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641042).length < 2 ^ (prefixWord ++ tailWord_1641042).sum := by decide
  have hdescent : baseEnd_1641042 < baseStart_1641042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641113 : List Nat := [1, 2, 1, 2, 1, 2, 5, 2, 2, 4]
def baseStart_1641113 : Nat := 118140960795 + 1641113 * 2 ^ 59
def prefixEnd_1641113 : Nat := 4983230072969 + 3 ^ 40 * 1641113 * 2
def baseEnd_1641113 : Nat := 561786518228095247693443

theorem tailTrace_1641113 : CollatzResearch.WordTrace tailWord_1641113 prefixEnd_1641113 561786518228095247693443 := by
  unfold tailWord_1641113
  simp only [CollatzResearch.WordTrace]
  refine ⟨59856308503535355631295993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39904205669023570420863995 59856308503535355631295993)
  ·
    refine ⟨44892231377651516723471995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59856308503535355631295993 44892231377651516723471995)
    ·
      refine ⟨67338347066477275085207993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44892231377651516723471995 67338347066477275085207993)
      ·
        refine ⟨50503760299857956313905995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67338347066477275085207993 50503760299857956313905995)
        ·
          refine ⟨75755640449786934470858993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50503760299857956313905995 75755640449786934470858993)
          ·
            refine ⟨56816730337340200853144245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75755640449786934470858993 56816730337340200853144245)
            ·
              refine ⟨5326568469125643829982273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56816730337340200853144245 5326568469125643829982273)
              ·
                refine ⟨3994926351844232872486705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5326568469125643829982273 3994926351844232872486705)
                ·
                  refine ⟨2996194763883174654365029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3994926351844232872486705 2996194763883174654365029)
                  ·
                    refine ⟨561786518228095247693443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2996194763883174654365029 561786518228095247693443)
                    ·
                      rfl

theorem cell22_1641113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 4].length) (baseStart_1641113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641113 prefixEnd_1641113 := by exact prefixLift 1641113
  have htrace : WordTrace (prefixWord ++ tailWord_1641113) baseStart_1641113 baseEnd_1641113 := by
    simpa [prefixWord, tailWord_1641113, baseEnd_1641113] using wordTrace_append hprefix tailTrace_1641113
  have hstable : (prefixWord ++ tailWord_1641113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641113).length < 2 ^ (prefixWord ++ tailWord_1641113).sum := by decide
  have hdescent : baseEnd_1641113 < baseStart_1641113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641177 : List Nat := [1, 2, 1, 2, 3, 2, 3, 4, 1, 3]
def baseStart_1641177 : Nat := 118140960795 + 1641177 * 2 ^ 59
def prefixEnd_1641177 : Nat := 4983230072969 + 3 ^ 40 * 1641177 * 2
def baseEnd_1641177 : Nat := 561808426736020414093247

theorem tailTrace_1641177 : CollatzResearch.WordTrace tailWord_1641177 prefixEnd_1641177 561808426736020414093247 := by
  unfold tailWord_1641177
  simp only [CollatzResearch.WordTrace]
  refine ⟨59858642775303494561625785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39905761850202329707750523 59858642775303494561625785)
  ·
    refine ⟨44893982081477620921219339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59858642775303494561625785 44893982081477620921219339)
    ·
      refine ⟨67340973122216431381829009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44893982081477620921219339 67340973122216431381829009)
      ·
        refine ⟨50505729841662323536371757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67340973122216431381829009 50505729841662323536371757)
        ·
          refine ⟨18939648690623371326139409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50505729841662323536371757 18939648690623371326139409)
          ·
            refine ⟨14204736517967528494604557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18939648690623371326139409 14204736517967528494604557)
            ·
              refine ⟨5326776194237823185476709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14204736517967528494604557 5326776194237823185476709)
              ·
                refine ⟨998770536419591847276883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5326776194237823185476709 998770536419591847276883)
                ·
                  refine ⟨1498155804629387770915325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 998770536419591847276883 1498155804629387770915325)
                  ·
                    refine ⟨561808426736020414093247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1498155804629387770915325 561808426736020414093247)
                    ·
                      rfl

theorem cell22_1641177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 1, 3].length) (baseStart_1641177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641177 prefixEnd_1641177 := by exact prefixLift 1641177
  have htrace : WordTrace (prefixWord ++ tailWord_1641177) baseStart_1641177 baseEnd_1641177 := by
    simpa [prefixWord, tailWord_1641177, baseEnd_1641177] using wordTrace_append hprefix tailTrace_1641177
  have hstable : (prefixWord ++ tailWord_1641177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641177).length < 2 ^ (prefixWord ++ tailWord_1641177).sum := by decide
  have hdescent : baseEnd_1641177 < baseStart_1641177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641188 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_1641188 : Nat := 118140960795 + 1641188 * 2 ^ 59
def prefixEnd_1641188 : Nat := 4983230072969 + 3 ^ 40 * 1641188 * 2
def baseEnd_1641188 : Nat := 561812192260820052068213

theorem tailTrace_1641188 : CollatzResearch.WordTrace tailWord_1641188 prefixEnd_1641188 561812192260820052068213 := by
  unfold tailWord_1641188
  simp only [CollatzResearch.WordTrace]
  refine ⟨29929521989131821720138109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39906029318842428960184145 29929521989131821720138109)
  ·
    refine ⟨11223570745924433145051791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29929521989131821720138109 11223570745924433145051791)
    ·
      refine ⟨16835356118886649717577687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11223570745924433145051791 16835356118886649717577687)
      ·
        refine ⟨25253034178329974576366531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16835356118886649717577687 25253034178329974576366531)
        ·
          refine ⟨37879551267494961864549797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25253034178329974576366531 37879551267494961864549797)
          ·
            refine ⟨7102415862655305349603087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37879551267494961864549797 7102415862655305349603087)
            ·
              refine ⟨10653623793982958024404631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7102415862655305349603087 10653623793982958024404631)
              ·
                refine ⟨15980435690974437036606947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10653623793982958024404631 15980435690974437036606947)
                ·
                  refine ⟨23970653536461655554910421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15980435690974437036606947 23970653536461655554910421)
                  ·
                    refine ⟨561812192260820052068213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23970653536461655554910421 561812192260820052068213)
                    ·
                      rfl

theorem cell22_1641188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_1641188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641188 prefixEnd_1641188 := by exact prefixLift 1641188
  have htrace : WordTrace (prefixWord ++ tailWord_1641188) baseStart_1641188 baseEnd_1641188 := by
    simpa [prefixWord, tailWord_1641188, baseEnd_1641188] using wordTrace_append hprefix tailTrace_1641188
  have hstable : (prefixWord ++ tailWord_1641188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641188).length < 2 ^ (prefixWord ++ tailWord_1641188).sum := by decide
  have hdescent : baseEnd_1641188 < baseStart_1641188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641233 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 3, 5]
def baseStart_1641233 : Nat := 118140960795 + 1641233 * 2 ^ 59
def prefixEnd_1641233 : Nat := 4983230072969 + 3 ^ 40 * 1641233 * 2
def baseEnd_1641233 : Nat := 561827596680454934693075

theorem tailTrace_1641233 : CollatzResearch.WordTrace tailWord_1641233 prefixEnd_1641233 561827596680454934693075 := by
  unfold tailWord_1641233
  simp only [CollatzResearch.WordTrace]
  refine ⟨59860685263100616125664353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39907123508733744083776235 59860685263100616125664353)
  ·
    refine ⟨44895513947325462094248265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59860685263100616125664353 44895513947325462094248265)
    ·
      refine ⟨33671635460494096570686199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44895513947325462094248265 33671635460494096570686199)
      ·
        refine ⟨50507453190741144856029299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33671635460494096570686199 50507453190741144856029299)
        ·
          refine ⟨75761179786111717284043949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50507453190741144856029299 75761179786111717284043949)
          ·
            refine ⟨28410442419791893981516481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75761179786111717284043949 28410442419791893981516481)
            ·
              refine ⟨21307831814843920486137361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28410442419791893981516481 21307831814843920486137361)
              ·
                refine ⟨15980873861132940364603021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21307831814843920486137361 15980873861132940364603021)
                ·
                  refine ⟨5992827697924852636726133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15980873861132940364603021 5992827697924852636726133)
                  ·
                    refine ⟨561827596680454934693075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5992827697924852636726133 561827596680454934693075)
                    ·
                      rfl

theorem cell22_1641233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_1641233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641233 prefixEnd_1641233 := by exact prefixLift 1641233
  have htrace : WordTrace (prefixWord ++ tailWord_1641233) baseStart_1641233 baseEnd_1641233 := by
    simpa [prefixWord, tailWord_1641233, baseEnd_1641233] using wordTrace_append hprefix tailTrace_1641233
  have hstable : (prefixWord ++ tailWord_1641233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641233).length < 2 ^ (prefixWord ++ tailWord_1641233).sum := by decide
  have hdescent : baseEnd_1641233 < baseStart_1641233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641235 : List Nat := [1, 1, 1, 2, 1, 3, 3, 6, 4]
def baseStart_1641235 : Nat := 118140960795 + 1641235 * 2 ^ 59
def prefixEnd_1641235 : Nat := 4983230072969 + 3 ^ 40 * 1641235 * 2
def baseEnd_1641235 : Nat := 187276093773775865381023

theorem tailTrace_1641235 : CollatzResearch.WordTrace tailWord_1641235 prefixEnd_1641235 187276093773775865381023 := by
  unfold tailWord_1641235
  simp only [CollatzResearch.WordTrace]
  refine ⟨59860758209093370467237159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39907172139395580311491439 59860758209093370467237159)
  ·
    refine ⟨89791137313640055700855739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59860758209093370467237159 89791137313640055700855739)
    ·
      refine ⟨134686705970460083551283609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89791137313640055700855739 134686705970460083551283609)
      ·
        refine ⟨101015029477845062663462707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134686705970460083551283609 101015029477845062663462707)
        ·
          refine ⟨151522544216767593995194061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101015029477845062663462707 151522544216767593995194061)
          ·
            refine ⟨56820954081287847748197773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151522544216767593995194061 56820954081287847748197773)
            ·
              refine ⟨21307857780482942905574165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56820954081287847748197773 21307857780482942905574165)
              ·
                refine ⟨998805833460137948698789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21307857780482942905574165 998805833460137948698789)
                ·
                  refine ⟨187276093773775865381023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 998805833460137948698789 187276093773775865381023)
                  ·
                    rfl

theorem cell22_1641235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 4].length) (baseStart_1641235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641235 prefixEnd_1641235 := by exact prefixLift 1641235
  have htrace : WordTrace (prefixWord ++ tailWord_1641235) baseStart_1641235 baseEnd_1641235 := by
    simpa [prefixWord, tailWord_1641235, baseEnd_1641235] using wordTrace_append hprefix tailTrace_1641235
  have hstable : (prefixWord ++ tailWord_1641235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641235).length < 2 ^ (prefixWord ++ tailWord_1641235).sum := by decide
  have hdescent : baseEnd_1641235 < baseStart_1641235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641265 : List Nat := [1, 2, 2, 3, 2, 1, 2, 3, 2, 4]
def baseStart_1641265 : Nat := 118140960795 + 1641265 * 2 ^ 59
def prefixEnd_1641265 : Nat := 4983230072969 + 3 ^ 40 * 1641265 * 2
def baseEnd_1641265 : Nat := 561838550934417517892977

theorem tailTrace_1641265 : CollatzResearch.WordTrace tailWord_1641265 prefixEnd_1641265 561838550934417517892977 := by
  unfold tailWord_1641265
  simp only [CollatzResearch.WordTrace]
  refine ⟨59861852398984685590829249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39907901599323123727219499 59861852398984685590829249)
  ·
    refine ⟨44896389299238514193121937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59861852398984685590829249 44896389299238514193121937)
    ·
      refine ⟨33672291974428885644841453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44896389299238514193121937 33672291974428885644841453)
      ·
        refine ⟨12627109490410832116815545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33672291974428885644841453 12627109490410832116815545)
        ·
          refine ⟨9470332117808124087611659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12627109490410832116815545 9470332117808124087611659)
          ·
            refine ⟨14205498176712186131417489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9470332117808124087611659 14205498176712186131417489)
            ·
              refine ⟨10654123632534139598563117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14205498176712186131417489 10654123632534139598563117)
              ·
                refine ⟨3995296362200302349461169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10654123632534139598563117 3995296362200302349461169)
                ·
                  refine ⟨2996472271650226762095877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3995296362200302349461169 2996472271650226762095877)
                  ·
                    refine ⟨561838550934417517892977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2996472271650226762095877 561838550934417517892977)
                    ·
                      rfl

theorem cell22_1641265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_1641265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641265 prefixEnd_1641265 := by exact prefixLift 1641265
  have htrace : WordTrace (prefixWord ++ tailWord_1641265) baseStart_1641265 baseEnd_1641265 := by
    simpa [prefixWord, tailWord_1641265, baseEnd_1641265] using wordTrace_append hprefix tailTrace_1641265
  have hstable : (prefixWord ++ tailWord_1641265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641265).length < 2 ^ (prefixWord ++ tailWord_1641265).sum := by decide
  have hdescent : baseEnd_1641265 < baseStart_1641265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641269 : List Nat := [1, 3, 3, 1, 3, 3, 1, 3, 4]
def baseStart_1641269 : Nat := 118140960795 + 1641269 * 2 ^ 59
def prefixEnd_1641269 : Nat := 4983230072969 + 3 ^ 40 * 1641269 * 2
def baseEnd_1641269 : Nat := 187279973405387613597655

theorem tailTrace_1641269 : CollatzResearch.WordTrace tailWord_1641269 prefixEnd_1641269 187279973405387613597655 := by
  unfold tailWord_1641269
  simp only [CollatzResearch.WordTrace]
  refine ⟨59861998290970194273974861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39907998860646796182649907 59861998290970194273974861)
  ·
    refine ⟨22448249359113822852740573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59861998290970194273974861 22448249359113822852740573)
    ·
      refine ⟨8418093509667683569777715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22448249359113822852740573 8418093509667683569777715)
      ·
        refine ⟨12627140264501525354666573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8418093509667683569777715 12627140264501525354666573)
        ·
          refine ⟨4735177599188072007999965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12627140264501525354666573 4735177599188072007999965)
          ·
            refine ⟨1775691599695527002999987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4735177599188072007999965 1775691599695527002999987)
            ·
              refine ⟨2663537399543290504499981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1775691599695527002999987 2663537399543290504499981)
              ·
                refine ⟨998826524828733939187493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2663537399543290504499981 998826524828733939187493)
                ·
                  refine ⟨187279973405387613597655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 998826524828733939187493 187279973405387613597655)
                  ·
                    rfl

theorem cell22_1641269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 4].length) (baseStart_1641269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641269 prefixEnd_1641269 := by exact prefixLift 1641269
  have htrace : WordTrace (prefixWord ++ tailWord_1641269) baseStart_1641269 baseEnd_1641269 := by
    simpa [prefixWord, tailWord_1641269, baseEnd_1641269] using wordTrace_append hprefix tailTrace_1641269
  have hstable : (prefixWord ++ tailWord_1641269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641269).length < 2 ^ (prefixWord ++ tailWord_1641269).sum := by decide
  have hdescent : baseEnd_1641269 < baseStart_1641269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641286 : List Nat := [6, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_1641286 : Nat := 118140960795 + 1641286 * 2 ^ 59
def prefixEnd_1641286 : Nat := 4983230072969 + 3 ^ 40 * 1641286 * 2
def baseEnd_1641286 : Nat := 187281913221193487705971

theorem tailTrace_1641286 : CollatzResearch.WordTrace tailWord_1641286 prefixEnd_1641286 187281913221193487705971 := by
  unfold tailWord_1641286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1870706822872143943041991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39908412221272404118229141 1870706822872143943041991)
  ·
    refine ⟨2806060234308215914562987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1870706822872143943041991 2806060234308215914562987)
    ·
      refine ⟨4209090351462323871844481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2806060234308215914562987 4209090351462323871844481)
      ·
        refine ⟨3156817763596742903883361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4209090351462323871844481 3156817763596742903883361)
        ·
          refine ⟨2367613322697557177912521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3156817763596742903883361 2367613322697557177912521)
          ·
            refine ⟨1775709992023167883434391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2367613322697557177912521 1775709992023167883434391)
            ·
              refine ⟨2663564988034751825151587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1775709992023167883434391 2663564988034751825151587)
              ·
                refine ⟨3995347482052127737727381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2663564988034751825151587 3995347482052127737727381)
                ·
                  refine ⟨187281913221193487705971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3995347482052127737727381 187281913221193487705971)
                  ·
                    rfl

theorem cell22_1641286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_1641286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641286 prefixEnd_1641286 := by exact prefixLift 1641286
  have htrace : WordTrace (prefixWord ++ tailWord_1641286) baseStart_1641286 baseEnd_1641286 := by
    simpa [prefixWord, tailWord_1641286, baseEnd_1641286] using wordTrace_append hprefix tailTrace_1641286
  have hstable : (prefixWord ++ tailWord_1641286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641286).length < 2 ^ (prefixWord ++ tailWord_1641286).sum := by decide
  have hdescent : baseEnd_1641286 < baseStart_1641286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641355 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 3, 4]
def baseStart_1641355 : Nat := 118140960795 + 1641355 * 2 ^ 59
def prefixEnd_1641355 : Nat := 4983230072969 + 3 ^ 40 * 1641355 * 2
def baseEnd_1641355 : Nat := 561869359773687283142701

theorem tailTrace_1641355 : CollatzResearch.WordTrace tailWord_1641355 prefixEnd_1641355 561869359773687283142701 := by
  unfold tailWord_1641355
  simp only [CollatzResearch.WordTrace]
  refine ⟨59865134968658630961605519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39910089979105753974403679 59865134968658630961605519)
  ·
    refine ⟨89797702452987946442408279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59865134968658630961605519 89797702452987946442408279)
    ·
      refine ⟨134696553679481919663612419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89797702452987946442408279 134696553679481919663612419)
      ·
        refine ⟨202044830519222879495418629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134696553679481919663612419 202044830519222879495418629)
        ·
          refine ⟨37883405722354289905390993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202044830519222879495418629 37883405722354289905390993)
          ·
            refine ⟨28412554291765717429043245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37883405722354289905390993 28412554291765717429043245)
            ·
              refine ⟨10654707859412144035891217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28412554291765717429043245 10654707859412144035891217)
              ·
                refine ⟨7991030894559108026918413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10654707859412144035891217 7991030894559108026918413)
                ·
                  refine ⟨2996636585459665510094405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7991030894559108026918413 2996636585459665510094405)
                  ·
                    refine ⟨561869359773687283142701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2996636585459665510094405 561869359773687283142701)
                    ·
                      rfl

theorem cell22_1641355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 4].length) (baseStart_1641355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641355 prefixEnd_1641355 := by exact prefixLift 1641355
  have htrace : WordTrace (prefixWord ++ tailWord_1641355) baseStart_1641355 baseEnd_1641355 := by
    simpa [prefixWord, tailWord_1641355, baseEnd_1641355] using wordTrace_append hprefix tailTrace_1641355
  have hstable : (prefixWord ++ tailWord_1641355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641355).length < 2 ^ (prefixWord ++ tailWord_1641355).sum := by decide
  have hdescent : baseEnd_1641355 < baseStart_1641355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641385 : List Nat := [1, 2, 1, 1, 1, 1, 5, 4, 1, 5]
def baseStart_1641385 : Nat := 118140960795 + 1641385 * 2 ^ 59
def prefixEnd_1641385 : Nat := 4983230072969 + 3 ^ 40 * 1641385 * 2
def baseEnd_1641385 : Nat := 561879629386777204892609

theorem tailTrace_1641385 : CollatzResearch.WordTrace tailWord_1641385 prefixEnd_1641385 561879629386777204892609 := by
  unfold tailWord_1641385
  simp only [CollatzResearch.WordTrace]
  refine ⟨59866229158549946085197609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39910819439033297390131739 59866229158549946085197609)
  ·
    refine ⟨44899671868912459563898207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59866229158549946085197609 44899671868912459563898207)
    ·
      refine ⟨67349507803368689345847311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44899671868912459563898207 67349507803368689345847311)
      ·
        refine ⟨101024261705053034018770967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67349507803368689345847311 101024261705053034018770967)
        ·
          refine ⟨151536392557579551028156451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101024261705053034018770967 151536392557579551028156451)
          ·
            refine ⟨227304588836369326542234677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151536392557579551028156451 227304588836369326542234677)
            ·
              refine ⟨21309805203409624363334501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 227304588836369326542234677 21309805203409624363334501)
              ·
                refine ⟨3995588475639304568125219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21309805203409624363334501 3995588475639304568125219)
                ·
                  refine ⟨5993382713458956852187829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3995588475639304568125219 5993382713458956852187829)
                  ·
                    refine ⟨561879629386777204892609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5993382713458956852187829 561879629386777204892609)
                    ·
                      rfl

theorem cell22_1641385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 5].length) (baseStart_1641385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1641385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1641385 prefixEnd_1641385 := by exact prefixLift 1641385
  have htrace : WordTrace (prefixWord ++ tailWord_1641385) baseStart_1641385 baseEnd_1641385 := by
    simpa [prefixWord, tailWord_1641385, baseEnd_1641385] using wordTrace_append hprefix tailTrace_1641385
  have hstable : (prefixWord ++ tailWord_1641385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641385).length < 2 ^ (prefixWord ++ tailWord_1641385).sum := by decide
  have hdescent : baseEnd_1641385 < baseStart_1641385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
