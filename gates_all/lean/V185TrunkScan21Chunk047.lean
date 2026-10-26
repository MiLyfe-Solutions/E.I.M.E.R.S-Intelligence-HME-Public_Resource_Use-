import V185TrunkScan21Chunk046

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_569336 : List Nat := [2, 1, 2, 1, 1, 3, 5, 2, 4]
def baseStart_569336 : Nat := 118140960795 + 569336 * 2 ^ 59
def prefixEnd_569336 : Nat := 4983230072969 + 3 ^ 40 * 569336 * 2
def baseEnd_569336 : Nat := 129930231959239868436301

theorem tailTrace_569336 : CollatzResearch.WordTrace tailWord_569336 prefixEnd_569336 129930231959239868436301 := by
  unfold tailWord_569336
  simp only [CollatzResearch.WordTrace]
  refine ⟨10382694932700190846323931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13843593243600254461765241 10382694932700190846323931)
  ·
    refine ⟨15574042399050286269485897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10382694932700190846323931 15574042399050286269485897)
    ·
      refine ⟨11680531799287714702114423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15574042399050286269485897 11680531799287714702114423)
      ·
        refine ⟨17520797698931572053171635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11680531799287714702114423 17520797698931572053171635)
        ·
          refine ⟨26281196548397358079757453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17520797698931572053171635 26281196548397358079757453)
          ·
            refine ⟨9855448705649009279909045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26281196548397358079757453 9855448705649009279909045)
            ·
              refine ⟨923948316154594619991473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9855448705649009279909045 923948316154594619991473)
              ·
                refine ⟨692961237115945964993605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 923948316154594619991473 692961237115945964993605)
                ·
                  refine ⟨129930231959239868436301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 692961237115945964993605 129930231959239868436301)
                  ·
                    rfl

theorem cell21_569336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 4].length) (baseStart_569336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_569336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_569336 prefixEnd_569336 := by exact prefixLift 569336
  have htrace : WordTrace (prefixWord ++ tailWord_569336) baseStart_569336 baseEnd_569336 := by
    simpa [prefixWord, tailWord_569336, baseEnd_569336] using wordTrace_append hprefix tailTrace_569336
  have hstable : (prefixWord ++ tailWord_569336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569336).length < 2 ^ (prefixWord ++ tailWord_569336).sum := by decide
  have hdescent : baseEnd_569336 < baseStart_569336 := by decide
  rcases family_descends (prefixWord ++ tailWord_569336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569367 : List Nat := [1, 1, 3, 5, 2, 1, 1, 7]
def baseStart_569367 : Nat := 118140960795 + 569367 * 2 ^ 59
def prefixEnd_569367 : Nat := 4983230072969 + 3 ^ 40 * 569367 * 2
def baseEnd_569367 : Nat := 43312435527196901139857

theorem tailTrace_569367 : CollatzResearch.WordTrace tailWord_569367 prefixEnd_569367 43312435527196901139857 := by
  unfold tailWord_569367
  simp only [CollatzResearch.WordTrace]
  refine ⟨20766520528288073987026355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13844347018858715991350903 20766520528288073987026355)
  ·
    refine ⟨31149780792432110980539533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20766520528288073987026355 31149780792432110980539533)
    ·
      refine ⟨11681167797162041617702325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31149780792432110980539533 11681167797162041617702325)
      ·
        refine ⟨1095109480983941401659593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11681167797162041617702325 1095109480983941401659593)
        ·
          refine ⟨821332110737956051244695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1095109480983941401659593 821332110737956051244695)
          ·
            refine ⟨1231998166106934076867043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821332110737956051244695 1231998166106934076867043)
            ·
              refine ⟨1847997249160401115300565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1231998166106934076867043 1847997249160401115300565)
              ·
                refine ⟨43312435527196901139857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1847997249160401115300565 43312435527196901139857)
                ·
                  rfl

theorem cell21_569367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 7].length) (baseStart_569367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_569367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_569367 prefixEnd_569367 := by exact prefixLift 569367
  have htrace : WordTrace (prefixWord ++ tailWord_569367) baseStart_569367 baseEnd_569367 := by
    simpa [prefixWord, tailWord_569367, baseEnd_569367] using wordTrace_append hprefix tailTrace_569367
  have hstable : (prefixWord ++ tailWord_569367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569367).length < 2 ^ (prefixWord ++ tailWord_569367).sum := by decide
  have hdescent : baseEnd_569367 < baseStart_569367 := by decide
  rcases family_descends (prefixWord ++ tailWord_569367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569384 : List Nat := [2, 1, 5, 3, 1, 2, 7]
def baseStart_569384 : Nat := 118140960795 + 569384 * 2 ^ 59
def prefixEnd_569384 : Nat := 4983230072969 + 3 ^ 40 * 569384 * 2
def baseEnd_569384 : Nat := 14437909579244716848467

theorem tailTrace_569384 : CollatzResearch.WordTrace tailWord_569384 prefixEnd_569384 14437909579244716848467 := by
  unfold tailWord_569384
  simp only [CollatzResearch.WordTrace]
  refine ⟨10383570284613242945197603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13844760379484323926930137 10383570284613242945197603)
  ·
    refine ⟨15575355426919864417796405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10383570284613242945197603 15575355426919864417796405)
    ·
      refine ⟨1460189571273737289168413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15575355426919864417796405 1460189571273737289168413)
      ·
        refine ⟨547571089227651483438155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1460189571273737289168413 547571089227651483438155)
        ·
          refine ⟨821356633841477225157233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 547571089227651483438155 821356633841477225157233)
          ·
            refine ⟨616017475381107918867925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 821356633841477225157233 616017475381107918867925)
            ·
              refine ⟨14437909579244716848467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 616017475381107918867925 14437909579244716848467)
              ·
                rfl

theorem cell21_569384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 7].length) (baseStart_569384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_569384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_569384 prefixEnd_569384 := by exact prefixLift 569384
  have htrace : WordTrace (prefixWord ++ tailWord_569384) baseStart_569384 baseEnd_569384 := by
    simpa [prefixWord, tailWord_569384, baseEnd_569384] using wordTrace_append hprefix tailTrace_569384
  have hstable : (prefixWord ++ tailWord_569384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569384).length < 2 ^ (prefixWord ++ tailWord_569384).sum := by decide
  have hdescent : baseEnd_569384 < baseStart_569384 := by decide
  rcases family_descends (prefixWord ++ tailWord_569384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569395 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 6]
def baseStart_569395 : Nat := 118140960795 + 569395 * 2 ^ 59
def prefixEnd_569395 : Nat := 4983230072969 + 3 ^ 40 * 569395 * 2
def baseEnd_569395 : Nat := 129943696563068876952847

theorem tailTrace_569395 : CollatzResearch.WordTrace tailWord_569395 prefixEnd_569395 129943696563068876952847 := by
  unfold tailWord_569395
  simp only [CollatzResearch.WordTrace]
  refine ⟨20767541772186634769045639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13845027848124423179363759 20767541772186634769045639)
  ·
    refine ⟨31151312658279952153568459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20767541772186634769045639 31151312658279952153568459)
    ·
      refine ⟨46726968987419928230352689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31151312658279952153568459 46726968987419928230352689)
      ·
        refine ⟨35045226740564946172764517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46726968987419928230352689 35045226740564946172764517)
        ·
          refine ⟨6570980013855927407393347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35045226740564946172764517 6570980013855927407393347)
          ·
            refine ⟨9856470020783891111090021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6570980013855927407393347 9856470020783891111090021)
            ·
              refine ⟨1848088128896979583329379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9856470020783891111090021 1848088128896979583329379)
              ·
                refine ⟨2772132193345469374994069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1848088128896979583329379 2772132193345469374994069)
                ·
                  refine ⟨129943696563068876952847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2772132193345469374994069 129943696563068876952847)
                  ·
                    rfl

theorem cell21_569395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 6].length) (baseStart_569395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_569395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_569395 prefixEnd_569395 := by exact prefixLift 569395
  have htrace : WordTrace (prefixWord ++ tailWord_569395) baseStart_569395 baseEnd_569395 := by
    simpa [prefixWord, tailWord_569395, baseEnd_569395] using wordTrace_append hprefix tailTrace_569395
  have hstable : (prefixWord ++ tailWord_569395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569395).length < 2 ^ (prefixWord ++ tailWord_569395).sum := by decide
  have hdescent : baseEnd_569395 < baseStart_569395 := by decide
  rcases family_descends (prefixWord ++ tailWord_569395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569494 : List Nat := [5, 3, 2, 1, 1, 1, 8]
def baseStart_569494 : Nat := 118140960795 + 569494 * 2 ^ 59
def prefixEnd_569494 : Nat := 4983230072969 + 3 ^ 40 * 569494 * 2
def baseEnd_569494 : Nat := 14440698856874078311405

theorem tailTrace_569494 : CollatzResearch.WordTrace tailWord_569494 prefixEnd_569494 14440698856874078311405 := by
  unfold tailWord_569494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1298197037426748417306221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13847435065885316451266357 1298197037426748417306221)
  ·
    refine ⟨486823889035030656489833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1298197037426748417306221 486823889035030656489833)
    ·
      refine ⟨365117916776272992367375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 486823889035030656489833 365117916776272992367375)
      ·
        refine ⟨547676875164409488551063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365117916776272992367375 547676875164409488551063)
        ·
          refine ⟨821515312746614232826595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 547676875164409488551063 821515312746614232826595)
          ·
            refine ⟨1232272969119921349239893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821515312746614232826595 1232272969119921349239893)
            ·
              refine ⟨14440698856874078311405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1232272969119921349239893 14440698856874078311405)
              ·
                rfl

theorem cell21_569494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 8].length) (baseStart_569494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_569494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_569494 prefixEnd_569494 := by exact prefixLift 569494
  have htrace : WordTrace (prefixWord ++ tailWord_569494) baseStart_569494 baseEnd_569494 := by
    simpa [prefixWord, tailWord_569494, baseEnd_569494] using wordTrace_append hprefix tailTrace_569494
  have hstable : (prefixWord ++ tailWord_569494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569494).length < 2 ^ (prefixWord ++ tailWord_569494).sum := by decide
  have hdescent : baseEnd_569494 < baseStart_569494 := by decide
  rcases family_descends (prefixWord ++ tailWord_569494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569505 : List Nat := [1, 2, 3, 3, 1, 4, 1, 2, 4]
def baseStart_569505 : Nat := 118140960795 + 569505 * 2 ^ 59
def prefixEnd_569505 : Nat := 4983230072969 + 3 ^ 40 * 569505 * 2
def baseEnd_569505 : Nat := 129968800061733130119289

theorem tailTrace_569505 : CollatzResearch.WordTrace tailWord_569505 prefixEnd_569505 129968800061733130119289 := by
  unfold tailWord_569505
  simp only [CollatzResearch.WordTrace]
  refine ⟨20771553801788123555549969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13847702534525415703699979 20771553801788123555549969)
  ·
    refine ⟨15578665351341092666662477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20771553801788123555549969 15578665351341092666662477)
    ·
      refine ⟨5841999506752909749998429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15578665351341092666662477 5841999506752909749998429)
      ·
        refine ⟨2190749815032341156249411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5841999506752909749998429 2190749815032341156249411)
        ·
          refine ⟨3286124722548511734374117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2190749815032341156249411 3286124722548511734374117)
          ·
            refine ⟨616148385477845950195147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3286124722548511734374117 616148385477845950195147)
            ·
              refine ⟨924222578216768925292721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616148385477845950195147 924222578216768925292721)
              ·
                refine ⟨693166933662576693969541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 924222578216768925292721 693166933662576693969541)
                ·
                  refine ⟨129968800061733130119289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 693166933662576693969541 129968800061733130119289)
                  ·
                    rfl

theorem cell21_569505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 4].length) (baseStart_569505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_569505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_569505 prefixEnd_569505 := by exact prefixLift 569505
  have htrace : WordTrace (prefixWord ++ tailWord_569505) baseStart_569505 baseEnd_569505 := by
    simpa [prefixWord, tailWord_569505, baseEnd_569505] using wordTrace_append hprefix tailTrace_569505
  have hstable : (prefixWord ++ tailWord_569505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569505).length < 2 ^ (prefixWord ++ tailWord_569505).sum := by decide
  have hdescent : baseEnd_569505 < baseStart_569505 := by decide
  rcases family_descends (prefixWord ++ tailWord_569505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569561 : List Nat := [1, 2, 1, 2, 3, 1, 11]
def baseStart_569561 : Nat := 118140960795 + 569561 * 2 ^ 59
def prefixEnd_569561 : Nat := 4983230072969 + 3 ^ 40 * 569561 * 2
def baseEnd_569561 : Nat := 14442397780521053020649

theorem tailTrace_569561 : CollatzResearch.WordTrace tailWord_569561 prefixEnd_569561 14442397780521053020649 := by
  unfold tailWord_569561
  simp only [CollatzResearch.WordTrace]
  refine ⟨20773596289585245119588537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13849064193056830079725691 20773596289585245119588537)
  ·
    refine ⟨15580197217188933839691403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20773596289585245119588537 15580197217188933839691403)
    ·
      refine ⟨23370295825783400759537105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15580197217188933839691403 23370295825783400759537105)
      ·
        refine ⟨17527721869337550569652829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23370295825783400759537105 17527721869337550569652829)
        ·
          refine ⟨6572895701001581463619811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17527721869337550569652829 6572895701001581463619811)
          ·
            refine ⟨9859343551502372195429717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6572895701001581463619811 9859343551502372195429717)
            ·
              refine ⟨14442397780521053020649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9859343551502372195429717 14442397780521053020649)
              ·
                rfl

theorem cell21_569561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 11].length) (baseStart_569561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_569561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_569561 prefixEnd_569561 := by exact prefixLift 569561
  have htrace : WordTrace (prefixWord ++ tailWord_569561) baseStart_569561 baseEnd_569561 := by
    simpa [prefixWord, tailWord_569561, baseEnd_569561] using wordTrace_append hprefix tailTrace_569561
  have hstable : (prefixWord ++ tailWord_569561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569561).length < 2 ^ (prefixWord ++ tailWord_569561).sum := by decide
  have hdescent : baseEnd_569561 < baseStart_569561 := by decide
  rcases family_descends (prefixWord ++ tailWord_569561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569578 : List Nat := [3, 1, 3, 1, 1, 2, 4, 6]
def baseStart_569578 : Nat := 118140960795 + 569578 * 2 ^ 59
def prefixEnd_569578 : Nat := 4983230072969 + 3 ^ 40 * 569578 * 2
def baseEnd_569578 : Nat := 43328486552100408467491

theorem tailTrace_569578 : CollatzResearch.WordTrace tailWord_569578 prefixEnd_569578 43328486552100408467491 := by
  unfold tailWord_569578
  simp only [CollatzResearch.WordTrace]
  refine ⟨5193554082630914255739347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13849477553682438015304925 5193554082630914255739347)
  ·
    refine ⟨7790331123946371383609021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5193554082630914255739347 7790331123946371383609021)
    ·
      refine ⟨2921374171479889268853383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7790331123946371383609021 2921374171479889268853383)
      ·
        refine ⟨4382061257219833903280075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2921374171479889268853383 4382061257219833903280075)
        ·
          refine ⟨6573091885829750854920113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4382061257219833903280075 6573091885829750854920113)
          ·
            refine ⟨4929818914372313141190085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6573091885829750854920113 4929818914372313141190085)
            ·
              refine ⟨924341046444808713973141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4929818914372313141190085 924341046444808713973141)
              ·
                refine ⟨43328486552100408467491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 924341046444808713973141 43328486552100408467491)
                ·
                  rfl

theorem cell21_569578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_569578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_569578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_569578 prefixEnd_569578 := by exact prefixLift 569578
  have htrace : WordTrace (prefixWord ++ tailWord_569578) baseStart_569578 baseEnd_569578 := by
    simpa [prefixWord, tailWord_569578, baseEnd_569578] using wordTrace_append hprefix tailTrace_569578
  have hstable : (prefixWord ++ tailWord_569578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569578).length < 2 ^ (prefixWord ++ tailWord_569578).sum := by decide
  have hdescent : baseEnd_569578 < baseStart_569578 := by decide
  rcases family_descends (prefixWord ++ tailWord_569578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569581 : List Nat := [1, 5, 1, 2, 3, 1, 1, 3, 4]
def baseStart_569581 : Nat := 118140960795 + 569581 * 2 ^ 59
def prefixEnd_569581 : Nat := 4983230072969 + 3 ^ 40 * 569581 * 2
def baseEnd_569581 : Nat := 129986144297173886852467

theorem tailTrace_569581 : CollatzResearch.WordTrace tailWord_569581 prefixEnd_569581 129986144297173886852467 := by
  unfold tailWord_569581
  simp only [CollatzResearch.WordTrace]
  refine ⟨20774325749512788535316597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13849550499675192356877731 20774325749512788535316597)
  ·
    refine ⟨1947593039016823925185931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20774325749512788535316597 1947593039016823925185931)
    ·
      refine ⟨2921389558525235887778897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1947593039016823925185931 2921389558525235887778897)
      ·
        refine ⟨2191042168893926915834173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2921389558525235887778897 2191042168893926915834173)
        ·
          refine ⟨821640813335222593437815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2191042168893926915834173 821640813335222593437815)
          ·
            refine ⟨1232461220002833890156723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821640813335222593437815 1232461220002833890156723)
            ·
              refine ⟨1848691830004250835235085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1232461220002833890156723 1848691830004250835235085)
              ·
                refine ⟨693259436251594063213157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1848691830004250835235085 693259436251594063213157)
                ·
                  refine ⟨129986144297173886852467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 693259436251594063213157 129986144297173886852467)
                  ·
                    rfl

theorem cell21_569581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_569581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_569581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_569581 prefixEnd_569581 := by exact prefixLift 569581
  have htrace : WordTrace (prefixWord ++ tailWord_569581) baseStart_569581 baseEnd_569581 := by
    simpa [prefixWord, tailWord_569581, baseEnd_569581] using wordTrace_append hprefix tailTrace_569581
  have hstable : (prefixWord ++ tailWord_569581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569581).length < 2 ^ (prefixWord ++ tailWord_569581).sum := by decide
  have hdescent : baseEnd_569581 < baseStart_569581 := by decide
  rcases family_descends (prefixWord ++ tailWord_569581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569592 : List Nat := [2, 1, 2, 1, 1, 2, 1, 6, 5]
def baseStart_569592 : Nat := 118140960795 + 569592 * 2 ^ 59
def prefixEnd_569592 : Nat := 4983230072969 + 3 ^ 40 * 569592 * 2
def baseEnd_569592 : Nat := 129988654647040312169111

theorem tailTrace_569592 : CollatzResearch.WordTrace tailWord_569592 prefixEnd_569592 129988654647040312169111 := by
  unfold tailWord_569592
  simp only [CollatzResearch.WordTrace]
  refine ⟨10387363476236468706983515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13849817968315291609311353 10387363476236468706983515)
  ·
    refine ⟨15581045214354703060475273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10387363476236468706983515 15581045214354703060475273)
    ·
      refine ⟨11685783910766027295356455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15581045214354703060475273 11685783910766027295356455)
      ·
        refine ⟨17528675866149040943034683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11685783910766027295356455 17528675866149040943034683)
        ·
          refine ⟨26293013799223561414552025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17528675866149040943034683 26293013799223561414552025)
          ·
            refine ⟨19719760349417671060914019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26293013799223561414552025 19719760349417671060914019)
            ·
              refine ⟨29579640524126506591371029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19719760349417671060914019 29579640524126506591371029)
              ·
                refine ⟨1386545649568429996470517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29579640524126506591371029 1386545649568429996470517)
                ·
                  refine ⟨129988654647040312169111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1386545649568429996470517 129988654647040312169111)
                  ·
                    rfl

theorem cell21_569592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_569592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_569592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_569592 prefixEnd_569592 := by exact prefixLift 569592
  have htrace : WordTrace (prefixWord ++ tailWord_569592) baseStart_569592 baseEnd_569592 := by
    simpa [prefixWord, tailWord_569592, baseEnd_569592] using wordTrace_append hprefix tailTrace_569592
  have hstable : (prefixWord ++ tailWord_569592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569592).length < 2 ^ (prefixWord ++ tailWord_569592).sum := by decide
  have hdescent : baseEnd_569592 < baseStart_569592 := by decide
  rcases family_descends (prefixWord ++ tailWord_569592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569789 : List Nat := [1, 4, 1, 2, 2, 11]
def baseStart_569789 : Nat := 118140960795 + 569789 * 2 ^ 59
def prefixEnd_569789 : Nat := 4983230072969 + 3 ^ 40 * 569789 * 2
def baseEnd_569789 : Nat := 4816059730778212866125

theorem tailTrace_569789 : CollatzResearch.WordTrace tailWord_569789 prefixEnd_569789 4816059730778212866125 := by
  unfold tailWord_569789
  simp only [CollatzResearch.WordTrace]
  refine ⟨20781912132759240058888421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13854608088506160039258947 20781912132759240058888421)
  ·
    refine ⟨3896608524892357511041579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20781912132759240058888421 3896608524892357511041579)
    ·
      refine ⟨5844912787338536266562369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3896608524892357511041579 5844912787338536266562369)
      ·
        refine ⟨4383684590503902199921777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5844912787338536266562369 4383684590503902199921777)
        ·
          refine ⟨3287763442877926649941333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4383684590503902199921777 3287763442877926649941333)
          ·
            refine ⟨4816059730778212866125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3287763442877926649941333 4816059730778212866125)
            ·
              rfl

theorem cell21_569789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 11].length) (baseStart_569789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_569789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_569789 prefixEnd_569789 := by exact prefixLift 569789
  have htrace : WordTrace (prefixWord ++ tailWord_569789) baseStart_569789 baseEnd_569789 := by
    simpa [prefixWord, tailWord_569789, baseEnd_569789] using wordTrace_append hprefix tailTrace_569789
  have hstable : (prefixWord ++ tailWord_569789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569789).length < 2 ^ (prefixWord ++ tailWord_569789).sum := by decide
  have hdescent : baseEnd_569789 < baseStart_569789 := by decide
  rcases family_descends (prefixWord ++ tailWord_569789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569882 : List Nat := [3, 1, 1, 3, 1, 1, 6, 5]
def baseStart_569882 : Nat := 118140960795 + 569882 * 2 ^ 59
def prefixEnd_569882 : Nat := 4983230072969 + 3 ^ 40 * 569882 * 2
def baseEnd_569882 : Nat := 43351612199354750778395

theorem tailTrace_569882 : CollatzResearch.WordTrace tailWord_569882 prefixEnd_569882 43351612199354750778395 := by
  unfold tailWord_569882
  simp only [CollatzResearch.WordTrace]
  refine ⟨5196326030355579235505975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13856869414281544628015933 5196326030355579235505975)
  ·
    refine ⟨7794489045533368853258963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5196326030355579235505975 7794489045533368853258963)
    ·
      refine ⟨11691733568300053279888445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7794489045533368853258963 11691733568300053279888445)
      ·
        refine ⟨4384400088112519979958167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11691733568300053279888445 4384400088112519979958167)
        ·
          refine ⟨6576600132168779969937251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4384400088112519979958167 6576600132168779969937251)
          ·
            refine ⟨9864900198253169954905877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6576600132168779969937251 9864900198253169954905877)
            ·
              refine ⟨462417196793117341636213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9864900198253169954905877 462417196793117341636213)
              ·
                refine ⟨43351612199354750778395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 462417196793117341636213 43351612199354750778395)
                ·
                  rfl

theorem cell21_569882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_569882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_569882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_569882 prefixEnd_569882 := by exact prefixLift 569882
  have htrace : WordTrace (prefixWord ++ tailWord_569882) baseStart_569882 baseEnd_569882 := by
    simpa [prefixWord, tailWord_569882, baseEnd_569882] using wordTrace_append hprefix tailTrace_569882
  have hstable : (prefixWord ++ tailWord_569882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569882).length < 2 ^ (prefixWord ++ tailWord_569882).sum := by decide
  have hdescent : baseEnd_569882 < baseStart_569882 := by decide
  rcases family_descends (prefixWord ++ tailWord_569882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569888 : List Nat := [2, 1, 1, 6, 3, 1, 1, 3, 3]
def baseStart_569888 : Nat := 118140960795 + 569888 * 2 ^ 59
def prefixEnd_569888 : Nat := 4983230072969 + 3 ^ 40 * 569888 * 2
def baseEnd_569888 : Nat := 130056205879809575235173

theorem tailTrace_569888 : CollatzResearch.WordTrace tailWord_569888 prefixEnd_569888 130056205879809575235173 := by
  unfold tailWord_569888
  simp only [CollatzResearch.WordTrace]
  refine ⟨10392761479700289983371159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13857015306267053311161545 10392761479700289983371159)
  ·
    refine ⟨15589142219550434975056739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10392761479700289983371159 15589142219550434975056739)
    ·
      refine ⟨23383713329325652462585109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15589142219550434975056739 23383713329325652462585109)
      ·
        refine ⟨1096111562312139959183677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23383713329325652462585109 1096111562312139959183677)
        ·
          refine ⟨411041835867052484693879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1096111562312139959183677 411041835867052484693879)
          ·
            refine ⟨616562753800578727040819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411041835867052484693879 616562753800578727040819)
            ·
              refine ⟨924844130700868090561229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616562753800578727040819 924844130700868090561229)
              ·
                refine ⟨346816549012825533960461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 924844130700868090561229 346816549012825533960461)
                ·
                  refine ⟨130056205879809575235173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 346816549012825533960461 130056205879809575235173)
                  ·
                    rfl

theorem cell21_569888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 3].length) (baseStart_569888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_569888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_569888 prefixEnd_569888 := by exact prefixLift 569888
  have htrace : WordTrace (prefixWord ++ tailWord_569888) baseStart_569888 baseEnd_569888 := by
    simpa [prefixWord, tailWord_569888, baseEnd_569888] using wordTrace_append hprefix tailTrace_569888
  have hstable : (prefixWord ++ tailWord_569888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569888).length < 2 ^ (prefixWord ++ tailWord_569888).sum := by decide
  have hdescent : baseEnd_569888 < baseStart_569888 := by decide
  rcases family_descends (prefixWord ++ tailWord_569888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569941 : List Nat := [1, 3, 2, 2, 1, 1, 4, 7]
def baseStart_569941 : Nat := 118140960795 + 569941 * 2 ^ 59
def prefixEnd_569941 : Nat := 4983230072969 + 3 ^ 40 * 569941 * 2
def baseEnd_569941 : Nat := 43356100400631086950577

theorem tailTrace_569941 : CollatzResearch.WordTrace tailWord_569941 prefixEnd_569941 43356100400631086950577 := by
  unfold tailWord_569941
  simp only [CollatzResearch.WordTrace]
  refine ⟨20787456028208570018421677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13858304018805713345614451 20787456028208570018421677)
  ·
    refine ⟨7795296010578213756908129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20787456028208570018421677 7795296010578213756908129)
    ·
      refine ⟨5846472007933660317681097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7795296010578213756908129 5846472007933660317681097)
      ·
        refine ⟨4384854005950245238260823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5846472007933660317681097 4384854005950245238260823)
        ·
          refine ⟨6577281008925367857391235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4384854005950245238260823 6577281008925367857391235)
          ·
            refine ⟨9865921513388051786086853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6577281008925367857391235 9865921513388051786086853)
            ·
              refine ⟨1849860283760259709891285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9865921513388051786086853 1849860283760259709891285)
              ·
                refine ⟨43356100400631086950577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1849860283760259709891285 43356100400631086950577)
                ·
                  rfl

theorem cell21_569941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 7].length) (baseStart_569941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_569941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_569941 prefixEnd_569941 := by exact prefixLift 569941
  have htrace : WordTrace (prefixWord ++ tailWord_569941) baseStart_569941 baseEnd_569941 := by
    simpa [prefixWord, tailWord_569941, baseEnd_569941] using wordTrace_append hprefix tailTrace_569941
  have hstable : (prefixWord ++ tailWord_569941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569941).length < 2 ^ (prefixWord ++ tailWord_569941).sum := by decide
  have hdescent : baseEnd_569941 < baseStart_569941 := by decide
  rcases family_descends (prefixWord ++ tailWord_569941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570037 : List Nat := [1, 3, 3, 3, 1, 2, 3, 1, 4]
def baseStart_570037 : Nat := 118140960795 + 570037 * 2 ^ 59
def prefixEnd_570037 : Nat := 4983230072969 + 3 ^ 40 * 570037 * 2
def baseEnd_570037 : Nat := 130090209709818427251535

theorem tailTrace_570037 : CollatzResearch.WordTrace tailWord_570037 prefixEnd_570037 130090209709818427251535 := by
  unfold tailWord_570037
  simp only [CollatzResearch.WordTrace]
  refine ⟨20790957435860778413916365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13860638290573852275944243 20790957435860778413916365)
  ·
    refine ⟨7796609038447791905218637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20790957435860778413916365 7796609038447791905218637)
    ·
      refine ⟨2923728389417921964456989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7796609038447791905218637 2923728389417921964456989)
      ·
        refine ⟨1096398146031720736671371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2923728389417921964456989 1096398146031720736671371)
        ·
          refine ⟨1644597219047581105007057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1096398146031720736671371 1644597219047581105007057)
          ·
            refine ⟨1233447914285685828755293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1644597219047581105007057 1233447914285685828755293)
            ·
              refine ⟨462542967857132185783235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1233447914285685828755293 462542967857132185783235)
              ·
                refine ⟨693814451785698278674853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462542967857132185783235 693814451785698278674853)
                ·
                  refine ⟨130090209709818427251535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 693814451785698278674853 130090209709818427251535)
                  ·
                    rfl

theorem cell21_570037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_570037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570037 prefixEnd_570037 := by exact prefixLift 570037
  have htrace : WordTrace (prefixWord ++ tailWord_570037) baseStart_570037 baseEnd_570037 := by
    simpa [prefixWord, tailWord_570037, baseEnd_570037] using wordTrace_append hprefix tailTrace_570037
  have hstable : (prefixWord ++ tailWord_570037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570037).length < 2 ^ (prefixWord ++ tailWord_570037).sum := by decide
  have hdescent : baseEnd_570037 < baseStart_570037 := by decide
  rcases family_descends (prefixWord ++ tailWord_570037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570048 : List Nat := [2, 1, 1, 2, 4, 2, 2, 2, 5]
def baseStart_570048 : Nat := 118140960795 + 570048 * 2 ^ 59
def prefixEnd_570048 : Nat := 4983230072969 + 3 ^ 40 * 570048 * 2
def baseEnd_570048 : Nat := 130092720059684852568179

theorem tailTrace_570048 : CollatzResearch.WordTrace tailWord_570048 prefixEnd_570048 130092720059684852568179 := by
  unfold tailWord_570048
  simp only [CollatzResearch.WordTrace]
  refine ⟨10395679319410463646283399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13860905759213951528377865 10395679319410463646283399)
  ·
    refine ⟨15593518979115695469425099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10395679319410463646283399 15593518979115695469425099)
    ·
      refine ⟨23390278468673543204137649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15593518979115695469425099 23390278468673543204137649)
      ·
        refine ⟨17542708851505157403103237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23390278468673543204137649 17542708851505157403103237)
        ·
          refine ⟨3289257909657217013081857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17542708851505157403103237 3289257909657217013081857)
          ·
            refine ⟨2466943432242912759811393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3289257909657217013081857 2466943432242912759811393)
            ·
              refine ⟨1850207574182184569858545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2466943432242912759811393 1850207574182184569858545)
              ·
                refine ⟨1387655680636638427393909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1850207574182184569858545 1387655680636638427393909)
                ·
                  refine ⟨130092720059684852568179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1387655680636638427393909 130092720059684852568179)
                  ·
                    rfl

theorem cell21_570048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_570048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570048 prefixEnd_570048 := by exact prefixLift 570048
  have htrace : WordTrace (prefixWord ++ tailWord_570048) baseStart_570048 baseEnd_570048 := by
    simpa [prefixWord, tailWord_570048, baseEnd_570048] using wordTrace_append hprefix tailTrace_570048
  have hstable : (prefixWord ++ tailWord_570048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570048).length < 2 ^ (prefixWord ++ tailWord_570048).sum := by decide
  have hdescent : baseEnd_570048 < baseStart_570048 := by decide
  rcases family_descends (prefixWord ++ tailWord_570048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570110 : List Nat := [4, 2, 2, 1, 2, 1, 2, 7]
def baseStart_570110 : Nat := 118140960795 + 570110 * 2 ^ 59
def prefixEnd_570110 : Nat := 4983230072969 + 3 ^ 40 * 570110 * 2
def baseEnd_570110 : Nat := 43368956434795507511573

theorem tailTrace_570110 : CollatzResearch.WordTrace tailWord_570110 prefixEnd_570110 43368956434795507511573 := by
  unfold tailWord_570110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2599202495574538985165473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13862413309730874587549189 2599202495574538985165473)
  ·
    refine ⟨1949401871680904238874105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2599202495574538985165473 1949401871680904238874105)
    ·
      refine ⟨1462051403760678179155579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1949401871680904238874105 1462051403760678179155579)
      ·
        refine ⟨2193077105641017268733369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1462051403760678179155579 2193077105641017268733369)
        ·
          refine ⟨1644807829230762951550027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2193077105641017268733369 1644807829230762951550027)
          ·
            refine ⟨2467211743846144427325041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1644807829230762951550027 2467211743846144427325041)
            ·
              refine ⟨1850408807884608320493781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2467211743846144427325041 1850408807884608320493781)
              ·
                refine ⟨43368956434795507511573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1850408807884608320493781 43368956434795507511573)
                ·
                  rfl

theorem cell21_570110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_570110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570110 prefixEnd_570110 := by exact prefixLift 570110
  have htrace : WordTrace (prefixWord ++ tailWord_570110) baseStart_570110 baseEnd_570110 := by
    simpa [prefixWord, tailWord_570110, baseEnd_570110] using wordTrace_append hprefix tailTrace_570110
  have hstable : (prefixWord ++ tailWord_570110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570110).length < 2 ^ (prefixWord ++ tailWord_570110).sum := by decide
  have hdescent : baseEnd_570110 < baseStart_570110 := by decide
  rcases family_descends (prefixWord ++ tailWord_570110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570183 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 9]
def baseStart_570183 : Nat := 118140960795 + 570183 * 2 ^ 59
def prefixEnd_570183 : Nat := 4983230072969 + 3 ^ 40 * 570183 * 2
def baseEnd_570183 : Nat := 130123528898954617817903

theorem tailTrace_570183 : CollatzResearch.WordTrace tailWord_570183 prefixEnd_570183 130123528898954617817903 := by
  unfold tailWord_570183
  simp only [CollatzResearch.WordTrace]
  refine ⟨20796282493331845348731203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13864188328887896899154135 20796282493331845348731203)
  ·
    refine ⟨31194423739997768023096805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20796282493331845348731203 31194423739997768023096805)
    ·
      refine ⟨5848954451249581504330651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31194423739997768023096805 5848954451249581504330651)
      ·
        refine ⟨8773431676874372256495977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5848954451249581504330651 8773431676874372256495977)
        ·
          refine ⟨6580073757655779192371983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8773431676874372256495977 6580073757655779192371983)
          ·
            refine ⟨9870110636483668788557975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6580073757655779192371983 9870110636483668788557975)
            ·
              refine ⟨14805165954725503182836963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9870110636483668788557975 14805165954725503182836963)
              ·
                refine ⟨22207748932088254774255445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14805165954725503182836963 22207748932088254774255445)
                ·
                  refine ⟨130123528898954617817903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22207748932088254774255445 130123528898954617817903)
                  ·
                    rfl

theorem cell21_570183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 9].length) (baseStart_570183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570183 prefixEnd_570183 := by exact prefixLift 570183
  have htrace : WordTrace (prefixWord ++ tailWord_570183) baseStart_570183 baseEnd_570183 := by
    simpa [prefixWord, tailWord_570183, baseEnd_570183] using wordTrace_append hprefix tailTrace_570183
  have hstable : (prefixWord ++ tailWord_570183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570183).length < 2 ^ (prefixWord ++ tailWord_570183).sum := by decide
  have hdescent : baseEnd_570183 < baseStart_570183 := by decide
  rcases family_descends (prefixWord ++ tailWord_570183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570245 : List Nat := [1, 3, 1, 1, 3, 5, 7]
def baseStart_570245 : Nat := 118140960795 + 570245 * 2 ^ 59
def prefixEnd_570245 : Nat := 4983230072969 + 3 ^ 40 * 570245 * 2
def baseEnd_570245 : Nat := 14459742015961809753827

theorem tailTrace_570245 : CollatzResearch.WordTrace tailWord_570245 prefixEnd_570245 14459742015961809753827 := by
  unfold tailWord_570245
  simp only [CollatzResearch.WordTrace]
  refine ⟨20798543819107229937488189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13865695879404819958325459 20798543819107229937488189)
  ·
    refine ⟨7799453932165211226558071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20798543819107229937488189 7799453932165211226558071)
    ·
      refine ⟨11699180898247816839837107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7799453932165211226558071 11699180898247816839837107)
      ·
        refine ⟨17548771347371725259755661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11699180898247816839837107 17548771347371725259755661)
        ·
          refine ⟨6580789255264396972408373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17548771347371725259755661 6580789255264396972408373)
          ·
            refine ⟨616948992681037216163285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6580789255264396972408373 616948992681037216163285)
            ·
              refine ⟨14459742015961809753827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 616948992681037216163285 14459742015961809753827)
              ·
                rfl

theorem cell21_570245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 7].length) (baseStart_570245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570245 prefixEnd_570245 := by exact prefixLift 570245
  have htrace : WordTrace (prefixWord ++ tailWord_570245) baseStart_570245 baseEnd_570245 := by
    simpa [prefixWord, tailWord_570245, baseEnd_570245] using wordTrace_append hprefix tailTrace_570245
  have hstable : (prefixWord ++ tailWord_570245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570245).length < 2 ^ (prefixWord ++ tailWord_570245).sum := by decide
  have hdescent : baseEnd_570245 < baseStart_570245 := by decide
  rcases family_descends (prefixWord ++ tailWord_570245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570259 : List Nat := [1, 1, 1, 2, 1, 2, 1, 7, 5]
def baseStart_570259 : Nat := 118140960795 + 570259 * 2 ^ 59
def prefixEnd_570259 : Nat := 4983230072969 + 3 ^ 40 * 570259 * 2
def baseEnd_570259 : Nat := 130140873134395374551081

theorem tailTrace_570259 : CollatzResearch.WordTrace tailWord_570259 prefixEnd_570259 130140873134395374551081 := by
  unfold tailWord_570259
  simp only [CollatzResearch.WordTrace]
  refine ⟨20799054441056510328497831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13866036294037673552331887 20799054441056510328497831)
  ·
    refine ⟨31198581661584765492746747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20799054441056510328497831 31198581661584765492746747)
    ·
      refine ⟨46797872492377148239120121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31198581661584765492746747 46797872492377148239120121)
      ·
        refine ⟨35098404369282861179340091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46797872492377148239120121 35098404369282861179340091)
        ·
          refine ⟨52647606553924291769010137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35098404369282861179340091 52647606553924291769010137)
          ·
            refine ⟨39485704915443218826757603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52647606553924291769010137 39485704915443218826757603)
            ·
              refine ⟨59228557373164828240136405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39485704915443218826757603 59228557373164828240136405)
              ·
                refine ⟨1388169313433550661878197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 59228557373164828240136405 1388169313433550661878197)
                ·
                  refine ⟨130140873134395374551081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1388169313433550661878197 130140873134395374551081)
                  ·
                    rfl

theorem cell21_570259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 5].length) (baseStart_570259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570259 prefixEnd_570259 := by exact prefixLift 570259
  have htrace : WordTrace (prefixWord ++ tailWord_570259) baseStart_570259 baseEnd_570259 := by
    simpa [prefixWord, tailWord_570259, baseEnd_570259] using wordTrace_append hprefix tailTrace_570259
  have hstable : (prefixWord ++ tailWord_570259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570259).length < 2 ^ (prefixWord ++ tailWord_570259).sum := by decide
  have hdescent : baseEnd_570259 < baseStart_570259 := by decide
  rcases family_descends (prefixWord ++ tailWord_570259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570293 : List Nat := [1, 3, 3, 2, 1, 1, 2, 5, 3]
def baseStart_570293 : Nat := 118140960795 + 570293 * 2 ^ 59
def prefixEnd_570293 : Nat := 4983230072969 + 3 ^ 40 * 570293 * 2
def baseEnd_570293 : Nat := 130148632397618870984345

theorem tailTrace_570293 : CollatzResearch.WordTrace tailWord_570293 prefixEnd_570293 130148632397618870984345 := by
  unfold tailWord_570293
  simp only [CollatzResearch.WordTrace]
  refine ⟨20800294522933334135235533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13866863015288889423490355 20800294522933334135235533)
  ·
    refine ⟨7800110446100000300713325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20800294522933334135235533 7800110446100000300713325)
    ·
      refine ⟨2925041417287500112767497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7800110446100000300713325 2925041417287500112767497)
      ·
        refine ⟨2193781062965625084575623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2925041417287500112767497 2193781062965625084575623)
        ·
          refine ⟨3290671594448437626863435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2193781062965625084575623 3290671594448437626863435)
          ·
            refine ⟨4936007391672656440295153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3290671594448437626863435 4936007391672656440295153)
            ·
              refine ⟨3702005543754492330221365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4936007391672656440295153 3702005543754492330221365)
              ·
                refine ⟨347063019726983655958253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3702005543754492330221365 347063019726983655958253)
                ·
                  refine ⟨130148632397618870984345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 347063019726983655958253 130148632397618870984345)
                  ·
                    rfl

theorem cell21_570293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_570293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570293 prefixEnd_570293 := by exact prefixLift 570293
  have htrace : WordTrace (prefixWord ++ tailWord_570293) baseStart_570293 baseEnd_570293 := by
    simpa [prefixWord, tailWord_570293, baseEnd_570293] using wordTrace_append hprefix tailTrace_570293
  have hstable : (prefixWord ++ tailWord_570293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570293).length < 2 ^ (prefixWord ++ tailWord_570293).sum := by decide
  have hdescent : baseEnd_570293 < baseStart_570293 := by decide
  rcases family_descends (prefixWord ++ tailWord_570293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570304 : List Nat := [2, 1, 1, 2, 3, 12]
def baseStart_570304 : Nat := 118140960795 + 570304 * 2 ^ 59
def prefixEnd_570304 : Nat := 4983230072969 + 3 ^ 40 * 570304 * 2
def baseEnd_570304 : Nat := 4820412694351307270407

theorem tailTrace_570304 : CollatzResearch.WordTrace tailWord_570304 prefixEnd_570304 4820412694351307270407 := by
  unfold tailWord_570304
  simp only [CollatzResearch.WordTrace]
  refine ⟨10400347862946741506942983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13867130483928988675923977 10400347862946741506942983)
  ·
    refine ⟨15600521794420112260414475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10400347862946741506942983 15600521794420112260414475)
    ·
      refine ⟨23400782691630168390621713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15600521794420112260414475 23400782691630168390621713)
      ·
        refine ⟨17550587018722626292966285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23400782691630168390621713 17550587018722626292966285)
        ·
          refine ⟨6581470132020984859862357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17550587018722626292966285 6581470132020984859862357)
          ·
            refine ⟨4820412694351307270407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 6581470132020984859862357 4820412694351307270407)
            ·
              rfl

theorem cell21_570304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 12].length) (baseStart_570304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570304 prefixEnd_570304 := by exact prefixLift 570304
  have htrace : WordTrace (prefixWord ++ tailWord_570304) baseStart_570304 baseEnd_570304 := by
    simpa [prefixWord, tailWord_570304, baseEnd_570304] using wordTrace_append hprefix tailTrace_570304
  have hstable : (prefixWord ++ tailWord_570304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570304).length < 2 ^ (prefixWord ++ tailWord_570304).sum := by decide
  have hdescent : baseEnd_570304 < baseStart_570304 := by decide
  rcases family_descends (prefixWord ++ tailWord_570304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570369 : List Nat := [1, 2, 4, 1, 2, 2, 2, 4, 3]
def baseStart_570369 : Nat := 118140960795 + 570369 * 2 ^ 59
def prefixEnd_570369 : Nat := 4983230072969 + 3 ^ 40 * 570369 * 2
def baseEnd_570369 : Nat := 130165976633059627717523

theorem tailTrace_570369 : CollatzResearch.WordTrace tailWord_570369 prefixEnd_570369 130165976633059627717523 := by
  unfold tailWord_570369
  simp only [CollatzResearch.WordTrace]
  refine ⟨20803066470657999115002161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13868710980438666076668107 20803066470657999115002161)
  ·
    refine ⟨15602299852993499336251621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20803066470657999115002161 15602299852993499336251621)
    ·
      refine ⟨2925431222436281125547179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15602299852993499336251621 2925431222436281125547179)
      ·
        refine ⟨4388146833654421688320769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2925431222436281125547179 4388146833654421688320769)
        ·
          refine ⟨3291110125240816266240577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4388146833654421688320769 3291110125240816266240577)
          ·
            refine ⟨2468332593930612199680433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3291110125240816266240577 2468332593930612199680433)
            ·
              refine ⟨1851249445447959149760325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2468332593930612199680433 1851249445447959149760325)
              ·
                refine ⟨347109271021492340580061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1851249445447959149760325 347109271021492340580061)
                ·
                  refine ⟨130165976633059627717523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 347109271021492340580061 130165976633059627717523)
                  ·
                    rfl

theorem cell21_570369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 3].length) (baseStart_570369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570369 prefixEnd_570369 := by exact prefixLift 570369
  have htrace : WordTrace (prefixWord ++ tailWord_570369) baseStart_570369 baseEnd_570369 := by
    simpa [prefixWord, tailWord_570369, baseEnd_570369] using wordTrace_append hprefix tailTrace_570369
  have hstable : (prefixWord ++ tailWord_570369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570369).length < 2 ^ (prefixWord ++ tailWord_570369).sum := by decide
  have hdescent : baseEnd_570369 < baseStart_570369 := by decide
  rcases family_descends (prefixWord ++ tailWord_570369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570428 : List Nat := [2, 2, 2, 2, 2, 2, 3, 1, 5]
def baseStart_570428 : Nat := 118140960795 + 570428 * 2 ^ 59
def prefixEnd_570428 : Nat := 4983230072969 + 3 ^ 40 * 570428 * 2
def baseEnd_570428 : Nat := 130179441236888636234069

theorem tailTrace_570428 : CollatzResearch.WordTrace tailWord_570428 prefixEnd_570428 130179441236888636234069 := by
  unfold tailWord_570428
  simp only [CollatzResearch.WordTrace]
  refine ⟨10402609188722126095699969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13870145584962834794266625 10402609188722126095699969)
  ·
    refine ⟨7801956891541594571774977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10402609188722126095699969 7801956891541594571774977)
    ·
      refine ⟨5851467668656195928831233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7801956891541594571774977 5851467668656195928831233)
      ·
        refine ⟨4388600751492146946623425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5851467668656195928831233 4388600751492146946623425)
        ·
          refine ⟨3291450563619110209967569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4388600751492146946623425 3291450563619110209967569)
          ·
            refine ⟨2468587922714332657475677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3291450563619110209967569 2468587922714332657475677)
            ·
              refine ⟨925720471017874746553379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2468587922714332657475677 925720471017874746553379)
              ·
                refine ⟨1388580706526812119830069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 925720471017874746553379 1388580706526812119830069)
                ·
                  refine ⟨130179441236888636234069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1388580706526812119830069 130179441236888636234069)
                  ·
                    rfl

theorem cell21_570428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_570428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570428 prefixEnd_570428 := by exact prefixLift 570428
  have htrace : WordTrace (prefixWord ++ tailWord_570428) baseStart_570428 baseEnd_570428 := by
    simpa [prefixWord, tailWord_570428, baseEnd_570428] using wordTrace_append hprefix tailTrace_570428
  have hstable : (prefixWord ++ tailWord_570428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570428).length < 2 ^ (prefixWord ++ tailWord_570428).sum := by decide
  have hdescent : baseEnd_570428 < baseStart_570428 := by decide
  rcases family_descends (prefixWord ++ tailWord_570428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570456 : List Nat := [2, 1, 2, 2, 1, 3, 1, 9]
def baseStart_570456 : Nat := 118140960795 + 570456 * 2 ^ 59
def prefixEnd_570456 : Nat := 4983230072969 + 3 ^ 40 * 570456 * 2
def baseEnd_570456 : Nat := 43395277072788936589115

theorem tailTrace_570456 : CollatzResearch.WordTrace tailWord_570456 prefixEnd_570456 43395277072788936589115 := by
  unfold tailWord_570456
  simp only [CollatzResearch.WordTrace]
  refine ⟨10403119810671406486709611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13870826414228541982279481 10403119810671406486709611)
  ·
    refine ⟨15604679716007109730064417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10403119810671406486709611 15604679716007109730064417)
    ·
      refine ⟨11703509787005332297548313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15604679716007109730064417 11703509787005332297548313)
      ·
        refine ⟨8777632340253999223161235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11703509787005332297548313 8777632340253999223161235)
        ·
          refine ⟨13166448510380998834741853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8777632340253999223161235 13166448510380998834741853)
          ·
            refine ⟨4937418191392874563028195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13166448510380998834741853 4937418191392874563028195)
            ·
              refine ⟨7406127287089311844542293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4937418191392874563028195 7406127287089311844542293)
              ·
                refine ⟨43395277072788936589115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7406127287089311844542293 43395277072788936589115)
                ·
                  rfl

theorem cell21_570456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 9].length) (baseStart_570456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570456 prefixEnd_570456 := by exact prefixLift 570456
  have htrace : WordTrace (prefixWord ++ tailWord_570456) baseStart_570456 baseEnd_570456 := by
    simpa [prefixWord, tailWord_570456, baseEnd_570456] using wordTrace_append hprefix tailTrace_570456
  have hstable : (prefixWord ++ tailWord_570456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570456).length < 2 ^ (prefixWord ++ tailWord_570456).sum := by decide
  have hdescent : baseEnd_570456 < baseStart_570456 := by decide
  rcases family_descends (prefixWord ++ tailWord_570456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570487 : List Nat := [1, 1, 3, 1, 1, 4, 2, 3, 5]
def baseStart_570487 : Nat := 118140960795 + 570487 * 2 ^ 59
def prefixEnd_570487 : Nat := 4983230072969 + 3 ^ 40 * 570487 * 2
def baseEnd_570487 : Nat := 130192905840717644750615

theorem tailTrace_570487 : CollatzResearch.WordTrace tailWord_570487 prefixEnd_570487 130192905840717644750615 := by
  unfold tailWord_570487
  simp only [CollatzResearch.WordTrace]
  refine ⟨20807370284230505267797715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13871580189487003511865143 20807370284230505267797715)
  ·
    refine ⟨31211055426345757901696573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20807370284230505267797715 31211055426345757901696573)
    ·
      refine ⟨11704145784879659213136215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31211055426345757901696573 11704145784879659213136215)
      ·
        refine ⟨17556218677319488819704323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11704145784879659213136215 17556218677319488819704323)
        ·
          refine ⟨26334328015979233229556485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17556218677319488819704323 26334328015979233229556485)
          ·
            refine ⟨4937686502996106230541841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26334328015979233229556485 4937686502996106230541841)
            ·
              refine ⟨3703264877247079672906381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4937686502996106230541841 3703264877247079672906381)
              ·
                refine ⟨1388724328967654877339893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3703264877247079672906381 1388724328967654877339893)
                ·
                  refine ⟨130192905840717644750615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1388724328967654877339893 130192905840717644750615)
                  ·
                    rfl

theorem cell21_570487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 5].length) (baseStart_570487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570487 prefixEnd_570487 := by exact prefixLift 570487
  have htrace : WordTrace (prefixWord ++ tailWord_570487) baseStart_570487 baseEnd_570487 := by
    simpa [prefixWord, tailWord_570487, baseEnd_570487] using wordTrace_append hprefix tailTrace_570487
  have hstable : (prefixWord ++ tailWord_570487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570487).length < 2 ^ (prefixWord ++ tailWord_570487).sum := by decide
  have hdescent : baseEnd_570487 < baseStart_570487 := by decide
  rcases family_descends (prefixWord ++ tailWord_570487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570535 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 6]
def baseStart_570535 : Nat := 118140960795 + 570535 * 2 ^ 59
def prefixEnd_570535 : Nat := 4983230072969 + 3 ^ 40 * 570535 * 2
def baseEnd_570535 : Nat := 130203860094680227950517

theorem tailTrace_570535 : CollatzResearch.WordTrace tailWord_570535 prefixEnd_570535 130203860094680227950517 := by
  unfold tailWord_570535
  simp only [CollatzResearch.WordTrace]
  refine ⟨20809120988056609465545059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13872747325371072977030039 20809120988056609465545059)
  ·
    refine ⟨31213681482084914198317589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20809120988056609465545059 31213681482084914198317589)
    ·
      refine ⟨1463141319472730353046137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31213681482084914198317589 1463141319472730353046137)
      ·
        refine ⟨1097355989604547764784603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1463141319472730353046137 1097355989604547764784603)
        ·
          refine ⟨1646033984406821647176905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1097355989604547764784603 1646033984406821647176905)
          ·
            refine ⟨1234525488305116235382679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1646033984406821647176905 1234525488305116235382679)
            ·
              refine ⟨1851788232457674353074019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1234525488305116235382679 1851788232457674353074019)
              ·
                refine ⟨2777682348686511529611029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1851788232457674353074019 2777682348686511529611029)
                ·
                  refine ⟨130203860094680227950517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2777682348686511529611029 130203860094680227950517)
                  ·
                    rfl

theorem cell21_570535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 6].length) (baseStart_570535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570535 prefixEnd_570535 := by exact prefixLift 570535
  have htrace : WordTrace (prefixWord ++ tailWord_570535) baseStart_570535 baseEnd_570535 := by
    simpa [prefixWord, tailWord_570535, baseEnd_570535] using wordTrace_append hprefix tailTrace_570535
  have hstable : (prefixWord ++ tailWord_570535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570535).length < 2 ^ (prefixWord ++ tailWord_570535).sum := by decide
  have hdescent : baseEnd_570535 < baseStart_570535 := by decide
  rcases family_descends (prefixWord ++ tailWord_570535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570538 : List Nat := [3, 1, 5, 1, 1, 1, 2, 4, 3]
def baseStart_570538 : Nat := 118140960795 + 570538 * 2 ^ 59
def prefixEnd_570538 : Nat := 4983230072969 + 3 ^ 40 * 570538 * 2
def baseEnd_570538 : Nat := 130204544735552889400511

theorem tailTrace_570538 : CollatzResearch.WordTrace tailWord_570538 prefixEnd_570538 130204544735552889400511 := by
  unfold tailWord_570538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5202307601761435244476067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13872820271363827318602845 5202307601761435244476067)
  ·
    refine ⟨7803461402642152866714101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5202307601761435244476067 7803461402642152866714101)
    ·
      refine ⟨731574506497701831254447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7803461402642152866714101 731574506497701831254447)
      ·
        refine ⟨1097361759746552746881671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 731574506497701831254447 1097361759746552746881671)
        ·
          refine ⟨1646042639619829120322507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1097361759746552746881671 1646042639619829120322507)
          ·
            refine ⟨2469063959429743680483761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1646042639619829120322507 2469063959429743680483761)
            ·
              refine ⟨1851797969572307760362821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2469063959429743680483761 1851797969572307760362821)
              ·
                refine ⟨347212119294807705068029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1851797969572307760362821 347212119294807705068029)
                ·
                  refine ⟨130204544735552889400511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 347212119294807705068029 130204544735552889400511)
                  ·
                    rfl

theorem cell21_570538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_570538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570538 prefixEnd_570538 := by exact prefixLift 570538
  have htrace : WordTrace (prefixWord ++ tailWord_570538) baseStart_570538 baseEnd_570538 := by
    simpa [prefixWord, tailWord_570538, baseEnd_570538] using wordTrace_append hprefix tailTrace_570538
  have hstable : (prefixWord ++ tailWord_570538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570538).length < 2 ^ (prefixWord ++ tailWord_570538).sum := by decide
  have hdescent : baseEnd_570538 < baseStart_570538 := by decide
  rcases family_descends (prefixWord ++ tailWord_570538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570597 : List Nat := [1, 3, 1, 4, 3, 2, 1, 1, 5]
def baseStart_570597 : Nat := 118140960795 + 570597 * 2 ^ 59
def prefixEnd_570597 : Nat := 4983230072969 + 3 ^ 40 * 570597 * 2
def baseEnd_570597 : Nat := 130218009339381897917057

theorem tailTrace_570597 : CollatzResearch.WordTrace tailWord_570597 prefixEnd_570597 130218009339381897917057 := by
  unfold tailWord_570597
  simp only [CollatzResearch.WordTrace]
  refine ⟨20811382313831994054302045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13874254875887996036201363 20811382313831994054302045)
  ·
    refine ⟨7804268367686997770363267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20811382313831994054302045 7804268367686997770363267)
    ·
      refine ⟨11706402551530496655544901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7804268367686997770363267 11706402551530496655544901)
      ·
        refine ⟨2194950478411968122914669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11706402551530496655544901 2194950478411968122914669)
        ·
          refine ⟨823106429404488046093001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2194950478411968122914669 823106429404488046093001)
          ·
            refine ⟨617329822053366034569751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 823106429404488046093001 617329822053366034569751)
            ·
              refine ⟨925994733080049051854627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 617329822053366034569751 925994733080049051854627)
              ·
                refine ⟨1388992099620073577781941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 925994733080049051854627 1388992099620073577781941)
                ·
                  refine ⟨130218009339381897917057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1388992099620073577781941 130218009339381897917057)
                  ·
                    rfl

theorem cell21_570597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_570597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570597 prefixEnd_570597 := by exact prefixLift 570597
  have htrace : WordTrace (prefixWord ++ tailWord_570597) baseStart_570597 baseEnd_570597 := by
    simpa [prefixWord, tailWord_570597, baseEnd_570597] using wordTrace_append hprefix tailTrace_570597
  have hstable : (prefixWord ++ tailWord_570597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570597).length < 2 ^ (prefixWord ++ tailWord_570597).sum := by decide
  have hdescent : baseEnd_570597 < baseStart_570597 := by decide
  rcases family_descends (prefixWord ++ tailWord_570597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570611 : List Nat := [1, 1, 1, 2, 2, 5, 4, 1, 4]
def baseStart_570611 : Nat := 118140960795 + 570611 * 2 ^ 59
def prefixEnd_570611 : Nat := 4983230072969 + 3 ^ 40 * 570611 * 2
def baseEnd_570611 : Nat := 130221204330120984683695

theorem tailTrace_570611 : CollatzResearch.WordTrace tailWord_570611 prefixEnd_570611 130221204330120984683695 := by
  unfold tailWord_570611
  simp only [CollatzResearch.WordTrace]
  refine ⟨20811892935781274445311687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13874595290520849630207791 20811892935781274445311687)
  ·
    refine ⟨31217839403671911667967531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20811892935781274445311687 31217839403671911667967531)
    ·
      refine ⟨46826759105507867501951297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31217839403671911667967531 46826759105507867501951297)
      ·
        refine ⟨35120069329130900626463473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46826759105507867501951297 35120069329130900626463473)
        ·
          refine ⟨26340051996848175469847605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35120069329130900626463473 26340051996848175469847605)
          ·
            refine ⟨2469379874704516450298213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26340051996848175469847605 2469379874704516450298213)
            ·
              refine ⟨463008726507096834430915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2469379874704516450298213 463008726507096834430915)
              ·
                refine ⟨694513089760645251646373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463008726507096834430915 694513089760645251646373)
                ·
                  refine ⟨130221204330120984683695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 694513089760645251646373 130221204330120984683695)
                  ·
                    rfl

theorem cell21_570611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 4].length) (baseStart_570611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570611 prefixEnd_570611 := by exact prefixLift 570611
  have htrace : WordTrace (prefixWord ++ tailWord_570611) baseStart_570611 baseEnd_570611 := by
    simpa [prefixWord, tailWord_570611, baseEnd_570611] using wordTrace_append hprefix tailTrace_570611
  have hstable : (prefixWord ++ tailWord_570611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570611).length < 2 ^ (prefixWord ++ tailWord_570611).sum := by decide
  have hdescent : baseEnd_570611 < baseStart_570611 := by decide
  rcases family_descends (prefixWord ++ tailWord_570611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570642 : List Nat := [3, 2, 4, 2, 1, 9]
def baseStart_570642 : Nat := 118140960795 + 570642 * 2 ^ 59
def prefixEnd_570642 : Nat := 4983230072969 + 3 ^ 40 * 570642 * 2
def baseEnd_570642 : Nat := 4823269590832289617295

theorem tailTrace_570642 : CollatzResearch.WordTrace tailWord_570642 prefixEnd_570642 4823269590832289617295 := by
  unfold tailWord_570642
  simp only [CollatzResearch.WordTrace]
  refine ⟨5203255899667241684922545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13875349065779311159793453 5203255899667241684922545)
  ·
    refine ⟨3902441924750431263691909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5203255899667241684922545 3902441924750431263691909)
    ·
      refine ⟨731707860890705861942233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3902441924750431263691909 731707860890705861942233)
      ·
        refine ⟨548780895668029396456675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 731707860890705861942233 548780895668029396456675)
        ·
          refine ⟨823171343502044094685013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548780895668029396456675 823171343502044094685013)
          ·
            refine ⟨4823269590832289617295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 823171343502044094685013 4823269590832289617295)
            ·
              rfl

theorem cell21_570642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 9].length) (baseStart_570642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570642 prefixEnd_570642 := by exact prefixLift 570642
  have htrace : WordTrace (prefixWord ++ tailWord_570642) baseStart_570642 baseEnd_570642 := by
    simpa [prefixWord, tailWord_570642, baseEnd_570642] using wordTrace_append hprefix tailTrace_570642
  have hstable : (prefixWord ++ tailWord_570642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570642).length < 2 ^ (prefixWord ++ tailWord_570642).sum := by decide
  have hdescent : baseEnd_570642 < baseStart_570642 := by decide
  rcases family_descends (prefixWord ++ tailWord_570642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570760 : List Nat := [2, 1, 3, 3, 1, 2, 9]
def baseStart_570760 : Nat := 118140960795 + 570760 * 2 ^ 59
def prefixEnd_570760 : Nat := 4983230072969 + 3 ^ 40 * 570760 * 2
def baseEnd_570760 : Nat := 14472800906681092966673

theorem tailTrace_570760 : CollatzResearch.WordTrace tailWord_570760 prefixEnd_570760 14472800906681092966673 := by
  unfold tailWord_570760
  simp only [CollatzResearch.WordTrace]
  refine ⟨10408663706120736446242867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13878218274827648594990489 10408663706120736446242867)
  ·
    refine ⟨15612995559181104669364301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10408663706120736446242867 15612995559181104669364301)
    ·
      refine ⟨5854873334692914251011613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15612995559181104669364301 5854873334692914251011613)
      ·
        refine ⟨2195577500509842844129355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5854873334692914251011613 2195577500509842844129355)
        ·
          refine ⟨3293366250764764266194033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2195577500509842844129355 3293366250764764266194033)
          ·
            refine ⟨2470024688073573199645525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3293366250764764266194033 2470024688073573199645525)
            ·
              refine ⟨14472800906681092966673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2470024688073573199645525 14472800906681092966673)
              ·
                rfl

theorem cell21_570760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 9].length) (baseStart_570760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570760 prefixEnd_570760 := by exact prefixLift 570760
  have htrace : WordTrace (prefixWord ++ tailWord_570760) baseStart_570760 baseEnd_570760 := by
    simpa [prefixWord, tailWord_570760, baseEnd_570760] using wordTrace_append hprefix tailTrace_570760
  have hstable : (prefixWord ++ tailWord_570760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570760).length < 2 ^ (prefixWord ++ tailWord_570760).sum := by decide
  have hdescent : baseEnd_570760 < baseStart_570760 := by decide
  rcases family_descends (prefixWord ++ tailWord_570760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570766 : List Nat := [4, 1, 1, 4, 3, 1, 1, 1, 5]
def baseStart_570766 : Nat := 118140960795 + 570766 * 2 ^ 59
def prefixEnd_570766 : Nat := 4983230072969 + 3 ^ 40 * 570766 * 2
def baseEnd_570766 : Nat := 130256577441875159600045

theorem tailTrace_570766 : CollatzResearch.WordTrace tailWord_570766 prefixEnd_570766 130256577441875159600045 := by
  unfold tailWord_570766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2602193281277466989650519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13878364166813157278136101 2602193281277466989650519)
  ·
    refine ⟨3903289921916200484475779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2602193281277466989650519 3903289921916200484475779)
    ·
      refine ⟨5854934882874300726713669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3903289921916200484475779 5854934882874300726713669)
      ·
        refine ⟨1097800290538931386258813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5854934882874300726713669 1097800290538931386258813)
        ·
          refine ⟨411675108952099269847055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1097800290538931386258813 411675108952099269847055)
          ·
            refine ⟨617512663428148904770583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411675108952099269847055 617512663428148904770583)
            ·
              refine ⟨926268995142223357155875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 617512663428148904770583 926268995142223357155875)
              ·
                refine ⟨1389403492713335035733813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 926268995142223357155875 1389403492713335035733813)
                ·
                  refine ⟨130256577441875159600045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1389403492713335035733813 130256577441875159600045)
                  ·
                    rfl

theorem cell21_570766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_570766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570766 prefixEnd_570766 := by exact prefixLift 570766
  have htrace : WordTrace (prefixWord ++ tailWord_570766) baseStart_570766 baseEnd_570766 := by
    simpa [prefixWord, tailWord_570766, baseEnd_570766] using wordTrace_append hprefix tailTrace_570766
  have hstable : (prefixWord ++ tailWord_570766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570766).length < 2 ^ (prefixWord ++ tailWord_570766).sum := by decide
  have hdescent : baseEnd_570766 < baseStart_570766 := by decide
  rcases family_descends (prefixWord ++ tailWord_570766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570780 : List Nat := [2, 2, 3, 4, 1, 1, 1, 3, 4]
def baseStart_570780 : Nat := 118140960795 + 570780 * 2 ^ 59
def prefixEnd_570780 : Nat := 4983230072969 + 3 ^ 40 * 570780 * 2
def baseEnd_570780 : Nat := 130259772432614246366683

theorem tailTrace_570780 : CollatzResearch.WordTrace tailWord_570780 prefixEnd_570780 130259772432614246366683 := by
  unfold tailWord_570780
  simp only [CollatzResearch.WordTrace]
  refine ⟨10409028436084508154106897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13878704581446010872142529 10409028436084508154106897)
  ·
    refine ⟨7806771327063381115580173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10409028436084508154106897 7806771327063381115580173)
    ·
      refine ⟨2927539247648767918342565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7806771327063381115580173 2927539247648767918342565)
      ·
        refine ⟨548913608934143984689231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2927539247648767918342565 548913608934143984689231)
        ·
          refine ⟨823370413401215977033847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548913608934143984689231 823370413401215977033847)
          ·
            refine ⟨1235055620101823965550771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823370413401215977033847 1235055620101823965550771)
            ·
              refine ⟨1852583430152735948326157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235055620101823965550771 1852583430152735948326157)
              ·
                refine ⟨694718786307275980622309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1852583430152735948326157 694718786307275980622309)
                ·
                  refine ⟨130259772432614246366683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 694718786307275980622309 130259772432614246366683)
                  ·
                    rfl

theorem cell21_570780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_570780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570780 prefixEnd_570780 := by exact prefixLift 570780
  have htrace : WordTrace (prefixWord ++ tailWord_570780) baseStart_570780 baseEnd_570780 := by
    simpa [prefixWord, tailWord_570780, baseEnd_570780] using wordTrace_append hprefix tailTrace_570780
  have hstable : (prefixWord ++ tailWord_570780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570780).length < 2 ^ (prefixWord ++ tailWord_570780).sum := by decide
  have hdescent : baseEnd_570780 < baseStart_570780 := by decide
  rcases family_descends (prefixWord ++ tailWord_570780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570791 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 7]
def baseStart_570791 : Nat := 118140960795 + 570791 * 2 ^ 59
def prefixEnd_570791 : Nat := 4983230072969 + 3 ^ 40 * 570791 * 2
def baseEnd_570791 : Nat := 130262282782480671683327

theorem tailTrace_570791 : CollatzResearch.WordTrace tailWord_570791 prefixEnd_570791 130262282782480671683327 := by
  unfold tailWord_570791
  simp only [CollatzResearch.WordTrace]
  refine ⟨20818458075129165186864227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13878972050086110124576151 20818458075129165186864227)
  ·
    refine ⟨31227687112693747780296341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20818458075129165186864227 31227687112693747780296341)
    ·
      refine ⟨1463797833407519427201391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31227687112693747780296341 1463797833407519427201391)
      ·
        refine ⟨2195696750111279140802087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1463797833407519427201391 2195696750111279140802087)
        ·
          refine ⟨3293545125166918711203131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2195696750111279140802087 3293545125166918711203131)
          ·
            refine ⟨4940317687750378066804697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3293545125166918711203131 4940317687750378066804697)
            ·
              refine ⟨3705238265812783550103523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4940317687750378066804697 3705238265812783550103523)
              ·
                refine ⟨5557857398719175325155285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3705238265812783550103523 5557857398719175325155285)
                ·
                  refine ⟨130262282782480671683327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5557857398719175325155285 130262282782480671683327)
                  ·
                    rfl

theorem cell21_570791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 7].length) (baseStart_570791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570791 prefixEnd_570791 := by exact prefixLift 570791
  have htrace : WordTrace (prefixWord ++ tailWord_570791) baseStart_570791 baseEnd_570791 := by
    simpa [prefixWord, tailWord_570791, baseEnd_570791] using wordTrace_append hprefix tailTrace_570791
  have hstable : (prefixWord ++ tailWord_570791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570791).length < 2 ^ (prefixWord ++ tailWord_570791).sum := by decide
  have hdescent : baseEnd_570791 < baseStart_570791 := by decide
  rcases family_descends (prefixWord ++ tailWord_570791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570943 : List Nat := [1, 1, 2, 2, 3, 3, 3, 1, 5]
def baseStart_570943 : Nat := 118140960795 + 570943 * 2 ^ 59
def prefixEnd_570943 : Nat := 4983230072969 + 3 ^ 40 * 570943 * 2
def baseEnd_570943 : Nat := 130296971253362185149683

theorem tailTrace_570943 : CollatzResearch.WordTrace tailWord_570943 prefixEnd_570943 130296971253362185149683 := by
  unfold tailWord_570943
  simp only [CollatzResearch.WordTrace]
  refine ⟨20824001970578495146397483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13882667980385663430931655 20824001970578495146397483)
  ·
    refine ⟨31236002955867742719596225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20824001970578495146397483 31236002955867742719596225)
    ·
      refine ⟨23427002216900807039697169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31236002955867742719596225 23427002216900807039697169)
      ·
        refine ⟨17570251662675605279772877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23427002216900807039697169 17570251662675605279772877)
        ·
          refine ⟨6588844373503351979914829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17570251662675605279772877 6588844373503351979914829)
          ·
            refine ⟨2470816640063756992468061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6588844373503351979914829 2470816640063756992468061)
            ·
              refine ⟨926556240023908872175523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2470816640063756992468061 926556240023908872175523)
              ·
                refine ⟨1389834360035863308263285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 926556240023908872175523 1389834360035863308263285)
                ·
                  refine ⟨130296971253362185149683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1389834360035863308263285 130296971253362185149683)
                  ·
                    rfl

theorem cell21_570943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 5].length) (baseStart_570943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570943 prefixEnd_570943 := by exact prefixLift 570943
  have htrace : WordTrace (prefixWord ++ tailWord_570943) baseStart_570943 baseEnd_570943 := by
    simpa [prefixWord, tailWord_570943, baseEnd_570943] using wordTrace_append hprefix tailTrace_570943
  have hstable : (prefixWord ++ tailWord_570943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570943).length < 2 ^ (prefixWord ++ tailWord_570943).sum := by decide
  have hdescent : baseEnd_570943 < baseStart_570943 := by decide
  rcases family_descends (prefixWord ++ tailWord_570943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570994 : List Nat := [3, 2, 1, 2, 3, 3, 2, 2, 3]
def baseStart_570994 : Nat := 118140960795 + 570994 * 2 ^ 59
def prefixEnd_570994 : Nat := 4983230072969 + 3 ^ 40 * 570994 * 2
def baseEnd_570994 : Nat := 130308610148197429799579

theorem tailTrace_570994 : CollatzResearch.WordTrace tailWord_570994 prefixEnd_570994 130308610148197429799579 := by
  unfold tailWord_570994
  simp only [CollatzResearch.WordTrace]
  refine ⟨5206465523348432714126009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13883908062262487237669357 5206465523348432714126009)
  ·
    refine ⟨3904849142511324535594507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5206465523348432714126009 3904849142511324535594507)
    ·
      refine ⟨5857273713766986803391761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3904849142511324535594507 5857273713766986803391761)
      ·
        refine ⟨4392955285325240102543821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5857273713766986803391761 4392955285325240102543821)
        ·
          refine ⟨1647358231996965038453933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4392955285325240102543821 1647358231996965038453933)
          ·
            refine ⟨617759336998861889420225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1647358231996965038453933 617759336998861889420225)
            ·
              refine ⟨463319502749146417065169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 617759336998861889420225 463319502749146417065169)
              ·
                refine ⟨347489627061859812798877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 463319502749146417065169 347489627061859812798877)
                ·
                  refine ⟨130308610148197429799579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 347489627061859812798877 130308610148197429799579)
                  ·
                    rfl

theorem cell21_570994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_570994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_570994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_570994 prefixEnd_570994 := by exact prefixLift 570994
  have htrace : WordTrace (prefixWord ++ tailWord_570994) baseStart_570994 baseEnd_570994 := by
    simpa [prefixWord, tailWord_570994, baseEnd_570994] using wordTrace_append hprefix tailTrace_570994
  have hstable : (prefixWord ++ tailWord_570994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570994).length < 2 ^ (prefixWord ++ tailWord_570994).sum := by decide
  have hdescent : baseEnd_570994 < baseStart_570994 := by decide
  rcases family_descends (prefixWord ++ tailWord_570994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571005 : List Nat := [1, 4, 1, 1, 4, 3, 1, 6]
def baseStart_571005 : Nat := 118140960795 + 571005 * 2 ^ 59
def prefixEnd_571005 : Nat := 4983230072969 + 3 ^ 40 * 571005 * 2
def baseEnd_571005 : Nat := 43437040166021285038741

theorem tailTrace_571005 : CollatzResearch.WordTrace tailWord_571005 prefixEnd_571005 43437040166021285038741 := by
  unfold tailWord_571005
  simp only [CollatzResearch.WordTrace]
  refine ⟨20826263296353879735154469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13884175530902586490102979 20826263296353879735154469)
  ·
    refine ⟨3904924368066352450341463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20826263296353879735154469 3904924368066352450341463)
    ·
      refine ⟨5857386552099528675512195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3904924368066352450341463 5857386552099528675512195)
      ·
        refine ⟨8786079828149293013268293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5857386552099528675512195 8786079828149293013268293)
        ·
          refine ⟨1647389967777992439987805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8786079828149293013268293 1647389967777992439987805)
          ·
            refine ⟨617771237916747164995427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1647389967777992439987805 617771237916747164995427)
            ·
              refine ⟨926656856875120747493141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 617771237916747164995427 926656856875120747493141)
              ·
                refine ⟨43437040166021285038741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 926656856875120747493141 43437040166021285038741)
                ·
                  rfl

theorem cell21_571005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 6].length) (baseStart_571005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571005 prefixEnd_571005 := by exact prefixLift 571005
  have htrace : WordTrace (prefixWord ++ tailWord_571005) baseStart_571005 baseEnd_571005 := by
    simpa [prefixWord, tailWord_571005, baseEnd_571005] using wordTrace_append hprefix tailTrace_571005
  have hstable : (prefixWord ++ tailWord_571005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571005).length < 2 ^ (prefixWord ++ tailWord_571005).sum := by decide
  have hdescent : baseEnd_571005 < baseStart_571005 := by decide
  rcases family_descends (prefixWord ++ tailWord_571005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571109 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 6]
def baseStart_571109 : Nat := 118140960795 + 571109 * 2 ^ 59
def prefixEnd_571109 : Nat := 4983230072969 + 3 ^ 40 * 571109 * 2
def baseEnd_571109 : Nat := 130334854714982785382677

theorem tailTrace_571109 : CollatzResearch.WordTrace tailWord_571109 prefixEnd_571109 130334854714982785382677 := by
  unfold tailWord_571109
  simp only [CollatzResearch.WordTrace]
  refine ⟨20830056487977105496940381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13886704325318070331293587 20830056487977105496940381)
  ·
    refine ⟨7811271182991414561352643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20830056487977105496940381 7811271182991414561352643)
    ·
      refine ⟨11716906774487121842028965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7811271182991414561352643 11716906774487121842028965)
      ·
        refine ⟨2196920020216335345380431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11716906774487121842028965 2196920020216335345380431)
        ·
          refine ⟨3295380030324503018070647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2196920020216335345380431 3295380030324503018070647)
          ·
            refine ⟨4943070045486754527105971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3295380030324503018070647 4943070045486754527105971)
            ·
              refine ⟨7414605068230131790658957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4943070045486754527105971 7414605068230131790658957)
              ·
                refine ⟨2780476900586299421497109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7414605068230131790658957 2780476900586299421497109)
                ·
                  refine ⟨130334854714982785382677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2780476900586299421497109 130334854714982785382677)
                  ·
                    rfl

theorem cell21_571109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_571109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571109 prefixEnd_571109 := by exact prefixLift 571109
  have htrace : WordTrace (prefixWord ++ tailWord_571109) baseStart_571109 baseEnd_571109 := by
    simpa [prefixWord, tailWord_571109, baseEnd_571109] using wordTrace_append hprefix tailTrace_571109
  have hstable : (prefixWord ++ tailWord_571109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571109).length < 2 ^ (prefixWord ++ tailWord_571109).sum := by decide
  have hdescent : baseEnd_571109 < baseStart_571109 := by decide
  rcases family_descends (prefixWord ++ tailWord_571109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571112 : List Nat := [2, 1, 4, 1, 3, 3, 1, 1, 5]
def baseStart_571112 : Nat := 118140960795 + 571112 * 2 ^ 59
def prefixEnd_571112 : Nat := 4983230072969 + 3 ^ 40 * 571112 * 2
def baseEnd_571112 : Nat := 130335539355855446832671

theorem tailTrace_571112 : CollatzResearch.WordTrace tailWord_571112 prefixEnd_571112 130335539355855446832671 := by
  unfold tailWord_571112
  simp only [CollatzResearch.WordTrace]
  refine ⟨10415082953483118504649795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13886777271310824672866393 10415082953483118504649795)
  ·
    refine ⟨15622624430224677756974693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10415082953483118504649795 15622624430224677756974693)
    ·
      refine ⟨2929242080667127079432755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15622624430224677756974693 2929242080667127079432755)
      ·
        refine ⟨4393863121000690619149133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2929242080667127079432755 4393863121000690619149133)
        ·
          refine ⟨1647698670375258982180925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4393863121000690619149133 1647698670375258982180925)
          ·
            refine ⟨617887001390722118317847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1647698670375258982180925 617887001390722118317847)
            ·
              refine ⟨926830502086083177476771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 617887001390722118317847 926830502086083177476771)
              ·
                refine ⟨1390245753129124766215157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 926830502086083177476771 1390245753129124766215157)
                ·
                  refine ⟨130335539355855446832671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1390245753129124766215157 130335539355855446832671)
                  ·
                    rfl

theorem cell21_571112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 5].length) (baseStart_571112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571112 prefixEnd_571112 := by exact prefixLift 571112
  have htrace : WordTrace (prefixWord ++ tailWord_571112) baseStart_571112 baseEnd_571112 := by
    simpa [prefixWord, tailWord_571112, baseEnd_571112] using wordTrace_append hprefix tailTrace_571112
  have hstable : (prefixWord ++ tailWord_571112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571112).length < 2 ^ (prefixWord ++ tailWord_571112).sum := by decide
  have hdescent : baseEnd_571112 < baseStart_571112 := by decide
  rcases family_descends (prefixWord ++ tailWord_571112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571123 : List Nat := [1, 1, 1, 2, 2, 3, 3, 8]
def baseStart_571123 : Nat := 118140960795 + 571123 * 2 ^ 59
def prefixEnd_571123 : Nat := 4983230072969 + 3 ^ 40 * 571123 * 2
def baseEnd_571123 : Nat := 43446016568573957383105

theorem tailTrace_571123 : CollatzResearch.WordTrace tailWord_571123 prefixEnd_571123 43446016568573957383105 := by
  unfold tailWord_571123
  simp only [CollatzResearch.WordTrace]
  refine ⟨20830567109926385887950023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13887044739950923925300015 20830567109926385887950023)
  ·
    refine ⟨31245850664889578831925035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20830567109926385887950023 31245850664889578831925035)
    ·
      refine ⟨46868775997334368247887553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31245850664889578831925035 46868775997334368247887553)
      ·
        refine ⟨35151581998000776185915665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46868775997334368247887553 35151581998000776185915665)
        ·
          refine ⟨26363686498500582139436749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35151581998000776185915665 26363686498500582139436749)
          ·
            refine ⟨9886382436937718302288781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26363686498500582139436749 9886382436937718302288781)
            ·
              refine ⟨3707393413851644363358293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9886382436937718302288781 3707393413851644363358293)
              ·
                refine ⟨43446016568573957383105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3707393413851644363358293 43446016568573957383105)
                ·
                  rfl

theorem cell21_571123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 8].length) (baseStart_571123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571123 prefixEnd_571123 := by exact prefixLift 571123
  have htrace : WordTrace (prefixWord ++ tailWord_571123) baseStart_571123 baseEnd_571123 := by
    simpa [prefixWord, tailWord_571123, baseEnd_571123] using wordTrace_append hprefix tailTrace_571123
  have hstable : (prefixWord ++ tailWord_571123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571123).length < 2 ^ (prefixWord ++ tailWord_571123).sum := by decide
  have hdescent : baseEnd_571123 < baseStart_571123 := by decide
  rcases family_descends (prefixWord ++ tailWord_571123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571140 : List Nat := [2, 3, 2, 2, 1, 2, 2, 7]
def baseStart_571140 : Nat := 118140960795 + 571140 * 2 ^ 59
def prefixEnd_571140 : Nat := 4983230072969 + 3 ^ 40 * 571140 * 2
def baseEnd_571140 : Nat := 43447309779111206788649

theorem tailTrace_571140 : CollatzResearch.WordTrace tailWord_571140 prefixEnd_571140 43447309779111206788649 := by
  unfold tailWord_571140
  simp only [CollatzResearch.WordTrace]
  refine ⟨10415593575432398895659437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13887458100576531860879249 10415593575432398895659437)
  ·
    refine ⟨3905847590787149585872289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10415593575432398895659437 3905847590787149585872289)
    ·
      refine ⟨2929385693090362189404217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3905847590787149585872289 2929385693090362189404217)
      ·
        refine ⟨2197039269817771642053163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2929385693090362189404217 2197039269817771642053163)
        ·
          refine ⟨3295558904726657463079745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2197039269817771642053163 3295558904726657463079745)
          ·
            refine ⟨2471669178544993097309809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3295558904726657463079745 2471669178544993097309809)
            ·
              refine ⟨1853751883908744822982357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2471669178544993097309809 1853751883908744822982357)
              ·
                refine ⟨43447309779111206788649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1853751883908744822982357 43447309779111206788649)
                ·
                  rfl

theorem cell21_571140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 7].length) (baseStart_571140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571140 prefixEnd_571140 := by exact prefixLift 571140
  have htrace : WordTrace (prefixWord ++ tailWord_571140) baseStart_571140 baseEnd_571140 := by
    simpa [prefixWord, tailWord_571140, baseEnd_571140] using wordTrace_append hprefix tailTrace_571140
  have hstable : (prefixWord ++ tailWord_571140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571140).length < 2 ^ (prefixWord ++ tailWord_571140).sum := by decide
  have hdescent : baseEnd_571140 < baseStart_571140 := by decide
  rcases family_descends (prefixWord ++ tailWord_571140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571188 : List Nat := [2, 5, 1, 1, 2, 2, 1, 2, 5]
def baseStart_571188 : Nat := 118140960795 + 571188 * 2 ^ 59
def prefixEnd_571188 : Nat := 4983230072969 + 3 ^ 40 * 571188 * 2
def baseEnd_571188 : Nat := 130352883591296203565849

theorem tailTrace_571188 : CollatzResearch.WordTrace tailWord_571188 prefixEnd_571188 130352883591296203565849 := by
  unfold tailWord_571188
  simp only [CollatzResearch.WordTrace]
  refine ⟨10416468927345450994533109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13888625236460601326044145 10416468927345450994533109)
  ·
    refine ⟨976543961938636030737479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10416468927345450994533109 976543961938636030737479)
    ·
      refine ⟨1464815942907954046106219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 976543961938636030737479 1464815942907954046106219)
      ·
        refine ⟨2197223914361931069159329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1464815942907954046106219 2197223914361931069159329)
        ·
          refine ⟨1647917935771448301869497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2197223914361931069159329 1647917935771448301869497)
          ·
            refine ⟨1235938451828586226402123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1647917935771448301869497 1235938451828586226402123)
            ·
              refine ⟨1853907677742879339603185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235938451828586226402123 1853907677742879339603185)
              ·
                refine ⟨1390430758307159504702389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1853907677742879339603185 1390430758307159504702389)
                ·
                  refine ⟨130352883591296203565849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1390430758307159504702389 130352883591296203565849)
                  ·
                    rfl

theorem cell21_571188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_571188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571188 prefixEnd_571188 := by exact prefixLift 571188
  have htrace : WordTrace (prefixWord ++ tailWord_571188) baseStart_571188 baseEnd_571188 := by
    simpa [prefixWord, tailWord_571188, baseEnd_571188] using wordTrace_append hprefix tailTrace_571188
  have hstable : (prefixWord ++ tailWord_571188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571188).length < 2 ^ (prefixWord ++ tailWord_571188).sum := by decide
  have hdescent : baseEnd_571188 < baseStart_571188 := by decide
  rcases family_descends (prefixWord ++ tailWord_571188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571292 : List Nat := [2, 2, 3, 3, 1, 1, 1, 8]
def baseStart_571292 : Nat := 118140960795 + 571292 * 2 ^ 59
def prefixEnd_571292 : Nat := 4983230072969 + 3 ^ 40 * 571292 * 2
def baseEnd_571292 : Nat := 43458872602738377944101

theorem tailTrace_571292 : CollatzResearch.WordTrace tailWord_571292 prefixEnd_571292 43458872602738377944101 := by
  unfold tailWord_571292
  simp only [CollatzResearch.WordTrace]
  refine ⟨10418365523157063875426065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13891154030876085167234753 10418365523157063875426065)
  ·
    refine ⟨7813774142367797906569549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10418365523157063875426065 7813774142367797906569549)
    ·
      refine ⟨2930165303387924214963581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7813774142367797906569549 2930165303387924214963581)
      ·
        refine ⟨1098811988770471580611343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2930165303387924214963581 1098811988770471580611343)
        ·
          refine ⟨1648217983155707370917015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1098811988770471580611343 1648217983155707370917015)
          ·
            refine ⟨2472326974733561056375523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1648217983155707370917015 2472326974733561056375523)
            ·
              refine ⟨3708490462100341584563285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2472326974733561056375523 3708490462100341584563285)
              ·
                refine ⟨43458872602738377944101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3708490462100341584563285 43458872602738377944101)
                ·
                  rfl

theorem cell21_571292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 8].length) (baseStart_571292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571292 prefixEnd_571292 := by exact prefixLift 571292
  have htrace : WordTrace (prefixWord ++ tailWord_571292) baseStart_571292 baseEnd_571292 := by
    simpa [prefixWord, tailWord_571292, baseEnd_571292] using wordTrace_append hprefix tailTrace_571292
  have hstable : (prefixWord ++ tailWord_571292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571292).length < 2 ^ (prefixWord ++ tailWord_571292).sum := by decide
  have hdescent : baseEnd_571292 < baseStart_571292 := by decide
  rcases family_descends (prefixWord ++ tailWord_571292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571340 : List Nat := [2, 2, 1, 4, 1, 3, 1, 4, 3]
def baseStart_571340 : Nat := 118140960795 + 571340 * 2 ^ 59
def prefixEnd_571340 : Nat := 4983230072969 + 3 ^ 40 * 571340 * 2
def baseEnd_571340 : Nat := 130387572062177717032205

theorem tailTrace_571340 : CollatzResearch.WordTrace tailWord_571340 prefixEnd_571340 130387572062177717032205 := by
  unfold tailWord_571340
  simp only [CollatzResearch.WordTrace]
  refine ⟨10419240875070115974299737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13892321166760154632399649 10419240875070115974299737)
  ·
    refine ⟨7814430656302586980724803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10419240875070115974299737 7814430656302586980724803)
    ·
      refine ⟨11721645984453880471087205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7814430656302586980724803 11721645984453880471087205)
      ·
        refine ⟨2197808622085102588328851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11721645984453880471087205 2197808622085102588328851)
        ·
          refine ⟨3296712933127653882493277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2197808622085102588328851 3296712933127653882493277)
          ·
            refine ⟨1236267349922870205934979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3296712933127653882493277 1236267349922870205934979)
            ·
              refine ⟨1854401024884305308902469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1236267349922870205934979 1854401024884305308902469)
              ·
                refine ⟨347700192165807245419213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1854401024884305308902469 347700192165807245419213)
                ·
                  refine ⟨130387572062177717032205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 347700192165807245419213 130387572062177717032205)
                  ·
                    rfl

theorem cell21_571340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_571340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571340 prefixEnd_571340 := by exact prefixLift 571340
  have htrace : WordTrace (prefixWord ++ tailWord_571340) baseStart_571340 baseEnd_571340 := by
    simpa [prefixWord, tailWord_571340, baseEnd_571340] using wordTrace_append hprefix tailTrace_571340
  have hstable : (prefixWord ++ tailWord_571340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571340).length < 2 ^ (prefixWord ++ tailWord_571340).sum := by decide
  have hdescent : baseEnd_571340 < baseStart_571340 := by decide
  rcases family_descends (prefixWord ++ tailWord_571340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571399 : List Nat := [1, 1, 4, 3, 1, 3, 2, 1, 5]
def baseStart_571399 : Nat := 118140960795 + 571399 * 2 ^ 59
def prefixEnd_571399 : Nat := 4983230072969 + 3 ^ 40 * 571399 * 2
def baseEnd_571399 : Nat := 130401036666006725548751

theorem tailTrace_571399 : CollatzResearch.WordTrace tailWord_571399 prefixEnd_571399 130401036666006725548751 := by
  unfold tailWord_571399
  simp only [CollatzResearch.WordTrace]
  refine ⟨20840633656926485024997251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13893755771284323349998167 20840633656926485024997251)
  ·
    refine ⟨31260950485389727537495877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20840633656926485024997251 31260950485389727537495877)
    ·
      refine ⟨5861428216010573913280477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31260950485389727537495877 5861428216010573913280477)
      ·
        refine ⟨2198035581003965217480179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5861428216010573913280477 2198035581003965217480179)
        ·
          refine ⟨3297053371505947826220269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2198035581003965217480179 3297053371505947826220269)
          ·
            refine ⟨1236395014314730434832601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3297053371505947826220269 1236395014314730434832601)
            ·
              refine ⟨927296260736047826124451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1236395014314730434832601 927296260736047826124451)
              ·
                refine ⟨1390944391104071739186677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 927296260736047826124451 1390944391104071739186677)
                ·
                  refine ⟨130401036666006725548751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1390944391104071739186677 130401036666006725548751)
                  ·
                    rfl

theorem cell21_571399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 5].length) (baseStart_571399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571399 prefixEnd_571399 := by exact prefixLift 571399
  have htrace : WordTrace (prefixWord ++ tailWord_571399) baseStart_571399 baseEnd_571399 := by
    simpa [prefixWord, tailWord_571399, baseEnd_571399] using wordTrace_append hprefix tailTrace_571399
  have hstable : (prefixWord ++ tailWord_571399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571399).length < 2 ^ (prefixWord ++ tailWord_571399).sum := by decide
  have hdescent : baseEnd_571399 < baseStart_571399 := by decide
  rcases family_descends (prefixWord ++ tailWord_571399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571427 : List Nat := [1, 1, 1, 4, 3, 1, 3, 7]
def baseStart_571427 : Nat := 118140960795 + 571427 * 2 ^ 59
def prefixEnd_571427 : Nat := 4983230072969 + 3 ^ 40 * 571427 * 2
def baseEnd_571427 : Nat := 43469142215828299694009

theorem tailTrace_571427 : CollatzResearch.WordTrace tailWord_571427 prefixEnd_571427 43469142215828299694009 := by
  unfold tailWord_571427
  simp only [CollatzResearch.WordTrace]
  refine ⟨20841654900825045807016535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13894436600550030538011023 20841654900825045807016535)
  ·
    refine ⟨31262482351237568710524803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20841654900825045807016535 31262482351237568710524803)
    ·
      refine ⟨46893723526856353065787205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31262482351237568710524803 46893723526856353065787205)
      ·
        refine ⟨8792573161285566199835101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46893723526856353065787205 8792573161285566199835101)
        ·
          refine ⟨3297214935482087324938163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8792573161285566199835101 3297214935482087324938163)
          ·
            refine ⟨4945822403223130987407245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3297214935482087324938163 4945822403223130987407245)
            ·
              refine ⟨1854683401208674120277717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4945822403223130987407245 1854683401208674120277717)
              ·
                refine ⟨43469142215828299694009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1854683401208674120277717 43469142215828299694009)
                ·
                  rfl

theorem cell21_571427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 7].length) (baseStart_571427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571427 prefixEnd_571427 := by exact prefixLift 571427
  have htrace : WordTrace (prefixWord ++ tailWord_571427) baseStart_571427 baseEnd_571427 := by
    simpa [prefixWord, tailWord_571427, baseEnd_571427] using wordTrace_append hprefix tailTrace_571427
  have hstable : (prefixWord ++ tailWord_571427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571427).length < 2 ^ (prefixWord ++ tailWord_571427).sum := by decide
  have hdescent : baseEnd_571427 < baseStart_571427 := by decide
  rcases family_descends (prefixWord ++ tailWord_571427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571506 : List Nat := [3, 2, 1, 2, 2, 3, 2, 2, 4]
def baseStart_571506 : Nat := 118140960795 + 571506 * 2 ^ 59
def prefixEnd_571506 : Nat := 4983230072969 + 3 ^ 40 * 571506 * 2
def baseEnd_571506 : Nat := 130425455523798317265199

theorem tailTrace_571506 : CollatzResearch.WordTrace tailWord_571506 prefixEnd_571506 130425455523798317265199 := by
  unfold tailWord_571506
  simp only [CollatzResearch.WordTrace]
  refine ⟨5211134066884710574785593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13896357511692561532761581 5211134066884710574785593)
  ·
    refine ⟨3908350550163532931089195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5211134066884710574785593 3908350550163532931089195)
    ·
      refine ⟨5862525825245299396633793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3908350550163532931089195 5862525825245299396633793)
      ·
        refine ⟨4396894368933974547475345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5862525825245299396633793 4396894368933974547475345)
        ·
          refine ⟨3297670776700480910606509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4396894368933974547475345 3297670776700480910606509)
          ·
            refine ⟨1236626541262680341477441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3297670776700480910606509 1236626541262680341477441)
            ·
              refine ⟨927469905947010256108081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1236626541262680341477441 927469905947010256108081)
              ·
                refine ⟨695602429460257692081061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 927469905947010256108081 695602429460257692081061)
                ·
                  refine ⟨130425455523798317265199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 695602429460257692081061 130425455523798317265199)
                  ·
                    rfl

theorem cell21_571506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_571506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571506 prefixEnd_571506 := by exact prefixLift 571506
  have htrace : WordTrace (prefixWord ++ tailWord_571506) baseStart_571506 baseEnd_571506 := by
    simpa [prefixWord, tailWord_571506, baseEnd_571506] using wordTrace_append hprefix tailTrace_571506
  have hstable : (prefixWord ++ tailWord_571506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571506).length < 2 ^ (prefixWord ++ tailWord_571506).sum := by decide
  have hdescent : baseEnd_571506 < baseStart_571506 := by decide
  rcases family_descends (prefixWord ++ tailWord_571506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571593 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 7]
def baseStart_571593 : Nat := 118140960795 + 571593 * 2 ^ 59
def prefixEnd_571593 : Nat := 4983230072969 + 3 ^ 40 * 571593 * 2
def baseEnd_571593 : Nat := 130445310109105499315021

theorem tailTrace_571593 : CollatzResearch.WordTrace tailWord_571593 prefixEnd_571593 130445310109105499315021 := by
  unfold tailWord_571593
  simp only [CollatzResearch.WordTrace]
  refine ⟨20847709418223656157559433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13898472945482437438372955 20847709418223656157559433)
  ·
    refine ⟨15635782063667742118169575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20847709418223656157559433 15635782063667742118169575)
    ·
      refine ⟨23453673095501613177254363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15635782063667742118169575 23453673095501613177254363)
      ·
        refine ⟨35180509643252419765881545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23453673095501613177254363 35180509643252419765881545)
        ·
          refine ⟨26385382232439314824411159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35180509643252419765881545 26385382232439314824411159)
          ·
            refine ⟨39578073348658972236616739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26385382232439314824411159 39578073348658972236616739)
            ·
              refine ⟨59367110022988458354925109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39578073348658972236616739 59367110022988458354925109)
              ·
                refine ⟨5565666564655167970774229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59367110022988458354925109 5565666564655167970774229)
                ·
                  refine ⟨130445310109105499315021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5565666564655167970774229 130445310109105499315021)
                  ·
                    rfl

theorem cell21_571593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_571593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571593 prefixEnd_571593 := by exact prefixLift 571593
  have htrace : WordTrace (prefixWord ++ tailWord_571593) baseStart_571593 baseEnd_571593 := by
    simpa [prefixWord, tailWord_571593, baseEnd_571593] using wordTrace_append hprefix tailTrace_571593
  have hstable : (prefixWord ++ tailWord_571593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571593).length < 2 ^ (prefixWord ++ tailWord_571593).sum := by decide
  have hdescent : baseEnd_571593 < baseStart_571593 := by decide
  rcases family_descends (prefixWord ++ tailWord_571593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571678 : List Nat := [4, 3, 2, 1, 1, 1, 4, 2, 3]
def baseStart_571678 : Nat := 118140960795 + 571678 * 2 ^ 59
def prefixEnd_571678 : Nat := 4983230072969 + 3 ^ 40 * 571678 * 2
def baseEnd_571678 : Nat := 130464708267164240398181

theorem tailTrace_571678 : CollatzResearch.WordTrace tailWord_571678 prefixEnd_571678 130464708267164240398181 := by
  unfold tailWord_571678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2606351202864464459300461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13900539748610477116269125 2606351202864464459300461)
  ·
    refine ⟨977381701074174172237673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2606351202864464459300461 977381701074174172237673)
    ·
      refine ⟨733036275805630629178255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 977381701074174172237673 733036275805630629178255)
      ·
        refine ⟨1099554413708445943767383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 733036275805630629178255 1099554413708445943767383)
        ·
          refine ⟨1649331620562668915651075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1099554413708445943767383 1649331620562668915651075)
          ·
            refine ⟨2473997430844003373476613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1649331620562668915651075 2473997430844003373476613)
            ·
              refine ⟨463874518283250632526865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2473997430844003373476613 463874518283250632526865)
              ·
                refine ⟨347905888712437974395149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 463874518283250632526865 347905888712437974395149)
                ·
                  refine ⟨130464708267164240398181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 347905888712437974395149 130464708267164240398181)
                  ·
                    rfl

theorem cell21_571678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_571678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571678 prefixEnd_571678 := by exact prefixLift 571678
  have htrace : WordTrace (prefixWord ++ tailWord_571678) baseStart_571678 baseEnd_571678 := by
    simpa [prefixWord, tailWord_571678, baseEnd_571678] using wordTrace_append hprefix tailTrace_571678
  have hstable : (prefixWord ++ tailWord_571678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571678).length < 2 ^ (prefixWord ++ tailWord_571678).sum := by decide
  have hdescent : baseEnd_571678 < baseStart_571678 := by decide
  rcases family_descends (prefixWord ++ tailWord_571678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571762 : List Nat := [3, 2, 1, 2, 1, 3, 2, 2, 5]
def baseStart_571762 : Nat := 118140960795 + 571762 * 2 ^ 59
def prefixEnd_571762 : Nat := 4983230072969 + 3 ^ 40 * 571762 * 2
def baseEnd_571762 : Nat := 130483878211598760998009

theorem tailTrace_571762 : CollatzResearch.WordTrace tailWord_571762 prefixEnd_571762 130483878211598760998009 := by
  unfold tailWord_571762
  simp only [CollatzResearch.WordTrace]
  refine ⟨5213468338652849505115385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13902582236407598680307693 5213468338652849505115385)
  ·
    refine ⟨3910101253989637128836539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5213468338652849505115385 3910101253989637128836539)
    ·
      refine ⟨5865151880984455693254809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3910101253989637128836539 5865151880984455693254809)
      ·
        refine ⟨4398863910738341769941107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5865151880984455693254809 4398863910738341769941107)
        ·
          refine ⟨6598295866107512654911661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4398863910738341769941107 6598295866107512654911661)
          ·
            refine ⟨2474360949790317245591873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6598295866107512654911661 2474360949790317245591873)
            ·
              refine ⟨1855770712342737934193905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2474360949790317245591873 1855770712342737934193905)
              ·
                refine ⟨1391828034257053450645429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1855770712342737934193905 1391828034257053450645429)
                ·
                  refine ⟨130483878211598760998009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1391828034257053450645429 130483878211598760998009)
                  ·
                    rfl

theorem cell21_571762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_571762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571762 prefixEnd_571762 := by exact prefixLift 571762
  have htrace : WordTrace (prefixWord ++ tailWord_571762) baseStart_571762 baseEnd_571762 := by
    simpa [prefixWord, tailWord_571762, baseEnd_571762] using wordTrace_append hprefix tailTrace_571762
  have hstable : (prefixWord ++ tailWord_571762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571762).length < 2 ^ (prefixWord ++ tailWord_571762).sum := by decide
  have hdescent : baseEnd_571762 < baseStart_571762 := by decide
  rcases family_descends (prefixWord ++ tailWord_571762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571765 : List Nat := [1, 3, 4, 1, 2, 3, 2, 5]
def baseStart_571765 : Nat := 118140960795 + 571765 * 2 ^ 59
def prefixEnd_571765 : Nat := 4983230072969 + 3 ^ 40 * 571765 * 2
def baseEnd_571765 : Nat := 43494854284157140816001

theorem tailTrace_571765 : CollatzResearch.WordTrace tailWord_571765 prefixEnd_571765 43494854284157140816001 := by
  unfold tailWord_571765
  simp only [CollatzResearch.WordTrace]
  refine ⟨20853982773600529532820749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13902655182400353021880499 20853982773600529532820749)
  ·
    refine ⟨7820243540100198574807781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20853982773600529532820749 7820243540100198574807781)
    ·
      refine ⟨1466295663768787232776459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7820243540100198574807781 1466295663768787232776459)
      ·
        refine ⟨2199443495653180849164689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1466295663768787232776459 2199443495653180849164689)
        ·
          refine ⟨1649582621739885636873517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2199443495653180849164689 1649582621739885636873517)
          ·
            refine ⟨618593483152457113827569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1649582621739885636873517 618593483152457113827569)
            ·
              refine ⟨463945112364342835370677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 618593483152457113827569 463945112364342835370677)
              ·
                refine ⟨43494854284157140816001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 463945112364342835370677 43494854284157140816001)
                ·
                  rfl

theorem cell21_571765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 5].length) (baseStart_571765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571765 prefixEnd_571765 := by exact prefixLift 571765
  have htrace : WordTrace (prefixWord ++ tailWord_571765) baseStart_571765 baseEnd_571765 := by
    simpa [prefixWord, tailWord_571765, baseEnd_571765] using wordTrace_append hprefix tailTrace_571765
  have hstable : (prefixWord ++ tailWord_571765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571765).length < 2 ^ (prefixWord ++ tailWord_571765).sum := by decide
  have hdescent : baseEnd_571765 < baseStart_571765 := by decide
  rcases family_descends (prefixWord ++ tailWord_571765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571796 : List Nat := [2, 4, 2, 1, 3, 2, 1, 1, 5]
def baseStart_571796 : Nat := 118140960795 + 571796 * 2 ^ 59
def prefixEnd_571796 : Nat := 4983230072969 + 3 ^ 40 * 571796 * 2
def baseEnd_571796 : Nat := 130491637474822257431273

theorem tailTrace_571796 : CollatzResearch.WordTrace tailWord_571796 prefixEnd_571796 130491637474822257431273 := by
  unfold tailWord_571796
  simp only [CollatzResearch.WordTrace]
  refine ⟨10427556718244110913599621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13903408957658814551466161 10427556718244110913599621)
  ·
    refine ⟨1955166884670770796299929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10427556718244110913599621 1955166884670770796299929)
    ·
      refine ⟨1466375163503078097224947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1955166884670770796299929 1466375163503078097224947)
      ·
        refine ⟨2199562745254617145837421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1466375163503078097224947 2199562745254617145837421)
        ·
          refine ⟨824836029470481429689033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2199562745254617145837421 824836029470481429689033)
          ·
            refine ⟨618627022102861072266775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 824836029470481429689033 618627022102861072266775)
            ·
              refine ⟨927940533154291608400163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 618627022102861072266775 927940533154291608400163)
              ·
                refine ⟨1391910799731437412600245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 927940533154291608400163 1391910799731437412600245)
                ·
                  refine ⟨130491637474822257431273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1391910799731437412600245 130491637474822257431273)
                  ·
                    rfl

theorem cell21_571796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_571796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571796 prefixEnd_571796 := by exact prefixLift 571796
  have htrace : WordTrace (prefixWord ++ tailWord_571796) baseStart_571796 baseEnd_571796 := by
    simpa [prefixWord, tailWord_571796, baseEnd_571796] using wordTrace_append hprefix tailTrace_571796
  have hstable : (prefixWord ++ tailWord_571796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571796).length < 2 ^ (prefixWord ++ tailWord_571796).sum := by decide
  have hdescent : baseEnd_571796 < baseStart_571796 := by decide
  rcases family_descends (prefixWord ++ tailWord_571796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571807 : List Nat := [1, 1, 2, 5, 1, 1, 4, 6]
def baseStart_571807 : Nat := 118140960795 + 571807 * 2 ^ 59
def prefixEnd_571807 : Nat := 4983230072969 + 3 ^ 40 * 571807 * 2
def baseEnd_571807 : Nat := 43498049274896227582639

theorem tailTrace_571807 : CollatzResearch.WordTrace tailWord_571807 prefixEnd_571807 43498049274896227582639 := by
  unfold tailWord_571807
  simp only [CollatzResearch.WordTrace]
  refine ⟨20855514639448370705849675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13903676426298913803899783 20855514639448370705849675)
  ·
    refine ⟨31283271959172556058774513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20855514639448370705849675 31283271959172556058774513)
    ·
      refine ⟨23462453969379417044080885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31283271959172556058774513 23462453969379417044080885)
      ·
        refine ⟨2199605059629320347882583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23462453969379417044080885 2199605059629320347882583)
        ·
          refine ⟨3299407589443980521823875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2199605059629320347882583 3299407589443980521823875)
          ·
            refine ⟨4949111384165970782735813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3299407589443980521823875 4949111384165970782735813)
            ·
              refine ⟨927958384531119521762965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4949111384165970782735813 927958384531119521762965)
              ·
                refine ⟨43498049274896227582639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 927958384531119521762965 43498049274896227582639)
                ·
                  rfl

theorem cell21_571807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 6].length) (baseStart_571807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571807 prefixEnd_571807 := by exact prefixLift 571807
  have htrace : WordTrace (prefixWord ++ tailWord_571807) baseStart_571807 baseEnd_571807 := by
    simpa [prefixWord, tailWord_571807, baseEnd_571807] using wordTrace_append hprefix tailTrace_571807
  have hstable : (prefixWord ++ tailWord_571807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571807).length < 2 ^ (prefixWord ++ tailWord_571807).sum := by decide
  have hdescent : baseEnd_571807 < baseStart_571807 := by decide
  rcases family_descends (prefixWord ++ tailWord_571807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571841 : List Nat := [1, 2, 7, 1, 1, 9]
def baseStart_571841 : Nat := 118140960795 + 571841 * 2 ^ 59
def prefixEnd_571841 : Nat := 4983230072969 + 3 ^ 40 * 571841 * 2
def baseEnd_571841 : Nat := 4833403966218969599303

theorem tailTrace_571841 : CollatzResearch.WordTrace tailWord_571841 prefixEnd_571841 4833403966218969599303 := by
  unfold tailWord_571841
  simp only [CollatzResearch.WordTrace]
  refine ⟨20856754721325194512587377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13904503147550129675058251 20856754721325194512587377)
  ·
    refine ⟨15642566040993895884440533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20856754721325194512587377 15642566040993895884440533)
    ·
      refine ⟨366622641585794434791575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 15642566040993895884440533 366622641585794434791575)
      ·
        refine ⟨549933962378691652187363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366622641585794434791575 549933962378691652187363)
        ·
          refine ⟨824900943568037478281045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549933962378691652187363 824900943568037478281045)
          ·
            refine ⟨4833403966218969599303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 824900943568037478281045 4833403966218969599303)
            ·
              rfl

theorem cell21_571841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 9].length) (baseStart_571841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571841 prefixEnd_571841 := by exact prefixLift 571841
  have htrace : WordTrace (prefixWord ++ tailWord_571841) baseStart_571841 baseEnd_571841 := by
    simpa [prefixWord, tailWord_571841, baseEnd_571841] using wordTrace_append hprefix tailTrace_571841
  have hstable : (prefixWord ++ tailWord_571841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571841).length < 2 ^ (prefixWord ++ tailWord_571841).sum := by decide
  have hdescent : baseEnd_571841 < baseStart_571841 := by decide
  rcases family_descends (prefixWord ++ tailWord_571841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571858 : List Nat := [3, 2, 2, 4, 2, 1, 1, 6]
def baseStart_571858 : Nat := 118140960795 + 571858 * 2 ^ 59
def prefixEnd_571858 : Nat := 4983230072969 + 3 ^ 40 * 571858 * 2
def baseEnd_571858 : Nat := 43501928906507975799271

theorem tailTrace_571858 : CollatzResearch.WordTrace tailWord_571858 prefixEnd_571858 43501928906507975799271 := by
  unfold tailWord_571858
  simp only [CollatzResearch.WordTrace]
  refine ⟨5214343690565901603989057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13904916508175737610637485 5214343690565901603989057)
  ·
    refine ⟨3910757767924426202991793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5214343690565901603989057 3910757767924426202991793)
    ·
      refine ⟨2933068325943319652243845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3910757767924426202991793 2933068325943319652243845)
      ·
        refine ⟨549950311114372434795721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2933068325943319652243845 549950311114372434795721)
        ·
          refine ⟨412462733335779326096791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 549950311114372434795721 412462733335779326096791)
          ·
            refine ⟨618694100003668989145187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412462733335779326096791 618694100003668989145187)
            ·
              refine ⟨928041150005503483717781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 618694100003668989145187 928041150005503483717781)
              ·
                refine ⟨43501928906507975799271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 928041150005503483717781 43501928906507975799271)
                ·
                  rfl

theorem cell21_571858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_571858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571858 prefixEnd_571858 := by exact prefixLift 571858
  have htrace : WordTrace (prefixWord ++ tailWord_571858) baseStart_571858 baseEnd_571858 := by
    simpa [prefixWord, tailWord_571858, baseEnd_571858] using wordTrace_append hprefix tailTrace_571858
  have hstable : (prefixWord ++ tailWord_571858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571858).length < 2 ^ (prefixWord ++ tailWord_571858).sum := by decide
  have hdescent : baseEnd_571858 < baseStart_571858 := by decide
  rcases family_descends (prefixWord ++ tailWord_571858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571869 : List Nat := [1, 4, 3, 1, 1, 1, 1, 5, 4]
def baseStart_571869 : Nat := 118140960795 + 571869 * 2 ^ 59
def prefixEnd_571869 : Nat := 4983230072969 + 3 ^ 40 * 571869 * 2
def baseEnd_571869 : Nat := 130508297069390352714457

theorem tailTrace_571869 : CollatzResearch.WordTrace tailWord_571869 prefixEnd_571869 130508297069390352714457 := by
  unfold tailWord_571869
  simp only [CollatzResearch.WordTrace]
  refine ⟨20857775965223755294606661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13905183976815836863071107 20857775965223755294606661)
  ·
    refine ⟨3910832993479454117738749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20857775965223755294606661 3910832993479454117738749)
    ·
      refine ⟨1466562372554795294152031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3910832993479454117738749 1466562372554795294152031)
      ·
        refine ⟨2199843558832192941228047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1466562372554795294152031 2199843558832192941228047)
        ·
          refine ⟨3299765338248289411842071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2199843558832192941228047 3299765338248289411842071)
          ·
            refine ⟨4949648007372434117763107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3299765338248289411842071 4949648007372434117763107)
            ·
              refine ⟨7424472011058651176644661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4949648007372434117763107 7424472011058651176644661)
              ·
                refine ⟨696044251036748547810437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7424472011058651176644661 696044251036748547810437)
                ·
                  refine ⟨130508297069390352714457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 696044251036748547810437 130508297069390352714457)
                  ·
                    rfl

theorem cell21_571869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_571869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571869 prefixEnd_571869 := by exact prefixLift 571869
  have htrace : WordTrace (prefixWord ++ tailWord_571869) baseStart_571869 baseEnd_571869 := by
    simpa [prefixWord, tailWord_571869, baseEnd_571869] using wordTrace_append hprefix tailTrace_571869
  have hstable : (prefixWord ++ tailWord_571869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571869).length < 2 ^ (prefixWord ++ tailWord_571869).sum := by decide
  have hdescent : baseEnd_571869 < baseStart_571869 := by decide
  rcases family_descends (prefixWord ++ tailWord_571869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571883 : List Nat := [1, 1, 1, 1, 2, 3, 7, 5]
def baseStart_571883 : Nat := 118140960795 + 571883 * 2 ^ 59
def prefixEnd_571883 : Nat := 4983230072969 + 3 ^ 40 * 571883 * 2
def baseEnd_571883 : Nat := 43503830686709813160365

theorem tailTrace_571883 : CollatzResearch.WordTrace tailWord_571883 prefixEnd_571883 43503830686709813160365 := by
  unfold tailWord_571883
  simp only [CollatzResearch.WordTrace]
  refine ⟨20858286587173035685616303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13905524391448690457077535 20858286587173035685616303)
  ·
    refine ⟨31287429880759553528424455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20858286587173035685616303 31287429880759553528424455)
    ·
      refine ⟨46931144821139330292636683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31287429880759553528424455 46931144821139330292636683)
      ·
        refine ⟨70396717231708995438955025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46931144821139330292636683 70396717231708995438955025)
        ·
          refine ⟨52797537923781746579216269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70396717231708995438955025 52797537923781746579216269)
          ·
            refine ⟨19799076721418154967206101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52797537923781746579216269 19799076721418154967206101)
            ·
              refine ⟨464040860658238007043893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19799076721418154967206101 464040860658238007043893)
              ·
                refine ⟨43503830686709813160365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 464040860658238007043893 43503830686709813160365)
                ·
                  rfl

theorem cell21_571883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 5].length) (baseStart_571883 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571883 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571883 prefixEnd_571883 := by exact prefixLift 571883
  have htrace : WordTrace (prefixWord ++ tailWord_571883) baseStart_571883 baseEnd_571883 := by
    simpa [prefixWord, tailWord_571883, baseEnd_571883] using wordTrace_append hprefix tailTrace_571883
  have hstable : (prefixWord ++ tailWord_571883).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571883).length < 2 ^ (prefixWord ++ tailWord_571883).sum := by decide
  have hdescent : baseEnd_571883 < baseStart_571883 := by decide
  rcases family_descends (prefixWord ++ tailWord_571883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571914 : List Nat := [3, 1, 2, 2, 2, 1, 4, 1, 5]
def baseStart_571914 : Nat := 118140960795 + 571914 * 2 ^ 59
def prefixEnd_571914 : Nat := 4983230072969 + 3 ^ 40 * 571914 * 2
def baseEnd_571914 : Nat := 130518566682480274464365

theorem tailTrace_571914 : CollatzResearch.WordTrace tailWord_571914 prefixEnd_571914 130518566682480274464365 := by
  unfold tailWord_571914
  simp only [CollatzResearch.WordTrace]
  refine ⟨5214854312515181994998699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13906278166707151986663197 5214854312515181994998699)
  ·
    refine ⟨7822281468772772992498049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5214854312515181994998699 7822281468772772992498049)
    ·
      refine ⟨5866711101579579744373537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7822281468772772992498049 5866711101579579744373537)
      ·
        refine ⟨4400033326184684808280153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5866711101579579744373537 4400033326184684808280153)
        ·
          refine ⟨3300024994638513606210115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4400033326184684808280153 3300024994638513606210115)
          ·
            refine ⟨4950037491957770409315173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3300024994638513606210115 4950037491957770409315173)
            ·
              refine ⟨928132029742081951746595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4950037491957770409315173 928132029742081951746595)
              ·
                refine ⟨1392198044613122927619893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 928132029742081951746595 1392198044613122927619893)
                ·
                  refine ⟨130518566682480274464365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1392198044613122927619893 130518566682480274464365)
                  ·
                    rfl

theorem cell21_571914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_571914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_571914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_571914 prefixEnd_571914 := by exact prefixLift 571914
  have htrace : WordTrace (prefixWord ++ tailWord_571914) baseStart_571914 baseEnd_571914 := by
    simpa [prefixWord, tailWord_571914, baseEnd_571914] using wordTrace_append hprefix tailTrace_571914
  have hstable : (prefixWord ++ tailWord_571914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571914).length < 2 ^ (prefixWord ++ tailWord_571914).sum := by decide
  have hdescent : baseEnd_571914 < baseStart_571914 := by decide
  rcases family_descends (prefixWord ++ tailWord_571914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572018 : List Nat := [3, 2, 1, 2, 13]
def baseStart_572018 : Nat := 118140960795 + 572018 * 2 ^ 59
def prefixEnd_572018 : Nat := 4983230072969 + 3 ^ 40 * 572018 * 2
def baseEnd_572018 : Nat := 1611633344437027218899

theorem tailTrace_572018 : CollatzResearch.WordTrace tailWord_572018 prefixEnd_572018 1611633344437027218899 := by
  unfold tailWord_572018
  simp only [CollatzResearch.WordTrace]
  refine ⟨5215802610420988435445177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13908806961122635827853805 5215802610420988435445177)
  ·
    refine ⟨3911851957815741326583883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5215802610420988435445177 3911851957815741326583883)
    ·
      refine ⟨5867777936723611989875825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3911851957815741326583883 5867777936723611989875825)
      ·
        refine ⟨4400833452542708992406869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5867777936723611989875825 4400833452542708992406869)
        ·
          refine ⟨1611633344437027218899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 4400833452542708992406869 1611633344437027218899)
          ·
            rfl

theorem cell21_572018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 13].length) (baseStart_572018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_572018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_572018 prefixEnd_572018 := by exact prefixLift 572018
  have htrace : WordTrace (prefixWord ++ tailWord_572018) baseStart_572018 baseEnd_572018 := by
    simpa [prefixWord, tailWord_572018, baseEnd_572018] using wordTrace_append hprefix tailTrace_572018
  have hstable : (prefixWord ++ tailWord_572018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572018).length < 2 ^ (prefixWord ++ tailWord_572018).sum := by decide
  have hdescent : baseEnd_572018 < baseStart_572018 := by decide
  rcases family_descends (prefixWord ++ tailWord_572018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572117 : List Nat := [1, 3, 2, 5, 1, 2, 1, 3, 3]
def baseStart_572117 : Nat := 118140960795 + 572117 * 2 ^ 59
def prefixEnd_572117 : Nat := 4983230072969 + 3 ^ 40 * 572117 * 2
def baseEnd_572117 : Nat := 130564894048197032580617

theorem tailTrace_572117 : CollatzResearch.WordTrace tailWord_572117 prefixEnd_572117 130564894048197032580617 := by
  unfold tailWord_572117
  simp only [CollatzResearch.WordTrace]
  refine ⟨20866821268325293649634605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13911214178883529099756403 20866821268325293649634605)
  ·
    refine ⟨7825057975621985118612977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20866821268325293649634605 7825057975621985118612977)
    ·
      refine ⟨5868793481716488838959733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7825057975621985118612977 5868793481716488838959733)
      ·
        refine ⟨550199388910920828652475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5868793481716488838959733 550199388910920828652475)
        ·
          refine ⟨825299083366381242978713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550199388910920828652475 825299083366381242978713)
          ·
            refine ⟨618974312524785932234035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 825299083366381242978713 618974312524785932234035)
            ·
              refine ⟨928461468787178898351053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 618974312524785932234035 928461468787178898351053)
              ·
                refine ⟨348173050795192086881645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 928461468787178898351053 348173050795192086881645)
                ·
                  refine ⟨130564894048197032580617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 348173050795192086881645 130564894048197032580617)
                  ·
                    rfl

theorem cell21_572117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_572117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_572117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_572117 prefixEnd_572117 := by exact prefixLift 572117
  have htrace : WordTrace (prefixWord ++ tailWord_572117) baseStart_572117 baseEnd_572117 := by
    simpa [prefixWord, tailWord_572117, baseEnd_572117] using wordTrace_append hprefix tailTrace_572117
  have hstable : (prefixWord ++ tailWord_572117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572117).length < 2 ^ (prefixWord ++ tailWord_572117).sum := by decide
  have hdescent : baseEnd_572117 < baseStart_572117 := by decide
  rcases family_descends (prefixWord ++ tailWord_572117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572142 : List Nat := [4, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_572142 : Nat := 118140960795 + 572142 * 2 ^ 59
def prefixEnd_572142 : Nat := 4983230072969 + 3 ^ 40 * 572142 * 2
def baseEnd_572142 : Nat := 130570599388802544663899

theorem tailTrace_572142 : CollatzResearch.WordTrace tailWord_572142 prefixEnd_572142 130570599388802544663899 := by
  unfold tailWord_572142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2608466636654340364911835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13911822062156481946196453 2608466636654340364911835)
  ·
    refine ⟨3912699954981510547367753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2608466636654340364911835 3912699954981510547367753)
    ·
      refine ⟨2934524966236132910525815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3912699954981510547367753 2934524966236132910525815)
      ·
        refine ⟨4401787449354199365788723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2934524966236132910525815 4401787449354199365788723)
        ·
          refine ⟨6602681174031299048683085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4401787449354199365788723 6602681174031299048683085)
          ·
            refine ⟨2476005440261737143256157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6602681174031299048683085 2476005440261737143256157)
            ·
              refine ⟨928502040098151428721059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2476005440261737143256157 928502040098151428721059)
              ·
                refine ⟨1392753060147227143081589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 928502040098151428721059 1392753060147227143081589)
                ·
                  refine ⟨130570599388802544663899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1392753060147227143081589 130570599388802544663899)
                  ·
                    rfl

theorem cell21_572142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_572142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_572142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_572142 prefixEnd_572142 := by exact prefixLift 572142
  have htrace : WordTrace (prefixWord ++ tailWord_572142) baseStart_572142 baseEnd_572142 := by
    simpa [prefixWord, tailWord_572142, baseEnd_572142] using wordTrace_append hprefix tailTrace_572142
  have hstable : (prefixWord ++ tailWord_572142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572142).length < 2 ^ (prefixWord ++ tailWord_572142).sum := by decide
  have hdescent : baseEnd_572142 < baseStart_572142 := by decide
  rcases family_descends (prefixWord ++ tailWord_572142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572170 : List Nat := [3, 1, 2, 2, 1, 2, 1, 9]
def baseStart_572170 : Nat := 118140960795 + 572170 * 2 ^ 59
def prefixEnd_572170 : Nat := 4983230072969 + 3 ^ 40 * 572170 * 2
def baseEnd_572170 : Nat := 43525663123426906065725

theorem tailTrace_572170 : CollatzResearch.WordTrace tailWord_572170 prefixEnd_572170 43525663123426906065725 := by
  unfold tailWord_572170
  simp only [CollatzResearch.WordTrace]
  refine ⟨5217188584283320925328491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13912502891422189134209309 5217188584283320925328491)
  ·
    refine ⟨7825782876424981387992737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5217188584283320925328491 7825782876424981387992737)
    ·
      refine ⟨5869337157318736040994553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7825782876424981387992737 5869337157318736040994553)
      ·
        refine ⟨4402002867989052030745915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5869337157318736040994553 4402002867989052030745915)
        ·
          refine ⟨6603004301983578046118873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4402002867989052030745915 6603004301983578046118873)
          ·
            refine ⟨4952253226487683534589155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6603004301983578046118873 4952253226487683534589155)
            ·
              refine ⟨7428379839731525301883733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4952253226487683534589155 7428379839731525301883733)
              ·
                refine ⟨43525663123426906065725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7428379839731525301883733 43525663123426906065725)
                ·
                  rfl

theorem cell21_572170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_572170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_572170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_572170 prefixEnd_572170 := by exact prefixLift 572170
  have htrace : WordTrace (prefixWord ++ tailWord_572170) baseStart_572170 baseEnd_572170 := by
    simpa [prefixWord, tailWord_572170, baseEnd_572170] using wordTrace_append hprefix tailTrace_572170
  have hstable : (prefixWord ++ tailWord_572170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572170).length < 2 ^ (prefixWord ++ tailWord_572170).sum := by decide
  have hdescent : baseEnd_572170 < baseStart_572170 := by decide
  rcases family_descends (prefixWord ++ tailWord_572170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572218 : List Nat := [3, 1, 1, 1, 6, 1, 1, 2, 5]
def baseStart_572218 : Nat := 118140960795 + 572218 * 2 ^ 59
def prefixEnd_572218 : Nat := 4983230072969 + 3 ^ 40 * 572218 * 2
def baseEnd_572218 : Nat := 130587943624243301397077

theorem tailTrace_572218 : CollatzResearch.WordTrace tailWord_572218 prefixEnd_572218 130587943624243301397077 := by
  unfold tailWord_572218
  simp only [CollatzResearch.WordTrace]
  refine ⟨5217626260239846974765327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13913670027306258599374205 5217626260239846974765327)
  ·
    refine ⟨7826439390359770462147991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5217626260239846974765327 7826439390359770462147991)
    ·
      refine ⟨11739659085539655693221987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7826439390359770462147991 11739659085539655693221987)
      ·
        refine ⟨17609488628309483539832981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11739659085539655693221987 17609488628309483539832981)
        ·
          refine ⟨825444779452007040929671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17609488628309483539832981 825444779452007040929671)
          ·
            refine ⟨1238167169178010561394507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 825444779452007040929671 1238167169178010561394507)
            ·
              refine ⟨1857250753767015842091761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1238167169178010561394507 1857250753767015842091761)
              ·
                refine ⟨1392938065325261881568821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1857250753767015842091761 1392938065325261881568821)
                ·
                  refine ⟨130587943624243301397077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1392938065325261881568821 130587943624243301397077)
                  ·
                    rfl

theorem cell21_572218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_572218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_572218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_572218 prefixEnd_572218 := by exact prefixLift 572218
  have htrace : WordTrace (prefixWord ++ tailWord_572218) baseStart_572218 baseEnd_572218 := by
    simpa [prefixWord, tailWord_572218, baseEnd_572218] using wordTrace_append hprefix tailTrace_572218
  have hstable : (prefixWord ++ tailWord_572218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572218).length < 2 ^ (prefixWord ++ tailWord_572218).sum := by decide
  have hdescent : baseEnd_572218 < baseStart_572218 := by decide
  rcases family_descends (prefixWord ++ tailWord_572218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572249 : List Nat := [1, 2, 1, 2, 2, 6, 1, 2, 4]
def baseStart_572249 : Nat := 118140960795 + 572249 * 2 ^ 59
def prefixEnd_572249 : Nat := 4983230072969 + 3 ^ 40 * 572249 * 2
def baseEnd_572249 : Nat := 130595018246594136380347

theorem tailTrace_572249 : CollatzResearch.WordTrace tailWord_572249 prefixEnd_572249 130595018246594136380347 := by
  unfold tailWord_572249
  simp only [CollatzResearch.WordTrace]
  refine ⟨20871635703847080193439801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13914423802564720128959867 20871635703847080193439801)
  ·
    refine ⟨15653726777885310145079851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20871635703847080193439801 15653726777885310145079851)
    ·
      refine ⟨23480590166827965217619777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15653726777885310145079851 23480590166827965217619777)
      ·
        refine ⟨17610442625120973913214833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23480590166827965217619777 17610442625120973913214833)
        ·
          refine ⟨13207831968840730434911125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17610442625120973913214833 13207831968840730434911125)
          ·
            refine ⟨619117123539409239136459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13207831968840730434911125 619117123539409239136459)
            ·
              refine ⟨928675685309113858704689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619117123539409239136459 928675685309113858704689)
              ·
                refine ⟨696506763981835394028517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 928675685309113858704689 696506763981835394028517)
                ·
                  refine ⟨130595018246594136380347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 696506763981835394028517 130595018246594136380347)
                  ·
                    rfl

theorem cell21_572249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 4].length) (baseStart_572249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_572249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_572249 prefixEnd_572249 := by exact prefixLift 572249
  have htrace : WordTrace (prefixWord ++ tailWord_572249) baseStart_572249 baseEnd_572249 := by
    simpa [prefixWord, tailWord_572249, baseEnd_572249] using wordTrace_append hprefix tailTrace_572249
  have hstable : (prefixWord ++ tailWord_572249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572249).length < 2 ^ (prefixWord ++ tailWord_572249).sum := by decide
  have hdescent : baseEnd_572249 < baseStart_572249 := by decide
  rcases family_descends (prefixWord ++ tailWord_572249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572286 : List Nat := [4, 2, 3, 1, 3, 1, 1, 3, 3]
def baseStart_572286 : Nat := 118140960795 + 572286 * 2 ^ 59
def prefixEnd_572286 : Nat := 4983230072969 + 3 ^ 40 * 572286 * 2
def baseEnd_572286 : Nat := 130603462150690294263605

theorem tailTrace_572286 : CollatzResearch.WordTrace tailWord_572286 prefixEnd_572286 130603462150690294263605 := by
  unfold tailWord_572286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2609123150589129439067089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13915323469808690341691141 2609123150589129439067089)
  ·
    refine ⟨1956842362941847079300317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2609123150589129439067089 1956842362941847079300317)
    ·
      refine ⟨733815886103192654737619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1956842362941847079300317 733815886103192654737619)
      ·
        refine ⟨1100723829154788982106429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 733815886103192654737619 1100723829154788982106429)
        ·
          refine ⟨412771435933045868289911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1100723829154788982106429 412771435933045868289911)
          ·
            refine ⟨619157153899568802434867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412771435933045868289911 619157153899568802434867)
            ·
              refine ⟨928735730849353203652301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619157153899568802434867 928735730849353203652301)
              ·
                refine ⟨348275899068507451369613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 928735730849353203652301 348275899068507451369613)
                ·
                  refine ⟨130603462150690294263605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 348275899068507451369613 130603462150690294263605)
                  ·
                    rfl

theorem cell21_572286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_572286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_572286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_572286 prefixEnd_572286 := by exact prefixLift 572286
  have htrace : WordTrace (prefixWord ++ tailWord_572286) baseStart_572286 baseEnd_572286 := by
    simpa [prefixWord, tailWord_572286, baseEnd_572286] using wordTrace_append hprefix tailTrace_572286
  have hstable : (prefixWord ++ tailWord_572286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572286).length < 2 ^ (prefixWord ++ tailWord_572286).sum := by decide
  have hdescent : baseEnd_572286 < baseStart_572286 := by decide
  rcases family_descends (prefixWord ++ tailWord_572286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572291 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 8]
def baseStart_572291 : Nat := 118140960795 + 572291 * 2 ^ 59
def prefixEnd_572291 : Nat := 4983230072969 + 3 ^ 40 * 572291 * 2
def baseEnd_572291 : Nat := 130604603218811396680261

theorem tailTrace_572291 : CollatzResearch.WordTrace tailWord_572291 prefixEnd_572291 130604603218811396680261 := by
  unfold tailWord_572291
  simp only [CollatzResearch.WordTrace]
  refine ⟨20873167569694921366468727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13915445046463280910979151 20873167569694921366468727)
  ·
    refine ⟨31309751354542382049703091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20873167569694921366468727 31309751354542382049703091)
    ·
      refine ⟨46964627031813573074554637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31309751354542382049703091 46964627031813573074554637)
      ·
        refine ⟨17611735136930089902957989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46964627031813573074554637 17611735136930089902957989)
        ·
          refine ⟨3302200338174391856804623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17611735136930089902957989 3302200338174391856804623)
          ·
            refine ⟨4953300507261587785206935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3302200338174391856804623 4953300507261587785206935)
            ·
              refine ⟨7429950760892381677810403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4953300507261587785206935 7429950760892381677810403)
              ·
                refine ⟨11144926141338572516715605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7429950760892381677810403 11144926141338572516715605)
                ·
                  refine ⟨130604603218811396680261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11144926141338572516715605 130604603218811396680261)
                  ·
                    rfl

theorem cell21_572291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 8].length) (baseStart_572291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_572291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_572291 prefixEnd_572291 := by exact prefixLift 572291
  have htrace : WordTrace (prefixWord ++ tailWord_572291) baseStart_572291 baseEnd_572291 := by
    simpa [prefixWord, tailWord_572291, baseEnd_572291] using wordTrace_append hprefix tailTrace_572291
  have hstable : (prefixWord ++ tailWord_572291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572291).length < 2 ^ (prefixWord ++ tailWord_572291).sum := by decide
  have hdescent : baseEnd_572291 < baseStart_572291 := by decide
  rcases family_descends (prefixWord ++ tailWord_572291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572308 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 6]
def baseStart_572308 : Nat := 118140960795 + 572308 * 2 ^ 59
def prefixEnd_572308 : Nat := 4983230072969 + 3 ^ 40 * 572308 * 2
def baseEnd_572308 : Nat := 130608482850423144896893

theorem tailTrace_572308 : CollatzResearch.WordTrace tailWord_572308 prefixEnd_572308 130608482850423144896893 := by
  unfold tailWord_572308
  simp only [CollatzResearch.WordTrace]
  refine ⟨10436893805316666634918789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13915858407088888846558385 10436893805316666634918789)
  ·
    refine ⟨1956917588496874994047273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10436893805316666634918789 1956917588496874994047273)
    ·
      refine ⟨1467688191372656245535455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1956917588496874994047273 1467688191372656245535455)
      ·
        refine ⟨2201532287058984368303183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1467688191372656245535455 2201532287058984368303183)
        ·
          refine ⟨3302298430588476552454775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2201532287058984368303183 3302298430588476552454775)
          ·
            refine ⟨4953447645882714828682163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3302298430588476552454775 4953447645882714828682163)
            ·
              refine ⟨7430171468824072243023245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4953447645882714828682163 7430171468824072243023245)
              ·
                refine ⟨2786314300809027091133717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7430171468824072243023245 2786314300809027091133717)
                ·
                  refine ⟨130608482850423144896893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2786314300809027091133717 130608482850423144896893)
                  ·
                    rfl

theorem cell21_572308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_572308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_572308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_572308 prefixEnd_572308 := by exact prefixLift 572308
  have htrace : WordTrace (prefixWord ++ tailWord_572308) baseStart_572308 baseEnd_572308 := by
    simpa [prefixWord, tailWord_572308, baseEnd_572308] using wordTrace_append hprefix tailTrace_572308
  have hstable : (prefixWord ++ tailWord_572308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572308).length < 2 ^ (prefixWord ++ tailWord_572308).sum := by decide
  have hdescent : baseEnd_572308 < baseStart_572308 := by decide
  rcases family_descends (prefixWord ++ tailWord_572308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572311 : List Nat := [1, 1, 3, 3, 1, 2, 5, 2, 3]
def baseStart_572311 : Nat := 118140960795 + 572311 * 2 ^ 59
def prefixEnd_572311 : Nat := 4983230072969 + 3 ^ 40 * 572311 * 2
def baseEnd_572311 : Nat := 130609167491295806346887

theorem tailTrace_572311 : CollatzResearch.WordTrace tailWord_572311 prefixEnd_572311 130609167491295806346887 := by
  unfold tailWord_572311
  simp only [CollatzResearch.WordTrace]
  refine ⟨20873897029622464782196787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13915931353081643188131191 20873897029622464782196787)
  ·
    refine ⟨31310845544433697173295181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20873897029622464782196787 31310845544433697173295181)
    ·
      refine ⟨11741567079162636439985693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31310845544433697173295181 11741567079162636439985693)
      ·
        refine ⟨4403087654685988664994635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11741567079162636439985693 4403087654685988664994635)
        ·
          refine ⟨6604631482028982997491953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4403087654685988664994635 6604631482028982997491953)
          ·
            refine ⟨4953473611521737248118965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6604631482028982997491953 4953473611521737248118965)
            ·
              refine ⟨464388151080162867011153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4953473611521737248118965 464388151080162867011153)
              ·
                refine ⟨348291113310122150258365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 464388151080162867011153 348291113310122150258365)
                ·
                  refine ⟨130609167491295806346887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 348291113310122150258365 130609167491295806346887)
                  ·
                    rfl

theorem cell21_572311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 3].length) (baseStart_572311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_572311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_572311 prefixEnd_572311 := by exact prefixLift 572311
  have htrace : WordTrace (prefixWord ++ tailWord_572311) baseStart_572311 baseEnd_572311 := by
    simpa [prefixWord, tailWord_572311, baseEnd_572311] using wordTrace_append hprefix tailTrace_572311
  have hstable : (prefixWord ++ tailWord_572311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572311).length < 2 ^ (prefixWord ++ tailWord_572311).sum := by decide
  have hdescent : baseEnd_572311 < baseStart_572311 := by decide
  rcases family_descends (prefixWord ++ tailWord_572311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572356 : List Nat := [2, 3, 3, 3, 2, 8]
def baseStart_572356 : Nat := 118140960795 + 572356 * 2 ^ 59
def prefixEnd_572356 : Nat := 4983230072969 + 3 ^ 40 * 572356 * 2
def baseEnd_572356 : Nat := 4837756929792064003585

theorem tailTrace_572356 : CollatzResearch.WordTrace tailWord_572356 prefixEnd_572356 4837756929792064003585 := by
  unfold tailWord_572356
  simp only [CollatzResearch.WordTrace]
  refine ⟨10437769157229718733792461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13917025542972958311723281 10437769157229718733792461)
  ·
    refine ⟨3914163433961144525172173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10437769157229718733792461 3914163433961144525172173)
    ·
      refine ⟨1467811287735429196939565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3914163433961144525172173 1467811287735429196939565)
      ·
        refine ⟨550429232900785948852337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1467811287735429196939565 550429232900785948852337)
        ·
          refine ⟨412821924675589461639253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 550429232900785948852337 412821924675589461639253)
          ·
            refine ⟨4837756929792064003585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 412821924675589461639253 4837756929792064003585)
            ·
              rfl

theorem cell21_572356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 8].length) (baseStart_572356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_572356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_572356 prefixEnd_572356 := by exact prefixLift 572356
  have htrace : WordTrace (prefixWord ++ tailWord_572356) baseStart_572356 baseEnd_572356 := by
    simpa [prefixWord, tailWord_572356, baseEnd_572356] using wordTrace_append hprefix tailTrace_572356
  have hstable : (prefixWord ++ tailWord_572356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572356).length < 2 ^ (prefixWord ++ tailWord_572356).sum := by decide
  have hdescent : baseEnd_572356 < baseStart_572356 := by decide
  rcases family_descends (prefixWord ++ tailWord_572356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572418 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 6]
def baseStart_572418 : Nat := 118140960795 + 572418 * 2 ^ 59
def prefixEnd_572418 : Nat := 4983230072969 + 3 ^ 40 * 572418 * 2
def baseEnd_572418 : Nat := 130633586349087398063335

theorem tailTrace_572418 : CollatzResearch.WordTrace tailWord_572418 prefixEnd_572418 130633586349087398063335 := by
  unfold tailWord_572418
  simp only [CollatzResearch.WordTrace]
  refine ⟨5219449910058705514085477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13918533093489881370894605 5219449910058705514085477)
  ·
    refine ⟨978646858136007283891027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5219449910058705514085477 978646858136007283891027)
    ·
      refine ⟨1467970287204010925836541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 978646858136007283891027 1467970287204010925836541)
      ·
        refine ⟨550488857701504097188703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1467970287204010925836541 550488857701504097188703)
        ·
          refine ⟨825733286552256145783055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550488857701504097188703 825733286552256145783055)
          ·
            refine ⟨1238599929828384218674583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 825733286552256145783055 1238599929828384218674583)
            ·
              refine ⟨1857899894742576328011875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1238599929828384218674583 1857899894742576328011875)
              ·
                refine ⟨2786849842113864492017813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1857899894742576328011875 2786849842113864492017813)
                ·
                  refine ⟨130633586349087398063335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2786849842113864492017813 130633586349087398063335)
                  ·
                    rfl

theorem cell21_572418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_572418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_572418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_572418 prefixEnd_572418 := by exact prefixLift 572418
  have htrace : WordTrace (prefixWord ++ tailWord_572418) baseStart_572418 baseEnd_572418 := by
    simpa [prefixWord, tailWord_572418, baseEnd_572418] using wordTrace_append hprefix tailTrace_572418
  have hstable : (prefixWord ++ tailWord_572418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572418).length < 2 ^ (prefixWord ++ tailWord_572418).sum := by decide
  have hdescent : baseEnd_572418 < baseStart_572418 := by decide
  rcases family_descends (prefixWord ++ tailWord_572418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572542 : List Nat := [4, 2, 4, 1, 1, 2, 1, 6]
def baseStart_572542 : Nat := 118140960795 + 572542 * 2 ^ 59
def prefixEnd_572542 : Nat := 4983230072969 + 3 ^ 40 * 572542 * 2
def baseEnd_572542 : Nat := 43553961612830245998805

theorem tailTrace_572542 : CollatzResearch.WordTrace tailWord_572542 prefixEnd_572542 43553961612830245998805 := by
  unfold tailWord_572542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2610290286473198904231985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13921548194523727489237253 2610290286473198904231985)
  ·
    refine ⟨1957717714854899178173989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2610290286473198904231985 1957717714854899178173989)
    ·
      refine ⟨367072071535293595907623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1957717714854899178173989 367072071535293595907623)
      ·
        refine ⟨550608107302940393861435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367072071535293595907623 550608107302940393861435)
        ·
          refine ⟨825912160954410590792153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550608107302940393861435 825912160954410590792153)
          ·
            refine ⟨619434120715807943094115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 825912160954410590792153 619434120715807943094115)
            ·
              refine ⟨929151181073711914641173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619434120715807943094115 929151181073711914641173)
              ·
                refine ⟨43553961612830245998805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 929151181073711914641173 43553961612830245998805)
                ·
                  rfl

theorem cell21_572542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_572542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_572542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_572542 prefixEnd_572542 := by exact prefixLift 572542
  have htrace : WordTrace (prefixWord ++ tailWord_572542) baseStart_572542 baseEnd_572542 := by
    simpa [prefixWord, tailWord_572542, baseEnd_572542] using wordTrace_append hprefix tailTrace_572542
  have hstable : (prefixWord ++ tailWord_572542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572542).length < 2 ^ (prefixWord ++ tailWord_572542).sum := by decide
  have hdescent : baseEnd_572542 < baseStart_572542 := by decide
  rcases family_descends (prefixWord ++ tailWord_572542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572567 : List Nat := [1, 1, 3, 3, 3, 2, 3, 5]
def baseStart_572567 : Nat := 118140960795 + 572567 * 2 ^ 59
def prefixEnd_572567 : Nat := 4983230072969 + 3 ^ 40 * 572567 * 2
def baseEnd_572567 : Nat := 43555863393032083359899

theorem tailTrace_572567 : CollatzResearch.WordTrace tailWord_572567 prefixEnd_572567 43555863393032083359899 := by
  unfold tailWord_572567
  simp only [CollatzResearch.WordTrace]
  refine ⟨20883234116695020503515955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13922156077796680335677303 20883234116695020503515955)
  ·
    refine ⟨31324851175042530755273933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20883234116695020503515955 31324851175042530755273933)
    ·
      refine ⟨11746819190640949033227725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31324851175042530755273933 11746819190640949033227725)
      ·
        refine ⟨4405057196490355887460397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11746819190640949033227725 4405057196490355887460397)
        ·
          refine ⟨1651896448683883457797649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4405057196490355887460397 1651896448683883457797649)
          ·
            refine ⟨1238922336512912593348237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1651896448683883457797649 1238922336512912593348237)
            ·
              refine ⟨464595876192342222505589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1238922336512912593348237 464595876192342222505589)
              ·
                refine ⟨43555863393032083359899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 464595876192342222505589 43555863393032083359899)
                ·
                  rfl

theorem cell21_572567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 5].length) (baseStart_572567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_572567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_572567 prefixEnd_572567 := by exact prefixLift 572567
  have htrace : WordTrace (prefixWord ++ tailWord_572567) baseStart_572567 baseEnd_572567 := by
    simpa [prefixWord, tailWord_572567, baseEnd_572567] using wordTrace_append hprefix tailTrace_572567
  have hstable : (prefixWord ++ tailWord_572567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572567).length < 2 ^ (prefixWord ++ tailWord_572567).sum := by decide
  have hdescent : baseEnd_572567 < baseStart_572567 := by decide
  rcases family_descends (prefixWord ++ tailWord_572567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572626 : List Nat := [3, 2, 2, 2, 1, 1, 3, 7]
def baseStart_572626 : Nat := 118140960795 + 572626 * 2 ^ 59
def prefixEnd_572626 : Nat := 4983230072969 + 3 ^ 40 * 572626 * 2
def baseEnd_572626 : Nat := 43560351594308419532081

theorem tailTrace_572626 : CollatzResearch.WordTrace tailWord_572626 prefixEnd_572626 43560351594308419532081 := by
  unfold tailWord_572626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5221346505870318394978433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13923590682320849053275821 5221346505870318394978433)
  ·
    refine ⟨3916009879402738796233825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5221346505870318394978433 3916009879402738796233825)
    ·
      refine ⟨2937007409552054097175369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3916009879402738796233825 2937007409552054097175369)
      ·
        refine ⟨2202755557164040572881527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2937007409552054097175369 2202755557164040572881527)
        ·
          refine ⟨3304133335746060859322291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2202755557164040572881527 3304133335746060859322291)
          ·
            refine ⟨4956200003619091288983437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3304133335746060859322291 4956200003619091288983437)
            ·
              refine ⟨1858575001357159233368789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4956200003619091288983437 1858575001357159233368789)
              ·
                refine ⟨43560351594308419532081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1858575001357159233368789 43560351594308419532081)
                ·
                  rfl

theorem cell21_572626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_572626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_572626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_572626 prefixEnd_572626 := by exact prefixLift 572626
  have htrace : WordTrace (prefixWord ++ tailWord_572626) baseStart_572626 baseEnd_572626 := by
    simpa [prefixWord, tailWord_572626, baseEnd_572626] using wordTrace_append hprefix tailTrace_572626
  have hstable : (prefixWord ++ tailWord_572626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572626).length < 2 ^ (prefixWord ++ tailWord_572626).sum := by decide
  have hdescent : baseEnd_572626 < baseStart_572626 := by decide
  rcases family_descends (prefixWord ++ tailWord_572626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572632 : List Nat := [2, 1, 2, 2, 6, 1, 1, 3, 3]
def baseStart_572632 : Nat := 118140960795 + 572632 * 2 ^ 59
def prefixEnd_572632 : Nat := 4983230072969 + 3 ^ 40 * 572632 * 2
def baseEnd_572632 : Nat := 130682424064670581496231

theorem tailTrace_572632 : CollatzResearch.WordTrace tailWord_572632 prefixEnd_572632 130682424064670581496231 := by
  unfold tailWord_572632
  simp only [CollatzResearch.WordTrace]
  refine ⟨10442802430729768302316075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13923736574306357736421433 10442802430729768302316075)
  ·
    refine ⟨15664203646094652453474113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10442802430729768302316075 15664203646094652453474113)
    ·
      refine ⟨11748152734570989340105585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15664203646094652453474113 11748152734570989340105585)
      ·
        refine ⟨8811114550928242005079189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11748152734570989340105585 8811114550928242005079189)
        ·
          refine ⟨413020994574761343988087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8811114550928242005079189 413020994574761343988087)
          ·
            refine ⟨619531491862142015982131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413020994574761343988087 619531491862142015982131)
            ·
              refine ⟨929297237793213023973197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619531491862142015982131 929297237793213023973197)
              ·
                refine ⟨348486464172454883989949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 929297237793213023973197 348486464172454883989949)
                ·
                  refine ⟨130682424064670581496231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 348486464172454883989949 130682424064670581496231)
                  ·
                    rfl

theorem cell21_572632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 3].length) (baseStart_572632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_572632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_572632 prefixEnd_572632 := by exact prefixLift 572632
  have htrace : WordTrace (prefixWord ++ tailWord_572632) baseStart_572632 baseEnd_572632 := by
    simpa [prefixWord, tailWord_572632, baseEnd_572632] using wordTrace_append hprefix tailTrace_572632
  have hstable : (prefixWord ++ tailWord_572632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572632).length < 2 ^ (prefixWord ++ tailWord_572632).sum := by decide
  have hdescent : baseEnd_572632 < baseStart_572632 := by decide
  rcases family_descends (prefixWord ++ tailWord_572632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572716 : List Nat := [2, 2, 1, 1, 1, 3, 1, 5, 5]
def baseStart_572716 : Nat := 118140960795 + 572716 * 2 ^ 59
def prefixEnd_572716 : Nat := 4983230072969 + 3 ^ 40 * 572716 * 2
def baseEnd_572716 : Nat := 130701594009105102096059

theorem tailTrace_572716 : CollatzResearch.WordTrace tailWord_572716 prefixEnd_572716 130701594009105102096059 := by
  unfold tailWord_572716
  simp only [CollatzResearch.WordTrace]
  refine ⟨10444334296577609475345001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13925779062103479300460001 10444334296577609475345001)
  ·
    refine ⟨7833250722433207106508751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10444334296577609475345001 7833250722433207106508751)
    ·
      refine ⟨11749876083649810659763127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7833250722433207106508751 11749876083649810659763127)
      ·
        refine ⟨17624814125474715989644691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11749876083649810659763127 17624814125474715989644691)
        ·
          refine ⟨26437221188212073984467037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17624814125474715989644691 26437221188212073984467037)
          ·
            refine ⟨9913957945579527744175139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26437221188212073984467037 9913957945579527744175139)
            ·
              refine ⟨14870936918369291616262709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9913957945579527744175139 14870936918369291616262709)
              ·
                refine ⟨1394150336097121089024629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14870936918369291616262709 1394150336097121089024629)
                ·
                  refine ⟨130701594009105102096059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1394150336097121089024629 130701594009105102096059)
                  ·
                    rfl

theorem cell21_572716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_572716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_572716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_572716 prefixEnd_572716 := by exact prefixLift 572716
  have htrace : WordTrace (prefixWord ++ tailWord_572716) baseStart_572716 baseEnd_572716 := by
    simpa [prefixWord, tailWord_572716, baseEnd_572716] using wordTrace_append hprefix tailTrace_572716
  have hstable : (prefixWord ++ tailWord_572716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572716).length < 2 ^ (prefixWord ++ tailWord_572716).sum := by decide
  have hdescent : baseEnd_572716 < baseStart_572716 := by decide
  rcases family_descends (prefixWord ++ tailWord_572716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572750 : List Nat := [4, 1, 1, 1, 1, 1, 6, 3, 3]
def baseStart_572750 : Nat := 118140960795 + 572750 * 2 ^ 59
def prefixEnd_572750 : Nat := 4983230072969 + 3 ^ 40 * 572750 * 2
def baseEnd_572750 : Nat := 130709353272328598529323

theorem tailTrace_572750 : CollatzResearch.WordTrace tailWord_572750 prefixEnd_572750 130709353272328598529323 := by
  unfold tailWord_572750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2611238584379005344678463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13926605783354695171618469 2611238584379005344678463)
  ·
    refine ⟨3916857876568508017017695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2611238584379005344678463 3916857876568508017017695)
    ·
      refine ⟨5875286814852762025526543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3916857876568508017017695 5875286814852762025526543)
      ·
        refine ⟨8812930222279143038289815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5875286814852762025526543 8812930222279143038289815)
        ·
          refine ⟨13219395333418714557434723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8812930222279143038289815 13219395333418714557434723)
          ·
            refine ⟨19829093000128071836152085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13219395333418714557434723 19829093000128071836152085)
            ·
              refine ⟨929488734381003367319629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19829093000128071836152085 929488734381003367319629)
              ·
                refine ⟨348558275392876262744861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 929488734381003367319629 348558275392876262744861)
                ·
                  refine ⟨130709353272328598529323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 348558275392876262744861 130709353272328598529323)
                  ·
                    rfl

theorem cell21_572750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_572750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_572750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_572750 prefixEnd_572750 := by exact prefixLift 572750
  have htrace : WordTrace (prefixWord ++ tailWord_572750) baseStart_572750 baseEnd_572750 := by
    simpa [prefixWord, tailWord_572750, baseEnd_572750] using wordTrace_append hprefix tailTrace_572750
  have hstable : (prefixWord ++ tailWord_572750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572750).length < 2 ^ (prefixWord ++ tailWord_572750).sum := by decide
  have hdescent : baseEnd_572750 < baseStart_572750 := by decide
  rcases family_descends (prefixWord ++ tailWord_572750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572781 : List Nat := [1, 5, 1, 1, 1, 4, 3, 1, 4]
def baseStart_572781 : Nat := 118140960795 + 572781 * 2 ^ 59
def prefixEnd_572781 : Nat := 4983230072969 + 3 ^ 40 * 572781 * 2
def baseEnd_572781 : Nat := 130716427894679433512593

theorem tailTrace_572781 : CollatzResearch.WordTrace tailWord_572781 prefixEnd_572781 130716427894679433512593 := by
  unfold tailWord_572781
  simp only [CollatzResearch.WordTrace]
  refine ⟨20891039337919735051806197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13927359558613156701204131 20891039337919735051806197)
  ·
    refine ⟨1958534937929975161106831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20891039337919735051806197 1958534937929975161106831)
    ·
      refine ⟨2937802406894962741660247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1958534937929975161106831 2937802406894962741660247)
      ·
        refine ⟨4406703610342444112490371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2937802406894962741660247 4406703610342444112490371)
        ·
          refine ⟨6610055415513666168735557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4406703610342444112490371 6610055415513666168735557)
          ·
            refine ⟨1239385390408812406637917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6610055415513666168735557 1239385390408812406637917)
            ·
              refine ⟨464769521403304652489219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1239385390408812406637917 464769521403304652489219)
              ·
                refine ⟨697154282104956978733829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464769521403304652489219 697154282104956978733829)
                ·
                  refine ⟨130716427894679433512593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 697154282104956978733829 130716427894679433512593)
                  ·
                    rfl

theorem cell21_572781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_572781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_572781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_572781 prefixEnd_572781 := by exact prefixLift 572781
  have htrace : WordTrace (prefixWord ++ tailWord_572781) baseStart_572781 baseEnd_572781 := by
    simpa [prefixWord, tailWord_572781, baseEnd_572781] using wordTrace_append hprefix tailTrace_572781
  have hstable : (prefixWord ++ tailWord_572781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572781).length < 2 ^ (prefixWord ++ tailWord_572781).sum := by decide
  have hdescent : baseEnd_572781 < baseStart_572781 := by decide
  rcases family_descends (prefixWord ++ tailWord_572781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572823 : List Nat := [1, 1, 3, 3, 1, 1, 1, 6, 4]
def baseStart_572823 : Nat := 118140960795 + 572823 * 2 ^ 59
def prefixEnd_572823 : Nat := 4983230072969 + 3 ^ 40 * 572823 * 2
def baseEnd_572823 : Nat := 130726012866896693812507

theorem tailTrace_572823 : CollatzResearch.WordTrace tailWord_572823 prefixEnd_572823 130726012866896693812507 := by
  unfold tailWord_572823
  simp only [CollatzResearch.WordTrace]
  refine ⟨20892571203767576224835123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13928380802511717483223415 20892571203767576224835123)
  ·
    refine ⟨31338856805651364337252685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20892571203767576224835123 31338856805651364337252685)
    ·
      refine ⟨11752071302119261626469757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31338856805651364337252685 11752071302119261626469757)
      ·
        refine ⟨4407026738294723109926159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11752071302119261626469757 4407026738294723109926159)
        ·
          refine ⟨6610540107442084664889239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4407026738294723109926159 6610540107442084664889239)
          ·
            refine ⟨9915810161163126997333859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6610540107442084664889239 9915810161163126997333859)
            ·
              refine ⟨14873715241744690496000789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9915810161163126997333859 14873715241744690496000789)
              ·
                refine ⟨697205401956782367000037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14873715241744690496000789 697205401956782367000037)
                ·
                  refine ⟨130726012866896693812507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 697205401956782367000037 130726012866896693812507)
                  ·
                    rfl

theorem cell21_572823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 4].length) (baseStart_572823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_572823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_572823 prefixEnd_572823 := by exact prefixLift 572823
  have htrace : WordTrace (prefixWord ++ tailWord_572823) baseStart_572823 baseEnd_572823 := by
    simpa [prefixWord, tailWord_572823, baseEnd_572823] using wordTrace_append hprefix tailTrace_572823
  have hstable : (prefixWord ++ tailWord_572823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572823).length < 2 ^ (prefixWord ++ tailWord_572823).sum := by decide
  have hdescent : baseEnd_572823 < baseStart_572823 := by decide
  rcases family_descends (prefixWord ++ tailWord_572823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573051 : List Nat := [1, 1, 1, 1, 1, 4, 6, 2, 4]
def baseStart_573051 : Nat := 118140960795 + 573051 * 2 ^ 59
def prefixEnd_573051 : Nat := 4983230072969 + 3 ^ 40 * 573051 * 2
def baseEnd_573051 : Nat := 130778045573218964012041

theorem tailTrace_573051 : CollatzResearch.WordTrace tailWord_573051 prefixEnd_573051 130778045573218964012041 := by
  unfold tailWord_573051
  simp only [CollatzResearch.WordTrace]
  refine ⟨20900887046941571164135007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13933924697961047442756671 20900887046941571164135007)
  ·
    refine ⟨31351330570412356746202511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20900887046941571164135007 31351330570412356746202511)
    ·
      refine ⟨47026995855618535119303767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31351330570412356746202511 47026995855618535119303767)
      ·
        refine ⟨70540493783427802678955651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47026995855618535119303767 70540493783427802678955651)
        ·
          refine ⟨105810740675141704018433477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70540493783427802678955651 105810740675141704018433477)
          ·
            refine ⟨19839513876589069503456277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105810740675141704018433477 19839513876589069503456277)
            ·
              refine ⟨929977212965112632974513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19839513876589069503456277 929977212965112632974513)
              ·
                refine ⟨697482909723834474730885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 929977212965112632974513 697482909723834474730885)
                ·
                  refine ⟨130778045573218964012041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 697482909723834474730885 130778045573218964012041)
                  ·
                    rfl

theorem cell21_573051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 4].length) (baseStart_573051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573051 prefixEnd_573051 := by exact prefixLift 573051
  have htrace : WordTrace (prefixWord ++ tailWord_573051) baseStart_573051 baseEnd_573051 := by
    simpa [prefixWord, tailWord_573051, baseEnd_573051] using wordTrace_append hprefix tailTrace_573051
  have hstable : (prefixWord ++ tailWord_573051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573051).length < 2 ^ (prefixWord ++ tailWord_573051).sum := by decide
  have hdescent : baseEnd_573051 < baseStart_573051 := by decide
  rcases family_descends (prefixWord ++ tailWord_573051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573065 : List Nat := [1, 2, 1, 1, 4, 1, 5, 6]
def baseStart_573065 : Nat := 118140960795 + 573065 * 2 ^ 59
def prefixEnd_573065 : Nat := 4983230072969 + 3 ^ 40 * 573065 * 2
def baseEnd_573065 : Nat := 43593746854652683592893

theorem tailTrace_573065 : CollatzResearch.WordTrace tailWord_573065 prefixEnd_573065 43593746854652683592893 := by
  unfold tailWord_573065
  simp only [CollatzResearch.WordTrace]
  refine ⟨20901397668890851555144649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13934265112593901036763099 20901397668890851555144649)
  ·
    refine ⟨15676048251668138666358487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20901397668890851555144649 15676048251668138666358487)
    ·
      refine ⟨23514072377502207999537731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15676048251668138666358487 23514072377502207999537731)
      ·
        refine ⟨35271108566253311999306597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23514072377502207999537731 35271108566253311999306597)
        ·
          refine ⟨6613332856172495999869987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35271108566253311999306597 6613332856172495999869987)
          ·
            refine ⟨9919999284258743999804981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6613332856172495999869987 9919999284258743999804981)
            ·
              refine ⟨929999932899257249981717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9919999284258743999804981 929999932899257249981717)
              ·
                refine ⟨43593746854652683592893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 929999932899257249981717 43593746854652683592893)
                ·
                  rfl

theorem cell21_573065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 6].length) (baseStart_573065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573065 prefixEnd_573065 := by exact prefixLift 573065
  have htrace : WordTrace (prefixWord ++ tailWord_573065) baseStart_573065 baseEnd_573065 := by
    simpa [prefixWord, tailWord_573065, baseEnd_573065] using wordTrace_append hprefix tailTrace_573065
  have hstable : (prefixWord ++ tailWord_573065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573065).length < 2 ^ (prefixWord ++ tailWord_573065).sum := by decide
  have hdescent : baseEnd_573065 < baseStart_573065 := by decide
  rcases family_descends (prefixWord ++ tailWord_573065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573102 : List Nat := [4, 1, 4, 1, 2, 2, 1, 2, 4]
def baseStart_573102 : Nat := 118140960795 + 573102 * 2 ^ 59
def prefixEnd_573102 : Nat := 4983230072969 + 3 ^ 40 * 573102 * 2
def baseEnd_573102 : Nat := 130789684468054208661937

theorem tailTrace_573102 : CollatzResearch.WordTrace tailWord_573102 prefixEnd_573102 130789684468054208661937 := by
  unfold tailWord_573102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2612843396219600859280195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13935164779837871249494373 2612843396219600859280195)
  ·
    refine ⟨3919265094329401288920293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2612843396219600859280195 3919265094329401288920293)
    ·
      refine ⟨734862205186762741672555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3919265094329401288920293 734862205186762741672555)
      ·
        refine ⟨1102293307780144112508833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 734862205186762741672555 1102293307780144112508833)
        ·
          refine ⟨826719980835108084381625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1102293307780144112508833 826719980835108084381625)
          ·
            refine ⟨620039985626331063286219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 826719980835108084381625 620039985626331063286219)
            ·
              refine ⟨930059978439496594929329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 620039985626331063286219 930059978439496594929329)
              ·
                refine ⟨697544983829622446196997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 930059978439496594929329 697544983829622446196997)
                ·
                  refine ⟨130789684468054208661937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 697544983829622446196997 130789684468054208661937)
                  ·
                    rfl

theorem cell21_573102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_573102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573102 prefixEnd_573102 := by exact prefixLift 573102
  have htrace : WordTrace (prefixWord ++ tailWord_573102) baseStart_573102 baseEnd_573102 := by
    simpa [prefixWord, tailWord_573102, baseEnd_573102] using wordTrace_append hprefix tailTrace_573102
  have hstable : (prefixWord ++ tailWord_573102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573102).length < 2 ^ (prefixWord ++ tailWord_573102).sum := by decide
  have hdescent : baseEnd_573102 < baseStart_573102 := by decide
  rcases family_descends (prefixWord ++ tailWord_573102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573113 : List Nat := [1, 2, 1, 4, 1, 1, 4, 4, 3]
def baseStart_573113 : Nat := 118140960795 + 573113 * 2 ^ 59
def prefixEnd_573113 : Nat := 4983230072969 + 3 ^ 40 * 573113 * 2
def baseEnd_573113 : Nat := 130792194817920633978581

theorem tailTrace_573113 : CollatzResearch.WordTrace tailWord_573113 prefixEnd_573113 130792194817920633978581 := by
  unfold tailWord_573113
  simp only [CollatzResearch.WordTrace]
  refine ⟨20903148372716955752891993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13935432248477970501927995 20903148372716955752891993)
  ·
    refine ⟨15677361279537716814668995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20903148372716955752891993 15677361279537716814668995)
    ·
      refine ⟨23516041919306575222003493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15677361279537716814668995 23516041919306575222003493)
      ·
        refine ⟨4409257859869982854125655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23516041919306575222003493 4409257859869982854125655)
        ·
          refine ⟨6613886789804974281188483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4409257859869982854125655 6613886789804974281188483)
          ·
            refine ⟨9920830184707461421782725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6613886789804974281188483 9920830184707461421782725)
            ·
              refine ⟨1860155659632649016584261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9920830184707461421782725 1860155659632649016584261)
              ·
                refine ⟨348779186181121690609549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1860155659632649016584261 348779186181121690609549)
                ·
                  refine ⟨130792194817920633978581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 348779186181121690609549 130792194817920633978581)
                  ·
                    rfl

theorem cell21_573113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 3].length) (baseStart_573113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573113 prefixEnd_573113 := by exact prefixLift 573113
  have htrace : WordTrace (prefixWord ++ tailWord_573113) baseStart_573113 baseEnd_573113 := by
    simpa [prefixWord, tailWord_573113, baseEnd_573113] using wordTrace_append hprefix tailTrace_573113
  have hstable : (prefixWord ++ tailWord_573113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573113).length < 2 ^ (prefixWord ++ tailWord_573113).sum := by decide
  have hdescent : baseEnd_573113 < baseStart_573113 := by decide
  rcases family_descends (prefixWord ++ tailWord_573113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573220 : List Nat := [2, 3, 1, 3, 2, 2, 2, 2, 4]
def baseStart_573220 : Nat := 118140960795 + 573220 * 2 ^ 59
def prefixEnd_573220 : Nat := 4983230072969 + 3 ^ 40 * 573220 * 2
def baseEnd_573220 : Nat := 130816613675712225695029

theorem tailTrace_573220 : CollatzResearch.WordTrace tailWord_573220 prefixEnd_573220 130816613675712225695029 := by
  unfold tailWord_573220
  simp only [CollatzResearch.WordTrace]
  refine ⟨10453525491664656513518557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13938033988886208684691409 10453525491664656513518557)
  ·
    refine ⟨3920072059374246192569459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10453525491664656513518557 3920072059374246192569459)
    ·
      refine ⟨5880108089061369288854189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3920072059374246192569459 5880108089061369288854189)
      ·
        refine ⟨2205040533398013483320321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5880108089061369288854189 2205040533398013483320321)
        ·
          refine ⟨1653780400048510112490241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2205040533398013483320321 1653780400048510112490241)
          ·
            refine ⟨1240335300036382584367681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1653780400048510112490241 1240335300036382584367681)
            ·
              refine ⟨930251475027286938275761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1240335300036382584367681 930251475027286938275761)
              ·
                refine ⟨697688606270465203706821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 930251475027286938275761 697688606270465203706821)
                ·
                  refine ⟨130816613675712225695029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 697688606270465203706821 130816613675712225695029)
                  ·
                    rfl

theorem cell21_573220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_573220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573220 prefixEnd_573220 := by exact prefixLift 573220
  have htrace : WordTrace (prefixWord ++ tailWord_573220) baseStart_573220 baseEnd_573220 := by
    simpa [prefixWord, tailWord_573220, baseEnd_573220] using wordTrace_append hprefix tailTrace_573220
  have hstable : (prefixWord ++ tailWord_573220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573220).length < 2 ^ (prefixWord ++ tailWord_573220).sum := by decide
  have hdescent : baseEnd_573220 < baseStart_573220 := by decide
  rcases family_descends (prefixWord ++ tailWord_573220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573234 : List Nat := [3, 2, 1, 1, 3, 4, 1, 6]
def baseStart_573234 : Nat := 118140960795 + 573234 * 2 ^ 59
def prefixEnd_573234 : Nat := 4983230072969 + 3 ^ 40 * 573234 * 2
def baseEnd_573234 : Nat := 43606602888817104153889

theorem tailTrace_573234 : CollatzResearch.WordTrace tailWord_573234 prefixEnd_573234 43606602888817104153889 := by
  unfold tailWord_573234
  simp only [CollatzResearch.WordTrace]
  refine ⟨5226890401319648354511689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13938374403519062278697837 5226890401319648354511689)
  ·
    refine ⟨3920167800989736265883767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5226890401319648354511689 3920167800989736265883767)
    ·
      refine ⟨5880251701484604398825651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3920167800989736265883767 5880251701484604398825651)
      ·
        refine ⟨8820377552226906598238477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5880251701484604398825651 8820377552226906598238477)
        ·
          refine ⟨3307641582085089974339429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8820377552226906598238477 3307641582085089974339429)
          ·
            refine ⟨620182796640954370188643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3307641582085089974339429 620182796640954370188643)
            ·
              refine ⟨930274194961431555282965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 620182796640954370188643 930274194961431555282965)
              ·
                refine ⟨43606602888817104153889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 930274194961431555282965 43606602888817104153889)
                ·
                  rfl

theorem cell21_573234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_573234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573234 prefixEnd_573234 := by exact prefixLift 573234
  have htrace : WordTrace (prefixWord ++ tailWord_573234) baseStart_573234 baseEnd_573234 := by
    simpa [prefixWord, tailWord_573234, baseEnd_573234] using wordTrace_append hprefix tailTrace_573234
  have hstable : (prefixWord ++ tailWord_573234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573234).length < 2 ^ (prefixWord ++ tailWord_573234).sum := by decide
  have hdescent : baseEnd_573234 < baseStart_573234 := by decide
  rcases family_descends (prefixWord ++ tailWord_573234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573265 : List Nat := [1, 2, 2, 1, 5, 1, 1, 5, 3]
def baseStart_573265 : Nat := 118140960795 + 573265 * 2 ^ 59
def prefixEnd_573265 : Nat := 4983230072969 + 3 ^ 40 * 573265 * 2
def baseEnd_573265 : Nat := 130826883288802147444937

theorem tailTrace_573265 : CollatzResearch.WordTrace tailWord_573265 prefixEnd_573265 130826883288802147444937 := by
  unfold tailWord_573265
  simp only [CollatzResearch.WordTrace]
  refine ⟨20908692268166285712425249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13939128178777523808283499 20908692268166285712425249)
  ·
    refine ⟨15681519201124714284318937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20908692268166285712425249 15681519201124714284318937)
    ·
      refine ⟨11761139400843535713239203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15681519201124714284318937 11761139400843535713239203)
      ·
        refine ⟨17641709101265303569858805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11761139400843535713239203 17641709101265303569858805)
        ·
          refine ⟨1653910228243622209674263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17641709101265303569858805 1653910228243622209674263)
          ·
            refine ⟨2480865342365433314511395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1653910228243622209674263 2480865342365433314511395)
            ·
              refine ⟨3721298013548149971767093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2480865342365433314511395 3721298013548149971767093)
              ·
                refine ⟨348871688770139059853165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3721298013548149971767093 348871688770139059853165)
                ·
                  refine ⟨130826883288802147444937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 348871688770139059853165 130826883288802147444937)
                  ·
                    rfl

theorem cell21_573265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 3].length) (baseStart_573265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573265 prefixEnd_573265 := by exact prefixLift 573265
  have htrace : WordTrace (prefixWord ++ tailWord_573265) baseStart_573265 baseEnd_573265 := by
    simpa [prefixWord, tailWord_573265, baseEnd_573265] using wordTrace_append hprefix tailTrace_573265
  have hstable : (prefixWord ++ tailWord_573265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573265).length < 2 ^ (prefixWord ++ tailWord_573265).sum := by decide
  have hdescent : baseEnd_573265 < baseStart_573265 := by decide
  rcases family_descends (prefixWord ++ tailWord_573265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573279 : List Nat := [1, 1, 2, 3, 1, 4, 3, 2, 4]
def baseStart_573279 : Nat := 118140960795 + 573279 * 2 ^ 59
def prefixEnd_573279 : Nat := 4983230072969 + 3 ^ 40 * 573279 * 2
def baseEnd_573279 : Nat := 130830078279541234211575

theorem tailTrace_573279 : CollatzResearch.WordTrace tailWord_573279 prefixEnd_573279 130830078279541234211575 := by
  unfold tailWord_573279
  simp only [CollatzResearch.WordTrace]
  refine ⟨20909202890115566103434891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13939468593410377402289927 20909202890115566103434891)
  ·
    refine ⟨31363804335173349155152337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20909202890115566103434891 31363804335173349155152337)
    ·
      refine ⟨23522853251380011866364253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31363804335173349155152337 23522853251380011866364253)
      ·
        refine ⟨8821069969267504449886595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23522853251380011866364253 8821069969267504449886595)
        ·
          refine ⟨13231604953901256674829893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8821069969267504449886595 13231604953901256674829893)
          ·
            refine ⟨2480925928856485626530605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13231604953901256674829893 2480925928856485626530605)
            ·
              refine ⟨930347223321182109948977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2480925928856485626530605 930347223321182109948977)
              ·
                refine ⟨697760417490886582461733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 930347223321182109948977 697760417490886582461733)
                ·
                  refine ⟨130830078279541234211575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 697760417490886582461733 130830078279541234211575)
                  ·
                    rfl

theorem cell21_573279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 4].length) (baseStart_573279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573279 prefixEnd_573279 := by exact prefixLift 573279
  have htrace : WordTrace (prefixWord ++ tailWord_573279) baseStart_573279 baseEnd_573279 := by
    simpa [prefixWord, tailWord_573279, baseEnd_573279] using wordTrace_append hprefix tailTrace_573279
  have hstable : (prefixWord ++ tailWord_573279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573279).length < 2 ^ (prefixWord ++ tailWord_573279).sum := by decide
  have hdescent : baseEnd_573279 < baseStart_573279 := by decide
  rcases family_descends (prefixWord ++ tailWord_573279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573282 : List Nat := [3, 3, 2, 1, 2, 1, 2, 4, 3]
def baseStart_573282 : Nat := 118140960795 + 573282 * 2 ^ 59
def prefixEnd_573282 : Nat := 4983230072969 + 3 ^ 40 * 573282 * 2
def baseEnd_573282 : Nat := 130830762920413895661569

theorem tailTrace_573282 : CollatzResearch.WordTrace tailWord_573282 prefixEnd_573282 130830762920413895661569 := by
  unfold tailWord_573282
  simp only [CollatzResearch.WordTrace]
  refine ⟨5227328077276174403948525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13939541539403131743862733 5227328077276174403948525)
  ·
    refine ⟨1960248028978565401480697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5227328077276174403948525 1960248028978565401480697)
    ·
      refine ⟨1470186021733924051110523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1960248028978565401480697 1470186021733924051110523)
      ·
        refine ⟨2205279032600886076665785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1470186021733924051110523 2205279032600886076665785)
        ·
          refine ⟨1653959274450664557499339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2205279032600886076665785 1653959274450664557499339)
          ·
            refine ⟨2480938911675996836249009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1653959274450664557499339 2480938911675996836249009)
            ·
              refine ⟨1860704183756997627186757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2480938911675996836249009 1860704183756997627186757)
              ·
                refine ⟨348882034454437055097517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1860704183756997627186757 348882034454437055097517)
                ·
                  refine ⟨130830762920413895661569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 348882034454437055097517 130830762920413895661569)
                  ·
                    rfl

theorem cell21_573282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_573282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573282 prefixEnd_573282 := by exact prefixLift 573282
  have htrace : WordTrace (prefixWord ++ tailWord_573282) baseStart_573282 baseEnd_573282 := by
    simpa [prefixWord, tailWord_573282, baseEnd_573282] using wordTrace_append hprefix tailTrace_573282
  have hstable : (prefixWord ++ tailWord_573282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573282).length < 2 ^ (prefixWord ++ tailWord_573282).sum := by decide
  have hdescent : baseEnd_573282 < baseStart_573282 := by decide
  rcases family_descends (prefixWord ++ tailWord_573282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573341 : List Nat := [1, 4, 2, 1, 2, 4, 1, 1, 5]
def baseStart_573341 : Nat := 118140960795 + 573341 * 2 ^ 59
def prefixEnd_573341 : Nat := 4983230072969 + 3 ^ 40 * 573341 * 2
def baseEnd_573341 : Nat := 130844227524242904178115

theorem tailTrace_573341 : CollatzResearch.WordTrace tailWord_573341 prefixEnd_573341 130844227524242904178115 := by
  unfold tailWord_573341
  simp only [CollatzResearch.WordTrace]
  refine ⟨20911464215890950692191877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13940976143927300461461251 20911464215890950692191877)
  ·
    refine ⟨3920899540479553254785977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20911464215890950692191877 3920899540479553254785977)
    ·
      refine ⟨2940674655359664941089483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3920899540479553254785977 2940674655359664941089483)
      ·
        refine ⟨4411011983039497411634225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2940674655359664941089483 4411011983039497411634225)
        ·
          refine ⟨3308258987279623058725669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4411011983039497411634225 3308258987279623058725669)
          ·
            refine ⟨620298560114929323511063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3308258987279623058725669 620298560114929323511063)
            ·
              refine ⟨930447840172393985266595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 620298560114929323511063 930447840172393985266595)
              ·
                refine ⟨1395671760258590977899893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 930447840172393985266595 1395671760258590977899893)
                ·
                  refine ⟨130844227524242904178115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1395671760258590977899893 130844227524242904178115)
                  ·
                    rfl

theorem cell21_573341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_573341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573341 prefixEnd_573341 := by exact prefixLift 573341
  have htrace : WordTrace (prefixWord ++ tailWord_573341) baseStart_573341 baseEnd_573341 := by
    simpa [prefixWord, tailWord_573341, baseEnd_573341] using wordTrace_append hprefix tailTrace_573341
  have hstable : (prefixWord ++ tailWord_573341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573341).length < 2 ^ (prefixWord ++ tailWord_573341).sum := by decide
  have hdescent : baseEnd_573341 < baseStart_573341 := by decide
  rcases family_descends (prefixWord ++ tailWord_573341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573459 : List Nat := [1, 1, 1, 2, 1, 4, 3, 3, 5]
def baseStart_573459 : Nat := 118140960795 + 573459 * 2 ^ 59
def prefixEnd_573459 : Nat := 4983230072969 + 3 ^ 40 * 573459 * 2
def baseEnd_573459 : Nat := 130871156731900921211207

theorem tailTrace_573459 : CollatzResearch.WordTrace tailWord_573459 prefixEnd_573459 130871156731900921211207 := by
  unfold tailWord_573459
  simp only [CollatzResearch.WordTrace]
  refine ⟨20915768029463456844987431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13943845352975637896658287 20915768029463456844987431)
  ·
    refine ⟨31373652044195185267481147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20915768029463456844987431 31373652044195185267481147)
    ·
      refine ⟨47060478066292777901221721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31373652044195185267481147 47060478066292777901221721)
      ·
        refine ⟨35295358549719583425916291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47060478066292777901221721 35295358549719583425916291)
        ·
          refine ⟨52943037824579375138874437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35295358549719583425916291 52943037824579375138874437)
          ·
            refine ⟨9926819592108632838538957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52943037824579375138874437 9926819592108632838538957)
            ·
              refine ⟨3722557347040737314452109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9926819592108632838538957 3722557347040737314452109)
              ·
                refine ⟨1395959005140276492919541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3722557347040737314452109 1395959005140276492919541)
                ·
                  refine ⟨130871156731900921211207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1395959005140276492919541 130871156731900921211207)
                  ·
                    rfl

theorem cell21_573459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 5].length) (baseStart_573459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573459 prefixEnd_573459 := by exact prefixLift 573459
  have htrace : WordTrace (prefixWord ++ tailWord_573459) baseStart_573459 baseEnd_573459 := by
    simpa [prefixWord, tailWord_573459, baseEnd_573459] using wordTrace_append hprefix tailTrace_573459
  have hstable : (prefixWord ++ tailWord_573459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573459).length < 2 ^ (prefixWord ++ tailWord_573459).sum := by decide
  have hdescent : baseEnd_573459 < baseStart_573459 := by decide
  rcases family_descends (prefixWord ++ tailWord_573459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573490 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 6]
def baseStart_573490 : Nat := 118140960795 + 573490 * 2 ^ 59
def prefixEnd_573490 : Nat := 4983230072969 + 3 ^ 40 * 573490 * 2
def baseEnd_573490 : Nat := 130878231354251756194477

theorem tailTrace_573490 : CollatzResearch.WordTrace tailWord_573490 prefixEnd_573490 130878231354251756194477 := by
  unfold tailWord_573490
  simp only [CollatzResearch.WordTrace]
  refine ⟨5229224673087787284841481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13944599128234099426243949 5229224673087787284841481)
  ·
    refine ⟨3921918504815840463631111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5229224673087787284841481 3921918504815840463631111)
    ·
      refine ⟨5882877757223760695446667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3921918504815840463631111 5882877757223760695446667)
      ·
        refine ⟨8824316635835641043170001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5882877757223760695446667 8824316635835641043170001)
        ·
          refine ⟨6618237476876730782377501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8824316635835641043170001 6618237476876730782377501)
          ·
            refine ⟨2481839053828774043391563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6618237476876730782377501 2481839053828774043391563)
            ·
              refine ⟨3722758580743161065087345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2481839053828774043391563 3722758580743161065087345)
              ·
                refine ⟨2792068935557370798815509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3722758580743161065087345 2792068935557370798815509)
                ·
                  refine ⟨130878231354251756194477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2792068935557370798815509 130878231354251756194477)
                  ·
                    rfl

theorem cell21_573490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_573490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573490 prefixEnd_573490 := by exact prefixLift 573490
  have htrace : WordTrace (prefixWord ++ tailWord_573490) baseStart_573490 baseEnd_573490 := by
    simpa [prefixWord, tailWord_573490, baseEnd_573490] using wordTrace_append hprefix tailTrace_573490
  have hstable : (prefixWord ++ tailWord_573490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573490).length < 2 ^ (prefixWord ++ tailWord_573490).sum := by decide
  have hdescent : baseEnd_573490 < baseStart_573490 := by decide
  rcases family_descends (prefixWord ++ tailWord_573490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573493 : List Nat := [1, 3, 3, 1, 1, 1, 5, 3, 3]
def baseStart_573493 : Nat := 118140960795 + 573493 * 2 ^ 59
def prefixEnd_573493 : Nat := 4983230072969 + 3 ^ 40 * 573493 * 2
def baseEnd_573493 : Nat := 130878915995124417644471

theorem tailTrace_573493 : CollatzResearch.WordTrace tailWord_573493 prefixEnd_573493 130878915995124417644471 := by
  unfold tailWord_573493
  simp only [CollatzResearch.WordTrace]
  refine ⟨20917008111340280651725133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13944672074226853767816755 20917008111340280651725133)
  ·
    refine ⟨7843878041752605244396925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20917008111340280651725133 7843878041752605244396925)
    ·
      refine ⟨2941454265657226966648847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7843878041752605244396925 2941454265657226966648847)
      ·
        refine ⟨4412181398485840449973271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2941454265657226966648847 4412181398485840449973271)
        ·
          refine ⟨6618272097728760674959907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4412181398485840449973271 6618272097728760674959907)
          ·
            refine ⟨9927408146593141012439861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6618272097728760674959907 9927408146593141012439861)
            ·
              refine ⟨930694513743106969916237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9927408146593141012439861 930694513743106969916237)
              ·
                refine ⟨349010442653665113718589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 930694513743106969916237 349010442653665113718589)
                ·
                  refine ⟨130878915995124417644471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 349010442653665113718589 130878915995124417644471)
                  ·
                    rfl

theorem cell21_573493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_573493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573493 prefixEnd_573493 := by exact prefixLift 573493
  have htrace : WordTrace (prefixWord ++ tailWord_573493) baseStart_573493 baseEnd_573493 := by
    simpa [prefixWord, tailWord_573493, baseEnd_573493] using wordTrace_append hprefix tailTrace_573493
  have hstable : (prefixWord ++ tailWord_573493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573493).length < 2 ^ (prefixWord ++ tailWord_573493).sum := by decide
  have hdescent : baseEnd_573493 < baseStart_573493 := by decide
  rcases family_descends (prefixWord ++ tailWord_573493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573504 : List Nat := [2, 1, 1, 2, 2, 4, 9]
def baseStart_573504 : Nat := 118140960795 + 573504 * 2 ^ 59
def prefixEnd_573504 : Nat := 4983230072969 + 3 ^ 40 * 573504 * 2
def baseEnd_573504 : Nat := 14542380704998982551235

theorem tailTrace_573504 : CollatzResearch.WordTrace tailWord_573504 prefixEnd_573504 14542380704998982551235 := by
  unfold tailWord_573504
  simp only [CollatzResearch.WordTrace]
  refine ⟨10458704657150214765187783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13944939542866953020250377 10458704657150214765187783)
  ·
    refine ⟨15688056985725322147781675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10458704657150214765187783 15688056985725322147781675)
    ·
      refine ⟨23532085478587983221672513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15688056985725322147781675 23532085478587983221672513)
      ·
        refine ⟨17649064108940987416254385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23532085478587983221672513 17649064108940987416254385)
        ·
          refine ⟨13236798081705740562190789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17649064108940987416254385 13236798081705740562190789)
          ·
            refine ⟨2481899640319826355410773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13236798081705740562190789 2481899640319826355410773)
            ·
              refine ⟨14542380704998982551235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2481899640319826355410773 14542380704998982551235)
              ·
                rfl

theorem cell21_573504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 9].length) (baseStart_573504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573504 prefixEnd_573504 := by exact prefixLift 573504
  have htrace : WordTrace (prefixWord ++ tailWord_573504) baseStart_573504 baseEnd_573504 := by
    simpa [prefixWord, tailWord_573504, baseEnd_573504] using wordTrace_append hprefix tailTrace_573504
  have hstable : (prefixWord ++ tailWord_573504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573504).length < 2 ^ (prefixWord ++ tailWord_573504).sum := by decide
  have hdescent : baseEnd_573504 < baseStart_573504 := by decide
  rcases family_descends (prefixWord ++ tailWord_573504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573617 : List Nat := [1, 2, 2, 5, 3, 1, 1, 2, 4]
def baseStart_573617 : Nat := 118140960795 + 573617 * 2 ^ 59
def prefixEnd_573617 : Nat := 4983230072969 + 3 ^ 40 * 573617 * 2
def baseEnd_573617 : Nat := 130907214484527757577551

theorem tailTrace_573617 : CollatzResearch.WordTrace tailWord_573617 prefixEnd_573617 130907214484527757577551 := by
  unfold tailWord_573617
  simp only [CollatzResearch.WordTrace]
  refine ⟨20921530762891049829239105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13947687175260699886159403 20921530762891049829239105)
  ·
    refine ⟨15691148072168287371929329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20921530762891049829239105 15691148072168287371929329)
    ·
      refine ⟨11768361054126215528946997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15691148072168287371929329 11768361054126215528946997)
      ·
        refine ⟨1103283848824332705838781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11768361054126215528946997 1103283848824332705838781)
        ·
          refine ⟨413731443309124764689543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1103283848824332705838781 413731443309124764689543)
          ·
            refine ⟨620597164963687147034315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413731443309124764689543 620597164963687147034315)
            ·
              refine ⟨930895747445530720551473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 620597164963687147034315 930895747445530720551473)
              ·
                refine ⟨698171810584148040413605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 930895747445530720551473 698171810584148040413605)
                ·
                  refine ⟨130907214484527757577551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 698171810584148040413605 130907214484527757577551)
                  ·
                    rfl

theorem cell21_573617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 4].length) (baseStart_573617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573617 prefixEnd_573617 := by exact prefixLift 573617
  have htrace : WordTrace (prefixWord ++ tailWord_573617) baseStart_573617 baseEnd_573617 := by
    simpa [prefixWord, tailWord_573617, baseEnd_573617] using wordTrace_append hprefix tailTrace_573617
  have hstable : (prefixWord ++ tailWord_573617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573617).length < 2 ^ (prefixWord ++ tailWord_573617).sum := by decide
  have hdescent : baseEnd_573617 < baseStart_573617 := by decide
  rcases family_descends (prefixWord ++ tailWord_573617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573634 : List Nat := [3, 5, 1, 1, 1, 2, 3, 1, 4]
def baseStart_573634 : Nat := 118140960795 + 573634 * 2 ^ 59
def prefixEnd_573634 : Nat := 4983230072969 + 3 ^ 40 * 573634 * 2
def baseEnd_573634 : Nat := 130911094116139505794183

theorem tailTrace_573634 : CollatzResearch.WordTrace tailWord_573634 prefixEnd_573634 130911094116139505794183 := by
  unfold tailWord_573634
  simp only [CollatzResearch.WordTrace]
  refine ⟨5230537700957365433151989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13948100535886307821738637 5230537700957365433151989)
  ·
    refine ⟨490362909464753009357999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5230537700957365433151989 490362909464753009357999)
    ·
      refine ⟨735544364197129514036999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 490362909464753009357999 735544364197129514036999)
      ·
        refine ⟨1103316546295694271055499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 735544364197129514036999 1103316546295694271055499)
        ·
          refine ⟨1654974819443541406583249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1103316546295694271055499 1654974819443541406583249)
          ·
            refine ⟨1241231114582656054937437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1654974819443541406583249 1241231114582656054937437)
            ·
              refine ⟨465461667968496020601539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1241231114582656054937437 465461667968496020601539)
              ·
                refine ⟨698192501952744030902309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465461667968496020601539 698192501952744030902309)
                ·
                  refine ⟨130911094116139505794183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 698192501952744030902309 130911094116139505794183)
                  ·
                    rfl

theorem cell21_573634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_573634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573634 prefixEnd_573634 := by exact prefixLift 573634
  have htrace : WordTrace (prefixWord ++ tailWord_573634) baseStart_573634 baseEnd_573634 := by
    simpa [prefixWord, tailWord_573634, baseEnd_573634] using wordTrace_append hprefix tailTrace_573634
  have hstable : (prefixWord ++ tailWord_573634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573634).length < 2 ^ (prefixWord ++ tailWord_573634).sum := by decide
  have hdescent : baseEnd_573634 < baseStart_573634 := by decide
  rcases family_descends (prefixWord ++ tailWord_573634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573701 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 8]
def baseStart_573701 : Nat := 118140960795 + 573701 * 2 ^ 59
def prefixEnd_573701 : Nat := 4983230072969 + 3 ^ 40 * 573701 * 2
def baseEnd_573701 : Nat := 130926384428962278177379

theorem tailTrace_573701 : CollatzResearch.WordTrace tailWord_573701 prefixEnd_573701 130926384428962278177379 := by
  unfold tailWord_573701
  simp only [CollatzResearch.WordTrace]
  refine ⟨20924594494586732175296957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13949729663057821450197971 20924594494586732175296957)
  ·
    refine ⟨7846722935470024565736359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20924594494586732175296957 7846722935470024565736359)
    ·
      refine ⟨11770084403205036848604539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7846722935470024565736359 11770084403205036848604539)
      ·
        refine ⟨17655126604807555272906809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11770084403205036848604539 17655126604807555272906809)
        ·
          refine ⟨13241344953605666454680107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17655126604807555272906809 13241344953605666454680107)
          ·
            refine ⟨19862017430408499682020161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13241344953605666454680107 19862017430408499682020161)
            ·
              refine ⟨14896513072806374761515121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19862017430408499682020161 14896513072806374761515121)
              ·
                refine ⟨11172384804604781071136341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14896513072806374761515121 11172384804604781071136341)
                ·
                  refine ⟨130926384428962278177379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11172384804604781071136341 130926384428962278177379)
                  ·
                    rfl

theorem cell21_573701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_573701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573701 prefixEnd_573701 := by exact prefixLift 573701
  have htrace : WordTrace (prefixWord ++ tailWord_573701) baseStart_573701 baseEnd_573701 := by
    simpa [prefixWord, tailWord_573701, baseEnd_573701] using wordTrace_append hprefix tailTrace_573701
  have hstable : (prefixWord ++ tailWord_573701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573701).length < 2 ^ (prefixWord ++ tailWord_573701).sum := by decide
  have hdescent : baseEnd_573701 < baseStart_573701 := by decide
  rcases family_descends (prefixWord ++ tailWord_573701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573732 : List Nat := [2, 3, 1, 3, 1, 11]
def baseStart_573732 : Nat := 118140960795 + 573732 * 2 ^ 59
def prefixEnd_573732 : Nat := 4983230072969 + 3 ^ 40 * 573732 * 2
def baseEnd_573732 : Nat := 4849387372270856042987

theorem tailTrace_573732 : CollatzResearch.WordTrace tailWord_573732 prefixEnd_573732 4849387372270856042987 := by
  unfold tailWord_573732
  simp only [CollatzResearch.WordTrace]
  refine ⟨10462862578737212234837725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13950483438316282979783633 10462862578737212234837725)
  ·
    refine ⟨3923573467026454588064147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10462862578737212234837725 3923573467026454588064147)
    ·
      refine ⟨5885360200539681882096221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3923573467026454588064147 5885360200539681882096221)
      ·
        refine ⟨2207010075202380705786083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5885360200539681882096221 2207010075202380705786083)
        ·
          refine ⟨3310515112803571058679125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2207010075202380705786083 3310515112803571058679125)
          ·
            refine ⟨4849387372270856042987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3310515112803571058679125 4849387372270856042987)
            ·
              rfl

theorem cell21_573732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 11].length) (baseStart_573732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573732 prefixEnd_573732 := by exact prefixLift 573732
  have htrace : WordTrace (prefixWord ++ tailWord_573732) baseStart_573732 baseEnd_573732 := by
    simpa [prefixWord, tailWord_573732, baseEnd_573732] using wordTrace_append hprefix tailTrace_573732
  have hstable : (prefixWord ++ tailWord_573732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573732).length < 2 ^ (prefixWord ++ tailWord_573732).sum := by decide
  have hdescent : baseEnd_573732 < baseStart_573732 := by decide
  rcases family_descends (prefixWord ++ tailWord_573732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573738 : List Nat := [3, 1, 4, 2, 2, 1, 1, 4, 3]
def baseStart_573738 : Nat := 118140960795 + 573738 * 2 ^ 59
def prefixEnd_573738 : Nat := 4983230072969 + 3 ^ 40 * 573738 * 2
def baseEnd_573738 : Nat := 130934828333058436060637

theorem tailTrace_573738 : CollatzResearch.WordTrace tailWord_573738 prefixEnd_573738 130934828333058436060637 := by
  unfold tailWord_573738
  simp only [CollatzResearch.WordTrace]
  refine ⟨5231485998863171873598467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13950629330301791662929245 5231485998863171873598467)
  ·
    refine ⟨7847228998294757810397701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5231485998863171873598467 7847228998294757810397701)
    ·
      refine ⟨1471355437180267089449569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7847228998294757810397701 1471355437180267089449569)
      ·
        refine ⟨1103516577885200317087177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1471355437180267089449569 1103516577885200317087177)
        ·
          refine ⟨827637433413900237815383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1103516577885200317087177 827637433413900237815383)
          ·
            refine ⟨1241456150120850356723075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827637433413900237815383 1241456150120850356723075)
            ·
              refine ⟨1862184225181275535084613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1241456150120850356723075 1862184225181275535084613)
              ·
                refine ⟨349159542221489162828365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1862184225181275535084613 349159542221489162828365)
                ·
                  refine ⟨130934828333058436060637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 349159542221489162828365 130934828333058436060637)
                  ·
                    rfl

theorem cell21_573738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_573738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573738 prefixEnd_573738 := by exact prefixLift 573738
  have htrace : WordTrace (prefixWord ++ tailWord_573738) baseStart_573738 baseEnd_573738 := by
    simpa [prefixWord, tailWord_573738, baseEnd_573738] using wordTrace_append hprefix tailTrace_573738
  have hstable : (prefixWord ++ tailWord_573738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573738).length < 2 ^ (prefixWord ++ tailWord_573738).sum := by decide
  have hdescent : baseEnd_573738 < baseStart_573738 := by decide
  rcases family_descends (prefixWord ++ tailWord_573738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573825 : List Nat := [1, 2, 4, 3, 1, 2, 1, 7]
def baseStart_573825 : Nat := 118140960795 + 573825 * 2 ^ 59
def prefixEnd_573825 : Nat := 4983230072969 + 3 ^ 40 * 573825 * 2
def baseEnd_573825 : Nat := 43651560972788539370153

theorem tailTrace_573825 : CollatzResearch.WordTrace tailWord_573825 prefixEnd_573825 43651560972788539370153 := by
  unfold tailWord_573825
  simp only [CollatzResearch.WordTrace]
  refine ⟨20929117146137501352810929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13952744764091667568540619 20929117146137501352810929)
  ·
    refine ⟨15696837859603126014608197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20929117146137501352810929 15696837859603126014608197)
    ·
      refine ⟨2943157098675586127739037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15696837859603126014608197 2943157098675586127739037)
      ·
        refine ⟨1103683912003344797902139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2943157098675586127739037 1103683912003344797902139)
        ·
          refine ⟨1655525868005017196853209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1103683912003344797902139 1655525868005017196853209)
          ·
            refine ⟨1241644401003762897639907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1655525868005017196853209 1241644401003762897639907)
            ·
              refine ⟨1862466601505644346459861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1241644401003762897639907 1862466601505644346459861)
              ·
                refine ⟨43651560972788539370153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1862466601505644346459861 43651560972788539370153)
                ·
                  rfl

theorem cell21_573825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 7].length) (baseStart_573825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573825 prefixEnd_573825 := by exact prefixLift 573825
  have htrace : WordTrace (prefixWord ++ tailWord_573825) baseStart_573825 baseEnd_573825 := by
    simpa [prefixWord, tailWord_573825, baseEnd_573825] using wordTrace_append hprefix tailTrace_573825
  have hstable : (prefixWord ++ tailWord_573825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573825).length < 2 ^ (prefixWord ++ tailWord_573825).sum := by decide
  have hdescent : baseEnd_573825 < baseStart_573825 := by decide
  rcases family_descends (prefixWord ++ tailWord_573825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573856 : List Nat := [2, 1, 1, 4, 1, 5, 1, 1, 5]
def baseStart_573856 : Nat := 118140960795 + 573856 * 2 ^ 59
def prefixEnd_573856 : Nat := 4983230072969 + 3 ^ 40 * 573856 * 2
def baseEnd_573856 : Nat := 130961757540716453093729

theorem tailTrace_573856 : CollatzResearch.WordTrace tailWord_573856 prefixEnd_573856 130961757540716453093729 := by
  unfold tailWord_573856
  simp only [CollatzResearch.WordTrace]
  refine ⟨10465123904512596823594711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13953498539350129098126281 10465123904512596823594711)
  ·
    refine ⟨15697685856768895235392067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10465123904512596823594711 15697685856768895235392067)
    ·
      refine ⟨23546528785153342853088101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15697685856768895235392067 23546528785153342853088101)
      ·
        refine ⟨4414974147216251784954019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23546528785153342853088101 4414974147216251784954019)
        ·
          refine ⟨6622461220824377677431029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4414974147216251784954019 6622461220824377677431029)
          ·
            refine ⟨620855739452285407259159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6622461220824377677431029 620855739452285407259159)
            ·
              refine ⟨931283609178428110888739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 620855739452285407259159 931283609178428110888739)
              ·
                refine ⟨1396925413767642166333109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 931283609178428110888739 1396925413767642166333109)
                ·
                  refine ⟨130961757540716453093729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1396925413767642166333109 130961757540716453093729)
                  ·
                    rfl

theorem cell21_573856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 5].length) (baseStart_573856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573856 prefixEnd_573856 := by exact prefixLift 573856
  have htrace : WordTrace (prefixWord ++ tailWord_573856) baseStart_573856 baseEnd_573856 := by
    simpa [prefixWord, tailWord_573856, baseEnd_573856] using wordTrace_append hprefix tailTrace_573856
  have hstable : (prefixWord ++ tailWord_573856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573856).length < 2 ^ (prefixWord ++ tailWord_573856).sum := by decide
  have hdescent : baseEnd_573856 < baseStart_573856 := by decide
  rcases family_descends (prefixWord ++ tailWord_573856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573963 : List Nat := [1, 1, 1, 1, 7, 3, 1, 2, 4]
def baseStart_573963 : Nat := 118140960795 + 573963 * 2 ^ 59
def prefixEnd_573963 : Nat := 4983230072969 + 3 ^ 40 * 573963 * 2
def baseEnd_573963 : Nat := 130986176398508044810177

theorem tailTrace_573963 : CollatzResearch.WordTrace tailWord_573963 prefixEnd_573963 130986176398508044810177 := by
  unfold tailWord_573963
  simp only [CollatzResearch.WordTrace]
  refine ⟨20934150419637550921334543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13956100279758367280889695 20934150419637550921334543)
  ·
    refine ⟨31401225629456326382001815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20934150419637550921334543 31401225629456326382001815)
    ·
      refine ⟨47101838444184489573002723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31401225629456326382001815 47101838444184489573002723)
      ·
        refine ⟨70652757666276734359504085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47101838444184489573002723 70652757666276734359504085)
        ·
          refine ⟨1655924007803360961550877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 70652757666276734359504085 1655924007803360961550877)
          ·
            refine ⟨620971502926260360581579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1655924007803360961550877 620971502926260360581579)
            ·
              refine ⟨931457254389390540872369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 620971502926260360581579 931457254389390540872369)
              ·
                refine ⟨698592940792042905654277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 931457254389390540872369 698592940792042905654277)
                ·
                  refine ⟨130986176398508044810177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 698592940792042905654277 130986176398508044810177)
                  ·
                    rfl

theorem cell21_573963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 4].length) (baseStart_573963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573963 prefixEnd_573963 := by exact prefixLift 573963
  have htrace : WordTrace (prefixWord ++ tailWord_573963) baseStart_573963 baseEnd_573963 := by
    simpa [prefixWord, tailWord_573963, baseEnd_573963] using wordTrace_append hprefix tailTrace_573963
  have hstable : (prefixWord ++ tailWord_573963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573963).length < 2 ^ (prefixWord ++ tailWord_573963).sum := by decide
  have hdescent : baseEnd_573963 < baseStart_573963 := by decide
  rcases family_descends (prefixWord ++ tailWord_573963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573994 : List Nat := [3, 1, 4, 1, 1, 4, 2, 5]
def baseStart_573994 : Nat := 118140960795 + 573994 * 2 ^ 59
def prefixEnd_573994 : Nat := 4983230072969 + 3 ^ 40 * 573994 * 2
def baseEnd_573994 : Nat := 43664417006952959931149

theorem tailTrace_573994 : CollatzResearch.WordTrace tailWord_573994 prefixEnd_573994 43664417006952959931149 := by
  unfold tailWord_573994
  simp only [CollatzResearch.WordTrace]
  refine ⟨5233820270631310803928259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13956854055016828810475357 5233820270631310803928259)
  ·
    refine ⟨7850730405946966205892389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5233820270631310803928259 7850730405946966205892389)
    ·
      refine ⟨1472011951115056163604823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7850730405946966205892389 1472011951115056163604823)
      ·
        refine ⟨2208017926672584245407235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1472011951115056163604823 2208017926672584245407235)
        ·
          refine ⟨3312026890008876368110853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2208017926672584245407235 3312026890008876368110853)
          ·
            refine ⟨621005041876664319020785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3312026890008876368110853 621005041876664319020785)
            ·
              refine ⟨465753781407498239265589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 621005041876664319020785 465753781407498239265589)
              ·
                refine ⟨43664417006952959931149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 465753781407498239265589 43664417006952959931149)
                ·
                  rfl

theorem cell21_573994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_573994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_573994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_573994 prefixEnd_573994 := by exact prefixLift 573994
  have htrace : WordTrace (prefixWord ++ tailWord_573994) baseStart_573994 baseEnd_573994 := by
    simpa [prefixWord, tailWord_573994, baseEnd_573994] using wordTrace_append hprefix tailTrace_573994
  have hstable : (prefixWord ++ tailWord_573994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573994).length < 2 ^ (prefixWord ++ tailWord_573994).sum := by decide
  have hdescent : baseEnd_573994 < baseStart_573994 := by decide
  rcases family_descends (prefixWord ++ tailWord_573994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574005 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 8]
def baseStart_574005 : Nat := 118140960795 + 574005 * 2 ^ 59
def prefixEnd_574005 : Nat := 4983230072969 + 3 ^ 40 * 574005 * 2
def baseEnd_574005 : Nat := 130995761370725305110091

theorem tailTrace_574005 : CollatzResearch.WordTrace tailWord_574005 prefixEnd_574005 130995761370725305110091 := by
  unfold tailWord_574005
  simp only [CollatzResearch.WordTrace]
  refine ⟨20935682285485392094363469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13957121523656928062908979 20935682285485392094363469)
  ·
    refine ⟨7850880857057022035386301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20935682285485392094363469 7850880857057022035386301)
    ·
      refine ⟨2944080321396383263269863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7850880857057022035386301 2944080321396383263269863)
      ·
        refine ⟨4416120482094574894904795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2944080321396383263269863 4416120482094574894904795)
        ·
          refine ⟨6624180723141862342357193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4416120482094574894904795 6624180723141862342357193)
          ·
            refine ⟨4968135542356396756767895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6624180723141862342357193 4968135542356396756767895)
            ·
              refine ⟨7452203313534595135151843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4968135542356396756767895 7452203313534595135151843)
              ·
                refine ⟨11178304970301892702727765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7452203313534595135151843 11178304970301892702727765)
                ·
                  refine ⟨130995761370725305110091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11178304970301892702727765 130995761370725305110091)
                  ·
                    rfl

theorem cell21_574005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_574005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574005 prefixEnd_574005 := by exact prefixLift 574005
  have htrace : WordTrace (prefixWord ++ tailWord_574005) baseStart_574005 baseEnd_574005 := by
    simpa [prefixWord, tailWord_574005, baseEnd_574005] using wordTrace_append hprefix tailTrace_574005
  have hstable : (prefixWord ++ tailWord_574005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574005).length < 2 ^ (prefixWord ++ tailWord_574005).sum := by decide
  have hdescent : baseEnd_574005 < baseStart_574005 := by decide
  rcases family_descends (prefixWord ++ tailWord_574005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574036 : List Nat := [2, 4, 1, 1, 1, 3, 1, 8]
def baseStart_574036 : Nat := 118140960795 + 574036 * 2 ^ 59
def prefixEnd_574036 : Nat := 4983230072969 + 3 ^ 40 * 574036 * 2
def baseEnd_574036 : Nat := 43667611997692046697787

theorem tailTrace_574036 : CollatzResearch.WordTrace tailWord_574036 prefixEnd_574036 43667611997692046697787 := by
  unfold tailWord_574036
  simp only [CollatzResearch.WordTrace]
  refine ⟨10468406474186542194370981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13957875298915389592494641 10468406474186542194370981)
  ·
    refine ⟨1962826213909976661444559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10468406474186542194370981 1962826213909976661444559)
    ·
      refine ⟨2944239320864964992166839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1962826213909976661444559 2944239320864964992166839)
      ·
        refine ⟨4416358981297447488250259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2944239320864964992166839 4416358981297447488250259)
        ·
          refine ⟨6624538471946171232375389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4416358981297447488250259 6624538471946171232375389)
          ·
            refine ⟨2484201926979814212140771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6624538471946171232375389 2484201926979814212140771)
            ·
              refine ⟨3726302890469721318211157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2484201926979814212140771 3726302890469721318211157)
              ·
                refine ⟨43667611997692046697787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3726302890469721318211157 43667611997692046697787)
                ·
                  rfl

theorem cell21_574036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 8].length) (baseStart_574036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574036 prefixEnd_574036 := by exact prefixLift 574036
  have htrace : WordTrace (prefixWord ++ tailWord_574036) baseStart_574036 baseEnd_574036 := by
    simpa [prefixWord, tailWord_574036, baseEnd_574036] using wordTrace_append hprefix tailTrace_574036
  have hstable : (prefixWord ++ tailWord_574036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574036).length < 2 ^ (prefixWord ++ tailWord_574036).sum := by decide
  have hdescent : baseEnd_574036 < baseStart_574036 := by decide
  rcases family_descends (prefixWord ++ tailWord_574036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574129 : List Nat := [1, 2, 2, 6, 1, 1, 8]
def baseStart_574129 : Nat := 118140960795 + 574129 * 2 ^ 59
def prefixEnd_574129 : Nat := 4983230072969 + 3 ^ 40 * 574129 * 2
def baseEnd_574129 : Nat := 14558228873347627227019

theorem tailTrace_574129 : CollatzResearch.WordTrace tailWord_574129 prefixEnd_574129 14558228873347627227019 := by
  unfold tailWord_574129
  simp only [CollatzResearch.WordTrace]
  refine ⟨20940204937036161271877441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13960136624690774181251627 20940204937036161271877441)
  ·
    refine ⟨15705153702777120953908081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20940204937036161271877441 15705153702777120953908081)
    ·
      refine ⟨11778865277082840715431061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15705153702777120953908081 11778865277082840715431061)
      ·
        refine ⟨552134309863258158535831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11778865277082840715431061 552134309863258158535831)
        ·
          refine ⟨828201464794887237803747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552134309863258158535831 828201464794887237803747)
          ·
            refine ⟨1242302197192330856705621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828201464794887237803747 1242302197192330856705621)
            ·
              refine ⟨14558228873347627227019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1242302197192330856705621 14558228873347627227019)
              ·
                rfl

theorem cell21_574129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 8].length) (baseStart_574129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574129 prefixEnd_574129 := by exact prefixLift 574129
  have htrace : WordTrace (prefixWord ++ tailWord_574129) baseStart_574129 baseEnd_574129 := by
    simpa [prefixWord, tailWord_574129, baseEnd_574129] using wordTrace_append hprefix tailTrace_574129
  have hstable : (prefixWord ++ tailWord_574129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574129).length < 2 ^ (prefixWord ++ tailWord_574129).sum := by decide
  have hdescent : baseEnd_574129 < baseStart_574129 := by decide
  rcases family_descends (prefixWord ++ tailWord_574129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574143 : List Nat := [1, 1, 2, 2, 2, 5, 2, 1, 5]
def baseStart_574143 : Nat := 118140960795 + 574143 * 2 ^ 59
def prefixEnd_574143 : Nat := 4983230072969 + 3 ^ 40 * 574143 * 2
def baseEnd_574143 : Nat := 131027254850867731809809

theorem tailTrace_574143 : CollatzResearch.WordTrace tailWord_574143 prefixEnd_574143 131027254850867731809809 := by
  unfold tailWord_574143
  simp only [CollatzResearch.WordTrace]
  refine ⟨20940715558985441662887083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13960477039323627775258055 20940715558985441662887083)
  ·
    refine ⟨31411073338478162494330625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20940715558985441662887083 31411073338478162494330625)
    ·
      refine ⟨23558305003858621870747969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31411073338478162494330625 23558305003858621870747969)
      ·
        refine ⟨17668728752893966403060977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23558305003858621870747969 17668728752893966403060977)
        ·
          refine ⟨13251546564670474802295733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17668728752893966403060977 13251546564670474802295733)
          ·
            refine ⟨1242332490437857012715225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13251546564670474802295733 1242332490437857012715225)
            ·
              refine ⟨931749367828392759536419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1242332490437857012715225 931749367828392759536419)
              ·
                refine ⟨1397624051742589139304629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 931749367828392759536419 1397624051742589139304629)
                ·
                  refine ⟨131027254850867731809809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1397624051742589139304629 131027254850867731809809)
                  ·
                    rfl

theorem cell21_574143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 5].length) (baseStart_574143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574143 prefixEnd_574143 := by exact prefixLift 574143
  have htrace : WordTrace (prefixWord ++ tailWord_574143) baseStart_574143 baseEnd_574143 := by
    simpa [prefixWord, tailWord_574143, baseEnd_574143] using wordTrace_append hprefix tailTrace_574143
  have hstable : (prefixWord ++ tailWord_574143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574143).length < 2 ^ (prefixWord ++ tailWord_574143).sum := by decide
  have hdescent : baseEnd_574143 < baseStart_574143 := by decide
  rcases family_descends (prefixWord ++ tailWord_574143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574177 : List Nat := [1, 2, 3, 1, 4, 3, 1, 3, 3]
def baseStart_574177 : Nat := 118140960795 + 574177 * 2 ^ 59
def prefixEnd_574177 : Nat := 4983230072969 + 3 ^ 40 * 574177 * 2
def baseEnd_574177 : Nat := 131035014114091228243073

theorem tailTrace_574177 : CollatzResearch.WordTrace tailWord_574177 prefixEnd_574177 131035014114091228243073 := by
  unfold tailWord_574177
  simp only [CollatzResearch.WordTrace]
  refine ⟨20941955640862265469624785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13961303760574843646416523 20941955640862265469624785)
  ·
    refine ⟨15706466730646699102218589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20941955640862265469624785 15706466730646699102218589)
    ·
      refine ⟨5889925023992512163331971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15706466730646699102218589 5889925023992512163331971)
      ·
        refine ⟨8834887535988768244997957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5889925023992512163331971 8834887535988768244997957)
        ·
          refine ⟨1656541412997894045937117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8834887535988768244997957 1656541412997894045937117)
          ·
            refine ⟨621203029874210267226419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1656541412997894045937117 621203029874210267226419)
            ·
              refine ⟨931804544811315400839629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 621203029874210267226419 931804544811315400839629)
              ·
                refine ⟨349426704304243275314861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 931804544811315400839629 349426704304243275314861)
                ·
                  refine ⟨131035014114091228243073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 349426704304243275314861 131035014114091228243073)
                  ·
                    rfl

theorem cell21_574177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 3].length) (baseStart_574177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574177 prefixEnd_574177 := by exact prefixLift 574177
  have htrace : WordTrace (prefixWord ++ tailWord_574177) baseStart_574177 baseEnd_574177 := by
    simpa [prefixWord, tailWord_574177, baseEnd_574177] using wordTrace_append hprefix tailTrace_574177
  have hstable : (prefixWord ++ tailWord_574177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574177).length < 2 ^ (prefixWord ++ tailWord_574177).sum := by decide
  have hdescent : baseEnd_574177 < baseStart_574177 := by decide
  rcases family_descends (prefixWord ++ tailWord_574177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574312 : List Nat := [2, 1, 4, 2, 1, 2, 2, 4, 3]
def baseStart_574312 : Nat := 118140960795 + 574312 * 2 ^ 59
def prefixEnd_574312 : Nat := 4983230072969 + 3 ^ 40 * 574312 * 2
def baseEnd_574312 : Nat := 131065822953360993492797

theorem tailTrace_574312 : CollatzResearch.WordTrace tailWord_574312 prefixEnd_574312 131065822953360993492797 := by
  unfold tailWord_574312
  simp only [CollatzResearch.WordTrace]
  refine ⟨10473439747686591762894595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13964586330248789017192793 10473439747686591762894595)
  ·
    refine ⟨15710159621529887644341893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10473439747686591762894595 15710159621529887644341893)
    ·
      refine ⟨2945654929036853933314105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15710159621529887644341893 2945654929036853933314105)
      ·
        refine ⟨2209241196777640449985579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2945654929036853933314105 2209241196777640449985579)
        ·
          refine ⟨3313861795166460674978369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2209241196777640449985579 3313861795166460674978369)
          ·
            refine ⟨2485396346374845506233777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3313861795166460674978369 2485396346374845506233777)
            ·
              refine ⟨1864047259781134129675333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2485396346374845506233777 1864047259781134129675333)
              ·
                refine ⟨349508861208962649314125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1864047259781134129675333 349508861208962649314125)
                ·
                  refine ⟨131065822953360993492797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 349508861208962649314125 131065822953360993492797)
                  ·
                    rfl

theorem cell21_574312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 3].length) (baseStart_574312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574312 prefixEnd_574312 := by exact prefixLift 574312
  have htrace : WordTrace (prefixWord ++ tailWord_574312) baseStart_574312 baseEnd_574312 := by
    simpa [prefixWord, tailWord_574312, baseEnd_574312] using wordTrace_append hprefix tailTrace_574312
  have hstable : (prefixWord ++ tailWord_574312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574312).length < 2 ^ (prefixWord ++ tailWord_574312).sum := by decide
  have hdescent : baseEnd_574312 < baseStart_574312 := by decide
  rcases family_descends (prefixWord ++ tailWord_574312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574371 : List Nat := [1, 1, 1, 4, 1, 2, 2, 6, 3]
def baseStart_574371 : Nat := 118140960795 + 574371 * 2 ^ 59
def prefixEnd_574371 : Nat := 4983230072969 + 3 ^ 40 * 574371 * 2
def baseEnd_574371 : Nat := 131079287557190002009343

theorem tailTrace_574371 : CollatzResearch.WordTrace tailWord_574371 prefixEnd_574371 131079287557190002009343 := by
  unfold tailWord_574371
  simp only [CollatzResearch.WordTrace]
  refine ⟨20949031402159436602186967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13966020934772957734791311 20949031402159436602186967)
  ·
    refine ⟨31423547103239154903280451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20949031402159436602186967 31423547103239154903280451)
    ·
      refine ⟨47135320654858732354920677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31423547103239154903280451 47135320654858732354920677)
      ·
        refine ⟨8837872622786012316547627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47135320654858732354920677 8837872622786012316547627)
        ·
          refine ⟨13256808934179018474821441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8837872622786012316547627 13256808934179018474821441)
          ·
            refine ⟨9942606700634263856116081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13256808934179018474821441 9942606700634263856116081)
            ·
              refine ⟨7456955025475697892087061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9942606700634263856116081 7456955025475697892087061)
              ·
                refine ⟨349544766819173338691581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7456955025475697892087061 349544766819173338691581)
                ·
                  refine ⟨131079287557190002009343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 349544766819173338691581 131079287557190002009343)
                  ·
                    rfl

theorem cell21_574371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 3].length) (baseStart_574371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574371 prefixEnd_574371 := by exact prefixLift 574371
  have htrace : WordTrace (prefixWord ++ tailWord_574371) baseStart_574371 baseEnd_574371 := by
    simpa [prefixWord, tailWord_574371, baseEnd_574371] using wordTrace_append hprefix tailTrace_574371
  have hstable : (prefixWord ++ tailWord_574371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574371).length < 2 ^ (prefixWord ++ tailWord_574371).sum := by decide
  have hdescent : baseEnd_574371 < baseStart_574371 := by decide
  rcases family_descends (prefixWord ++ tailWord_574371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574422 : List Nat := [5, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_574422 : Nat := 118140960795 + 574422 * 2 ^ 59
def prefixEnd_574422 : Nat := 4983230072969 + 3 ^ 40 * 574422 * 2
def baseEnd_574422 : Nat := 131090926452025246659239

theorem tailTrace_574422 : CollatzResearch.WordTrace tailWord_574422 prefixEnd_574422 131090926452025246659239 := by
  unfold tailWord_574422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1309430720310917019518345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13967261016649781541529013 1309430720310917019518345)
  ·
    refine ⟨982073040233187764638759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1309430720310917019518345 982073040233187764638759)
    ·
      refine ⟨1473109560349781646958139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 982073040233187764638759 1473109560349781646958139)
      ·
        refine ⟨2209664340524672470437209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1473109560349781646958139 2209664340524672470437209)
        ·
          refine ⟨1657248255393504352827907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2209664340524672470437209 1657248255393504352827907)
          ·
            refine ⟨2485872383090256529241861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657248255393504352827907 2485872383090256529241861)
            ·
              refine ⟨466101071829423099232849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2485872383090256529241861 466101071829423099232849)
              ·
                refine ⟨349575803872067324424637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466101071829423099232849 349575803872067324424637)
                ·
                  refine ⟨131090926452025246659239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 349575803872067324424637 131090926452025246659239)
                  ·
                    rfl

theorem cell21_574422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_574422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574422 prefixEnd_574422 := by exact prefixLift 574422
  have htrace : WordTrace (prefixWord ++ tailWord_574422) baseStart_574422 baseEnd_574422 := by
    simpa [prefixWord, tailWord_574422, baseEnd_574422] using wordTrace_append hprefix tailTrace_574422
  have hstable : (prefixWord ++ tailWord_574422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574422).length < 2 ^ (prefixWord ++ tailWord_574422).sum := by decide
  have hdescent : baseEnd_574422 < baseStart_574422 := by decide
  rcases family_descends (prefixWord ++ tailWord_574422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574444 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 10]
def baseStart_574444 : Nat := 118140960795 + 574444 * 2 ^ 59
def prefixEnd_574444 : Nat := 4983230072969 + 3 ^ 40 * 574444 * 2
def baseEnd_574444 : Nat := 131095947151758097292527

theorem tailTrace_574444 : CollatzResearch.WordTrace tailWord_574444 prefixEnd_574444 131095947151758097292527 := by
  unfold tailWord_574444
  simp only [CollatzResearch.WordTrace]
  refine ⟨10475846965447485034797193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13967795953929980046396257 10475846965447485034797193)
  ·
    refine ⟨7856885224085613776097895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10475846965447485034797193 7856885224085613776097895)
    ·
      refine ⟨11785327836128420664146843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7856885224085613776097895 11785327836128420664146843)
      ·
        refine ⟨17677991754192630996220265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11785327836128420664146843 17677991754192630996220265)
        ·
          refine ⟨13258493815644473247165199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17677991754192630996220265 13258493815644473247165199)
          ·
            refine ⟨19887740723466709870747799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13258493815644473247165199 19887740723466709870747799)
            ·
              refine ⟨29831611085200064806121699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19887740723466709870747799 29831611085200064806121699)
              ·
                refine ⟨44747416627800097209182549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29831611085200064806121699 44747416627800097209182549)
                ·
                  refine ⟨131095947151758097292527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 44747416627800097209182549 131095947151758097292527)
                  ·
                    rfl

theorem cell21_574444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_574444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574444 prefixEnd_574444 := by exact prefixLift 574444
  have htrace : WordTrace (prefixWord ++ tailWord_574444) baseStart_574444 baseEnd_574444 := by
    simpa [prefixWord, tailWord_574444, baseEnd_574444] using wordTrace_append hprefix tailTrace_574444
  have hstable : (prefixWord ++ tailWord_574444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574444).length < 2 ^ (prefixWord ++ tailWord_574444).sum := by decide
  have hdescent : baseEnd_574444 < baseStart_574444 := by decide
  rcases family_descends (prefixWord ++ tailWord_574444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574450 : List Nat := [3, 2, 1, 5, 1, 1, 3, 5]
def baseStart_574450 : Nat := 118140960795 + 574450 * 2 ^ 59
def prefixEnd_574450 : Nat := 4983230072969 + 3 ^ 40 * 574450 * 2
def baseEnd_574450 : Nat := 43699105477834473397505

theorem tailTrace_574450 : CollatzResearch.WordTrace tailWord_574450 prefixEnd_574450 43699105477834473397505 := by
  unfold tailWord_574450
  simp only [CollatzResearch.WordTrace]
  refine ⟨5237978192218308273578201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13967941845915488729541869 5237978192218308273578201)
  ·
    refine ⟨3928483644163731205183651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5237978192218308273578201 3928483644163731205183651)
    ·
      refine ⟨5892725466245596807775477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3928483644163731205183651 5892725466245596807775477)
      ·
        refine ⟨552443012460524700728951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5892725466245596807775477 552443012460524700728951)
        ·
          refine ⟨828664518690787051093427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552443012460524700728951 828664518690787051093427)
          ·
            refine ⟨1242996778036180576640141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828664518690787051093427 1242996778036180576640141)
            ·
              refine ⟨466123791763567716240053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1242996778036180576640141 466123791763567716240053)
              ·
                refine ⟨43699105477834473397505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 466123791763567716240053 43699105477834473397505)
                ·
                  rfl

theorem cell21_574450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_574450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574450 prefixEnd_574450 := by exact prefixLift 574450
  have htrace : WordTrace (prefixWord ++ tailWord_574450) baseStart_574450 baseEnd_574450 := by
    simpa [prefixWord, tailWord_574450, baseEnd_574450] using wordTrace_append hprefix tailTrace_574450
  have hstable : (prefixWord ++ tailWord_574450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574450).length < 2 ^ (prefixWord ++ tailWord_574450).sum := by decide
  have hdescent : baseEnd_574450 < baseStart_574450 := by decide
  rcases family_descends (prefixWord ++ tailWord_574450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574475 : List Nat := [1, 1, 1, 1, 6, 3, 8]
def baseStart_574475 : Nat := 118140960795 + 574475 * 2 ^ 59
def prefixEnd_574475 : Nat := 4983230072969 + 3 ^ 40 * 574475 * 2
def baseEnd_574475 : Nat := 14567002419345436919533

theorem tailTrace_574475 : CollatzResearch.WordTrace tailWord_574475 prefixEnd_574475 14567002419345436919533 := by
  unfold tailWord_574475
  simp only [CollatzResearch.WordTrace]
  refine ⟨20952824593782662363972879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13968549729188441575981919 20952824593782662363972879)
  ·
    refine ⟨31429236890673993545959319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20952824593782662363972879 31429236890673993545959319)
    ·
      refine ⟨47143855336010990318938979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31429236890673993545959319 47143855336010990318938979)
      ·
        refine ⟨70715783004016485478408469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47143855336010990318938979 70715783004016485478408469)
        ·
          refine ⟨3314802328313272756800397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 70715783004016485478408469 3314802328313272756800397)
          ·
            refine ⟨1243050873117477283800149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3314802328313272756800397 1243050873117477283800149)
            ·
              refine ⟨14567002419345436919533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1243050873117477283800149 14567002419345436919533)
              ·
                rfl

theorem cell21_574475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 8].length) (baseStart_574475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574475 prefixEnd_574475 := by exact prefixLift 574475
  have htrace : WordTrace (prefixWord ++ tailWord_574475) baseStart_574475 baseEnd_574475 := by
    simpa [prefixWord, tailWord_574475, baseEnd_574475] using wordTrace_append hprefix tailTrace_574475
  have hstable : (prefixWord ++ tailWord_574475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574475).length < 2 ^ (prefixWord ++ tailWord_574475).sum := by decide
  have hdescent : baseEnd_574475 < baseStart_574475 := by decide
  rcases family_descends (prefixWord ++ tailWord_574475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574478 : List Nat := [4, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_574478 : Nat := 118140960795 + 574478 * 2 ^ 59
def prefixEnd_574478 : Nat := 4983230072969 + 3 ^ 40 * 574478 * 2
def baseEnd_574478 : Nat := 131103706414981593725791

theorem tailTrace_574478 : CollatzResearch.WordTrace tailWord_574478 prefixEnd_574478 131103706414981593725791 := by
  unfold tailWord_574478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2619116751596474234541511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13968622675181195917554725 2619116751596474234541511)
  ·
    refine ⟨3928675127394711351812267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2619116751596474234541511 3928675127394711351812267)
    ·
      refine ⟨5893012691092067027718401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3928675127394711351812267 5893012691092067027718401)
      ·
        refine ⟨4419759518319050270788801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5893012691092067027718401 4419759518319050270788801)
        ·
          refine ⟨3314819638739287703091601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4419759518319050270788801 3314819638739287703091601)
          ·
            refine ⟨2486114729054465777318701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3314819638739287703091601 2486114729054465777318701)
            ·
              refine ⟨932293023395424666494513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2486114729054465777318701 932293023395424666494513)
              ·
                refine ⟨699219767546568499870885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 932293023395424666494513 699219767546568499870885)
                ·
                  refine ⟨131103706414981593725791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 699219767546568499870885 131103706414981593725791)
                  ·
                    rfl

theorem cell21_574478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_574478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574478 prefixEnd_574478 := by exact prefixLift 574478
  have htrace : WordTrace (prefixWord ++ tailWord_574478) baseStart_574478 baseEnd_574478 := by
    simpa [prefixWord, tailWord_574478, baseEnd_574478] using wordTrace_append hprefix tailTrace_574478
  have hstable : (prefixWord ++ tailWord_574478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574478).length < 2 ^ (prefixWord ++ tailWord_574478).sum := by decide
  have hdescent : baseEnd_574478 < baseStart_574478 := by decide
  rcases family_descends (prefixWord ++ tailWord_574478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574748 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 8]
def baseStart_574748 : Nat := 118140960795 + 574748 * 2 ^ 59
def prefixEnd_574748 : Nat := 4983230072969 + 3 ^ 40 * 574748 * 2
def baseEnd_574748 : Nat := 131165324093521124225239

theorem tailTrace_574748 : CollatzResearch.WordTrace tailWord_574748 prefixEnd_574748 131165324093521124225239 := by
  unfold tailWord_574748
  simp only [CollatzResearch.WordTrace]
  refine ⟨10481390860896814994330449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13975187814529086659107265 10481390860896814994330449)
  ·
    refine ⟨7861043145672611245747837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10481390860896814994330449 7861043145672611245747837)
    ·
      refine ⟨2947891179627229217155439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7861043145672611245747837 2947891179627229217155439)
      ·
        refine ⟨4421836769440843825733159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2947891179627229217155439 4421836769440843825733159)
        ·
          refine ⟨6632755154161265738599739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4421836769440843825733159 6632755154161265738599739)
          ·
            refine ⟨9949132731241898607899609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6632755154161265738599739 9949132731241898607899609)
            ·
              refine ⟨7461849548431423955924707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9949132731241898607899609 7461849548431423955924707)
              ·
                refine ⟨11192774322647135933887061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7461849548431423955924707 11192774322647135933887061)
                ·
                  refine ⟨131165324093521124225239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11192774322647135933887061 131165324093521124225239)
                  ·
                    rfl

theorem cell21_574748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_574748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574748 prefixEnd_574748 := by exact prefixLift 574748
  have htrace : WordTrace (prefixWord ++ tailWord_574748) baseStart_574748 baseEnd_574748 := by
    simpa [prefixWord, tailWord_574748, baseEnd_574748] using wordTrace_append hprefix tailTrace_574748
  have hstable : (prefixWord ++ tailWord_574748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574748).length < 2 ^ (prefixWord ++ tailWord_574748).sum := by decide
  have hdescent : baseEnd_574748 < baseStart_574748 := by decide
  rcases family_descends (prefixWord ++ tailWord_574748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574793 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 7]
def baseStart_574793 : Nat := 118140960795 + 574793 * 2 ^ 59
def prefixEnd_574793 : Nat := 4983230072969 + 3 ^ 40 * 574793 * 2
def baseEnd_574793 : Nat := 131175593706611045975147

theorem tailTrace_574793 : CollatzResearch.WordTrace tailWord_574793 prefixEnd_574793 131175593706611045975147 := by
  unfold tailWord_574793
  simp only [CollatzResearch.WordTrace]
  refine ⟨20964423006630602674049033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13976282004420401782699355 20964423006630602674049033)
  ·
    refine ⟨15723317254972952005536775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20964423006630602674049033 15723317254972952005536775)
    ·
      refine ⟨23584975882459428008305163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15723317254972952005536775 23584975882459428008305163)
      ·
        refine ⟨35377463823689142012457745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23584975882459428008305163 35377463823689142012457745)
        ·
          refine ⟨26533097867766856509343309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35377463823689142012457745 26533097867766856509343309)
          ·
            refine ⟨9949911700412571191003741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26533097867766856509343309 9949911700412571191003741)
            ·
              refine ⟨3731216887654714196626403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9949911700412571191003741 3731216887654714196626403)
              ·
                refine ⟨5596825331482071294939605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3731216887654714196626403 5596825331482071294939605)
                ·
                  refine ⟨131175593706611045975147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5596825331482071294939605 131175593706611045975147)
                  ·
                    rfl

theorem cell21_574793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_574793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574793 prefixEnd_574793 := by exact prefixLift 574793
  have htrace : WordTrace (prefixWord ++ tailWord_574793) baseStart_574793 baseEnd_574793 := by
    simpa [prefixWord, tailWord_574793, baseEnd_574793] using wordTrace_append hprefix tailTrace_574793
  have hstable : (prefixWord ++ tailWord_574793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574793).length < 2 ^ (prefixWord ++ tailWord_574793).sum := by decide
  have hdescent : baseEnd_574793 < baseStart_574793 := by decide
  rcases family_descends (prefixWord ++ tailWord_574793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574796 : List Nat := [2, 2, 1, 3, 2, 3, 3, 5]
def baseStart_574796 : Nat := 118140960795 + 574796 * 2 ^ 59
def prefixEnd_574796 : Nat := 4983230072969 + 3 ^ 40 * 574796 * 2
def baseEnd_574796 : Nat := 43725426115827902475047

theorem tailTrace_574796 : CollatzResearch.WordTrace tailWord_574796 prefixEnd_574796 43725426115827902475047 := by
  unfold tailWord_574796
  simp only [CollatzResearch.WordTrace]
  refine ⟨10482266212809867093204121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13976354950413156124272161 10482266212809867093204121)
  ·
    refine ⟨7861699659607400319903091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10482266212809867093204121 7861699659607400319903091)
    ·
      refine ⟨11792549489411100479854637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7861699659607400319903091 11792549489411100479854637)
      ·
        refine ⟨4422206058529162679945489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11792549489411100479854637 4422206058529162679945489)
        ·
          refine ⟨3316654543896872009959117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4422206058529162679945489 3316654543896872009959117)
          ·
            refine ⟨1243745453961327003734669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3316654543896872009959117 1243745453961327003734669)
            ·
              refine ⟨466404545235497626400501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1243745453961327003734669 466404545235497626400501)
              ·
                refine ⟨43725426115827902475047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 466404545235497626400501 43725426115827902475047)
                ·
                  rfl

theorem cell21_574796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 5].length) (baseStart_574796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574796 prefixEnd_574796 := by exact prefixLift 574796
  have htrace : WordTrace (prefixWord ++ tailWord_574796) baseStart_574796 baseEnd_574796 := by
    simpa [prefixWord, tailWord_574796, baseEnd_574796] using wordTrace_append hprefix tailTrace_574796
  have hstable : (prefixWord ++ tailWord_574796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574796).length < 2 ^ (prefixWord ++ tailWord_574796).sum := by decide
  have hdescent : baseEnd_574796 < baseStart_574796 := by decide
  rcases family_descends (prefixWord ++ tailWord_574796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574855 : List Nat := [1, 1, 4, 2, 2, 3, 1, 7]
def baseStart_574855 : Nat := 118140960795 + 574855 * 2 ^ 59
def prefixEnd_574855 : Nat := 4983230072969 + 3 ^ 40 * 574855 * 2
def baseEnd_574855 : Nat := 43729914317104238647229

theorem tailTrace_574855 : CollatzResearch.WordTrace tailWord_574855 prefixEnd_574855 43729914317104238647229 := by
  unfold tailWord_574855
  simp only [CollatzResearch.WordTrace]
  refine ⟨20966684332405987262806019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13977789554937324841870679 20966684332405987262806019)
  ·
    refine ⟨31450026498608980894209029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20966684332405987262806019 31450026498608980894209029)
    ·
      refine ⟨5896879968489183917664193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31450026498608980894209029 5896879968489183917664193)
      ·
        refine ⟨4422659976366887938248145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5896879968489183917664193 4422659976366887938248145)
        ·
          refine ⟨3316994982275165953686109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4422659976366887938248145 3316994982275165953686109)
          ·
            refine ⟨1243873118353187232632291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3316994982275165953686109 1243873118353187232632291)
            ·
              refine ⟨1865809677529780848948437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243873118353187232632291 1865809677529780848948437)
              ·
                refine ⟨43729914317104238647229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1865809677529780848948437 43729914317104238647229)
                ·
                  rfl

theorem cell21_574855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 7].length) (baseStart_574855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574855 prefixEnd_574855 := by exact prefixLift 574855
  have htrace : WordTrace (prefixWord ++ tailWord_574855) baseStart_574855 baseEnd_574855 := by
    simpa [prefixWord, tailWord_574855, baseEnd_574855] using wordTrace_append hprefix tailTrace_574855
  have hstable : (prefixWord ++ tailWord_574855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574855).length < 2 ^ (prefixWord ++ tailWord_574855).sum := by decide
  have hdescent : baseEnd_574855 < baseStart_574855 := by decide
  rcases family_descends (prefixWord ++ tailWord_574855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574869 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 7]
def baseStart_574869 : Nat := 118140960795 + 574869 * 2 ^ 59
def prefixEnd_574869 : Nat := 4983230072969 + 3 ^ 40 * 574869 * 2
def baseEnd_574869 : Nat := 131192937942051802708325

theorem tailTrace_574869 : CollatzResearch.WordTrace tailWord_574869 prefixEnd_574869 131192937942051802708325 := by
  unfold tailWord_574869
  simp only [CollatzResearch.WordTrace]
  refine ⟨20967194954355267653815661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13978129969570178435877107 20967194954355267653815661)
  ·
    refine ⟨7862698107883225370180873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20967194954355267653815661 7862698107883225370180873)
    ·
      refine ⟨5897023580912419027635655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7862698107883225370180873 5897023580912419027635655)
      ·
        refine ⟨8845535371368628541453483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5897023580912419027635655 8845535371368628541453483)
        ·
          refine ⟨13268303057052942812180225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8845535371368628541453483 13268303057052942812180225)
          ·
            refine ⟨9951227292789707109135169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13268303057052942812180225 9951227292789707109135169)
            ·
              refine ⟨7463420469592280331851377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9951227292789707109135169 7463420469592280331851377)
              ·
                refine ⟨5597565352194210248888533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7463420469592280331851377 5597565352194210248888533)
                ·
                  refine ⟨131192937942051802708325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5597565352194210248888533 131192937942051802708325)
                  ·
                    rfl

theorem cell21_574869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_574869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574869 prefixEnd_574869 := by exact prefixLift 574869
  have htrace : WordTrace (prefixWord ++ tailWord_574869) baseStart_574869 baseEnd_574869 := by
    simpa [prefixWord, tailWord_574869, baseEnd_574869] using wordTrace_append hprefix tailTrace_574869
  have hstable : (prefixWord ++ tailWord_574869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574869).length < 2 ^ (prefixWord ++ tailWord_574869).sum := by decide
  have hdescent : baseEnd_574869 < baseStart_574869 := by decide
  rcases family_descends (prefixWord ++ tailWord_574869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574872 : List Nat := [2, 1, 2, 5, 2, 2, 7]
def baseStart_574872 : Nat := 118140960795 + 574872 * 2 ^ 59
def prefixEnd_574872 : Nat := 4983230072969 + 3 ^ 40 * 574872 * 2
def baseEnd_574872 : Nat := 14577069175880496017591

theorem tailTrace_574872 : CollatzResearch.WordTrace tailWord_574872 prefixEnd_574872 14577069175880496017591 := by
  unfold tailWord_574872
  simp only [CollatzResearch.WordTrace]
  refine ⟨10483652186672199583087435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13978202915562932777449913 10483652186672199583087435)
  ·
    refine ⟨15725478280008299374631153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10483652186672199583087435 15725478280008299374631153)
    ·
      refine ⟨11794108710006224530973365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15725478280008299374631153 11794108710006224530973365)
      ·
        refine ⟨1105697691563083549778753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11794108710006224530973365 1105697691563083549778753)
        ·
          refine ⟨829273268672312662334065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1105697691563083549778753 829273268672312662334065)
          ·
            refine ⟨621954951504234496750549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 829273268672312662334065 621954951504234496750549)
            ·
              refine ⟨14577069175880496017591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 621954951504234496750549 14577069175880496017591)
              ·
                rfl

theorem cell21_574872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 7].length) (baseStart_574872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574872 prefixEnd_574872 := by exact prefixLift 574872
  have htrace : WordTrace (prefixWord ++ tailWord_574872) baseStart_574872 baseEnd_574872 := by
    simpa [prefixWord, tailWord_574872, baseEnd_574872] using wordTrace_append hprefix tailTrace_574872
  have hstable : (prefixWord ++ tailWord_574872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574872).length < 2 ^ (prefixWord ++ tailWord_574872).sum := by decide
  have hdescent : baseEnd_574872 < baseStart_574872 := by decide
  rcases family_descends (prefixWord ++ tailWord_574872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574878 : List Nat := [4, 3, 1, 2, 2, 1, 3, 2, 3]
def baseStart_574878 : Nat := 118140960795 + 574878 * 2 ^ 59
def prefixEnd_574878 : Nat := 4983230072969 + 3 ^ 40 * 574878 * 2
def baseEnd_574878 : Nat := 131194991864669787058307

theorem tailTrace_574878 : CollatzResearch.WordTrace tailWord_574878 prefixEnd_574878 131194991864669787058307 := by
  unfold tailWord_574878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2620940401415332773861661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13978348807548441460595525 2620940401415332773861661)
  ·
    refine ⟨982852650530749790198123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2620940401415332773861661 982852650530749790198123)
    ·
      refine ⟨1474278975796124685297185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 982852650530749790198123 1474278975796124685297185)
      ·
        refine ⟨1105709231847093513972889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1474278975796124685297185 1105709231847093513972889)
        ·
          refine ⟨829281923885320135479667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1105709231847093513972889 829281923885320135479667)
          ·
            refine ⟨1243922885827980203219501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829281923885320135479667 1243922885827980203219501)
            ·
              refine ⟨466471082185492576207313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1243922885827980203219501 466471082185492576207313)
              ·
                refine ⟨349853311639119432155485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466471082185492576207313 349853311639119432155485)
                ·
                  refine ⟨131194991864669787058307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 349853311639119432155485 131194991864669787058307)
                  ·
                    rfl

theorem cell21_574878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_574878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574878 prefixEnd_574878 := by exact prefixLift 574878
  have htrace : WordTrace (prefixWord ++ tailWord_574878) baseStart_574878 baseEnd_574878 := by
    simpa [prefixWord, tailWord_574878, baseEnd_574878] using wordTrace_append hprefix tailTrace_574878
  have hstable : (prefixWord ++ tailWord_574878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574878).length < 2 ^ (prefixWord ++ tailWord_574878).sum := by decide
  have hdescent : baseEnd_574878 < baseStart_574878 := by decide
  rcases family_descends (prefixWord ++ tailWord_574878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574934 : List Nat := [5, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_574934 : Nat := 118140960795 + 574934 * 2 ^ 59
def prefixEnd_574934 : Nat := 4983230072969 + 3 ^ 40 * 574934 * 2
def baseEnd_574934 : Nat := 131207771827626134124859

theorem tailTrace_574934 : CollatzResearch.WordTrace tailWord_574934 prefixEnd_574934 131207771827626134124859 := by
  unfold tailWord_574934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1310597856194986484683241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13979710466079855836621237 1310597856194986484683241)
  ·
    refine ⟨982948392146239863512431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1310597856194986484683241 982948392146239863512431)
    ·
      refine ⟨1474422588219359795268647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 982948392146239863512431 1474422588219359795268647)
      ·
        refine ⟨2211633882329039692902971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1474422588219359795268647 2211633882329039692902971)
        ·
          refine ⟨3317450823493559539354457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2211633882329039692902971 3317450823493559539354457)
          ·
            refine ⟨2488088117620169654515843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3317450823493559539354457 2488088117620169654515843)
            ·
              refine ⟨3732132176430254481773765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2488088117620169654515843 3732132176430254481773765)
              ·
                refine ⟨699774783080672715332581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3732132176430254481773765 699774783080672715332581)
                ·
                  refine ⟨131207771827626134124859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 699774783080672715332581 131207771827626134124859)
                  ·
                    rfl

theorem cell21_574934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_574934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574934 prefixEnd_574934 := by exact prefixLift 574934
  have htrace : WordTrace (prefixWord ++ tailWord_574934) baseStart_574934 baseEnd_574934 := by
    simpa [prefixWord, tailWord_574934, baseEnd_574934] using wordTrace_append hprefix tailTrace_574934
  have hstable : (prefixWord ++ tailWord_574934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574934).length < 2 ^ (prefixWord ++ tailWord_574934).sum := by decide
  have hdescent : baseEnd_574934 < baseStart_574934 := by decide
  rcases family_descends (prefixWord ++ tailWord_574934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574962 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 7]
def baseStart_574962 : Nat := 118140960795 + 574962 * 2 ^ 59
def prefixEnd_574962 : Nat := 4983230072969 + 3 ^ 40 * 574962 * 2
def baseEnd_574962 : Nat := 131214161809104307658135

theorem tailTrace_574962 : CollatzResearch.WordTrace tailWord_574962 prefixEnd_574962 131214161809104307658135 := by
  unfold tailWord_574962
  simp only [CollatzResearch.WordTrace]
  refine ⟨5242646735754586134237785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13980391295345563024634093 5242646735754586134237785)
  ·
    refine ⟨3931985051815939600678339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5242646735754586134237785 3931985051815939600678339)
    ·
      refine ⟨5897977577723909401017509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3931985051815939600678339 5897977577723909401017509)
      ·
        refine ⟨1105870795823233012690783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5897977577723909401017509 1105870795823233012690783)
        ·
          refine ⟨1658806193734849519036175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1105870795823233012690783 1658806193734849519036175)
          ·
            refine ⟨2488209290602274278554263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1658806193734849519036175 2488209290602274278554263)
            ·
              refine ⟨3732313935903411417831395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2488209290602274278554263 3732313935903411417831395)
              ·
                refine ⟨5598470903855117126747093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3732313935903411417831395 5598470903855117126747093)
                ·
                  refine ⟨131214161809104307658135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5598470903855117126747093 131214161809104307658135)
                  ·
                    rfl

theorem cell21_574962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_574962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574962 prefixEnd_574962 := by exact prefixLift 574962
  have htrace : WordTrace (prefixWord ++ tailWord_574962) baseStart_574962 baseEnd_574962 := by
    simpa [prefixWord, tailWord_574962, baseEnd_574962] using wordTrace_append hprefix tailTrace_574962
  have hstable : (prefixWord ++ tailWord_574962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574962).length < 2 ^ (prefixWord ++ tailWord_574962).sum := by decide
  have hdescent : baseEnd_574962 < baseStart_574962 := by decide
  rcases family_descends (prefixWord ++ tailWord_574962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574965 : List Nat := [1, 3, 5, 1, 1, 2, 3, 5]
def baseStart_574965 : Nat := 118140960795 + 574965 * 2 ^ 59
def prefixEnd_574965 : Nat := 4983230072969 + 3 ^ 40 * 574965 * 2
def baseEnd_574965 : Nat := 43738282149992323036043

theorem tailTrace_574965 : CollatzResearch.WordTrace tailWord_574965 prefixEnd_574965 43738282149992323036043 := by
  unfold tailWord_574965
  simp only [CollatzResearch.WordTrace]
  refine ⟨20970696362007476049310349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13980464241338317366206899 20970696362007476049310349)
  ·
    refine ⟨7864011135752803518491381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20970696362007476049310349 7864011135752803518491381)
    ·
      refine ⟨737251043976825329858567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7864011135752803518491381 737251043976825329858567)
      ·
        refine ⟨1105876565965237994787851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 737251043976825329858567 1105876565965237994787851)
        ·
          refine ⟨1658814848947856992181777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1105876565965237994787851 1658814848947856992181777)
          ·
            refine ⟨1244111136710892744136333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1658814848947856992181777 1244111136710892744136333)
            ·
              refine ⟨466541676266584779051125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1244111136710892744136333 466541676266584779051125)
              ·
                refine ⟨43738282149992323036043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 466541676266584779051125 43738282149992323036043)
                ·
                  rfl

theorem cell21_574965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 5].length) (baseStart_574965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574965 prefixEnd_574965 := by exact prefixLift 574965
  have htrace : WordTrace (prefixWord ++ tailWord_574965) baseStart_574965 baseEnd_574965 := by
    simpa [prefixWord, tailWord_574965, baseEnd_574965] using wordTrace_append hprefix tailTrace_574965
  have hstable : (prefixWord ++ tailWord_574965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574965).length < 2 ^ (prefixWord ++ tailWord_574965).sum := by decide
  have hdescent : baseEnd_574965 < baseStart_574965 := by decide
  rcases family_descends (prefixWord ++ tailWord_574965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574982 : List Nat := [6, 2, 1, 1, 2, 1, 8]
def baseStart_574982 : Nat := 118140960795 + 574982 * 2 ^ 59
def prefixEnd_574982 : Nat := 4983230072969 + 3 ^ 40 * 574982 * 2
def baseEnd_574982 : Nat := 14579858453509857480529

theorem tailTrace_574982 : CollatzResearch.WordTrace tailWord_574982 prefixEnd_574982 14579858453509857480529 := by
  unfold tailWord_574982
  simp only [CollatzResearch.WordTrace]
  refine ⟨655353637592058998521225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13980877601963925301786133 655353637592058998521225)
  ·
    refine ⟨491515228194044248890919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 655353637592058998521225 491515228194044248890919)
    ·
      refine ⟨737272842291066373336379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 491515228194044248890919 737272842291066373336379)
      ·
        refine ⟨1105909263436599560004569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 737272842291066373336379 1105909263436599560004569)
        ·
          refine ⟨829431947577449670003427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1105909263436599560004569 829431947577449670003427)
          ·
            refine ⟨1244147921366174505005141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829431947577449670003427 1244147921366174505005141)
            ·
              refine ⟨14579858453509857480529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1244147921366174505005141 14579858453509857480529)
              ·
                rfl

theorem cell21_574982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 8].length) (baseStart_574982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574982 prefixEnd_574982 := by exact prefixLift 574982
  have htrace : WordTrace (prefixWord ++ tailWord_574982) baseStart_574982 baseEnd_574982 := by
    simpa [prefixWord, tailWord_574982, baseEnd_574982] using wordTrace_append hprefix tailTrace_574982
  have hstable : (prefixWord ++ tailWord_574982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574982).length < 2 ^ (prefixWord ++ tailWord_574982).sum := by decide
  have hdescent : baseEnd_574982 < baseStart_574982 := by decide
  rcases family_descends (prefixWord ++ tailWord_574982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574996 : List Nat := [2, 4, 3, 1, 2, 1, 2, 1, 5]
def baseStart_574996 : Nat := 118140960795 + 574996 * 2 ^ 59
def prefixEnd_574996 : Nat := 4983230072969 + 3 ^ 40 * 574996 * 2
def baseEnd_574996 : Nat := 131221921072327804091399

theorem tailTrace_574996 : CollatzResearch.WordTrace tailWord_574996 prefixEnd_574996 131221921072327804091399 := by
  unfold tailWord_574996
  simp only [CollatzResearch.WordTrace]
  refine ⟨10485913512447584171844421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13981218016596778895792561 10485913512447584171844421)
  ·
    refine ⟨1966108783583922032220829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10485913512447584171844421 1966108783583922032220829)
    ·
      refine ⟨737290793843970762082811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1966108783583922032220829 737290793843970762082811)
      ·
        refine ⟨1105936190765956143124217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 737290793843970762082811 1105936190765956143124217)
        ·
          refine ⟨829452143074467107343163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1105936190765956143124217 829452143074467107343163)
          ·
            refine ⟨1244178214611700661014745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829452143074467107343163 1244178214611700661014745)
            ·
              refine ⟨933133660958775495761059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1244178214611700661014745 933133660958775495761059)
              ·
                refine ⟨1399700491438163243641589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 933133660958775495761059 1399700491438163243641589)
                ·
                  refine ⟨131221921072327804091399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1399700491438163243641589 131221921072327804091399)
                  ·
                    rfl

theorem cell21_574996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_574996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_574996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_574996 prefixEnd_574996 := by exact prefixLift 574996
  have htrace : WordTrace (prefixWord ++ tailWord_574996) baseStart_574996 baseEnd_574996 := by
    simpa [prefixWord, tailWord_574996, baseEnd_574996] using wordTrace_append hprefix tailTrace_574996
  have hstable : (prefixWord ++ tailWord_574996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574996).length < 2 ^ (prefixWord ++ tailWord_574996).sum := by decide
  have hdescent : baseEnd_574996 < baseStart_574996 := by decide
  rcases family_descends (prefixWord ++ tailWord_574996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575030 : List Nat := [5, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_575030 : Nat := 118140960795 + 575030 * 2 ^ 59
def prefixEnd_575030 : Nat := 4983230072969 + 3 ^ 40 * 575030 * 2
def baseEnd_575030 : Nat := 131229680335551300524663

theorem tailTrace_575030 : CollatzResearch.WordTrace tailWord_575030 prefixEnd_575030 131229680335551300524663 := by
  unfold tailWord_575030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1310816694173249509401659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13982044737847994766951029 1310816694173249509401659)
  ·
    refine ⟨1966225041259874264102489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1310816694173249509401659 1966225041259874264102489)
    ·
      refine ⟨1474668780944905698076867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1966225041259874264102489 1474668780944905698076867)
      ·
        refine ⟨2212003171417358547115301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1474668780944905698076867 2212003171417358547115301)
        ·
          refine ⟨414750594640754727584119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2212003171417358547115301 414750594640754727584119)
          ·
            refine ⟨622125891961132091376179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414750594640754727584119 622125891961132091376179)
            ·
              refine ⟨933188837941698137064269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622125891961132091376179 933188837941698137064269)
              ·
                refine ⟨349945814228136801399101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 933188837941698137064269 349945814228136801399101)
                ·
                  refine ⟨131229680335551300524663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 349945814228136801399101 131229680335551300524663)
                  ·
                    rfl

theorem cell21_575030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_575030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_575030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_575030 prefixEnd_575030 := by exact prefixLift 575030
  have htrace : WordTrace (prefixWord ++ tailWord_575030) baseStart_575030 baseEnd_575030 := by
    simpa [prefixWord, tailWord_575030, baseEnd_575030] using wordTrace_append hprefix tailTrace_575030
  have hstable : (prefixWord ++ tailWord_575030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575030).length < 2 ^ (prefixWord ++ tailWord_575030).sum := by decide
  have hdescent : baseEnd_575030 < baseStart_575030 := by decide
  rcases family_descends (prefixWord ++ tailWord_575030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575052 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 6]
def baseStart_575052 : Nat := 118140960795 + 575052 * 2 ^ 59
def prefixEnd_575052 : Nat := 4983230072969 + 3 ^ 40 * 575052 * 2
def baseEnd_575052 : Nat := 131234701035284151157951

theorem tailTrace_575052 : CollatzResearch.WordTrace tailWord_575052 prefixEnd_575052 131234701035284151157951 := by
  unfold tailWord_575052
  simp only [CollatzResearch.WordTrace]
  refine ⟨10486934756346144953863705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13982579675128193271818273 10486934756346144953863705)
  ·
    refine ⟨7865201067259608715397779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10486934756346144953863705 7865201067259608715397779)
    ·
      refine ⟨11797801600889413073096669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7865201067259608715397779 11797801600889413073096669)
      ·
        refine ⟨4424175600333529902411251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11797801600889413073096669 4424175600333529902411251)
        ·
          refine ⟨6636263400500294853616877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4424175600333529902411251 6636263400500294853616877)
          ·
            refine ⟨2488598775187610570106329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6636263400500294853616877 2488598775187610570106329)
            ·
              refine ⟨1866449081390707927579747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2488598775187610570106329 1866449081390707927579747)
              ·
                refine ⟨2799673622086061891369621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1866449081390707927579747 2799673622086061891369621)
                ·
                  refine ⟨131234701035284151157951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2799673622086061891369621 131234701035284151157951)
                  ·
                    rfl

theorem cell21_575052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_575052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_575052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_575052 prefixEnd_575052 := by exact prefixLift 575052
  have htrace : WordTrace (prefixWord ++ tailWord_575052) baseStart_575052 baseEnd_575052 := by
    simpa [prefixWord, tailWord_575052, baseEnd_575052] using wordTrace_append hprefix tailTrace_575052
  have hstable : (prefixWord ++ tailWord_575052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575052).length < 2 ^ (prefixWord ++ tailWord_575052).sum := by decide
  have hdescent : baseEnd_575052 < baseStart_575052 := by decide
  rcases family_descends (prefixWord ++ tailWord_575052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575283 : List Nat := [1, 1, 1, 2, 7, 1, 1, 4, 3]
def baseStart_575283 : Nat := 118140960795 + 575283 * 2 ^ 59
def prefixEnd_575283 : Nat := 4983230072969 + 3 ^ 40 * 575283 * 2
def baseEnd_575283 : Nat := 131287418382479082807479

theorem tailTrace_575283 : CollatzResearch.WordTrace tailWord_575283 prefixEnd_575283 131287418382479082807479 := by
  unfold tailWord_575283
  simp only [CollatzResearch.WordTrace]
  refine ⟨20982294774855416359386503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13988196516570277572924335 20982294774855416359386503)
  ·
    refine ⟨31473442162283124539079755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20982294774855416359386503 31473442162283124539079755)
    ·
      refine ⟨47210163243424686808619633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31473442162283124539079755 47210163243424686808619633)
      ·
        refine ⟨35407622432568515106464725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47210163243424686808619633 35407622432568515106464725)
        ·
          refine ⟨829866150763324572807767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 35407622432568515106464725 829866150763324572807767)
          ·
            refine ⟨1244799226144986859211651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829866150763324572807767 1244799226144986859211651)
            ·
              refine ⟨1867198839217480288817477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1244799226144986859211651 1867198839217480288817477)
              ·
                refine ⟨350099782353277554153277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1867198839217480288817477 350099782353277554153277)
                ·
                  refine ⟨131287418382479082807479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 350099782353277554153277 131287418382479082807479)
                  ·
                    rfl

theorem cell21_575283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 3].length) (baseStart_575283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_575283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_575283 prefixEnd_575283 := by exact prefixLift 575283
  have htrace : WordTrace (prefixWord ++ tailWord_575283) baseStart_575283 baseEnd_575283 := by
    simpa [prefixWord, tailWord_575283, baseEnd_575283] using wordTrace_append hprefix tailTrace_575283
  have hstable : (prefixWord ++ tailWord_575283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575283).length < 2 ^ (prefixWord ++ tailWord_575283).sum := by decide
  have hdescent : baseEnd_575283 < baseStart_575283 := by decide
  rcases family_descends (prefixWord ++ tailWord_575283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575342 : List Nat := [4, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_575342 : Nat := 118140960795 + 575342 * 2 ^ 59
def prefixEnd_575342 : Nat := 4983230072969 + 3 ^ 40 * 575342 * 2
def baseEnd_575342 : Nat := 131300882986308091324025

theorem tailTrace_575342 : CollatzResearch.WordTrace tailWord_575342 prefixEnd_575342 131300882986308091324025 := by
  unfold tailWord_575342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2623055835205208679473035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13989631121094446290522853 2623055835205208679473035)
  ·
    refine ⟨3934583752807813019209553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2623055835205208679473035 3934583752807813019209553)
    ·
      refine ⟨2950937814605859764407165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3934583752807813019209553 2950937814605859764407165)
      ·
        refine ⟨1106601680477197411652687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2950937814605859764407165 1106601680477197411652687)
        ·
          refine ⟨1659902520715796117479031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1106601680477197411652687 1659902520715796117479031)
          ·
            refine ⟨2489853781073694176218547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1659902520715796117479031 2489853781073694176218547)
            ·
              refine ⟨3734780671610541264327821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2489853781073694176218547 3734780671610541264327821)
              ·
                refine ⟨1400542751853952974122933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3734780671610541264327821 1400542751853952974122933)
                ·
                  refine ⟨131300882986308091324025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1400542751853952974122933 131300882986308091324025)
                  ·
                    rfl

theorem cell21_575342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_575342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_575342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_575342 prefixEnd_575342 := by exact prefixLift 575342
  have htrace : WordTrace (prefixWord ++ tailWord_575342) baseStart_575342 baseEnd_575342 := by
    simpa [prefixWord, tailWord_575342, baseEnd_575342] using wordTrace_append hprefix tailTrace_575342
  have hstable : (prefixWord ++ tailWord_575342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575342).length < 2 ^ (prefixWord ++ tailWord_575342).sum := by decide
  have hdescent : baseEnd_575342 < baseStart_575342 := by decide
  rcases family_descends (prefixWord ++ tailWord_575342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575449 : List Nat := [1, 2, 1, 2, 6, 1, 2, 2, 4]
def baseStart_575449 : Nat := 118140960795 + 575449 * 2 ^ 59
def prefixEnd_575449 : Nat := 4983230072969 + 3 ^ 40 * 575449 * 2
def baseEnd_575449 : Nat := 131325301844099683040473

theorem tailTrace_575449 : CollatzResearch.WordTrace tailWord_575449 prefixEnd_575449 131325301844099683040473 := by
  unfold tailWord_575449
  simp only [CollatzResearch.WordTrace]
  refine ⟨20988349292254026709929401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13992232861502684473286267 20988349292254026709929401)
  ·
    refine ⟨15741261969190520032447051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20988349292254026709929401 15741261969190520032447051)
    ·
      refine ⟨23611892953785780048670577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15741261969190520032447051 23611892953785780048670577)
      ·
        refine ⟨17708919715339335036502933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23611892953785780048670577 17708919715339335036502933)
        ·
          refine ⟨830105611656531329836075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17708919715339335036502933 830105611656531329836075)
          ·
            refine ⟨1245158417484796994754113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830105611656531329836075 1245158417484796994754113)
            ·
              refine ⟨933868813113597746065585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1245158417484796994754113 933868813113597746065585)
              ·
                refine ⟨700401609835198309549189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 933868813113597746065585 700401609835198309549189)
                ·
                  refine ⟨131325301844099683040473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 700401609835198309549189 131325301844099683040473)
                  ·
                    rfl

theorem cell21_575449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 4].length) (baseStart_575449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_575449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_575449 prefixEnd_575449 := by exact prefixLift 575449
  have htrace : WordTrace (prefixWord ++ tailWord_575449) baseStart_575449 baseEnd_575449 := by
    simpa [prefixWord, tailWord_575449, baseEnd_575449] using wordTrace_append hprefix tailTrace_575449
  have hstable : (prefixWord ++ tailWord_575449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575449).length < 2 ^ (prefixWord ++ tailWord_575449).sum := by decide
  have hdescent : baseEnd_575449 < baseStart_575449 := by decide
  rcases family_descends (prefixWord ++ tailWord_575449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575522 : List Nat := [3, 3, 1, 1, 1, 2, 2, 8]
def baseStart_575522 : Nat := 118140960795 + 575522 * 2 ^ 59
def prefixEnd_575522 : Nat := 4983230072969 + 3 ^ 40 * 575522 * 2
def baseEnd_575522 : Nat := 43780653812889259441219

theorem tailTrace_575522 : CollatzResearch.WordTrace tailWord_575522 prefixEnd_575522 43780653812889259441219 := by
  unfold tailWord_575522
  simp only [CollatzResearch.WordTrace]
  refine ⟨5247752955247390044334205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13994007880659706784891213 5247752955247390044334205)
  ·
    refine ⟨1967907358217771266625327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5247752955247390044334205 1967907358217771266625327)
    ·
      refine ⟨2951861037326656899937991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1967907358217771266625327 2951861037326656899937991)
      ·
        refine ⟨4427791555989985349906987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2951861037326656899937991 4427791555989985349906987)
        ·
          refine ⟨6641687333984978024860481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4427791555989985349906987 6641687333984978024860481)
          ·
            refine ⟨4981265500488733518645361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6641687333984978024860481 4981265500488733518645361)
            ·
              refine ⟨3735949125366550138984021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4981265500488733518645361 3735949125366550138984021)
              ·
                refine ⟨43780653812889259441219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3735949125366550138984021 43780653812889259441219)
                ·
                  rfl

theorem cell21_575522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_575522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_575522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_575522 prefixEnd_575522 := by exact prefixLift 575522
  have htrace : WordTrace (prefixWord ++ tailWord_575522) baseStart_575522 baseEnd_575522 := by
    simpa [prefixWord, tailWord_575522, baseEnd_575522] using wordTrace_append hprefix tailTrace_575522
  have hstable : (prefixWord ++ tailWord_575522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575522).length < 2 ^ (prefixWord ++ tailWord_575522).sum := by decide
  have hdescent : baseEnd_575522 < baseStart_575522 := by decide
  rcases family_descends (prefixWord ++ tailWord_575522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575525 : List Nat := [1, 3, 1, 2, 2, 4, 3, 1, 4]
def baseStart_575525 : Nat := 118140960795 + 575525 * 2 ^ 59
def prefixEnd_575525 : Nat := 4983230072969 + 3 ^ 40 * 575525 * 2
def baseEnd_575525 : Nat := 131342646079540439773651

theorem tailTrace_575525 : CollatzResearch.WordTrace tailWord_575525 prefixEnd_575525 131342646079540439773651 := by
  unfold tailWord_575525
  simp only [CollatzResearch.WordTrace]
  refine ⟨20991121239978691689696029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13994080826652461126464019 20991121239978691689696029)
  ·
    refine ⟨7871670464992009383636011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20991121239978691689696029 7871670464992009383636011)
    ·
      refine ⟨11807505697488014075454017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7871670464992009383636011 11807505697488014075454017)
      ·
        refine ⟨8855629273116010556590513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11807505697488014075454017 8855629273116010556590513)
        ·
          refine ⟨6641721954837007917442885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8855629273116010556590513 6641721954837007917442885)
          ·
            refine ⟨1245322866531938984520541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6641721954837007917442885 1245322866531938984520541)
            ·
              refine ⟨466996074949477119195203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1245322866531938984520541 466996074949477119195203)
              ·
                refine ⟨700494112424215678792805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 466996074949477119195203 700494112424215678792805)
                ·
                  refine ⟨131342646079540439773651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 700494112424215678792805 131342646079540439773651)
                  ·
                    rfl

theorem cell21_575525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_575525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_575525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_575525 prefixEnd_575525 := by exact prefixLift 575525
  have htrace : WordTrace (prefixWord ++ tailWord_575525) baseStart_575525 baseEnd_575525 := by
    simpa [prefixWord, tailWord_575525, baseEnd_575525] using wordTrace_append hprefix tailTrace_575525
  have hstable : (prefixWord ++ tailWord_575525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575525).length < 2 ^ (prefixWord ++ tailWord_575525).sum := by decide
  have hdescent : baseEnd_575525 < baseStart_575525 := by decide
  rcases family_descends (prefixWord ++ tailWord_575525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575584 : List Nat := [2, 1, 1, 3, 2, 4, 1, 3, 4]
def baseStart_575584 : Nat := 118140960795 + 575584 * 2 ^ 59
def prefixEnd_575584 : Nat := 4983230072969 + 3 ^ 40 * 575584 * 2
def baseEnd_575584 : Nat := 131356110683369448290197

theorem tailTrace_575584 : CollatzResearch.WordTrace tailWord_575584 prefixEnd_575584 131356110683369448290197 := by
  unfold tailWord_575584
  simp only [CollatzResearch.WordTrace]
  refine ⟨10496636573382472383046903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13995515431176629844062537 10496636573382472383046903)
  ·
    refine ⟨15744954860073708574570355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10496636573382472383046903 15744954860073708574570355)
    ·
      refine ⟨23617432290110562861855533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15744954860073708574570355 23617432290110562861855533)
      ·
        refine ⟨8856537108791461073195825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23617432290110562861855533 8856537108791461073195825)
        ·
          refine ⟨6642402831593595804896869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8856537108791461073195825 6642402831593595804896869)
          ·
            refine ⟨1245450530923799213418163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6642402831593595804896869 1245450530923799213418163)
            ·
              refine ⟨1868175796385698820127245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1245450530923799213418163 1868175796385698820127245)
              ·
                refine ⟨700565923644637057547717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1868175796385698820127245 700565923644637057547717)
                ·
                  refine ⟨131356110683369448290197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 700565923644637057547717 131356110683369448290197)
                  ·
                    rfl

theorem cell21_575584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 4].length) (baseStart_575584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_575584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_575584 prefixEnd_575584 := by exact prefixLift 575584
  have htrace : WordTrace (prefixWord ++ tailWord_575584) baseStart_575584 baseEnd_575584 := by
    simpa [prefixWord, tailWord_575584, baseEnd_575584] using wordTrace_append hprefix tailTrace_575584
  have hstable : (prefixWord ++ tailWord_575584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575584).length < 2 ^ (prefixWord ++ tailWord_575584).sum := by decide
  have hdescent : baseEnd_575584 < baseStart_575584 := by decide
  rcases family_descends (prefixWord ++ tailWord_575584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575598 : List Nat := [4, 1, 2, 2, 1, 1, 1, 9]
def baseStart_575598 : Nat := 118140960795 + 575598 * 2 ^ 59
def prefixEnd_575598 : Nat := 4983230072969 + 3 ^ 40 * 575598 * 2
def baseEnd_575598 : Nat := 43786435224702845018945

theorem tailTrace_575598 : CollatzResearch.WordTrace tailWord_575598 prefixEnd_575598 43786435224702845018945 := by
  unfold tailWord_575598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2624222971089278144637931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13995855845809483438068965 2624222971089278144637931)
  ·
    refine ⟨3936334456633917216956897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2624222971089278144637931 3936334456633917216956897)
    ·
      refine ⟨2952250842475437912717673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3936334456633917216956897 2952250842475437912717673)
      ·
        refine ⟨2214188131856578434538255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2952250842475437912717673 2214188131856578434538255)
        ·
          refine ⟨3321282197784867651807383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2214188131856578434538255 3321282197784867651807383)
          ·
            refine ⟨4981923296677301477711075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3321282197784867651807383 4981923296677301477711075)
            ·
              refine ⟨7472884945015952216566613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4981923296677301477711075 7472884945015952216566613)
              ·
                refine ⟨43786435224702845018945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7472884945015952216566613 43786435224702845018945)
                ·
                  rfl

theorem cell21_575598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_575598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_575598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_575598 prefixEnd_575598 := by exact prefixLift 575598
  have htrace : WordTrace (prefixWord ++ tailWord_575598) baseStart_575598 baseEnd_575598 := by
    simpa [prefixWord, tailWord_575598, baseEnd_575598] using wordTrace_append hprefix tailTrace_575598
  have hstable : (prefixWord ++ tailWord_575598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575598).length < 2 ^ (prefixWord ++ tailWord_575598).sum := by decide
  have hdescent : baseEnd_575598 < baseStart_575598 := by decide
  rcases family_descends (prefixWord ++ tailWord_575598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575643 : List Nat := [1, 1, 1, 1, 1, 1, 2, 9, 4]
def baseStart_575643 : Nat := 118140960795 + 575643 * 2 ^ 59
def prefixEnd_575643 : Nat := 4983230072969 + 3 ^ 40 * 575643 * 2
def baseEnd_575643 : Nat := 131369575287198456806743

theorem tailTrace_575643 : CollatzResearch.WordTrace tailWord_575643 prefixEnd_575643 131369575287198456806743 := by
  unfold tailWord_575643
  simp only [CollatzResearch.WordTrace]
  refine ⟨20995425053551197842491583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13996950035700798561661055 20995425053551197842491583)
  ·
    refine ⟨31493137580326796763737375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20995425053551197842491583 31493137580326796763737375)
    ·
      refine ⟨47239706370490195145606063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31493137580326796763737375 47239706370490195145606063)
      ·
        refine ⟨70859559555735292718409095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47239706370490195145606063 70859559555735292718409095)
        ·
          refine ⟨106289339333602939077613643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70859559555735292718409095 106289339333602939077613643)
          ·
            refine ⟨159434009000404408616420465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106289339333602939077613643 159434009000404408616420465)
            ·
              refine ⟨119575506750303306462315349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159434009000404408616420465 119575506750303306462315349)
              ·
                refine ⟨700637734865058436302629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 119575506750303306462315349 700637734865058436302629)
                ·
                  refine ⟨131369575287198456806743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 700637734865058436302629 131369575287198456806743)
                  ·
                    rfl

theorem cell21_575643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 4].length) (baseStart_575643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_575643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_575643 prefixEnd_575643 := by exact prefixLift 575643
  have htrace : WordTrace (prefixWord ++ tailWord_575643) baseStart_575643 baseEnd_575643 := by
    simpa [prefixWord, tailWord_575643, baseEnd_575643] using wordTrace_append hprefix tailTrace_575643
  have hstable : (prefixWord ++ tailWord_575643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575643).length < 2 ^ (prefixWord ++ tailWord_575643).sum := by decide
  have hdescent : baseEnd_575643 < baseStart_575643 := by decide
  rcases family_descends (prefixWord ++ tailWord_575643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575708 : List Nat := [2, 2, 5, 2, 1, 1, 1, 7]
def baseStart_575708 : Nat := 118140960795 + 575708 * 2 ^ 59
def prefixEnd_575708 : Nat := 4983230072969 + 3 ^ 40 * 575708 * 2
def baseEnd_575708 : Nat := 43794803057590929407759

theorem tailTrace_575708 : CollatzResearch.WordTrace tailWord_575708 prefixEnd_575708 43794803057590929407759 := by
  unfold tailWord_575708
  simp only [CollatzResearch.WordTrace]
  refine ⟨10498897899157856971803889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13998530532210475962405185 10498897899157856971803889)
  ·
    refine ⟨7874173424368392728852917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10498897899157856971803889 7874173424368392728852917)
    ·
      refine ⟨738203758534536818329961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7874173424368392728852917 738203758534536818329961)
      ·
        refine ⟨553652818900902613747471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 738203758534536818329961 553652818900902613747471)
        ·
          refine ⟨830479228351353920621207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553652818900902613747471 830479228351353920621207)
          ·
            refine ⟨1245718842527030880931811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830479228351353920621207 1245718842527030880931811)
            ·
              refine ⟨1868578263790546321397717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1245718842527030880931811 1868578263790546321397717)
              ·
                refine ⟨43794803057590929407759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1868578263790546321397717 43794803057590929407759)
                ·
                  rfl

theorem cell21_575708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 7].length) (baseStart_575708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_575708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_575708 prefixEnd_575708 := by exact prefixLift 575708
  have htrace : WordTrace (prefixWord ++ tailWord_575708) baseStart_575708 baseEnd_575708 := by
    simpa [prefixWord, tailWord_575708, baseEnd_575708] using wordTrace_append hprefix tailTrace_575708
  have hstable : (prefixWord ++ tailWord_575708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575708).length < 2 ^ (prefixWord ++ tailWord_575708).sum := by decide
  have hdescent : baseEnd_575708 < baseStart_575708 := by decide
  rcases family_descends (prefixWord ++ tailWord_575708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575714 : List Nat := [3, 3, 4, 1, 1, 2, 1, 3, 3]
def baseStart_575714 : Nat := 118140960795 + 575714 * 2 ^ 59
def prefixEnd_575714 : Nat := 4983230072969 + 3 ^ 40 * 575714 * 2
def baseEnd_575714 : Nat := 131385778454518111123265

theorem tailTrace_575714 : CollatzResearch.WordTrace tailWord_575714 prefixEnd_575714 131385778454518111123265 := by
  unfold tailWord_575714
  simp only [CollatzResearch.WordTrace]
  refine ⟨5249503659073494242081549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13998676424195984645550797 5249503659073494242081549)
  ·
    refine ⟨1968563872152560340780581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5249503659073494242081549 1968563872152560340780581)
    ·
      refine ⟨369105726028605063896359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1968563872152560340780581 369105726028605063896359)
      ·
        refine ⟨553658589042907595844539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369105726028605063896359 553658589042907595844539)
        ·
          refine ⟨830487883564361393766809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553658589042907595844539 830487883564361393766809)
          ·
            refine ⟨622865912673271045325107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 830487883564361393766809 622865912673271045325107)
            ·
              refine ⟨934298869009906567987661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622865912673271045325107 934298869009906567987661)
              ·
                refine ⟨350362075878714962995373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 934298869009906567987661 350362075878714962995373)
                ·
                  refine ⟨131385778454518111123265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 350362075878714962995373 131385778454518111123265)
                  ·
                    rfl

theorem cell21_575714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_575714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_575714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_575714 prefixEnd_575714 := by exact prefixLift 575714
  have htrace : WordTrace (prefixWord ++ tailWord_575714) baseStart_575714 baseEnd_575714 := by
    simpa [prefixWord, tailWord_575714, baseEnd_575714] using wordTrace_append hprefix tailTrace_575714
  have hstable : (prefixWord ++ tailWord_575714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575714).length < 2 ^ (prefixWord ++ tailWord_575714).sum := by decide
  have hdescent : baseEnd_575714 < baseStart_575714 := by decide
  rcases family_descends (prefixWord ++ tailWord_575714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575753 : List Nat := [1, 2, 1, 1, 3, 6, 2, 1, 4]
def baseStart_575753 : Nat := 118140960795 + 575753 * 2 ^ 59
def prefixEnd_575753 : Nat := 4983230072969 + 3 ^ 40 * 575753 * 2
def baseEnd_575753 : Nat := 131394678785862709973185

theorem tailTrace_575753 : CollatzResearch.WordTrace tailWord_575753 prefixEnd_575753 131394678785862709973185 := by
  unfold tailWord_575753
  simp only [CollatzResearch.WordTrace]
  refine ⟨20999437083152686628995913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13999624722101791085997275 20999437083152686628995913)
  ·
    refine ⟨15749577812364514971746935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20999437083152686628995913 15749577812364514971746935)
    ·
      refine ⟨23624366718546772457620403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15749577812364514971746935 23624366718546772457620403)
      ·
        refine ⟨35436550077820158686430605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23624366718546772457620403 35436550077820158686430605)
        ·
          refine ⟨13288706279182559507411477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35436550077820158686430605 13288706279182559507411477)
          ·
            refine ⟨622908106836682476909913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13288706279182559507411477 622908106836682476909913)
            ·
              refine ⟨467181080127511857682435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622908106836682476909913 467181080127511857682435)
              ·
                refine ⟨700771620191267786523653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 467181080127511857682435 700771620191267786523653)
                ·
                  refine ⟨131394678785862709973185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 700771620191267786523653 131394678785862709973185)
                  ·
                    rfl

theorem cell21_575753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 4].length) (baseStart_575753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_575753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_575753 prefixEnd_575753 := by exact prefixLift 575753
  have htrace : WordTrace (prefixWord ++ tailWord_575753) baseStart_575753 baseEnd_575753 := by
    simpa [prefixWord, tailWord_575753, baseEnd_575753] using wordTrace_append hprefix tailTrace_575753
  have hstable : (prefixWord ++ tailWord_575753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575753).length < 2 ^ (prefixWord ++ tailWord_575753).sum := by decide
  have hdescent : baseEnd_575753 < baseStart_575753 := by decide
  rcases family_descends (prefixWord ++ tailWord_575753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575790 : List Nat := [4, 1, 3, 3, 2, 1, 2, 2, 3]
def baseStart_575790 : Nat := 118140960795 + 575790 * 2 ^ 59
def prefixEnd_575790 : Nat := 4983230072969 + 3 ^ 40 * 575790 * 2
def baseEnd_575790 : Nat := 131403122689958867856443

theorem tailTrace_575790 : CollatzResearch.WordTrace tailWord_575790 prefixEnd_575790 131403122689958867856443 := by
  unfold tailWord_575790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2625098323002330243511603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14000524389345761298728549 2625098323002330243511603)
  ·
    refine ⟨3937647484503495365267405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2625098323002330243511603 3937647484503495365267405)
    ·
      refine ⟨1476617806688810761975277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3937647484503495365267405 1476617806688810761975277)
      ·
        refine ⟨553731677508304035740729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1476617806688810761975277 553731677508304035740729)
        ·
          refine ⟨415298758131228026805547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 553731677508304035740729 415298758131228026805547)
          ·
            refine ⟨622948137196842040208321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415298758131228026805547 622948137196842040208321)
            ·
              refine ⟨467211102897631530156241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622948137196842040208321 467211102897631530156241)
              ·
                refine ⟨350408327173223647617181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 467211102897631530156241 350408327173223647617181)
                ·
                  refine ⟨131403122689958867856443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 350408327173223647617181 131403122689958867856443)
                  ·
                    rfl

theorem cell21_575790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_575790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_575790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_575790 prefixEnd_575790 := by exact prefixLift 575790
  have htrace : WordTrace (prefixWord ++ tailWord_575790) baseStart_575790 baseEnd_575790 := by
    simpa [prefixWord, tailWord_575790, baseEnd_575790] using wordTrace_append hprefix tailTrace_575790
  have hstable : (prefixWord ++ tailWord_575790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575790).length < 2 ^ (prefixWord ++ tailWord_575790).sum := by decide
  have hdescent : baseEnd_575790 < baseStart_575790 := by decide
  rcases family_descends (prefixWord ++ tailWord_575790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575894 : List Nat := [5, 3, 1, 2, 2, 1, 7]
def baseStart_575894 : Nat := 118140960795 + 575894 * 2 ^ 59
def prefixEnd_575894 : Nat := 4983230072969 + 3 ^ 40 * 575894 * 2
def baseEnd_575894 : Nat := 14602984100764199791433

theorem tailTrace_575894 : CollatzResearch.WordTrace tailWord_575894 prefixEnd_575894 14602984100764199791433 := by
  unfold tailWord_575894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1312786235977616731867421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14003053183761245139919157 1312786235977616731867421)
  ·
    refine ⟨492294838491606274450283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1312786235977616731867421 492294838491606274450283)
    ·
      refine ⟨738442257737409411675425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 492294838491606274450283 738442257737409411675425)
      ·
        refine ⟨553831693303057058756569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 738442257737409411675425 553831693303057058756569)
        ·
          refine ⟨415373769977292794067427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 553831693303057058756569 415373769977292794067427)
          ·
            refine ⟨623060654965939191101141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415373769977292794067427 623060654965939191101141)
            ·
              refine ⟨14602984100764199791433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 623060654965939191101141 14602984100764199791433)
              ·
                rfl

theorem cell21_575894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 7].length) (baseStart_575894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_575894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_575894 prefixEnd_575894 := by exact prefixLift 575894
  have htrace : WordTrace (prefixWord ++ tailWord_575894) baseStart_575894 baseEnd_575894 := by
    simpa [prefixWord, tailWord_575894, baseEnd_575894] using wordTrace_append hprefix tailTrace_575894
  have hstable : (prefixWord ++ tailWord_575894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575894).length < 2 ^ (prefixWord ++ tailWord_575894).sum := by decide
  have hdescent : baseEnd_575894 < baseStart_575894 := by decide
  rcases family_descends (prefixWord ++ tailWord_575894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575967 : List Nat := [1, 1, 2, 3, 3, 4, 2, 2, 3]
def baseStart_575967 : Nat := 118140960795 + 575967 * 2 ^ 59
def prefixEnd_575967 : Nat := 4983230072969 + 3 ^ 40 * 575967 * 2
def baseEnd_575967 : Nat := 131443516501445893406081

theorem tailTrace_575967 : CollatzResearch.WordTrace tailWord_575967 prefixEnd_575967 131443516501445893406081 := by
  unfold tailWord_575967
  simp only [CollatzResearch.WordTrace]
  refine ⟨21007242304377401177286155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14004828202918267451524103 21007242304377401177286155)
  ·
    refine ⟨31510863456566101765929233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21007242304377401177286155 31510863456566101765929233)
    ·
      refine ⟨23633147592424576324446925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31510863456566101765929233 23633147592424576324446925)
      ·
        refine ⟨8862430347159216121667597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23633147592424576324446925 8862430347159216121667597)
        ·
          refine ⟨3323411380184706045625349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8862430347159216121667597 3323411380184706045625349)
          ·
            refine ⟨623139633784632383554753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3323411380184706045625349 623139633784632383554753)
            ·
              refine ⟨467354725338474287666065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 623139633784632383554753 467354725338474287666065)
              ·
                refine ⟨350516044003855715749549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 467354725338474287666065 350516044003855715749549)
                ·
                  refine ⟨131443516501445893406081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 350516044003855715749549 131443516501445893406081)
                  ·
                    rfl

theorem cell21_575967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 3].length) (baseStart_575967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_575967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_575967 prefixEnd_575967 := by exact prefixLift 575967
  have htrace : WordTrace (prefixWord ++ tailWord_575967) baseStart_575967 baseEnd_575967 := by
    simpa [prefixWord, tailWord_575967, baseEnd_575967] using wordTrace_append hprefix tailTrace_575967
  have hstable : (prefixWord ++ tailWord_575967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575967).length < 2 ^ (prefixWord ++ tailWord_575967).sum := by decide
  have hdescent : baseEnd_575967 < baseStart_575967 := by decide
  rcases family_descends (prefixWord ++ tailWord_575967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575978 : List Nat := [3, 1, 3, 1, 3, 1, 3, 6]
def baseStart_575978 : Nat := 118140960795 + 575978 * 2 ^ 59
def prefixEnd_575978 : Nat := 4983230072969 + 3 ^ 40 * 575978 * 2
def baseEnd_575978 : Nat := 43815342283770772907575

theorem tailTrace_575978 : CollatzResearch.WordTrace tailWord_575978 prefixEnd_575978 43815342283770772907575 := by
  unfold tailWord_575978
  simp only [CollatzResearch.WordTrace]
  refine ⟨5251910876834387513984147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14005095671558366703957725 5251910876834387513984147)
  ·
    refine ⟨7877866315251581270976221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5251910876834387513984147 7877866315251581270976221)
    ·
      refine ⟨2954199868219342976616083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7877866315251581270976221 2954199868219342976616083)
      ·
        refine ⟨4431299802329014464924125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2954199868219342976616083 4431299802329014464924125)
        ·
          refine ⟨1661737425873380424346547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4431299802329014464924125 1661737425873380424346547)
          ·
            refine ⟨2492606138810070636519821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1661737425873380424346547 2492606138810070636519821)
            ·
              refine ⟨934727302053776488694933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2492606138810070636519821 934727302053776488694933)
              ·
                refine ⟨43815342283770772907575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 934727302053776488694933 43815342283770772907575)
                ·
                  rfl

theorem cell21_575978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_575978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_575978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_575978 prefixEnd_575978 := by exact prefixLift 575978
  have htrace : WordTrace (prefixWord ++ tailWord_575978) baseStart_575978 baseEnd_575978 := by
    simpa [prefixWord, tailWord_575978, baseEnd_575978] using wordTrace_append hprefix tailTrace_575978
  have hstable : (prefixWord ++ tailWord_575978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575978).length < 2 ^ (prefixWord ++ tailWord_575978).sum := by decide
  have hdescent : baseEnd_575978 < baseStart_575978 := by decide
  rcases family_descends (prefixWord ++ tailWord_575978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575992 : List Nat := [2, 1, 2, 1, 1, 4, 3, 2, 5]
def baseStart_575992 : Nat := 118140960795 + 575992 * 2 ^ 59
def prefixEnd_575992 : Nat := 4983230072969 + 3 ^ 40 * 575992 * 2
def baseEnd_575992 : Nat := 131449221842051405489363

theorem tailTrace_575992 : CollatzResearch.WordTrace tailWord_575992 prefixEnd_575992 131449221842051405489363 := by
  unfold tailWord_575992
  simp only [CollatzResearch.WordTrace]
  refine ⟨10504077064643415223473115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14005436086191220297964153 10504077064643415223473115)
  ·
    refine ⟨15756115596965122835209673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10504077064643415223473115 15756115596965122835209673)
    ·
      refine ⟨11817086697723842126407255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15756115596965122835209673 11817086697723842126407255)
      ·
        refine ⟨17725630046585763189610883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11817086697723842126407255 17725630046585763189610883)
        ·
          refine ⟨26588445069878644784416325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17725630046585763189610883 26588445069878644784416325)
          ·
            refine ⟨4985333450602245897078061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26588445069878644784416325 4985333450602245897078061)
            ·
              refine ⟨1869500043975842211404273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4985333450602245897078061 1869500043975842211404273)
              ·
                refine ⟨1402125032981881658553205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1869500043975842211404273 1402125032981881658553205)
                ·
                  refine ⟨131449221842051405489363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1402125032981881658553205 131449221842051405489363)
                  ·
                    rfl

theorem cell21_575992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_575992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_575992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_575992 prefixEnd_575992 := by exact prefixLift 575992
  have htrace : WordTrace (prefixWord ++ tailWord_575992) baseStart_575992 baseEnd_575992 := by
    simpa [prefixWord, tailWord_575992, baseEnd_575992] using wordTrace_append hprefix tailTrace_575992
  have hstable : (prefixWord ++ tailWord_575992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575992).length < 2 ^ (prefixWord ++ tailWord_575992).sum := by decide
  have hdescent : baseEnd_575992 < baseStart_575992 := by decide
  rcases family_descends (prefixWord ++ tailWord_575992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576085 : List Nat := [1, 3, 2, 2, 1, 1, 2, 6, 3]
def baseStart_576085 : Nat := 118140960795 + 576085 * 2 ^ 59
def prefixEnd_576085 : Nat := 4983230072969 + 3 ^ 40 * 576085 * 2
def baseEnd_576085 : Nat := 131470445709103910439173

theorem tailTrace_576085 : CollatzResearch.WordTrace tailWord_576085 prefixEnd_576085 131470445709103910439173 := by
  unfold tailWord_576085
  simp only [CollatzResearch.WordTrace]
  refine ⟨21011546117949907330081709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14007697411966604886721139 21011546117949907330081709)
  ·
    refine ⟨7879329794231215248780641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21011546117949907330081709 7879329794231215248780641)
    ·
      refine ⟨5909497345673411436585481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7879329794231215248780641 5909497345673411436585481)
      ·
        refine ⟨4432123009255058577439111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5909497345673411436585481 4432123009255058577439111)
        ·
          refine ⟨6648184513882587866158667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4432123009255058577439111 6648184513882587866158667)
          ·
            refine ⟨9972276770823881799238001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6648184513882587866158667 9972276770823881799238001)
            ·
              refine ⟨7479207578117911349428501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9972276770823881799238001 7479207578117911349428501)
              ·
                refine ⟨350587855224277094504461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7479207578117911349428501 350587855224277094504461)
                ·
                  refine ⟨131470445709103910439173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 350587855224277094504461 131470445709103910439173)
                  ·
                    rfl

theorem cell21_576085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_576085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576085 prefixEnd_576085 := by exact prefixLift 576085
  have htrace : WordTrace (prefixWord ++ tailWord_576085) baseStart_576085 baseEnd_576085 := by
    simpa [prefixWord, tailWord_576085, baseEnd_576085] using wordTrace_append hprefix tailTrace_576085
  have hstable : (prefixWord ++ tailWord_576085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576085).length < 2 ^ (prefixWord ++ tailWord_576085).sum := by decide
  have hdescent : baseEnd_576085 < baseStart_576085 := by decide
  rcases family_descends (prefixWord ++ tailWord_576085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576099 : List Nat := [1, 1, 1, 5, 1, 2, 3, 3, 4]
def baseStart_576099 : Nat := 118140960795 + 576099 * 2 ^ 59
def prefixEnd_576099 : Nat := 4983230072969 + 3 ^ 40 * 576099 * 2
def baseEnd_576099 : Nat := 131473640699842997205811

theorem tailTrace_576099 : CollatzResearch.WordTrace tailWord_576099 prefixEnd_576099 131473640699842997205811 := by
  unfold tailWord_576099
  simp only [CollatzResearch.WordTrace]
  refine ⟨21012056739899187721091351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14008037826599458480727567 21012056739899187721091351)
  ·
    refine ⟨31518085109848781581637027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21012056739899187721091351 31518085109848781581637027)
    ·
      refine ⟨47277127664773172372455541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31518085109848781581637027 47277127664773172372455541)
      ·
        refine ⟨4432230718572484909917707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47277127664773172372455541 4432230718572484909917707)
        ·
          refine ⟨6648346077858727364876561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4432230718572484909917707 6648346077858727364876561)
          ·
            refine ⟨4986259558394045523657421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6648346077858727364876561 4986259558394045523657421)
            ·
              refine ⟨1869847334397767071371533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4986259558394045523657421 1869847334397767071371533)
              ·
                refine ⟨701192750399162651764325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1869847334397767071371533 701192750399162651764325)
                ·
                  refine ⟨131473640699842997205811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 701192750399162651764325 131473640699842997205811)
                  ·
                    rfl

theorem cell21_576099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 4].length) (baseStart_576099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576099 prefixEnd_576099 := by exact prefixLift 576099
  have htrace : WordTrace (prefixWord ++ tailWord_576099) baseStart_576099 baseEnd_576099 := by
    simpa [prefixWord, tailWord_576099, baseEnd_576099] using wordTrace_append hprefix tailTrace_576099
  have hstable : (prefixWord ++ tailWord_576099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576099).length < 2 ^ (prefixWord ++ tailWord_576099).sum := by decide
  have hdescent : baseEnd_576099 < baseStart_576099 := by decide
  rcases family_descends (prefixWord ++ tailWord_576099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576127 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 9]
def baseStart_576127 : Nat := 118140960795 + 576127 * 2 ^ 59
def prefixEnd_576127 : Nat := 4983230072969 + 3 ^ 40 * 576127 * 2
def baseEnd_576127 : Nat := 131480030681321170739087

theorem tailTrace_576127 : CollatzResearch.WordTrace tailWord_576127 prefixEnd_576127 131480030681321170739087 := by
  unfold tailWord_576127
  simp only [CollatzResearch.WordTrace]
  refine ⟨21013077983797748503110635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14008718655865165668740423 21013077983797748503110635)
  ·
    refine ⟨31519616975696622754665953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21013077983797748503110635 31519616975696622754665953)
    ·
      refine ⟨23639712731772467065999465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31519616975696622754665953 23639712731772467065999465)
      ·
        refine ⟨17729784548829350299499599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23639712731772467065999465 17729784548829350299499599)
        ·
          refine ⟨26594676823244025449249399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17729784548829350299499599 26594676823244025449249399)
          ·
            refine ⟨39892015234866038173874099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26594676823244025449249399 39892015234866038173874099)
            ·
              refine ⟨59838022852299057260811149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39892015234866038173874099 59838022852299057260811149)
              ·
                refine ⟨22439258569612146472804181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59838022852299057260811149 22439258569612146472804181)
                ·
                  refine ⟨131480030681321170739087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22439258569612146472804181 131480030681321170739087)
                  ·
                    rfl

theorem cell21_576127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 9].length) (baseStart_576127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576127 prefixEnd_576127 := by exact prefixLift 576127
  have htrace : WordTrace (prefixWord ++ tailWord_576127) baseStart_576127 baseEnd_576127 := by
    simpa [prefixWord, tailWord_576127, baseEnd_576127] using wordTrace_append hprefix tailTrace_576127
  have hstable : (prefixWord ++ tailWord_576127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576127).length < 2 ^ (prefixWord ++ tailWord_576127).sum := by decide
  have hdescent : baseEnd_576127 < baseStart_576127 := by decide
  rcases family_descends (prefixWord ++ tailWord_576127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576161 : List Nat := [1, 2, 3, 3, 3, 1, 1, 2, 5]
def baseStart_576161 : Nat := 118140960795 + 576161 * 2 ^ 59
def prefixEnd_576161 : Nat := 4983230072969 + 3 ^ 40 * 576161 * 2
def baseEnd_576161 : Nat := 131487789944544667172351

theorem tailTrace_576161 : CollatzResearch.WordTrace tailWord_576161 prefixEnd_576161 131487789944544667172351 := by
  unfold tailWord_576161
  simp only [CollatzResearch.WordTrace]
  refine ⟨21014318065674572309848337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14009545377116381539898891 21014318065674572309848337)
  ·
    refine ⟨15760738549255929232386253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21014318065674572309848337 15760738549255929232386253)
    ·
      refine ⟨5910276955970973462144845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15760738549255929232386253 5910276955970973462144845)
      ·
        refine ⟨2216353858489115048304317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5910276955970973462144845 2216353858489115048304317)
        ·
          refine ⟨831132696933418143114119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2216353858489115048304317 831132696933418143114119)
          ·
            refine ⟨1246699045400127214671179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 831132696933418143114119 1246699045400127214671179)
            ·
              refine ⟨1870048568100190822006769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1246699045400127214671179 1870048568100190822006769)
              ·
                refine ⟨1402536426075143116505077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1870048568100190822006769 1402536426075143116505077)
                ·
                  refine ⟨131487789944544667172351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1402536426075143116505077 131487789944544667172351)
                  ·
                    rfl

theorem cell21_576161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 5].length) (baseStart_576161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576161 prefixEnd_576161 := by exact prefixLift 576161
  have htrace : WordTrace (prefixWord ++ tailWord_576161) baseStart_576161 baseEnd_576161 := by
    simpa [prefixWord, tailWord_576161, baseEnd_576161] using wordTrace_append hprefix tailTrace_576161
  have hstable : (prefixWord ++ tailWord_576161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576161).length < 2 ^ (prefixWord ++ tailWord_576161).sum := by decide
  have hdescent : baseEnd_576161 < baseStart_576161 := by decide
  rcases family_descends (prefixWord ++ tailWord_576161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576189 : List Nat := [1, 4, 1, 2, 1, 4, 8]
def baseStart_576189 : Nat := 118140960795 + 576189 * 2 ^ 59
def prefixEnd_576189 : Nat := 4983230072969 + 3 ^ 40 * 576189 * 2
def baseEnd_576189 : Nat := 14610464436224760078403

theorem tailTrace_576189 : CollatzResearch.WordTrace tailWord_576189 prefixEnd_576189 14610464436224760078403 := by
  unfold tailWord_576189
  simp only [CollatzResearch.WordTrace]
  refine ⟨21015339309573133091867621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14010226206382088727911747 21015339309573133091867621)
  ·
    refine ⟨3940376120544962454725179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21015339309573133091867621 3940376120544962454725179)
    ·
      refine ⟨5910564180817443682087769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3940376120544962454725179 5910564180817443682087769)
      ·
        refine ⟨4432923135613082761565827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5910564180817443682087769 4432923135613082761565827)
        ·
          refine ⟨6649384703419624142348741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4432923135613082761565827 6649384703419624142348741)
          ·
            refine ⟨1246759631891179526690389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6649384703419624142348741 1246759631891179526690389)
            ·
              refine ⟨14610464436224760078403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1246759631891179526690389 14610464436224760078403)
              ·
                rfl

theorem cell21_576189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 8].length) (baseStart_576189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576189 prefixEnd_576189 := by exact prefixLift 576189
  have htrace : WordTrace (prefixWord ++ tailWord_576189) baseStart_576189 baseEnd_576189 := by
    simpa [prefixWord, tailWord_576189, baseEnd_576189] using wordTrace_append hprefix tailTrace_576189
  have hstable : (prefixWord ++ tailWord_576189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576189).length < 2 ^ (prefixWord ++ tailWord_576189).sum := by decide
  have hdescent : baseEnd_576189 < baseStart_576189 := by decide
  rcases family_descends (prefixWord ++ tailWord_576189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576192 : List Nat := [2, 1, 1, 2, 4, 4, 1, 2, 4]
def baseStart_576192 : Nat := 118140960795 + 576192 * 2 ^ 59
def prefixEnd_576192 : Nat := 4983230072969 + 3 ^ 40 * 576192 * 2
def baseEnd_576192 : Nat := 131494864566895502155621

theorem tailTrace_576192 : CollatzResearch.WordTrace tailWord_576192 prefixEnd_576192 131494864566895502155621 := by
  unfold tailWord_576192
  simp only [CollatzResearch.WordTrace]
  refine ⟨10507724364281132302113415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14010299152374843069484553 10507724364281132302113415)
  ·
    refine ⟨15761586546421698453170123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10507724364281132302113415 15761586546421698453170123)
    ·
      refine ⟨23642379819632547679755185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15761586546421698453170123 23642379819632547679755185)
      ·
        refine ⟨17731784864724410759816389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23642379819632547679755185 17731784864724410759816389)
        ·
          refine ⟨3324709662135827017465573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17731784864724410759816389 3324709662135827017465573)
          ·
            refine ⟨623383061650467565774795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3324709662135827017465573 623383061650467565774795)
            ·
              refine ⟨935074592475701348662193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 623383061650467565774795 935074592475701348662193)
              ·
                refine ⟨701305944356776011496645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 935074592475701348662193 701305944356776011496645)
                ·
                  refine ⟨131494864566895502155621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 701305944356776011496645 131494864566895502155621)
                  ·
                    rfl

theorem cell21_576192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 4].length) (baseStart_576192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576192 prefixEnd_576192 := by exact prefixLift 576192
  have htrace : WordTrace (prefixWord ++ tailWord_576192) baseStart_576192 baseEnd_576192 := by
    simpa [prefixWord, tailWord_576192, baseEnd_576192] using wordTrace_append hprefix tailTrace_576192
  have hstable : (prefixWord ++ tailWord_576192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576192).length < 2 ^ (prefixWord ++ tailWord_576192).sum := by decide
  have hdescent : baseEnd_576192 < baseStart_576192 := by decide
  rcases family_descends (prefixWord ++ tailWord_576192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576254 : List Nat := [4, 2, 2, 1, 2, 3, 1, 1, 5]
def baseStart_576254 : Nat := 118140960795 + 576254 * 2 ^ 59
def prefixEnd_576254 : Nat := 4983230072969 + 3 ^ 40 * 576254 * 2
def baseEnd_576254 : Nat := 131509013811597172122161

theorem tailTrace_576254 : CollatzResearch.WordTrace tailWord_576254 prefixEnd_576254 131509013811597172122161 := by
  unfold tailWord_576254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2627213756792206149122977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14011806702891766128655877 2627213756792206149122977)
  ·
    refine ⟨1970410317594154611842233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2627213756792206149122977 1970410317594154611842233)
    ·
      refine ⟨1477807738195615958881675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1970410317594154611842233 1477807738195615958881675)
      ·
        refine ⟨2216711607293423938322513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1477807738195615958881675 2216711607293423938322513)
        ·
          refine ⟨1662533705470067953741885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2216711607293423938322513 1662533705470067953741885)
          ·
            refine ⟨623450139551275482653207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1662533705470067953741885 623450139551275482653207)
            ·
              refine ⟨935175209326913223979811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 623450139551275482653207 935175209326913223979811)
              ·
                refine ⟨1402762813990369835969717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 935175209326913223979811 1402762813990369835969717)
                ·
                  refine ⟨131509013811597172122161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1402762813990369835969717 131509013811597172122161)
                  ·
                    rfl

theorem cell21_576254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_576254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576254 prefixEnd_576254 := by exact prefixLift 576254
  have htrace : WordTrace (prefixWord ++ tailWord_576254) baseStart_576254 baseEnd_576254 := by
    simpa [prefixWord, tailWord_576254, baseEnd_576254] using wordTrace_append hprefix tailTrace_576254
  have hstable : (prefixWord ++ tailWord_576254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576254).length < 2 ^ (prefixWord ++ tailWord_576254).sum := by decide
  have hdescent : baseEnd_576254 < baseStart_576254 := by decide
  rcases family_descends (prefixWord ++ tailWord_576254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576417 : List Nat := [1, 2, 3, 4, 1, 1, 9]
def baseStart_576417 : Nat := 118140960795 + 576417 * 2 ^ 59
def prefixEnd_576417 : Nat := 4983230072969 + 3 ^ 40 * 576417 * 2
def baseEnd_576417 : Nat := 14616245848038345656129

theorem tailTrace_576417 : CollatzResearch.WordTrace tailWord_576417 prefixEnd_576417 14616245848038345656129 := by
  unfold tailWord_576417
  simp only [CollatzResearch.WordTrace]
  refine ⟨21023655152747128031167505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14015770101831418687445003 21023655152747128031167505)
  ·
    refine ⟨15767741364560346023375629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21023655152747128031167505 15767741364560346023375629)
    ·
      refine ⟨5912903011710129758765861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15767741364560346023375629 5912903011710129758765861)
      ·
        refine ⟨1108669314695649329768599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5912903011710129758765861 1108669314695649329768599)
        ·
          refine ⟨1663003972043473994652899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1108669314695649329768599 1663003972043473994652899)
          ·
            refine ⟨2494505958065210991979349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1663003972043473994652899 2494505958065210991979349)
            ·
              refine ⟨14616245848038345656129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2494505958065210991979349 14616245848038345656129)
              ·
                rfl

theorem cell21_576417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 9].length) (baseStart_576417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576417 prefixEnd_576417 := by exact prefixLift 576417
  have htrace : WordTrace (prefixWord ++ tailWord_576417) baseStart_576417 baseEnd_576417 := by
    simpa [prefixWord, tailWord_576417, baseEnd_576417] using wordTrace_append hprefix tailTrace_576417
  have hstable : (prefixWord ++ tailWord_576417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576417).length < 2 ^ (prefixWord ++ tailWord_576417).sum := by decide
  have hdescent : baseEnd_576417 < baseStart_576417 := by decide
  rcases family_descends (prefixWord ++ tailWord_576417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576423 : List Nat := [1, 1, 6, 1, 3, 1, 3, 2, 3]
def baseStart_576423 : Nat := 118140960795 + 576423 * 2 ^ 59
def prefixEnd_576423 : Nat := 4983230072969 + 3 ^ 40 * 576423 * 2
def baseEnd_576423 : Nat := 131547581914090433805149

theorem tailTrace_576423 : CollatzResearch.WordTrace tailWord_576423 prefixEnd_576423 131547581914090433805149 := by
  unfold tailWord_576423
  simp only [CollatzResearch.WordTrace]
  refine ⟨21023873990725391055885923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14015915993816927370590615 21023873990725391055885923)
  ·
    refine ⟨31535810986088086583828885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21023873990725391055885923 31535810986088086583828885)
    ·
      refine ⟨1478241139972879058616979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31535810986088086583828885 1478241139972879058616979)
      ·
        refine ⟨2217361709959318587925469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1478241139972879058616979 2217361709959318587925469)
        ·
          refine ⟨831510641234744470472051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2217361709959318587925469 831510641234744470472051)
          ·
            refine ⟨1247265961852116705708077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 831510641234744470472051 1247265961852116705708077)
            ·
              refine ⟨467724735694543764640529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1247265961852116705708077 467724735694543764640529)
              ·
                refine ⟨350793551770907823480397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 467724735694543764640529 350793551770907823480397)
                ·
                  refine ⟨131547581914090433805149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 350793551770907823480397 131547581914090433805149)
                  ·
                    rfl

theorem cell21_576423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 3].length) (baseStart_576423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576423 prefixEnd_576423 := by exact prefixLift 576423
  have htrace : WordTrace (prefixWord ++ tailWord_576423) baseStart_576423 baseEnd_576423 := by
    simpa [prefixWord, tailWord_576423, baseEnd_576423] using wordTrace_append hprefix tailTrace_576423
  have hstable : (prefixWord ++ tailWord_576423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576423).length < 2 ^ (prefixWord ++ tailWord_576423).sum := by decide
  have hdescent : baseEnd_576423 < baseStart_576423 := by decide
  rcases family_descends (prefixWord ++ tailWord_576423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576431 : List Nat := [1, 1, 2, 1, 2, 2, 2, 5, 5]
def baseStart_576431 : Nat := 118140960795 + 576431 * 2 ^ 59
def prefixEnd_576431 : Nat := 4983230072969 + 3 ^ 40 * 576431 * 2
def baseEnd_576431 : Nat := 131549407623084197671799

theorem tailTrace_576431 : CollatzResearch.WordTrace tailWord_576431 prefixEnd_576431 131549407623084197671799 := by
  unfold tailWord_576431
  simp only [CollatzResearch.WordTrace]
  refine ⟨21024165774696408422177147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14016110516464272281451431 21024165774696408422177147)
  ·
    refine ⟨31536248662044612633265721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21024165774696408422177147 31536248662044612633265721)
    ·
      refine ⟨23652186496533459474949291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31536248662044612633265721 23652186496533459474949291)
      ·
        refine ⟨35478279744800189212423937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23652186496533459474949291 35478279744800189212423937)
        ·
          refine ⟨26608709808600141909317953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35478279744800189212423937 26608709808600141909317953)
          ·
            refine ⟨19956532356450106431988465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26608709808600141909317953 19956532356450106431988465)
            ·
              refine ⟨14967399267337579823991349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19956532356450106431988465 14967399267337579823991349)
              ·
                refine ⟨1403193681312898108499189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14967399267337579823991349 1403193681312898108499189)
                ·
                  refine ⟨131549407623084197671799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1403193681312898108499189 131549407623084197671799)
                  ·
                    rfl

theorem cell21_576431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 5].length) (baseStart_576431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576431 prefixEnd_576431 := by exact prefixLift 576431
  have htrace : WordTrace (prefixWord ++ tailWord_576431) baseStart_576431 baseEnd_576431 := by
    simpa [prefixWord, tailWord_576431, baseEnd_576431] using wordTrace_append hprefix tailTrace_576431
  have hstable : (prefixWord ++ tailWord_576431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576431).length < 2 ^ (prefixWord ++ tailWord_576431).sum := by decide
  have hdescent : baseEnd_576431 < baseStart_576431 := by decide
  rcases family_descends (prefixWord ++ tailWord_576431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576538 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 6]
def baseStart_576538 : Nat := 118140960795 + 576538 * 2 ^ 59
def prefixEnd_576538 : Nat := 4983230072969 + 3 ^ 40 * 576538 * 2
def baseEnd_576538 : Nat := 131573826480875789388247

theorem tailTrace_576538 : CollatzResearch.WordTrace tailWord_576538 prefixEnd_576538 131573826480875789388247 := by
  unfold tailWord_576538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5257017096327191424080567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14018712256872510464214845 5257017096327191424080567)
  ·
    refine ⟨7885525644490787136120851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5257017096327191424080567 7885525644490787136120851)
    ·
      refine ⟨11828288466736180704181277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7885525644490787136120851 11828288466736180704181277)
      ·
        refine ⟨4435608175026067764067979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11828288466736180704181277 4435608175026067764067979)
        ·
          refine ⟨6653412262539101646101969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4435608175026067764067979 6653412262539101646101969)
          ·
            refine ⟨4990059196904326234576477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6653412262539101646101969 4990059196904326234576477)
            ·
              refine ⟨1871272198839122337966179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4990059196904326234576477 1871272198839122337966179)
              ·
                refine ⟨2806908298258683506949269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1871272198839122337966179 2806908298258683506949269)
                ·
                  refine ⟨131573826480875789388247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2806908298258683506949269 131573826480875789388247)
                  ·
                    rfl

theorem cell21_576538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_576538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576538 prefixEnd_576538 := by exact prefixLift 576538
  have htrace : WordTrace (prefixWord ++ tailWord_576538) baseStart_576538 baseEnd_576538 := by
    simpa [prefixWord, tailWord_576538, baseEnd_576538] using wordTrace_append hprefix tailTrace_576538
  have hstable : (prefixWord ++ tailWord_576538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576538).length < 2 ^ (prefixWord ++ tailWord_576538).sum := by decide
  have hdescent : baseEnd_576538 < baseStart_576538 := by decide
  rcases family_descends (prefixWord ++ tailWord_576538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576541 : List Nat := [1, 4, 2, 2, 3, 1, 2, 1, 5]
def baseStart_576541 : Nat := 118140960795 + 576541 * 2 ^ 59
def prefixEnd_576541 : Nat := 4983230072969 + 3 ^ 40 * 576541 * 2
def baseEnd_576541 : Nat := 131574511121748450838241

theorem tailTrace_576541 : CollatzResearch.WordTrace tailWord_576541 prefixEnd_576541 131574511121748450838241 := by
  unfold tailWord_576541
  simp only [CollatzResearch.WordTrace]
  refine ⟨21028177804297897208681477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14018785202865264805787651 21028177804297897208681477)
  ·
    refine ⟨3942783338305855726627777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21028177804297897208681477 3942783338305855726627777)
    ·
      refine ⟨2957087503729391794970833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3942783338305855726627777 2957087503729391794970833)
      ·
        refine ⟨2217815627797043846228125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2957087503729391794970833 2217815627797043846228125)
        ·
          refine ⟨831680860423891442335547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2217815627797043846228125 831680860423891442335547)
          ·
            refine ⟨1247521290635837163503321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 831680860423891442335547 1247521290635837163503321)
            ·
              refine ⟨935640967976877872627491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1247521290635837163503321 935640967976877872627491)
              ·
                refine ⟨1403461451965316808941237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 935640967976877872627491 1403461451965316808941237)
                ·
                  refine ⟨131574511121748450838241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1403461451965316808941237 131574511121748450838241)
                  ·
                    rfl

theorem cell21_576541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_576541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576541 prefixEnd_576541 := by exact prefixLift 576541
  have htrace : WordTrace (prefixWord ++ tailWord_576541) baseStart_576541 baseEnd_576541 := by
    simpa [prefixWord, tailWord_576541, baseEnd_576541] using wordTrace_append hprefix tailTrace_576541
  have hstable : (prefixWord ++ tailWord_576541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576541).length < 2 ^ (prefixWord ++ tailWord_576541).sum := by decide
  have hdescent : baseEnd_576541 < baseStart_576541 := by decide
  rcases family_descends (prefixWord ++ tailWord_576541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576555 : List Nat := [1, 1, 1, 1, 2, 1, 9, 1, 4]
def baseStart_576555 : Nat := 118140960795 + 576555 * 2 ^ 59
def prefixEnd_576555 : Nat := 4983230072969 + 3 ^ 40 * 576555 * 2
def baseEnd_576555 : Nat := 131577706112487537604879

theorem tailTrace_576555 : CollatzResearch.WordTrace tailWord_576555 prefixEnd_576555 131577706112487537604879 := by
  unfold tailWord_576555
  simp only [CollatzResearch.WordTrace]
  refine ⟨21028688426247177599691119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14019125617498118399794079 21028688426247177599691119)
  ·
    refine ⟨31543032639370766399536679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21028688426247177599691119 31543032639370766399536679)
    ·
      refine ⟨47314548959056149599305019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31543032639370766399536679 47314548959056149599305019)
      ·
        refine ⟨70971823438584224398957529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47314548959056149599305019 70971823438584224398957529)
        ·
          refine ⟨53228867578938168299218147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70971823438584224398957529 53228867578938168299218147)
          ·
            refine ⟨79843301368407252448827221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53228867578938168299218147 79843301368407252448827221)
            ·
              refine ⟨467831843955511244817347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 79843301368407252448827221 467831843955511244817347)
              ·
                refine ⟨701747765933266867226021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 467831843955511244817347 701747765933266867226021)
                ·
                  refine ⟨131577706112487537604879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 701747765933266867226021 131577706112487537604879)
                  ·
                    rfl

theorem cell21_576555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 4].length) (baseStart_576555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576555 prefixEnd_576555 := by exact prefixLift 576555
  have htrace : WordTrace (prefixWord ++ tailWord_576555) baseStart_576555 baseEnd_576555 := by
    simpa [prefixWord, tailWord_576555, baseEnd_576555] using wordTrace_append hprefix tailTrace_576555
  have hstable : (prefixWord ++ tailWord_576555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576555).length < 2 ^ (prefixWord ++ tailWord_576555).sum := by decide
  have hdescent : baseEnd_576555 < baseStart_576555 := by decide
  rcases family_descends (prefixWord ++ tailWord_576555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576569 : List Nat := [1, 2, 1, 5, 2, 2, 1, 7]
def baseStart_576569 : Nat := 118140960795 + 576569 * 2 ^ 59
def prefixEnd_576569 : Nat := 4983230072969 + 3 ^ 40 * 576569 * 2
def baseEnd_576569 : Nat := 43860300367742208123839

theorem tailTrace_576569 : CollatzResearch.WordTrace tailWord_576569 prefixEnd_576569 43860300367742208123839 := by
  unfold tailWord_576569
  simp only [CollatzResearch.WordTrace]
  refine ⟨21029199048196457990700761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14019466032130971993800507 21029199048196457990700761)
  ·
    refine ⟨15771899286147343493025571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21029199048196457990700761 15771899286147343493025571)
    ·
      refine ⟨23657848929221015239538357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15771899286147343493025571 23657848929221015239538357)
      ·
        refine ⟨2217923337114470178706721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23657848929221015239538357 2217923337114470178706721)
        ·
          refine ⟨1663442502835852634030041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2217923337114470178706721 1663442502835852634030041)
          ·
            refine ⟨1247581877126889475522531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1663442502835852634030041 1247581877126889475522531)
            ·
              refine ⟨1871372815690334213283797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1247581877126889475522531 1871372815690334213283797)
              ·
                refine ⟨43860300367742208123839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1871372815690334213283797 43860300367742208123839)
                ·
                  rfl

theorem cell21_576569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 7].length) (baseStart_576569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576569 prefixEnd_576569 := by exact prefixLift 576569
  have htrace : WordTrace (prefixWord ++ tailWord_576569) baseStart_576569 baseEnd_576569 := by
    simpa [prefixWord, tailWord_576569, baseEnd_576569] using wordTrace_append hprefix tailTrace_576569
  have hstable : (prefixWord ++ tailWord_576569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576569).length < 2 ^ (prefixWord ++ tailWord_576569).sum := by decide
  have hdescent : baseEnd_576569 < baseStart_576569 := by decide
  rcases family_descends (prefixWord ++ tailWord_576569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576606 : List Nat := [4, 4, 1, 1, 1, 1, 4, 1, 4]
def baseStart_576606 : Nat := 118140960795 + 576606 * 2 ^ 59
def prefixEnd_576606 : Nat := 4983230072969 + 3 ^ 40 * 576606 * 2
def baseEnd_576606 : Nat := 131589345007322782254775

theorem tailTrace_576606 : CollatzResearch.WordTrace tailWord_576606 prefixEnd_576606 131589345007322782254775 := by
  unfold tailWord_576606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2628818568632801663724709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14020365699374942206531781 2628818568632801663724709)
  ·
    refine ⟨492903481618650311948383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2628818568632801663724709 492903481618650311948383)
    ·
      refine ⟨739355222427975467922575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 492903481618650311948383 739355222427975467922575)
      ·
        refine ⟨1109032833641963201883863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 739355222427975467922575 1109032833641963201883863)
        ·
          refine ⟨1663549250462944802825795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109032833641963201883863 1663549250462944802825795)
          ·
            refine ⟨2495323875694417204238693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1663549250462944802825795 2495323875694417204238693)
            ·
              refine ⟨467873226692703225794755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2495323875694417204238693 467873226692703225794755)
              ·
                refine ⟨701809840039054838692133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 467873226692703225794755 701809840039054838692133)
                ·
                  refine ⟨131589345007322782254775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 701809840039054838692133 131589345007322782254775)
                  ·
                    rfl

theorem cell21_576606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_576606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576606 prefixEnd_576606 := by exact prefixLift 576606
  have htrace : WordTrace (prefixWord ++ tailWord_576606) baseStart_576606 baseEnd_576606 := by
    simpa [prefixWord, tailWord_576606, baseEnd_576606] using wordTrace_append hprefix tailTrace_576606
  have hstable : (prefixWord ++ tailWord_576606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576606).length < 2 ^ (prefixWord ++ tailWord_576606).sum := by decide
  have hdescent : baseEnd_576606 < baseStart_576606 := by decide
  rcases family_descends (prefixWord ++ tailWord_576606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576645 : List Nat := [1, 3, 1, 1, 7, 8]
def baseStart_576645 : Nat := 118140960795 + 576645 * 2 ^ 59
def prefixEnd_576645 : Nat := 4983230072969 + 3 ^ 40 * 576645 * 2
def baseEnd_576645 : Nat := 4874009086617310411285

theorem tailTrace_576645 : CollatzResearch.WordTrace tailWord_576645 prefixEnd_576645 4874009086617310411285 := by
  unfold tailWord_576645
  simp only [CollatzResearch.WordTrace]
  refine ⟨21031970995921122970467389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14021313997280748646978259 21031970995921122970467389)
  ·
    refine ⟨7886989123470421113925271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21031970995921122970467389 7886989123470421113925271)
    ·
      refine ⟨11830483685205631670887907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7886989123470421113925271 11830483685205631670887907)
      ·
        refine ⟨17745725527808447506331861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11830483685205631670887907 17745725527808447506331861)
        ·
          refine ⟨415915442058010488429653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 17745725527808447506331861 415915442058010488429653)
          ·
            refine ⟨4874009086617310411285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 415915442058010488429653 4874009086617310411285)
            ·
              rfl

theorem cell21_576645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 8].length) (baseStart_576645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576645 prefixEnd_576645 := by exact prefixLift 576645
  have htrace : WordTrace (prefixWord ++ tailWord_576645) baseStart_576645 baseEnd_576645 := by
    simpa [prefixWord, tailWord_576645, baseEnd_576645] using wordTrace_append hprefix tailTrace_576645
  have hstable : (prefixWord ++ tailWord_576645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576645).length < 2 ^ (prefixWord ++ tailWord_576645).sum := by decide
  have hdescent : baseEnd_576645 < baseStart_576645 := by decide
  rcases family_descends (prefixWord ++ tailWord_576645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576648 : List Nat := [2, 1, 3, 4, 2, 1, 2, 2, 4]
def baseStart_576648 : Nat := 118140960795 + 576648 * 2 ^ 59
def prefixEnd_576648 : Nat := 4983230072969 + 3 ^ 40 * 576648 * 2
def baseEnd_576648 : Nat := 131598929979540042554689

theorem tailTrace_576648 : CollatzResearch.WordTrace tailWord_576648 prefixEnd_576648 131598929979540042554689 := by
  unfold tailWord_576648
  simp only [CollatzResearch.WordTrace]
  refine ⟨10516040207455127241413299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14021386943273502988551065 10516040207455127241413299)
  ·
    refine ⟨15774060311182690862119949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10516040207455127241413299 15774060311182690862119949)
    ·
      refine ⟨5915272616693509073294981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15774060311182690862119949 5915272616693509073294981)
      ·
        refine ⟨1109113615630032951242809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5915272616693509073294981 1109113615630032951242809)
        ·
          refine ⟨831835211722524713432107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1109113615630032951242809 831835211722524713432107)
          ·
            refine ⟨1247752817583787070148161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 831835211722524713432107 1247752817583787070148161)
            ·
              refine ⟨935814613187840302611121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1247752817583787070148161 935814613187840302611121)
              ·
                refine ⟨701860959890880226958341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 935814613187840302611121 701860959890880226958341)
                ·
                  refine ⟨131598929979540042554689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 701860959890880226958341 131598929979540042554689)
                  ·
                    rfl

theorem cell21_576648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 4].length) (baseStart_576648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576648 prefixEnd_576648 := by exact prefixLift 576648
  have htrace : WordTrace (prefixWord ++ tailWord_576648) baseStart_576648 baseEnd_576648 := by
    simpa [prefixWord, tailWord_576648, baseEnd_576648] using wordTrace_append hprefix tailTrace_576648
  have hstable : (prefixWord ++ tailWord_576648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576648).length < 2 ^ (prefixWord ++ tailWord_576648).sum := by decide
  have hdescent : baseEnd_576648 < baseStart_576648 := by decide
  rcases family_descends (prefixWord ++ tailWord_576648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576676 : List Nat := [2, 3, 1, 2, 3, 2, 1, 2, 5]
def baseStart_576676 : Nat := 118140960795 + 576676 * 2 ^ 59
def prefixEnd_576676 : Nat := 4983230072969 + 3 ^ 40 * 576676 * 2
def baseEnd_576676 : Nat := 131605319961018216087965

theorem tailTrace_576676 : CollatzResearch.WordTrace tailWord_576676 prefixEnd_576676 131605319961018216087965 := by
  unfold tailWord_576676
  simp only [CollatzResearch.WordTrace]
  refine ⟨10516550829404407632422941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14022067772539210176563921 10516550829404407632422941)
  ·
    refine ⟨3943706561026652862158603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10516550829404407632422941 3943706561026652862158603)
    ·
      refine ⟨5915559841539979293237905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3943706561026652862158603 5915559841539979293237905)
      ·
        refine ⟨4436669881154984469928429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5915559841539979293237905 4436669881154984469928429)
        ·
          refine ⟨1663751205433119176223161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4436669881154984469928429 1663751205433119176223161)
          ·
            refine ⟨1247813404074839382167371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1663751205433119176223161 1247813404074839382167371)
            ·
              refine ⟨1871720106112259073251057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1247813404074839382167371 1871720106112259073251057)
              ·
                refine ⟨1403790079584194304938293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1871720106112259073251057 1403790079584194304938293)
                ·
                  refine ⟨131605319961018216087965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1403790079584194304938293 131605319961018216087965)
                  ·
                    rfl

theorem cell21_576676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_576676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576676 prefixEnd_576676 := by exact prefixLift 576676
  have htrace : WordTrace (prefixWord ++ tailWord_576676) baseStart_576676 baseEnd_576676 := by
    simpa [prefixWord, tailWord_576676, baseEnd_576676] using wordTrace_append hprefix tailTrace_576676
  have hstable : (prefixWord ++ tailWord_576676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576676).length < 2 ^ (prefixWord ++ tailWord_576676).sum := by decide
  have hdescent : baseEnd_576676 < baseStart_576676 := by decide
  rcases family_descends (prefixWord ++ tailWord_576676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576735 : List Nat := [1, 1, 2, 3, 2, 1, 4, 2, 5]
def baseStart_576735 : Nat := 118140960795 + 576735 * 2 ^ 59
def prefixEnd_576735 : Nat := 4983230072969 + 3 ^ 40 * 576735 * 2
def baseEnd_576735 : Nat := 131618784564847224604511

theorem tailTrace_576735 : CollatzResearch.WordTrace tailWord_576735 prefixEnd_576735 131618784564847224604511 := by
  unfold tailWord_576735
  simp only [CollatzResearch.WordTrace]
  refine ⟨21035253565595068341243659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14023502377063378894162439 21035253565595068341243659)
  ·
    refine ⟨31552880348392602511865489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21035253565595068341243659 31552880348392602511865489)
    ·
      refine ⟨23664660261294451883899117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31552880348392602511865489 23664660261294451883899117)
      ·
        refine ⟨8874247597985419456462169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23664660261294451883899117 8874247597985419456462169)
        ·
          refine ⟨6655685698489064592346627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8874247597985419456462169 6655685698489064592346627)
          ·
            refine ⟨9983528547733596888519941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6655685698489064592346627 9983528547733596888519941)
            ·
              refine ⟨1871911602700049416597489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9983528547733596888519941 1871911602700049416597489)
              ·
                refine ⟨1403933702025037062448117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1871911602700049416597489 1403933702025037062448117)
                ·
                  refine ⟨131618784564847224604511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1403933702025037062448117 131618784564847224604511)
                  ·
                    rfl

theorem cell21_576735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 5].length) (baseStart_576735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576735 prefixEnd_576735 := by exact prefixLift 576735
  have htrace : WordTrace (prefixWord ++ tailWord_576735) baseStart_576735 baseEnd_576735 := by
    simpa [prefixWord, tailWord_576735, baseEnd_576735] using wordTrace_append hprefix tailTrace_576735
  have hstable : (prefixWord ++ tailWord_576735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576735).length < 2 ^ (prefixWord ++ tailWord_576735).sum := by decide
  have hdescent : baseEnd_576735 < baseStart_576735 := by decide
  rcases family_descends (prefixWord ++ tailWord_576735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576780 : List Nat := [2, 2, 1, 2, 2, 3, 1, 8]
def baseStart_576780 : Nat := 118140960795 + 576780 * 2 ^ 59
def prefixEnd_576780 : Nat := 4983230072969 + 3 ^ 40 * 576780 * 2
def baseEnd_576780 : Nat := 43876351392645715451473

theorem tailTrace_576780 : CollatzResearch.WordTrace tailWord_576780 prefixEnd_576780 43876351392645715451473 := by
  unfold tailWord_576780
  simp only [CollatzResearch.WordTrace]
  refine ⟨10518447425216020513315897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14024596566954694017754529 10518447425216020513315897)
  ·
    refine ⟨7888835568912015384986923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10518447425216020513315897 7888835568912015384986923)
    ·
      refine ⟨11833253353368023077480385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7888835568912015384986923 11833253353368023077480385)
      ·
        refine ⟨8874940015026017308110289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11833253353368023077480385 8874940015026017308110289)
        ·
          refine ⟨6656205011269512981082717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8874940015026017308110289 6656205011269512981082717)
          ·
            refine ⟨2496076879226067367906019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6656205011269512981082717 2496076879226067367906019)
            ·
              refine ⟨3744115318839101051859029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2496076879226067367906019 3744115318839101051859029)
              ·
                refine ⟨43876351392645715451473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3744115318839101051859029 43876351392645715451473)
                ·
                  rfl

theorem cell21_576780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 8].length) (baseStart_576780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576780 prefixEnd_576780 := by exact prefixLift 576780
  have htrace : WordTrace (prefixWord ++ tailWord_576780) baseStart_576780 baseEnd_576780 := by
    simpa [prefixWord, tailWord_576780, baseEnd_576780] using wordTrace_append hprefix tailTrace_576780
  have hstable : (prefixWord ++ tailWord_576780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576780).length < 2 ^ (prefixWord ++ tailWord_576780).sum := by decide
  have hdescent : baseEnd_576780 < baseStart_576780 := by decide
  rcases family_descends (prefixWord ++ tailWord_576780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576797 : List Nat := [1, 4, 2, 3, 1, 1, 2, 7]
def baseStart_576797 : Nat := 118140960795 + 576797 * 2 ^ 59
def prefixEnd_576797 : Nat := 4983230072969 + 3 ^ 40 * 576797 * 2
def baseEnd_576797 : Nat := 43877644603182964857017

theorem tailTrace_576797 : CollatzResearch.WordTrace tailWord_576797 prefixEnd_576797 43877644603182964857017 := by
  unfold tailWord_576797
  simp only [CollatzResearch.WordTrace]
  refine ⟨21037514891370452930000645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14025009927580301953333763 21037514891370452930000645)
  ·
    refine ⟨3944534042131959924375121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21037514891370452930000645 3944534042131959924375121)
    ·
      refine ⟨2958400531598969943281341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3944534042131959924375121 2958400531598969943281341)
      ·
        refine ⟨1109400199349613728730503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2958400531598969943281341 1109400199349613728730503)
        ·
          refine ⟨1664100299024420593095755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109400199349613728730503 1664100299024420593095755)
          ·
            refine ⟨2496150448536630889643633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1664100299024420593095755 2496150448536630889643633)
            ·
              refine ⟨1872112836402473167232725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2496150448536630889643633 1872112836402473167232725)
              ·
                refine ⟨43877644603182964857017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1872112836402473167232725 43877644603182964857017)
                ·
                  rfl

theorem cell21_576797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 7].length) (baseStart_576797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576797 prefixEnd_576797 := by exact prefixLift 576797
  have htrace : WordTrace (prefixWord ++ tailWord_576797) baseStart_576797 baseEnd_576797 := by
    simpa [prefixWord, tailWord_576797, baseEnd_576797] using wordTrace_append hprefix tailTrace_576797
  have hstable : (prefixWord ++ tailWord_576797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576797).length < 2 ^ (prefixWord ++ tailWord_576797).sum := by decide
  have hdescent : baseEnd_576797 < baseStart_576797 := by decide
  rcases family_descends (prefixWord ++ tailWord_576797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576887 : List Nat := [1, 1, 3, 1, 1, 2, 6, 1, 5]
def baseStart_576887 : Nat := 118140960795 + 576887 * 2 ^ 59
def prefixEnd_576887 : Nat := 4983230072969 + 3 ^ 40 * 576887 * 2
def baseEnd_576887 : Nat := 131653473035728738070867

theorem tailTrace_576887 : CollatzResearch.WordTrace tailWord_576887 prefixEnd_576887 131653473035728738070867 := by
  unfold tailWord_576887
  simp only [CollatzResearch.WordTrace]
  refine ⟨21040797461044398300776915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14027198307362932200517943 21040797461044398300776915)
  ·
    refine ⟨31561196191566597451165373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21040797461044398300776915 31561196191566597451165373)
    ·
      refine ⟨11835448571837474044187015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31561196191566597451165373 11835448571837474044187015)
      ·
        refine ⟨17753172857756211066280523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11835448571837474044187015 17753172857756211066280523)
        ·
          refine ⟨26629759286634316599420785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17753172857756211066280523 26629759286634316599420785)
          ·
            refine ⟨19972319464975737449565589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26629759286634316599420785 19972319464975737449565589)
            ·
              refine ⟨936202474920737692948387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19972319464975737449565589 936202474920737692948387)
              ·
                refine ⟨1404303712381106539422581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 936202474920737692948387 1404303712381106539422581)
                ·
                  refine ⟨131653473035728738070867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1404303712381106539422581 131653473035728738070867)
                  ·
                    rfl

theorem cell21_576887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 5].length) (baseStart_576887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576887 prefixEnd_576887 := by exact prefixLift 576887
  have htrace : WordTrace (prefixWord ++ tailWord_576887) baseStart_576887 baseEnd_576887 := by
    simpa [prefixWord, tailWord_576887, baseEnd_576887] using wordTrace_append hprefix tailTrace_576887
  have hstable : (prefixWord ++ tailWord_576887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576887).length < 2 ^ (prefixWord ++ tailWord_576887).sum := by decide
  have hdescent : baseEnd_576887 < baseStart_576887 := by decide
  rcases family_descends (prefixWord ++ tailWord_576887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576921 : List Nat := [1, 2, 1, 2, 1, 7, 1, 3, 3]
def baseStart_576921 : Nat := 118140960795 + 576921 * 2 ^ 59
def prefixEnd_576921 : Nat := 4983230072969 + 3 ^ 40 * 576921 * 2
def baseEnd_576921 : Nat := 131661232298952234504131

theorem tailTrace_576921 : CollatzResearch.WordTrace tailWord_576921 prefixEnd_576921 131661232298952234504131 := by
  unfold tailWord_576921
  simp only [CollatzResearch.WordTrace]
  refine ⟨21042037542921222107514617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14028025028614148071676411 21042037542921222107514617)
  ·
    refine ⟨15781528157190916580635963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21042037542921222107514617 15781528157190916580635963)
    ·
      refine ⟨23672292235786374870953945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15781528157190916580635963 23672292235786374870953945)
      ·
        refine ⟨17754219176839781153215459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23672292235786374870953945 17754219176839781153215459)
        ·
          refine ⟨26631328765259671729823189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17754219176839781153215459 26631328765259671729823189)
          ·
            refine ⟨624171767935773556167731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 26631328765259671729823189 624171767935773556167731)
            ·
              refine ⟨936257651903660334251597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624171767935773556167731 936257651903660334251597)
              ·
                refine ⟨351096619463872625344349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 936257651903660334251597 351096619463872625344349)
                ·
                  refine ⟨131661232298952234504131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351096619463872625344349 131661232298952234504131)
                  ·
                    rfl

theorem cell21_576921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 3].length) (baseStart_576921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576921 prefixEnd_576921 := by exact prefixLift 576921
  have htrace : WordTrace (prefixWord ++ tailWord_576921) baseStart_576921 baseEnd_576921 := by
    simpa [prefixWord, tailWord_576921, baseEnd_576921] using wordTrace_append hprefix tailTrace_576921
  have hstable : (prefixWord ++ tailWord_576921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576921).length < 2 ^ (prefixWord ++ tailWord_576921).sum := by decide
  have hdescent : baseEnd_576921 < baseStart_576921 := by decide
  rcases family_descends (prefixWord ++ tailWord_576921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576949 : List Nat := [1, 3, 3, 2, 2, 2, 2, 6]
def baseStart_576949 : Nat := 118140960795 + 576949 * 2 ^ 59
def prefixEnd_576949 : Nat := 4983230072969 + 3 ^ 40 * 576949 * 2
def baseEnd_576949 : Nat := 43889207426810136012469

theorem tailTrace_576949 : CollatzResearch.WordTrace tailWord_576949 prefixEnd_576949 43889207426810136012469 := by
  unfold tailWord_576949
  simp only [CollatzResearch.WordTrace]
  refine ⟨21043058786819782889533901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14028705857879855259689267 21043058786819782889533901)
  ·
    refine ⟨7891147045057418583575213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21043058786819782889533901 7891147045057418583575213)
    ·
      refine ⟨2959180141896531968840705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7891147045057418583575213 2959180141896531968840705)
      ·
        refine ⟨2219385106422398976630529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2959180141896531968840705 2219385106422398976630529)
        ·
          refine ⟨1664538829816799232472897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2219385106422398976630529 1664538829816799232472897)
          ·
            refine ⟨1248404122362599424354673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1664538829816799232472897 1248404122362599424354673)
            ·
              refine ⟨936303091771949568266005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1248404122362599424354673 936303091771949568266005)
              ·
                refine ⟨43889207426810136012469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 936303091771949568266005 43889207426810136012469)
                ·
                  rfl

theorem cell21_576949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 6].length) (baseStart_576949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576949 prefixEnd_576949 := by exact prefixLift 576949
  have htrace : WordTrace (prefixWord ++ tailWord_576949) baseStart_576949 baseEnd_576949 := by
    simpa [prefixWord, tailWord_576949, baseEnd_576949] using wordTrace_append hprefix tailTrace_576949
  have hstable : (prefixWord ++ tailWord_576949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576949).length < 2 ^ (prefixWord ++ tailWord_576949).sum := by decide
  have hdescent : baseEnd_576949 < baseStart_576949 := by decide
  rcases family_descends (prefixWord ++ tailWord_576949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576997 : List Nat := [1, 3, 1, 5, 1, 2, 1, 4, 3]
def baseStart_576997 : Nat := 118140960795 + 576997 * 2 ^ 59
def prefixEnd_576997 : Nat := 4983230072969 + 3 ^ 40 * 576997 * 2
def baseEnd_576997 : Nat := 131678576534392991237309

theorem tailTrace_576997 : CollatzResearch.WordTrace tailWord_576997 prefixEnd_576997 131678576534392991237309 := by
  unfold tailWord_576997
  simp only [CollatzResearch.WordTrace]
  refine ⟨21044809490645887087281245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14029872993763924724854163 21044809490645887087281245)
  ·
    refine ⟨7891803558992207657730467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21044809490645887087281245 7891803558992207657730467)
    ·
      refine ⟨11837705338488311486595701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7891803558992207657730467 11837705338488311486595701)
      ·
        refine ⟨1109784875483279201868347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11837705338488311486595701 1109784875483279201868347)
        ·
          refine ⟨1664677313224918802802521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109784875483279201868347 1664677313224918802802521)
          ·
            refine ⟨1248507984918689102101891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1664677313224918802802521 1248507984918689102101891)
            ·
              refine ⟨1872761977378033653152837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1248507984918689102101891 1872761977378033653152837)
              ·
                refine ⟨351142870758381309966157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1872761977378033653152837 351142870758381309966157)
                ·
                  refine ⟨131678576534392991237309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351142870758381309966157 131678576534392991237309)
                  ·
                    rfl

theorem cell21_576997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_576997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_576997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_576997 prefixEnd_576997 := by exact prefixLift 576997
  have htrace : WordTrace (prefixWord ++ tailWord_576997) baseStart_576997 baseEnd_576997 := by
    simpa [prefixWord, tailWord_576997, baseEnd_576997] using wordTrace_append hprefix tailTrace_576997
  have hstable : (prefixWord ++ tailWord_576997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576997).length < 2 ^ (prefixWord ++ tailWord_576997).sum := by decide
  have hdescent : baseEnd_576997 < baseStart_576997 := by decide
  rcases family_descends (prefixWord ++ tailWord_576997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577008 : List Nat := [2, 1, 1, 1, 3, 4, 3, 6]
def baseStart_577008 : Nat := 118140960795 + 577008 * 2 ^ 59
def prefixEnd_577008 : Nat := 4983230072969 + 3 ^ 40 * 577008 * 2
def baseEnd_577008 : Nat := 43893695628086472184651

theorem tailTrace_577008 : CollatzResearch.WordTrace tailWord_577008 prefixEnd_577008 43893695628086472184651 := by
  unfold tailWord_577008
  simp only [CollatzResearch.WordTrace]
  refine ⟨10522605346803017982965839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14030140462404023977287785 10522605346803017982965839)
  ·
    refine ⟨15783908020204526974448759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10522605346803017982965839 15783908020204526974448759)
    ·
      refine ⟨23675862030306790461673139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15783908020204526974448759 23675862030306790461673139)
      ·
        refine ⟨35513793045460185692509709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23675862030306790461673139 35513793045460185692509709)
        ·
          refine ⟨13317672392047569634691141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35513793045460185692509709 13317672392047569634691141)
          ·
            refine ⟨2497063573508919306504589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13317672392047569634691141 2497063573508919306504589)
            ·
              refine ⟨936398840065844739939221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2497063573508919306504589 936398840065844739939221)
              ·
                refine ⟨43893695628086472184651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 936398840065844739939221 43893695628086472184651)
                ·
                  rfl

theorem cell21_577008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 6].length) (baseStart_577008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_577008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_577008 prefixEnd_577008 := by exact prefixLift 577008
  have htrace : WordTrace (prefixWord ++ tailWord_577008) baseStart_577008 baseEnd_577008 := by
    simpa [prefixWord, tailWord_577008, baseEnd_577008] using wordTrace_append hprefix tailTrace_577008
  have hstable : (prefixWord ++ tailWord_577008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577008).length < 2 ^ (prefixWord ++ tailWord_577008).sum := by decide
  have hdescent : baseEnd_577008 < baseStart_577008 := by decide
  rcases family_descends (prefixWord ++ tailWord_577008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577056 : List Nat := [2, 1, 1, 6, 1, 2, 2, 1, 5]
def baseStart_577056 : Nat := 118140960795 + 577056 * 2 ^ 59
def prefixEnd_577056 : Nat := 4983230072969 + 3 ^ 40 * 577056 * 2
def baseEnd_577056 : Nat := 131692041138221999753855

theorem tailTrace_577056 : CollatzResearch.WordTrace tailWord_577056 prefixEnd_577056 131692041138221999753855 := by
  unfold tailWord_577056
  simp only [CollatzResearch.WordTrace]
  refine ⟨10523480698716070081839511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14031307598288093442452681 10523480698716070081839511)
  ·
    refine ⟨15785221048074105122759267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10523480698716070081839511 15785221048074105122759267)
    ·
      refine ⟨23677831572111157684138901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15785221048074105122759267 23677831572111157684138901)
      ·
        refine ⟨1109898354942710516444011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23677831572111157684138901 1109898354942710516444011)
        ·
          refine ⟨1664847532414065774666017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109898354942710516444011 1664847532414065774666017)
          ·
            refine ⟨1248635649310549330999513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1664847532414065774666017 1248635649310549330999513)
            ·
              refine ⟨936476736982911998249635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1248635649310549330999513 936476736982911998249635)
              ·
                refine ⟨1404715105474367997374453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 936476736982911998249635 1404715105474367997374453)
                ·
                  refine ⟨131692041138221999753855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1404715105474367997374453 131692041138221999753855)
                  ·
                    rfl

theorem cell21_577056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 5].length) (baseStart_577056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_577056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_577056 prefixEnd_577056 := by exact prefixLift 577056
  have htrace : WordTrace (prefixWord ++ tailWord_577056) baseStart_577056 baseEnd_577056 := by
    simpa [prefixWord, tailWord_577056, baseEnd_577056] using wordTrace_append hprefix tailTrace_577056
  have hstable : (prefixWord ++ tailWord_577056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577056).length < 2 ^ (prefixWord ++ tailWord_577056).sum := by decide
  have hdescent : baseEnd_577056 < baseStart_577056 := by decide
  rcases family_descends (prefixWord ++ tailWord_577056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577160 : List Nat := [2, 1, 3, 5, 10]
def baseStart_577160 : Nat := 118140960795 + 577160 * 2 ^ 59
def prefixEnd_577160 : Nat := 4983230072969 + 3 ^ 40 * 577160 * 2
def baseEnd_577160 : Nat := 1626120683396801605189

theorem tailTrace_577160 : CollatzResearch.WordTrace tailWord_577160 prefixEnd_577160 1626120683396801605189 := by
  unfold tailWord_577160
  simp only [CollatzResearch.WordTrace]
  refine ⟨10525377294527682962732467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14033836392703577283643289 10525377294527682962732467)
  ·
    refine ⟨15788065941791524444098701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10525377294527682962732467 15788065941791524444098701)
    ·
      refine ⟨5920524728171821666537013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15788065941791524444098701 5920524728171821666537013)
      ·
        refine ⟨555049193266108281237845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5920524728171821666537013 555049193266108281237845)
        ·
          refine ⟨1626120683396801605189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 555049193266108281237845 1626120683396801605189)
          ·
            rfl

theorem cell21_577160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 10].length) (baseStart_577160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_577160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_577160 prefixEnd_577160 := by exact prefixLift 577160
  have htrace : WordTrace (prefixWord ++ tailWord_577160) baseStart_577160 baseEnd_577160 := by
    simpa [prefixWord, tailWord_577160, baseEnd_577160] using wordTrace_append hprefix tailTrace_577160
  have hstable : (prefixWord ++ tailWord_577160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577160).length < 2 ^ (prefixWord ++ tailWord_577160).sum := by decide
  have hdescent : baseEnd_577160 < baseStart_577160 := by decide
  rcases family_descends (prefixWord ++ tailWord_577160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577166 : List Nat := [4, 1, 1, 3, 1, 4, 2, 2, 3]
def baseStart_577166 : Nat := 118140960795 + 577166 * 2 ^ 59
def prefixEnd_577166 : Nat := 4983230072969 + 3 ^ 40 * 577166 * 2
def baseEnd_577166 : Nat := 131717144636886252920297

theorem tailTrace_577166 : CollatzResearch.WordTrace tailWord_577166 prefixEnd_577166 131717144636886252920297 := by
  unfold tailWord_577166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2631371678379203618772919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14033982284689085966788901 2631371678379203618772919)
  ·
    refine ⟨3947057517568805428159379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2631371678379203618772919 3947057517568805428159379)
    ·
      refine ⟨5920586276353208142239069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3947057517568805428159379 5920586276353208142239069)
      ·
        refine ⟨2220219853632453053339651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5920586276353208142239069 2220219853632453053339651)
        ·
          refine ⟨3330329780448679580009477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2220219853632453053339651 3330329780448679580009477)
          ·
            refine ⟨624436833834127421251777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3330329780448679580009477 624436833834127421251777)
            ·
              refine ⟨468327625375595565938833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 624436833834127421251777 468327625375595565938833)
              ·
                refine ⟨351245719031696674454125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 468327625375595565938833 351245719031696674454125)
                ·
                  refine ⟨131717144636886252920297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351245719031696674454125 131717144636886252920297)
                  ·
                    rfl

theorem cell21_577166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_577166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_577166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_577166 prefixEnd_577166 := by exact prefixLift 577166
  have htrace : WordTrace (prefixWord ++ tailWord_577166) baseStart_577166 baseEnd_577166 := by
    simpa [prefixWord, tailWord_577166, baseEnd_577166] using wordTrace_append hprefix tailTrace_577166
  have hstable : (prefixWord ++ tailWord_577166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577166).length < 2 ^ (prefixWord ++ tailWord_577166).sum := by decide
  have hdescent : baseEnd_577166 < baseStart_577166 := by decide
  rcases family_descends (prefixWord ++ tailWord_577166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577281 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 6]
def baseStart_577281 : Nat := 118140960795 + 577281 * 2 ^ 59
def prefixEnd_577281 : Nat := 4983230072969 + 3 ^ 40 * 577281 * 2
def baseEnd_577281 : Nat := 131743389203671608503395

theorem tailTrace_577281 : CollatzResearch.WordTrace tailWord_577281 prefixEnd_577281 131743389203671608503395 := by
  unfold tailWord_577281
  simp only [CollatzResearch.WordTrace]
  refine ⟨21055167821617003590619697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14036778547744669060413131 21055167821617003590619697)
  ·
    refine ⟨15791375866212752692964773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21055167821617003590619697 15791375866212752692964773)
    ·
      refine ⟨2960882974914891129930895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15791375866212752692964773 2960882974914891129930895)
      ·
        refine ⟨4441324462372336694896343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2960882974914891129930895 4441324462372336694896343)
        ·
          refine ⟨6661986693558505042344515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4441324462372336694896343 6661986693558505042344515)
          ·
            refine ⟨9992980040337757563516773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6661986693558505042344515 9992980040337757563516773)
            ·
              refine ⟨1873683757563329543159395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9992980040337757563516773 1873683757563329543159395)
              ·
                refine ⟨2810525636344994314739093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1873683757563329543159395 2810525636344994314739093)
                ·
                  refine ⟨131743389203671608503395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2810525636344994314739093 131743389203671608503395)
                  ·
                    rfl

theorem cell21_577281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_577281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_577281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_577281 prefixEnd_577281 := by exact prefixLift 577281
  have htrace : WordTrace (prefixWord ++ tailWord_577281) baseStart_577281 baseEnd_577281 := by
    simpa [prefixWord, tailWord_577281, baseEnd_577281] using wordTrace_append hprefix tailTrace_577281
  have hstable : (prefixWord ++ tailWord_577281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577281).length < 2 ^ (prefixWord ++ tailWord_577281).sum := by decide
  have hdescent : baseEnd_577281 < baseStart_577281 := by decide
  rcases family_descends (prefixWord ++ tailWord_577281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577284 : List Nat := [2, 3, 2, 2, 1, 4, 1, 1, 5]
def baseStart_577284 : Nat := 118140960795 + 577284 * 2 ^ 59
def prefixEnd_577284 : Nat := 4983230072969 + 3 ^ 40 * 577284 * 2
def baseEnd_577284 : Nat := 131744073844544269953389

theorem tailTrace_577284 : CollatzResearch.WordTrace tailWord_577284 prefixEnd_577284 131744073844544269953389 := by
  unfold tailWord_577284
  simp only [CollatzResearch.WordTrace]
  refine ⟨10527638620303067551489453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14036851493737423401985937 10527638620303067551489453)
  ·
    refine ⟨3947864482613650331808545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10527638620303067551489453 3947864482613650331808545)
    ·
      refine ⟨2960898361960237748856409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3947864482613650331808545 2960898361960237748856409)
      ·
        refine ⟨2220673771470178311642307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2960898361960237748856409 2220673771470178311642307)
        ·
          refine ⟨3331010657205267467463461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2220673771470178311642307 3331010657205267467463461)
          ·
            refine ⟨624564498225987650149399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3331010657205267467463461 624564498225987650149399)
            ·
              refine ⟨936846747338981475224099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624564498225987650149399 936846747338981475224099)
              ·
                refine ⟨1405270121008472212836149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 936846747338981475224099 1405270121008472212836149)
                ·
                  refine ⟨131744073844544269953389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1405270121008472212836149 131744073844544269953389)
                  ·
                    rfl

theorem cell21_577284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_577284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_577284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_577284 prefixEnd_577284 := by exact prefixLift 577284
  have htrace : WordTrace (prefixWord ++ tailWord_577284) baseStart_577284 baseEnd_577284 := by
    simpa [prefixWord, tailWord_577284, baseEnd_577284] using wordTrace_append hprefix tailTrace_577284
  have hstable : (prefixWord ++ tailWord_577284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577284).length < 2 ^ (prefixWord ++ tailWord_577284).sum := by decide
  have hdescent : baseEnd_577284 < baseStart_577284 := by decide
  rcases family_descends (prefixWord ++ tailWord_577284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577402 : List Nat := [3, 1, 1, 1, 1, 1, 5, 3, 5]
def baseStart_577402 : Nat := 118140960795 + 577402 * 2 ^ 59
def prefixEnd_577402 : Nat := 4983230072969 + 3 ^ 40 * 577402 * 2
def baseEnd_577402 : Nat := 131771003052202286986481

theorem tailTrace_577402 : CollatzResearch.WordTrace tailWord_577402 prefixEnd_577402 131771003052202286986481 := by
  unfold tailWord_577402
  simp only [CollatzResearch.WordTrace]
  refine ⟨5264895263544660313943615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14039720702785760837182973 5264895263544660313943615)
  ·
    refine ⟨7897342895316990470915423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5264895263544660313943615 7897342895316990470915423)
    ·
      refine ⟨11846014342975485706373135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7897342895316990470915423 11846014342975485706373135)
      ·
        refine ⟨17769021514463228559559703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11846014342975485706373135 17769021514463228559559703)
        ·
          refine ⟨26653532271694842839339555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17769021514463228559559703 26653532271694842839339555)
          ·
            refine ⟨39980298407542264259009333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26653532271694842839339555 39980298407542264259009333)
            ·
              refine ⟨3748152975707087274282125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39980298407542264259009333 3748152975707087274282125)
              ·
                refine ⟨1405557365890157727855797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3748152975707087274282125 1405557365890157727855797)
                ·
                  refine ⟨131771003052202286986481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1405557365890157727855797 131771003052202286986481)
                  ·
                    rfl

theorem cell21_577402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_577402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_577402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_577402 prefixEnd_577402 := by exact prefixLift 577402
  have htrace : WordTrace (prefixWord ++ tailWord_577402) baseStart_577402 baseEnd_577402 := by
    simpa [prefixWord, tailWord_577402, baseEnd_577402] using wordTrace_append hprefix tailTrace_577402
  have hstable : (prefixWord ++ tailWord_577402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577402).length < 2 ^ (prefixWord ++ tailWord_577402).sum := by decide
  have hdescent : baseEnd_577402 < baseStart_577402 := by decide
  rcases family_descends (prefixWord ++ tailWord_577402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577495 : List Nat := [1, 1, 3, 2, 1, 1, 4, 5, 3]
def baseStart_577495 : Nat := 118140960795 + 577495 * 2 ^ 59
def prefixEnd_577495 : Nat := 4983230072969 + 3 ^ 40 * 577495 * 2
def baseEnd_577495 : Nat := 131792226919254791936291

theorem tailTrace_577495 : CollatzResearch.WordTrace tailWord_577495 prefixEnd_577495 131792226919254791936291 := by
  unfold tailWord_577495
  simp only [CollatzResearch.WordTrace]
  refine ⟨21062973042841718138909939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14041982028561145425939959 21062973042841718138909939)
  ·
    refine ⟨31594459564262577208364909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21062973042841718138909939 31594459564262577208364909)
    ·
      refine ⟨11847922336598466453136841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31594459564262577208364909 11847922336598466453136841)
      ·
        refine ⟨8885941752448849839852631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11847922336598466453136841 8885941752448849839852631)
        ·
          refine ⟨13328912628673274759778947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8885941752448849839852631 13328912628673274759778947)
          ·
            refine ⟨19993368943009912139668421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13328912628673274759778947 19993368943009912139668421)
            ·
              refine ⟨3748756676814358526187829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19993368943009912139668421 3748756676814358526187829)
              ·
                refine ⟨351445938451346111830109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3748756676814358526187829 351445938451346111830109)
                ·
                  refine ⟨131792226919254791936291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351445938451346111830109 131792226919254791936291)
                  ·
                    rfl

theorem cell21_577495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 3].length) (baseStart_577495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_577495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_577495 prefixEnd_577495 := by exact prefixLift 577495
  have htrace : WordTrace (prefixWord ++ tailWord_577495) baseStart_577495 baseEnd_577495 := by
    simpa [prefixWord, tailWord_577495, baseEnd_577495] using wordTrace_append hprefix tailTrace_577495
  have hstable : (prefixWord ++ tailWord_577495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577495).length < 2 ^ (prefixWord ++ tailWord_577495).sum := by decide
  have hdescent : baseEnd_577495 < baseStart_577495 := by decide
  rcases family_descends (prefixWord ++ tailWord_577495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577571 : List Nat := [1, 1, 1, 4, 3, 1, 1, 6, 3]
def baseStart_577571 : Nat := 118140960795 + 577571 * 2 ^ 59
def prefixEnd_577571 : Nat := 4983230072969 + 3 ^ 40 * 577571 * 2
def baseEnd_577571 : Nat := 131809571154695548669469

theorem tailTrace_577571 : CollatzResearch.WordTrace tailWord_577571 prefixEnd_577571 131809571154695548669469 := by
  unfold tailWord_577571
  simp only [CollatzResearch.WordTrace]
  refine ⟨21065744990566383118676567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14043829993710922079117711 21065744990566383118676567)
  ·
    refine ⟨31598617485849574678014851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21065744990566383118676567 31598617485849574678014851)
    ·
      refine ⟨47397926228774362017022277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31598617485849574678014851 47397926228774362017022277)
      ·
        refine ⟨8887111167895192878191677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47397926228774362017022277 8887111167895192878191677)
        ·
          refine ⟨3332666687960697329321879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8887111167895192878191677 3332666687960697329321879)
          ·
            refine ⟨4999000031941045993982819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3332666687960697329321879 4999000031941045993982819)
            ·
              refine ⟨7498500047911568990974229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4999000031941045993982819 7498500047911568990974229)
              ·
                refine ⟨351492189745854796451917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7498500047911568990974229 351492189745854796451917)
                ·
                  refine ⟨131809571154695548669469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351492189745854796451917 131809571154695548669469)
                  ·
                    rfl

theorem cell21_577571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 3].length) (baseStart_577571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_577571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_577571 prefixEnd_577571 := by exact prefixLift 577571
  have htrace : WordTrace (prefixWord ++ tailWord_577571) baseStart_577571 baseEnd_577571 := by
    simpa [prefixWord, tailWord_577571, baseEnd_577571] using wordTrace_append hprefix tailTrace_577571
  have hstable : (prefixWord ++ tailWord_577571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577571).length < 2 ^ (prefixWord ++ tailWord_577571).sum := by decide
  have hdescent : baseEnd_577571 < baseStart_577571 := by decide
  rcases family_descends (prefixWord ++ tailWord_577571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577689 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 9]
def baseStart_577689 : Nat := 118140960795 + 577689 * 2 ^ 59
def prefixEnd_577689 : Nat := 4983230072969 + 3 ^ 40 * 577689 * 2
def baseEnd_577689 : Nat := 131836500362353565702561

theorem tailTrace_577689 : CollatzResearch.WordTrace tailWord_577689 prefixEnd_577689 131836500362353565702561 := by
  unfold tailWord_577689
  simp only [CollatzResearch.WordTrace]
  refine ⟨21070048804138889271472121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14046699202759259514314747 21070048804138889271472121)
  ·
    refine ⟨15802536603104166953604091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21070048804138889271472121 15802536603104166953604091)
    ·
      refine ⟨23703804904656250430406137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15802536603104166953604091 23703804904656250430406137)
      ·
        refine ⟨17777853678492187822804603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23703804904656250430406137 17777853678492187822804603)
        ·
          refine ⟨26666780517738281734206905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17777853678492187822804603 26666780517738281734206905)
          ·
            refine ⟨20000085388303711300655179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26666780517738281734206905 20000085388303711300655179)
            ·
              refine ⟨30000128082455566950982769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20000085388303711300655179 30000128082455566950982769)
              ·
                refine ⟨22500096061841675213237077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30000128082455566950982769 22500096061841675213237077)
                ·
                  refine ⟨131836500362353565702561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22500096061841675213237077 131836500362353565702561)
                  ·
                    rfl

theorem cell21_577689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_577689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_577689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_577689 prefixEnd_577689 := by exact prefixLift 577689
  have htrace : WordTrace (prefixWord ++ tailWord_577689) baseStart_577689 baseEnd_577689 := by
    simpa [prefixWord, tailWord_577689, baseEnd_577689] using wordTrace_append hprefix tailTrace_577689
  have hstable : (prefixWord ++ tailWord_577689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577689).length < 2 ^ (prefixWord ++ tailWord_577689).sum := by decide
  have hdescent : baseEnd_577689 < baseStart_577689 := by decide
  rcases family_descends (prefixWord ++ tailWord_577689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577709 : List Nat := [1, 5, 2, 1, 2, 2, 3, 5]
def baseStart_577709 : Nat := 118140960795 + 577709 * 2 ^ 59
def prefixEnd_577709 : Nat := 4983230072969 + 3 ^ 40 * 577709 * 2
def baseEnd_577709 : Nat := 43947021544945991789729

theorem tailTrace_577709 : CollatzResearch.WordTrace tailWord_577709 prefixEnd_577709 43947021544945991789729 := by
  unfold tailWord_577709
  simp only [CollatzResearch.WordTrace]
  refine ⟨21070778264066432687200181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14047185509377621791466787 21070778264066432687200181)
  ·
    refine ⟨1975385462256228064425017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21070778264066432687200181 1975385462256228064425017)
    ·
      refine ⟨1481539096692171048318763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1975385462256228064425017 1481539096692171048318763)
      ·
        refine ⟨2222308645038256572478145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1481539096692171048318763 2222308645038256572478145)
        ·
          refine ⟨1666731483778692429358609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2222308645038256572478145 1666731483778692429358609)
          ·
            refine ⟨1250048612834019322018957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1666731483778692429358609 1250048612834019322018957)
            ·
              refine ⟨468768229812757245757109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1250048612834019322018957 468768229812757245757109)
              ·
                refine ⟨43947021544945991789729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 468768229812757245757109 43947021544945991789729)
                ·
                  rfl

theorem cell21_577709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 5].length) (baseStart_577709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_577709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_577709 prefixEnd_577709 := by exact prefixLift 577709
  have htrace : WordTrace (prefixWord ++ tailWord_577709) baseStart_577709 baseEnd_577709 := by
    simpa [prefixWord, tailWord_577709, baseEnd_577709] using wordTrace_append hprefix tailTrace_577709
  have hstable : (prefixWord ++ tailWord_577709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577709).length < 2 ^ (prefixWord ++ tailWord_577709).sum := by decide
  have hdescent : baseEnd_577709 < baseStart_577709 := by decide
  rcases family_descends (prefixWord ++ tailWord_577709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577720 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 6]
def baseStart_577720 : Nat := 118140960795 + 577720 * 2 ^ 59
def prefixEnd_577720 : Nat := 4983230072969 + 3 ^ 40 * 577720 * 2
def baseEnd_577720 : Nat := 131843574984704400685831

theorem tailTrace_577720 : CollatzResearch.WordTrace tailWord_577720 prefixEnd_577720 131843574984704400685831 := by
  unfold tailWord_577720
  simp only [CollatzResearch.WordTrace]
  refine ⟨10535589733513290782925307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14047452978017721043900409 10535589733513290782925307)
  ·
    refine ⟨15803384600269936174387961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10535589733513290782925307 15803384600269936174387961)
    ·
      refine ⟨11852538450202452130790971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15803384600269936174387961 11852538450202452130790971)
      ·
        refine ⟨17778807675303678196186457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11852538450202452130790971 17778807675303678196186457)
        ·
          refine ⟨13334105756477758647139843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17778807675303678196186457 13334105756477758647139843)
          ·
            refine ⟨20001158634716637970709765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13334105756477758647139843 20001158634716637970709765)
            ·
              refine ⟨3750217244009369619508081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20001158634716637970709765 3750217244009369619508081)
              ·
                refine ⟨2812662933007027214631061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3750217244009369619508081 2812662933007027214631061)
                ·
                  refine ⟨131843574984704400685831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2812662933007027214631061 131843574984704400685831)
                  ·
                    rfl

theorem cell21_577720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_577720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_577720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_577720 prefixEnd_577720 := by exact prefixLift 577720
  have htrace : WordTrace (prefixWord ++ tailWord_577720) baseStart_577720 baseEnd_577720 := by
    simpa [prefixWord, tailWord_577720, baseEnd_577720] using wordTrace_append hprefix tailTrace_577720
  have hstable : (prefixWord ++ tailWord_577720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577720).length < 2 ^ (prefixWord ++ tailWord_577720).sum := by decide
  have hdescent : baseEnd_577720 < baseStart_577720 := by decide
  rcases family_descends (prefixWord ++ tailWord_577720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577723 : List Nat := [1, 1, 1, 1, 1, 2, 8, 3, 3]
def baseStart_577723 : Nat := 118140960795 + 577723 * 2 ^ 59
def prefixEnd_577723 : Nat := 4983230072969 + 3 ^ 40 * 577723 * 2
def baseEnd_577723 : Nat := 131844259625577062135825

theorem tailTrace_577723 : CollatzResearch.WordTrace tailWord_577723 prefixEnd_577723 131844259625577062135825 := by
  unfold tailWord_577723
  simp only [CollatzResearch.WordTrace]
  refine ⟨21071288886015713078209823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14047525924010475385473215 21071288886015713078209823)
  ·
    refine ⟨31606933329023569617314735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21071288886015713078209823 31606933329023569617314735)
    ·
      refine ⟨47410399993535354425972103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31606933329023569617314735 47410399993535354425972103)
      ·
        refine ⟨71115599990303031638958155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47410399993535354425972103 71115599990303031638958155)
        ·
          refine ⟨106673399985454547458437233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71115599990303031638958155 106673399985454547458437233)
          ·
            refine ⟨80005049989090910593827925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106673399985454547458437233 80005049989090910593827925)
            ·
              refine ⟨937559179559659108521421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 80005049989090910593827925 937559179559659108521421)
              ·
                refine ⟨351584692334872165695533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 937559179559659108521421 351584692334872165695533)
                ·
                  refine ⟨131844259625577062135825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351584692334872165695533 131844259625577062135825)
                  ·
                    rfl

theorem cell21_577723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 3].length) (baseStart_577723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_577723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_577723 prefixEnd_577723 := by exact prefixLift 577723
  have htrace : WordTrace (prefixWord ++ tailWord_577723) baseStart_577723 baseEnd_577723 := by
    simpa [prefixWord, tailWord_577723, baseEnd_577723] using wordTrace_append hprefix tailTrace_577723
  have hstable : (prefixWord ++ tailWord_577723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577723).length < 2 ^ (prefixWord ++ tailWord_577723).sum := by decide
  have hdescent : baseEnd_577723 < baseStart_577723 := by decide
  rcases family_descends (prefixWord ++ tailWord_577723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577740 : List Nat := [2, 2, 1, 6, 1, 1, 2, 1, 5]
def baseStart_577740 : Nat := 118140960795 + 577740 * 2 ^ 59
def prefixEnd_577740 : Nat := 4983230072969 + 3 ^ 40 * 577740 * 2
def baseEnd_577740 : Nat := 131848139257188810352457

theorem tailTrace_577740 : CollatzResearch.WordTrace tailWord_577740 prefixEnd_577740 131848139257188810352457 := by
  unfold tailWord_577740
  simp only [CollatzResearch.WordTrace]
  refine ⟨10535954463477062490789337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14047939284636083321052449 10535954463477062490789337)
  ·
    refine ⟨7901965847607796868092003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10535954463477062490789337 7901965847607796868092003)
    ·
      refine ⟨11852948771411695302138005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7901965847607796868092003 11852948771411695302138005)
      ·
        refine ⟨555606973659923217287719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11852948771411695302138005 555606973659923217287719)
        ·
          refine ⟨833410460489884825931579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555606973659923217287719 833410460489884825931579)
          ·
            refine ⟨1250115690734827238897369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833410460489884825931579 1250115690734827238897369)
            ·
              refine ⟨937586768051120429173027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1250115690734827238897369 937586768051120429173027)
              ·
                refine ⟨1406380152076680643759541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937586768051120429173027 1406380152076680643759541)
                ·
                  refine ⟨131848139257188810352457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1406380152076680643759541 131848139257188810352457)
                  ·
                    rfl

theorem cell21_577740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_577740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_577740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_577740 prefixEnd_577740 := by exact prefixLift 577740
  have htrace : WordTrace (prefixWord ++ tailWord_577740) baseStart_577740 baseEnd_577740 := by
    simpa [prefixWord, tailWord_577740, baseEnd_577740] using wordTrace_append hprefix tailTrace_577740
  have hstable : (prefixWord ++ tailWord_577740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577740).length < 2 ^ (prefixWord ++ tailWord_577740).sum := by decide
  have hdescent : baseEnd_577740 < baseStart_577740 := by decide
  rcases family_descends (prefixWord ++ tailWord_577740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577768 : List Nat := [2, 1, 4, 1, 2, 2, 4, 5]
def baseStart_577768 : Nat := 118140960795 + 577768 * 2 ^ 59
def prefixEnd_577768 : Nat := 4983230072969 + 3 ^ 40 * 577768 * 2
def baseEnd_577768 : Nat := 43951509746222327961911

theorem tailTrace_577768 : CollatzResearch.WordTrace tailWord_577768 prefixEnd_577768 43951509746222327961911 := by
  unfold tailWord_577768
  simp only [CollatzResearch.WordTrace]
  refine ⟨10536465085426342881798979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14048620113901790509065305 10536465085426342881798979)
  ·
    refine ⟨15804697628139514322698469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10536465085426342881798979 15804697628139514322698469)
    ·
      refine ⟨2963380805276158935505963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15804697628139514322698469 2963380805276158935505963)
      ·
        refine ⟨4445071207914238403258945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2963380805276158935505963 4445071207914238403258945)
        ·
          refine ⟨3333803405935678802444209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4445071207914238403258945 3333803405935678802444209)
          ·
            refine ⟨2500352554451759101833157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3333803405935678802444209 2500352554451759101833157)
            ·
              refine ⟨468816103959704831593717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2500352554451759101833157 468816103959704831593717)
              ·
                refine ⟨43951509746222327961911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 468816103959704831593717 43951509746222327961911)
                ·
                  rfl

theorem cell21_577768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 5].length) (baseStart_577768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_577768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_577768 prefixEnd_577768 := by exact prefixLift 577768
  have htrace : WordTrace (prefixWord ++ tailWord_577768) baseStart_577768 baseEnd_577768 := by
    simpa [prefixWord, tailWord_577768, baseEnd_577768] using wordTrace_append hprefix tailTrace_577768
  have hstable : (prefixWord ++ tailWord_577768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577768).length < 2 ^ (prefixWord ++ tailWord_577768).sum := by decide
  have hdescent : baseEnd_577768 < baseStart_577768 := by decide
  rcases family_descends (prefixWord ++ tailWord_577768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577782 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_577782 : Nat := 118140960795 + 577782 * 2 ^ 59
def prefixEnd_577782 : Nat := 4983230072969 + 3 ^ 40 * 577782 * 2
def baseEnd_577782 : Nat := 131857724229406070652371

theorem tailTrace_577782 : CollatzResearch.WordTrace tailWord_577782 prefixEnd_577782 131857724229406070652371 := by
  unfold tailWord_577782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1317090049550122884662975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14048960528534644103071733 1317090049550122884662975)
  ·
    refine ⟨1975635074325184326994463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1317090049550122884662975 1975635074325184326994463)
    ·
      refine ⟨2963452611487776490491695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1975635074325184326994463 2963452611487776490491695)
      ·
        refine ⟨4445178917231664735737543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2963452611487776490491695 4445178917231664735737543)
        ·
          refine ⟨6667768375847497103606315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4445178917231664735737543 6667768375847497103606315)
          ·
            refine ⟨10001652563771245655409473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6667768375847497103606315 10001652563771245655409473)
            ·
              refine ⟨7501239422828434241557105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10001652563771245655409473 7501239422828434241557105)
              ·
                refine ⟨5625929567121325681167829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7501239422828434241557105 5625929567121325681167829)
                ·
                  refine ⟨131857724229406070652371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5625929567121325681167829 131857724229406070652371)
                  ·
                    rfl

theorem cell21_577782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_577782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_577782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_577782 prefixEnd_577782 := by exact prefixLift 577782
  have htrace : WordTrace (prefixWord ++ tailWord_577782) baseStart_577782 baseEnd_577782 := by
    simpa [prefixWord, tailWord_577782, baseEnd_577782] using wordTrace_append hprefix tailTrace_577782
  have hstable : (prefixWord ++ tailWord_577782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577782).length < 2 ^ (prefixWord ++ tailWord_577782).sum := by decide
  have hdescent : baseEnd_577782 < baseStart_577782 := by decide
  rcases family_descends (prefixWord ++ tailWord_577782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577906 : List Nat := [3, 2, 1, 2, 1, 5, 1, 2, 4]
def baseStart_577906 : Nat := 118140960795 + 577906 * 2 ^ 59
def prefixEnd_577906 : Nat := 4983230072969 + 3 ^ 40 * 577906 * 2
def baseEnd_577906 : Nat := 131886022718809410585451

theorem tailTrace_577906 : CollatzResearch.WordTrace tailWord_577906 prefixEnd_577906 131886022718809410585451 := by
  unfold tailWord_577906
  simp only [CollatzResearch.WordTrace]
  refine ⟨5269490861088183833030393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14051975629568490221414381 5269490861088183833030393)
  ·
    refine ⟨3952118145816137874772795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5269490861088183833030393 3952118145816137874772795)
    ·
      refine ⟨5928177218724206812159193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3952118145816137874772795 5928177218724206812159193)
      ·
        refine ⟨4446132914043155109119395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5928177218724206812159193 4446132914043155109119395)
        ·
          refine ⟨6669199371064732663679093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4446132914043155109119395 6669199371064732663679093)
          ·
            refine ⟨625237441037318687219915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6669199371064732663679093 625237441037318687219915)
            ·
              refine ⟨937856161555978030829873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625237441037318687219915 937856161555978030829873)
              ·
                refine ⟨703392121166983523122405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 937856161555978030829873 703392121166983523122405)
                ·
                  refine ⟨131886022718809410585451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 703392121166983523122405 131886022718809410585451)
                  ·
                    rfl

theorem cell21_577906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_577906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_577906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_577906 prefixEnd_577906 := by exact prefixLift 577906
  have htrace : WordTrace (prefixWord ++ tailWord_577906) baseStart_577906 baseEnd_577906 := by
    simpa [prefixWord, tailWord_577906, baseEnd_577906] using wordTrace_append hprefix tailTrace_577906
  have hstable : (prefixWord ++ tailWord_577906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577906).length < 2 ^ (prefixWord ++ tailWord_577906).sum := by decide
  have hdescent : baseEnd_577906 < baseStart_577906 := by decide
  rcases family_descends (prefixWord ++ tailWord_577906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577982 : List Nat := [4, 2, 1, 1, 1, 1, 6, 1, 4]
def baseStart_577982 : Nat := 118140960795 + 577982 * 2 ^ 59
def prefixEnd_577982 : Nat := 4983230072969 + 3 ^ 40 * 577982 * 2
def baseEnd_577982 : Nat := 131903366954250167318629

theorem tailTrace_577982 : CollatzResearch.WordTrace tailWord_577982 prefixEnd_577982 131903366954250167318629 := by
  unfold tailWord_577982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2635091924009675038986025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14053823594718266874592133 2635091924009675038986025)
  ·
    refine ⟨1976318943007256279239519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2635091924009675038986025 1976318943007256279239519)
    ·
      refine ⟨2964478414510884418859279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1976318943007256279239519 2964478414510884418859279)
      ·
        refine ⟨4446717621766326628288919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2964478414510884418859279 4446717621766326628288919)
        ·
          refine ⟨6670076432649489942433379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4446717621766326628288919 6670076432649489942433379)
          ·
            refine ⟨10005114648974234913650069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6670076432649489942433379 10005114648974234913650069)
            ·
              refine ⟨468989749170667261577347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10005114648974234913650069 468989749170667261577347)
              ·
                refine ⟨703484623756000892366021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468989749170667261577347 703484623756000892366021)
                ·
                  refine ⟨131903366954250167318629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 703484623756000892366021 131903366954250167318629)
                  ·
                    rfl

theorem cell21_577982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_577982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_577982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_577982 prefixEnd_577982 := by exact prefixLift 577982
  have htrace : WordTrace (prefixWord ++ tailWord_577982) baseStart_577982 baseEnd_577982 := by
    simpa [prefixWord, tailWord_577982, baseEnd_577982] using wordTrace_append hprefix tailTrace_577982
  have hstable : (prefixWord ++ tailWord_577982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577982).length < 2 ^ (prefixWord ++ tailWord_577982).sum := by decide
  have hdescent : baseEnd_577982 < baseStart_577982 := by decide
  rcases family_descends (prefixWord ++ tailWord_577982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577993 : List Nat := [1, 2, 1, 1, 2, 1, 4, 4, 5]
def baseStart_577993 : Nat := 118140960795 + 577993 * 2 ^ 59
def prefixEnd_577993 : Nat := 4983230072969 + 3 ^ 40 * 577993 * 2
def baseEnd_577993 : Nat := 131905877304116592635273

theorem tailTrace_577993 : CollatzResearch.WordTrace tailWord_577993 prefixEnd_577993 131905877304116592635273 := by
  unfold tailWord_577993
  simp only [CollatzResearch.WordTrace]
  refine ⟨21081136595037549190538633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14054091063358366127025755 21081136595037549190538633)
  ·
    refine ⟨15810852446278161892903975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21081136595037549190538633 15810852446278161892903975)
    ·
      refine ⟨23716278669417242839355963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15810852446278161892903975 23716278669417242839355963)
      ·
        refine ⟨35574418004125864259033945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23716278669417242839355963 35574418004125864259033945)
        ·
          refine ⟨26680813503094398194275459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35574418004125864259033945 26680813503094398194275459)
          ·
            refine ⟨40021220254641597291413189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26680813503094398194275459 40021220254641597291413189)
            ·
              refine ⟨7503978797745299492139973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40021220254641597291413189 7503978797745299492139973)
              ·
                refine ⟨1406996024577243654776245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7503978797745299492139973 1406996024577243654776245)
                ·
                  refine ⟨131905877304116592635273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1406996024577243654776245 131905877304116592635273)
                  ·
                    rfl

theorem cell21_577993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_577993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_577993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_577993 prefixEnd_577993 := by exact prefixLift 577993
  have htrace : WordTrace (prefixWord ++ tailWord_577993) baseStart_577993 baseEnd_577993 := by
    simpa [prefixWord, tailWord_577993, baseEnd_577993] using wordTrace_append hprefix tailTrace_577993
  have hstable : (prefixWord ++ tailWord_577993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577993).length < 2 ^ (prefixWord ++ tailWord_577993).sum := by decide
  have hdescent : baseEnd_577993 < baseStart_577993 := by decide
  rcases family_descends (prefixWord ++ tailWord_577993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578061 : List Nat := [1, 7, 1, 1, 1, 1, 1, 5, 3]
def baseStart_578061 : Nat := 118140960795 + 578061 * 2 ^ 59
def prefixEnd_578061 : Nat := 4983230072969 + 3 ^ 40 * 578061 * 2
def baseEnd_578061 : Nat := 131921395830563585501801

theorem tailTrace_578061 : CollatzResearch.WordTrace tailWord_578061 prefixEnd_578061 131921395830563585501801 := by
  unfold tailWord_578061
  simp only [CollatzResearch.WordTrace]
  refine ⟨21083616758791196804014037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14055744505860797869342691 21083616758791196804014037)
  ·
    refine ⟨494147267784168675094079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 21083616758791196804014037 494147267784168675094079)
    ·
      refine ⟨741220901676253012641119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 494147267784168675094079 741220901676253012641119)
      ·
        refine ⟨1111831352514379518961679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741220901676253012641119 1111831352514379518961679)
        ·
          refine ⟨1667747028771569278442519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1111831352514379518961679 1667747028771569278442519)
          ·
            refine ⟨2501620543157353917663779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1667747028771569278442519 2501620543157353917663779)
            ·
              refine ⟨3752430814736030876495669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2501620543157353917663779 3752430814736030876495669)
              ·
                refine ⟨351790388881502894671469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3752430814736030876495669 351790388881502894671469)
                ·
                  refine ⟨131921395830563585501801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351790388881502894671469 131921395830563585501801)
                  ·
                    rfl

theorem cell21_578061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_578061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_578061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_578061 prefixEnd_578061 := by exact prefixLift 578061
  have htrace : WordTrace (prefixWord ++ tailWord_578061) baseStart_578061 baseEnd_578061 := by
    simpa [prefixWord, tailWord_578061, baseEnd_578061] using wordTrace_append hprefix tailTrace_578061
  have hstable : (prefixWord ++ tailWord_578061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578061).length < 2 ^ (prefixWord ++ tailWord_578061).sum := by decide
  have hdescent : baseEnd_578061 < baseStart_578061 := by decide
  rcases family_descends (prefixWord ++ tailWord_578061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578069 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 7]
def baseStart_578069 : Nat := 118140960795 + 578069 * 2 ^ 59
def prefixEnd_578069 : Nat := 4983230072969 + 3 ^ 40 * 578069 * 2
def baseEnd_578069 : Nat := 131923221539557349368451

theorem tailTrace_578069 : CollatzResearch.WordTrace tailWord_578069 prefixEnd_578069 131923221539557349368451 := by
  unfold tailWord_578069
  simp only [CollatzResearch.WordTrace]
  refine ⟨21083908542762214170305261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14055939028508142780203507 21083908542762214170305261)
  ·
    refine ⟨7906465703535830313864473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21083908542762214170305261 7906465703535830313864473)
    ·
      refine ⟨5929849277651872735398355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7906465703535830313864473 5929849277651872735398355)
      ·
        refine ⟨8894773916477809103097533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5929849277651872735398355 8894773916477809103097533)
        ·
          refine ⟨3335540218679178413661575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8894773916477809103097533 3335540218679178413661575)
          ·
            refine ⟨5003310328018767620492363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3335540218679178413661575 5003310328018767620492363)
            ·
              refine ⟨7504965492028151430738545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5003310328018767620492363 7504965492028151430738545)
              ·
                refine ⟨5628724119021113573053909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7504965492028151430738545 5628724119021113573053909)
                ·
                  refine ⟨131923221539557349368451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5628724119021113573053909 131923221539557349368451)
                  ·
                    rfl

theorem cell21_578069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_578069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_578069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_578069 prefixEnd_578069 := by exact prefixLift 578069
  have htrace : WordTrace (prefixWord ++ tailWord_578069) baseStart_578069 baseEnd_578069 := by
    simpa [prefixWord, tailWord_578069, baseEnd_578069] using wordTrace_append hprefix tailTrace_578069
  have hstable : (prefixWord ++ tailWord_578069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578069).length < 2 ^ (prefixWord ++ tailWord_578069).sum := by decide
  have hdescent : baseEnd_578069 < baseStart_578069 := by decide
  rcases family_descends (prefixWord ++ tailWord_578069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578196 : List Nat := [2, 4, 2, 2, 1, 2, 1, 4, 3]
def baseStart_578196 : Nat := 118140960795 + 578196 * 2 ^ 59
def prefixEnd_578196 : Nat := 4983230072969 + 3 ^ 40 * 578196 * 2
def baseEnd_578196 : Nat := 131952204669833350751525

theorem tailTrace_578196 : CollatzResearch.WordTrace tailWord_578196 prefixEnd_578196 131952204669833350751525 := by
  unfold tailWord_578196
  simp only [CollatzResearch.WordTrace]
  refine ⟨10544270306651057430089221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14059027075534743240118961 10544270306651057430089221)
  ·
    refine ⟨1977050682497073268141729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10544270306651057430089221 1977050682497073268141729)
    ·
      refine ⟨1482788011872804951106297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1977050682497073268141729 1482788011872804951106297)
      ·
        refine ⟨1112091008904603713329723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1482788011872804951106297 1112091008904603713329723)
        ·
          refine ⟨1668136513356905569994585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1112091008904603713329723 1668136513356905569994585)
          ·
            refine ⟨1251102385017679177495939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1668136513356905569994585 1251102385017679177495939)
            ·
              refine ⟨1876653577526518766243909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1251102385017679177495939 1876653577526518766243909)
              ·
                refine ⟨351872545786222268670733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1876653577526518766243909 351872545786222268670733)
                ·
                  refine ⟨131952204669833350751525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351872545786222268670733 131952204669833350751525)
                  ·
                    rfl

theorem cell21_578196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_578196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_578196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_578196 prefixEnd_578196 := by exact prefixLift 578196
  have htrace : WordTrace (prefixWord ++ tailWord_578196) baseStart_578196 baseEnd_578196 := by
    simpa [prefixWord, tailWord_578196, baseEnd_578196] using wordTrace_append hprefix tailTrace_578196
  have hstable : (prefixWord ++ tailWord_578196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578196).length < 2 ^ (prefixWord ++ tailWord_578196).sum := by decide
  have hdescent : baseEnd_578196 < baseStart_578196 := by decide
  rcases family_descends (prefixWord ++ tailWord_578196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578266 : List Nat := [3, 1, 1, 2, 2, 2, 2, 8]
def baseStart_578266 : Nat := 118140960795 + 578266 * 2 ^ 59
def prefixEnd_578266 : Nat := 4983230072969 + 3 ^ 40 * 578266 * 2
def baseEnd_578266 : Nat := 43989393207842928194905

theorem tailTrace_578266 : CollatzResearch.WordTrace tailWord_578266 prefixEnd_578266 43989393207842928194905 := by
  unfold tailWord_578266
  simp only [CollatzResearch.WordTrace]
  refine ⟨5272773430762129203806663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14060729148699011210151101 5272773430762129203806663)
  ·
    refine ⟨7909160146143193805709995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5272773430762129203806663 7909160146143193805709995)
    ·
      refine ⟨11863740219214790708564993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7909160146143193805709995 11863740219214790708564993)
      ·
        refine ⟨8897805164411093031423745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11863740219214790708564993 8897805164411093031423745)
        ·
          refine ⟨6673353873308319773567809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8897805164411093031423745 6673353873308319773567809)
          ·
            refine ⟨5005015404981239830175857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6673353873308319773567809 5005015404981239830175857)
            ·
              refine ⟨3753761553735929872631893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5005015404981239830175857 3753761553735929872631893)
              ·
                refine ⟨43989393207842928194905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3753761553735929872631893 43989393207842928194905)
                ·
                  rfl

theorem cell21_578266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_578266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_578266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_578266 prefixEnd_578266 := by exact prefixLift 578266
  have htrace : WordTrace (prefixWord ++ tailWord_578266) baseStart_578266 baseEnd_578266 := by
    simpa [prefixWord, tailWord_578266, baseEnd_578266] using wordTrace_append hprefix tailTrace_578266
  have hstable : (prefixWord ++ tailWord_578266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578266).length < 2 ^ (prefixWord ++ tailWord_578266).sum := by decide
  have hdescent : baseEnd_578266 < baseStart_578266 := by decide
  rcases family_descends (prefixWord ++ tailWord_578266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578365 : List Nat := [1, 4, 1, 4, 2, 2, 2, 2, 3]
def baseStart_578365 : Nat := 118140960795 + 578365 * 2 ^ 59
def prefixEnd_578365 : Nat := 4983230072969 + 3 ^ 40 * 578365 * 2
def baseEnd_578365 : Nat := 131990772772326612434513

theorem tailTrace_578365 : CollatzResearch.WordTrace tailWord_578365 prefixEnd_578365 131990772772326612434513 := by
  unfold tailWord_578365
  simp only [CollatzResearch.WordTrace]
  refine ⟨21094704549689856723080549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14063136366459904482053699 21094704549689856723080549)
  ·
    refine ⟨3955257103066848135577603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21094704549689856723080549 3955257103066848135577603)
    ·
      refine ⟨5932885654600272203366405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3955257103066848135577603 5932885654600272203366405)
      ·
        refine ⟨1112416060237551038131201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5932885654600272203366405 1112416060237551038131201)
        ·
          refine ⟨834312045178163278598401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1112416060237551038131201 834312045178163278598401)
          ·
            refine ⟨625734033883622458948801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 834312045178163278598401 625734033883622458948801)
            ·
              refine ⟨469300525412716844211601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 625734033883622458948801 469300525412716844211601)
              ·
                refine ⟨351975394059537633158701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469300525412716844211601 351975394059537633158701)
                ·
                  refine ⟨131990772772326612434513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351975394059537633158701 131990772772326612434513)
                  ·
                    rfl

theorem cell21_578365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_578365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_578365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_578365 prefixEnd_578365 := by exact prefixLift 578365
  have htrace : WordTrace (prefixWord ++ tailWord_578365) baseStart_578365 baseEnd_578365 := by
    simpa [prefixWord, tailWord_578365, baseEnd_578365] using wordTrace_append hprefix tailTrace_578365
  have hstable : (prefixWord ++ tailWord_578365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578365).length < 2 ^ (prefixWord ++ tailWord_578365).sum := by decide
  have hdescent : baseEnd_578365 < baseStart_578365 := by decide
  rcases family_descends (prefixWord ++ tailWord_578365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578407 : List Nat := [1, 1, 5, 1, 2, 3, 2, 3, 3]
def baseStart_578407 : Nat := 118140960795 + 578407 * 2 ^ 59
def prefixEnd_578407 : Nat := 4983230072969 + 3 ^ 40 * 578407 * 2
def baseEnd_578407 : Nat := 132000357744543872734427

theorem tailTrace_578407 : CollatzResearch.WordTrace tailWord_578407 prefixEnd_578407 132000357744543872734427 := by
  unfold tailWord_578407
  simp only [CollatzResearch.WordTrace]
  refine ⟨21096236415537697896109475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14064157610358465264072983 21096236415537697896109475)
  ·
    refine ⟨31644354623306546844164213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21096236415537697896109475 31644354623306546844164213)
    ·
      refine ⟨2966658245934988766640395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31644354623306546844164213 2966658245934988766640395)
      ·
        refine ⟨4449987368902483149960593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2966658245934988766640395 4449987368902483149960593)
        ·
          refine ⟨3337490526676862362470445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4449987368902483149960593 3337490526676862362470445)
          ·
            refine ⟨1251558947503823385926417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3337490526676862362470445 1251558947503823385926417)
            ·
              refine ⟨938669210627867539444813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1251558947503823385926417 938669210627867539444813)
              ·
                refine ⟨352000953985450327291805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 938669210627867539444813 352000953985450327291805)
                ·
                  refine ⟨132000357744543872734427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 352000953985450327291805 132000357744543872734427)
                  ·
                    rfl

theorem cell21_578407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 3].length) (baseStart_578407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_578407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_578407 prefixEnd_578407 := by exact prefixLift 578407
  have htrace : WordTrace (prefixWord ++ tailWord_578407) baseStart_578407 baseEnd_578407 := by
    simpa [prefixWord, tailWord_578407, baseEnd_578407] using wordTrace_append hprefix tailTrace_578407
  have hstable : (prefixWord ++ tailWord_578407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578407).length < 2 ^ (prefixWord ++ tailWord_578407).sum := by decide
  have hdescent : baseEnd_578407 < baseStart_578407 := by decide
  rcases family_descends (prefixWord ++ tailWord_578407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578421 : List Nat := [1, 3, 4, 1, 1, 2, 3, 2, 4]
def baseStart_578421 : Nat := 118140960795 + 578421 * 2 ^ 59
def prefixEnd_578421 : Nat := 4983230072969 + 3 ^ 40 * 578421 * 2
def baseEnd_578421 : Nat := 132003552735282959501065

theorem tailTrace_578421 : CollatzResearch.WordTrace tailWord_578421 prefixEnd_578421 132003552735282959501065 := by
  unfold tailWord_578421
  simp only [CollatzResearch.WordTrace]
  refine ⟨21096747037486978287119117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14064498024991318858079411 21096747037486978287119117)
  ·
    refine ⟨7911280139057616857669669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21096747037486978287119117 7911280139057616857669669)
    ·
      refine ⟨1483365026073303160813063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7911280139057616857669669 1483365026073303160813063)
      ·
        refine ⟨2225047539109954741219595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1483365026073303160813063 2225047539109954741219595)
        ·
          refine ⟨3337571308664932111829393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2225047539109954741219595 3337571308664932111829393)
          ·
            refine ⟨2503178481498699083872045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3337571308664932111829393 2503178481498699083872045)
            ·
              refine ⟨938691930562012156452017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2503178481498699083872045 938691930562012156452017)
              ·
                refine ⟨704018947921509117339013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 938691930562012156452017 704018947921509117339013)
                ·
                  refine ⟨132003552735282959501065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 704018947921509117339013 132003552735282959501065)
                  ·
                    rfl

theorem cell21_578421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_578421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_578421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_578421 prefixEnd_578421 := by exact prefixLift 578421
  have htrace : WordTrace (prefixWord ++ tailWord_578421) baseStart_578421 baseEnd_578421 := by
    simpa [prefixWord, tailWord_578421, baseEnd_578421] using wordTrace_append hprefix tailTrace_578421
  have hstable : (prefixWord ++ tailWord_578421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578421).length < 2 ^ (prefixWord ++ tailWord_578421).sum := by decide
  have hdescent : baseEnd_578421 < baseStart_578421 := by decide
  rcases family_descends (prefixWord ++ tailWord_578421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578486 : List Nat := [5, 1, 4, 1, 1, 1, 2, 6]
def baseStart_578486 : Nat := 118140960795 + 578486 * 2 ^ 59
def prefixEnd_578486 : Nat := 4983230072969 + 3 ^ 40 * 578486 * 2
def baseEnd_578486 : Nat := 44006128873619096972533

theorem tailTrace_578486 : CollatzResearch.WordTrace tailWord_578486 prefixEnd_578486 44006128873619096972533 := by
  unfold tailWord_578486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1318694861390718399264707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14066078521500996258823541 1318694861390718399264707)
  ·
    refine ⟨1978042292086077598897061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1318694861390718399264707 1978042292086077598897061)
    ·
      refine ⟨370882929766139549793199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1978042292086077598897061 370882929766139549793199)
      ·
        refine ⟨556324394649209324689799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370882929766139549793199 556324394649209324689799)
        ·
          refine ⟨834486591973813987034699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556324394649209324689799 834486591973813987034699)
          ·
            refine ⟨1251729887960720980552049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 834486591973813987034699 1251729887960720980552049)
            ·
              refine ⟨938797415970540735414037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1251729887960720980552049 938797415970540735414037)
              ·
                refine ⟨44006128873619096972533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 938797415970540735414037 44006128873619096972533)
                ·
                  rfl

theorem cell21_578486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_578486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_578486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_578486 prefixEnd_578486 := by exact prefixLift 578486
  have htrace : WordTrace (prefixWord ++ tailWord_578486) baseStart_578486 baseEnd_578486 := by
    simpa [prefixWord, tailWord_578486, baseEnd_578486] using wordTrace_append hprefix tailTrace_578486
  have hstable : (prefixWord ++ tailWord_578486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578486).length < 2 ^ (prefixWord ++ tailWord_578486).sum := by decide
  have hdescent : baseEnd_578486 < baseStart_578486 := by decide
  rcases family_descends (prefixWord ++ tailWord_578486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578556 : List Nat := [2, 2, 2, 1, 2, 3, 2, 3, 4]
def baseStart_578556 : Nat := 118140960795 + 578556 * 2 ^ 59
def prefixEnd_578556 : Nat := 4983230072969 + 3 ^ 40 * 578556 * 2
def baseEnd_578556 : Nat := 132034361574552724750789

theorem tailTrace_578556 : CollatzResearch.WordTrace tailWord_578556 prefixEnd_578556 132034361574552724750789 := by
  unfold tailWord_578556
  simp only [CollatzResearch.WordTrace]
  refine ⟨10550835445998948171641761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14067780594665264228855681 10550835445998948171641761)
  ·
    refine ⟨7913126584499211128731321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10550835445998948171641761 7913126584499211128731321)
    ·
      refine ⟨5934844938374408346548491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7913126584499211128731321 5934844938374408346548491)
      ·
        refine ⟨8902267407561612519822737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5934844938374408346548491 8902267407561612519822737)
        ·
          refine ⟨6676700555671209389867053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8902267407561612519822737 6676700555671209389867053)
          ·
            refine ⟨2503762708376703521200145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6676700555671209389867053 2503762708376703521200145)
            ·
              refine ⟨1877822031282527640900109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2503762708376703521200145 1877822031282527640900109)
              ·
                refine ⟨704183261730947865337541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1877822031282527640900109 704183261730947865337541)
                ·
                  refine ⟨132034361574552724750789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 704183261730947865337541 132034361574552724750789)
                  ·
                    rfl

theorem cell21_578556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_578556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_578556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_578556 prefixEnd_578556 := by exact prefixLift 578556
  have htrace : WordTrace (prefixWord ++ tailWord_578556) baseStart_578556 baseEnd_578556 := by
    simpa [prefixWord, tailWord_578556, baseEnd_578556] using wordTrace_append hprefix tailTrace_578556
  have hstable : (prefixWord ++ tailWord_578556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578556).length < 2 ^ (prefixWord ++ tailWord_578556).sum := by decide
  have hdescent : baseEnd_578556 < baseStart_578556 := by decide
  rcases family_descends (prefixWord ++ tailWord_578556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578666 : List Nat := [3, 1, 3, 2, 2, 3, 2, 1, 4]
def baseStart_578666 : Nat := 118140960795 + 578666 * 2 ^ 59
def prefixEnd_578666 : Nat := 4983230072969 + 3 ^ 40 * 578666 * 2
def baseEnd_578666 : Nat := 132059465073216977917231

theorem tailTrace_578666 : CollatzResearch.WordTrace tailWord_578666 prefixEnd_578666 132059465073216977917231 := by
  unfold tailWord_578666
  simp only [CollatzResearch.WordTrace]
  refine ⟨5276420730399846282446963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14070455281066256753191901 5276420730399846282446963)
  ·
    refine ⟨7914631095599769423670445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5276420730399846282446963 7914631095599769423670445)
    ·
      refine ⟨2967986660849913533876417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7914631095599769423670445 2967986660849913533876417)
      ·
        refine ⟨2225989995637435150407313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2967986660849913533876417 2225989995637435150407313)
        ·
          refine ⟨1669492496728076362805485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2225989995637435150407313 1669492496728076362805485)
          ·
            refine ⟨626059686273028636052057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1669492496728076362805485 626059686273028636052057)
            ·
              refine ⟨469544764704771477039043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 626059686273028636052057 469544764704771477039043)
              ·
                refine ⟨704317147057157215558565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469544764704771477039043 704317147057157215558565)
                ·
                  refine ⟨132059465073216977917231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 704317147057157215558565 132059465073216977917231)
                  ·
                    rfl

theorem cell21_578666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_578666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_578666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_578666 prefixEnd_578666 := by exact prefixLift 578666
  have htrace : WordTrace (prefixWord ++ tailWord_578666) baseStart_578666 baseEnd_578666 := by
    simpa [prefixWord, tailWord_578666, baseEnd_578666] using wordTrace_append hprefix tailTrace_578666
  have hstable : (prefixWord ++ tailWord_578666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578666).length < 2 ^ (prefixWord ++ tailWord_578666).sum := by decide
  have hdescent : baseEnd_578666 < baseStart_578666 := by decide
  rcases family_descends (prefixWord ++ tailWord_578666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578711 : List Nat := [1, 1, 3, 3, 3, 1, 4, 2, 3]
def baseStart_578711 : Nat := 118140960795 + 578711 * 2 ^ 59
def prefixEnd_578711 : Nat := 4983230072969 + 3 ^ 40 * 578711 * 2
def baseEnd_578711 : Nat := 132069734686306899667139

theorem tailTrace_578711 : CollatzResearch.WordTrace tailWord_578711 prefixEnd_578711 132069734686306899667139 := by
  unfold tailWord_578711
  simp only [CollatzResearch.WordTrace]
  refine ⟨21107324206436357815175987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14071549470957571876783991 21107324206436357815175987)
  ·
    refine ⟨31660986309654536722763981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21107324206436357815175987 31660986309654536722763981)
    ·
      refine ⟨11872869866120451271036493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31660986309654536722763981 11872869866120451271036493)
      ·
        refine ⟨4452326199795169226638685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11872869866120451271036493 4452326199795169226638685)
        ·
          refine ⟨1669622324923188459989507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4452326199795169226638685 1669622324923188459989507)
          ·
            refine ⟨2504433487384782689984261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669622324923188459989507 2504433487384782689984261)
            ·
              refine ⟨469581278884646754372049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2504433487384782689984261 469581278884646754372049)
              ·
                refine ⟨352185959163485065779037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 469581278884646754372049 352185959163485065779037)
                ·
                  refine ⟨132069734686306899667139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 352185959163485065779037 132069734686306899667139)
                  ·
                    rfl

theorem cell21_578711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 3].length) (baseStart_578711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_578711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_578711 prefixEnd_578711 := by exact prefixLift 578711
  have htrace : WordTrace (prefixWord ++ tailWord_578711) baseStart_578711 baseEnd_578711 := by
    simpa [prefixWord, tailWord_578711, baseEnd_578711] using wordTrace_append hprefix tailTrace_578711
  have hstable : (prefixWord ++ tailWord_578711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578711).length < 2 ^ (prefixWord ++ tailWord_578711).sum := by decide
  have hdescent : baseEnd_578711 < baseStart_578711 := by decide
  rcases family_descends (prefixWord ++ tailWord_578711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578736 : List Nat := [2, 1, 1, 1, 2, 1, 2, 6, 5]
def baseStart_578736 : Nat := 118140960795 + 578736 * 2 ^ 59
def prefixEnd_578736 : Nat := 4983230072969 + 3 ^ 40 * 578736 * 2
def baseEnd_578736 : Nat := 132075440026912411750421

theorem tailTrace_578736 : CollatzResearch.WordTrace tailWord_578736 prefixEnd_578736 132075440026912411750421 := by
  unfold tailWord_578736
  simp only [CollatzResearch.WordTrace]
  refine ⟨10554118015672893542418031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14072157354230524723224041 10554118015672893542418031)
  ·
    refine ⟨15831177023509340313627047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10554118015672893542418031 15831177023509340313627047)
    ·
      refine ⟨23746765535264010470440571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15831177023509340313627047 23746765535264010470440571)
      ·
        refine ⟨35620148302896015705660857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23746765535264010470440571 35620148302896015705660857)
        ·
          refine ⟨26715111227172011779245643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35620148302896015705660857 26715111227172011779245643)
          ·
            refine ⟨40072666840758017668868465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26715111227172011779245643 40072666840758017668868465)
            ·
              refine ⟨30054500130568513251651349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40072666840758017668868465 30054500130568513251651349)
              ·
                refine ⟨1408804693620399058671157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30054500130568513251651349 1408804693620399058671157)
                ·
                  refine ⟨132075440026912411750421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1408804693620399058671157 132075440026912411750421)
                  ·
                    rfl

theorem cell21_578736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_578736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_578736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_578736 prefixEnd_578736 := by exact prefixLift 578736
  have htrace : WordTrace (prefixWord ++ tailWord_578736) baseStart_578736 baseEnd_578736 := by
    simpa [prefixWord, tailWord_578736, baseEnd_578736] using wordTrace_append hprefix tailTrace_578736
  have hstable : (prefixWord ++ tailWord_578736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578736).length < 2 ^ (prefixWord ++ tailWord_578736).sum := by decide
  have hdescent : baseEnd_578736 < baseStart_578736 := by decide
  rcases family_descends (prefixWord ++ tailWord_578736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578767 : List Nat := [1, 1, 2, 1, 1, 3, 2, 6, 4]
def baseStart_578767 : Nat := 118140960795 + 578767 * 2 ^ 59
def prefixEnd_578767 : Nat := 4983230072969 + 3 ^ 40 * 578767 * 2
def baseEnd_578767 : Nat := 132082514649263246733691

theorem tailTrace_578767 : CollatzResearch.WordTrace tailWord_578767 prefixEnd_578767 132082514649263246733691 := by
  unfold tailWord_578767
  simp only [CollatzResearch.WordTrace]
  refine ⟨21109366694233479379214555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14072911129488986252809703 21109366694233479379214555)
  ·
    refine ⟨31664050041350219068821833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21109366694233479379214555 31664050041350219068821833)
    ·
      refine ⟨23748037531012664301616375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31664050041350219068821833 23748037531012664301616375)
      ·
        refine ⟨35622056296518996452424563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23748037531012664301616375 35622056296518996452424563)
        ·
          refine ⟨53433084444778494678636845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35622056296518996452424563 53433084444778494678636845)
          ·
            refine ⟨20037406666791935504488817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53433084444778494678636845 20037406666791935504488817)
            ·
              refine ⟨15028055000093951628366613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20037406666791935504488817 15028055000093951628366613)
              ·
                refine ⟨704440078129403982579685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15028055000093951628366613 704440078129403982579685)
                ·
                  refine ⟨132082514649263246733691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 704440078129403982579685 132082514649263246733691)
                  ·
                    rfl

theorem cell21_578767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 4].length) (baseStart_578767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_578767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_578767 prefixEnd_578767 := by exact prefixLift 578767
  have htrace : WordTrace (prefixWord ++ tailWord_578767) baseStart_578767 baseEnd_578767 := by
    simpa [prefixWord, tailWord_578767, baseEnd_578767] using wordTrace_append hprefix tailTrace_578767
  have hstable : (prefixWord ++ tailWord_578767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578767).length < 2 ^ (prefixWord ++ tailWord_578767).sum := by decide
  have hdescent : baseEnd_578767 < baseStart_578767 := by decide
  rcases family_descends (prefixWord ++ tailWord_578767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578770 : List Nat := [3, 2, 2, 2, 1, 1, 1, 6, 3]
def baseStart_578770 : Nat := 118140960795 + 578770 * 2 ^ 59
def prefixEnd_578770 : Nat := 4983230072969 + 3 ^ 40 * 578770 * 2
def baseEnd_578770 : Nat := 132083199290135908183685

theorem tailTrace_578770 : CollatzResearch.WordTrace tailWord_578770 prefixEnd_578770 132083199290135908183685 := by
  unfold tailWord_578770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5277369028305652722893441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14072984075481740594382509 5277369028305652722893441)
  ·
    refine ⟨3958026771229239542170081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5277369028305652722893441 3958026771229239542170081)
    ·
      refine ⟨2968520078421929656627561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3958026771229239542170081 2968520078421929656627561)
      ·
        refine ⟨2226390058816447242470671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2968520078421929656627561 2226390058816447242470671)
        ·
          refine ⟨3339585088224670863706007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2226390058816447242470671 3339585088224670863706007)
          ·
            refine ⟨5009377632337006295559011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3339585088224670863706007 5009377632337006295559011)
            ·
              refine ⟨7514066448505509443338517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5009377632337006295559011 7514066448505509443338517)
              ·
                refine ⟨352221864773695755156493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7514066448505509443338517 352221864773695755156493)
                ·
                  refine ⟨132083199290135908183685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 352221864773695755156493 132083199290135908183685)
                  ·
                    rfl

theorem cell21_578770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_578770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_578770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_578770 prefixEnd_578770 := by exact prefixLift 578770
  have htrace : WordTrace (prefixWord ++ tailWord_578770) baseStart_578770 baseEnd_578770 := by
    simpa [prefixWord, tailWord_578770, baseEnd_578770] using wordTrace_append hprefix tailTrace_578770
  have hstable : (prefixWord ++ tailWord_578770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578770).length < 2 ^ (prefixWord ++ tailWord_578770).sum := by decide
  have hdescent : baseEnd_578770 < baseStart_578770 := by decide
  rcases family_descends (prefixWord ++ tailWord_578770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578888 : List Nat := [2, 1, 3, 1, 1, 2, 1, 5, 5]
def baseStart_578888 : Nat := 118140960795 + 578888 * 2 ^ 59
def prefixEnd_578888 : Nat := 4983230072969 + 3 ^ 40 * 578888 * 2
def baseEnd_578888 : Nat := 132110128497793925216777

theorem tailTrace_578888 : CollatzResearch.WordTrace tailWord_578888 prefixEnd_578888 132110128497793925216777 := by
  unfold tailWord_578888
  simp only [CollatzResearch.WordTrace]
  refine ⟨10556889963397558522184659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14075853284530078029579545 10556889963397558522184659)
  ·
    refine ⟨15835334945096337783276989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10556889963397558522184659 15835334945096337783276989)
    ·
      refine ⟨5938250604411126668728871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15835334945096337783276989 5938250604411126668728871)
      ·
        refine ⟨8907375906616690003093307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5938250604411126668728871 8907375906616690003093307)
        ·
          refine ⟨13361063859925035004639961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8907375906616690003093307 13361063859925035004639961)
          ·
            refine ⟨10020797894943776253479971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13361063859925035004639961 10020797894943776253479971)
            ·
              refine ⟨15031196842415664380219957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10020797894943776253479971 15031196842415664380219957)
              ·
                refine ⟨1409174703976468535645621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15031196842415664380219957 1409174703976468535645621)
                ·
                  refine ⟨132110128497793925216777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1409174703976468535645621 132110128497793925216777)
                  ·
                    rfl

theorem cell21_578888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_578888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_578888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_578888 prefixEnd_578888 := by exact prefixLift 578888
  have htrace : WordTrace (prefixWord ++ tailWord_578888) baseStart_578888 baseEnd_578888 := by
    simpa [prefixWord, tailWord_578888, baseEnd_578888] using wordTrace_append hprefix tailTrace_578888
  have hstable : (prefixWord ++ tailWord_578888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578888).length < 2 ^ (prefixWord ++ tailWord_578888).sum := by decide
  have hdescent : baseEnd_578888 < baseStart_578888 := by decide
  rcases family_descends (prefixWord ++ tailWord_578888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578953 : List Nat := [1, 2, 1, 1, 7, 1, 3, 1, 4]
def baseStart_578953 : Nat := 118140960795 + 578953 * 2 ^ 59
def prefixEnd_578953 : Nat := 4983230072969 + 3 ^ 40 * 578953 * 2
def baseEnd_578953 : Nat := 132124962383368256633311

theorem tailTrace_578953 : CollatzResearch.WordTrace tailWord_578953 prefixEnd_578953 132124962383368256633311 := by
  unfold tailWord_578953
  simp only [CollatzResearch.WordTrace]
  refine ⟨21116150671559633145485513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14077433781039755430323675 21116150671559633145485513)
  ·
    refine ⟨15837113003669724859114135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21116150671559633145485513 15837113003669724859114135)
    ·
      refine ⟨23755669505504587288671203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15837113003669724859114135 23755669505504587288671203)
      ·
        refine ⟨35633504258256880933006805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23755669505504587288671203 35633504258256880933006805)
        ·
          refine ⟨835160256052895646867347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 35633504258256880933006805 835160256052895646867347)
          ·
            refine ⟨1252740384079343470301021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 835160256052895646867347 1252740384079343470301021)
            ·
              refine ⟨469777644029753801362883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1252740384079343470301021 469777644029753801362883)
              ·
                refine ⟨704666466044630702044325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469777644029753801362883 704666466044630702044325)
                ·
                  refine ⟨132124962383368256633311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 704666466044630702044325 132124962383368256633311)
                  ·
                    rfl

theorem cell21_578953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 4].length) (baseStart_578953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_578953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_578953 prefixEnd_578953 := by exact prefixLift 578953
  have htrace : WordTrace (prefixWord ++ tailWord_578953) baseStart_578953 baseEnd_578953 := by
    simpa [prefixWord, tailWord_578953, baseEnd_578953] using wordTrace_append hprefix tailTrace_578953
  have hstable : (prefixWord ++ tailWord_578953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578953).length < 2 ^ (prefixWord ++ tailWord_578953).sum := by decide
  have hdescent : baseEnd_578953 < baseStart_578953 := by decide
  rcases family_descends (prefixWord ++ tailWord_578953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578981 : List Nat := [1, 3, 1, 2, 1, 1, 2, 7, 3]
def baseStart_578981 : Nat := 118140960795 + 578981 * 2 ^ 59
def prefixEnd_578981 : Nat := 4983230072969 + 3 ^ 40 * 578981 * 2
def baseEnd_578981 : Nat := 132131352364846430166587

theorem tailTrace_578981 : CollatzResearch.WordTrace tailWord_578981 prefixEnd_578981 132131352364846430166587 := by
  unfold tailWord_578981
  simp only [CollatzResearch.WordTrace]
  refine ⟨21117171915458193927504797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14078114610305462618336531 21117171915458193927504797)
  ·
    refine ⟨7918939468296822722814299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21117171915458193927504797 7918939468296822722814299)
    ·
      refine ⟨11878409202445234084221449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7918939468296822722814299 11878409202445234084221449)
      ·
        refine ⟨8908806901833925563166087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11878409202445234084221449 8908806901833925563166087)
        ·
          refine ⟨13363210352750888344749131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8908806901833925563166087 13363210352750888344749131)
          ·
            refine ⟨20044815529126332517123697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13363210352750888344749131 20044815529126332517123697)
            ·
              refine ⟨15033611646844749387842773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20044815529126332517123697 15033611646844749387842773)
              ·
                refine ⟨352350272972923813777565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15033611646844749387842773 352350272972923813777565)
                ·
                  refine ⟨132131352364846430166587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 352350272972923813777565 132131352364846430166587)
                  ·
                    rfl

theorem cell21_578981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_578981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_578981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_578981 prefixEnd_578981 := by exact prefixLift 578981
  have htrace : WordTrace (prefixWord ++ tailWord_578981) baseStart_578981 baseEnd_578981 := by
    simpa [prefixWord, tailWord_578981, baseEnd_578981] using wordTrace_append hprefix tailTrace_578981
  have hstable : (prefixWord ++ tailWord_578981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578981).length < 2 ^ (prefixWord ++ tailWord_578981).sum := by decide
  have hdescent : baseEnd_578981 < baseStart_578981 := by decide
  rcases family_descends (prefixWord ++ tailWord_578981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578984 : List Nat := [2, 1, 6, 1, 3, 1, 7]
def baseStart_578984 : Nat := 118140960795 + 578984 * 2 ^ 59
def prefixEnd_578984 : Nat := 4983230072969 + 3 ^ 40 * 578984 * 2
def baseEnd_578984 : Nat := 14681337445079899068509

theorem tailTrace_578984 : CollatzResearch.WordTrace tailWord_578984 prefixEnd_578984 14681337445079899068509 := by
  unfold tailWord_578984
  simp only [CollatzResearch.WordTrace]
  refine ⟨10558640667223662719932003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14078187556298216959909337 10558640667223662719932003)
  ·
    refine ⟨15837961000835494079898005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10558640667223662719932003 15837961000835494079898005)
    ·
      refine ⟨742404421914163784995219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15837961000835494079898005 742404421914163784995219)
      ·
        refine ⟨1113606632871245677492829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 742404421914163784995219 1113606632871245677492829)
        ·
          refine ⟨417602487326717129059811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1113606632871245677492829 417602487326717129059811)
          ·
            refine ⟨626403730990075693589717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417602487326717129059811 626403730990075693589717)
            ·
              refine ⟨14681337445079899068509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 626403730990075693589717 14681337445079899068509)
              ·
                rfl

theorem cell21_578984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 7].length) (baseStart_578984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_578984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_578984 prefixEnd_578984 := by exact prefixLift 578984
  have htrace : WordTrace (prefixWord ++ tailWord_578984) baseStart_578984 baseEnd_578984 := by
    simpa [prefixWord, tailWord_578984, baseEnd_578984] using wordTrace_append hprefix tailTrace_578984
  have hstable : (prefixWord ++ tailWord_578984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578984).length < 2 ^ (prefixWord ++ tailWord_578984).sum := by decide
  have hdescent : baseEnd_578984 < baseStart_578984 := by decide
  rcases family_descends (prefixWord ++ tailWord_578984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579074 : List Nat := [3, 4, 1, 2, 1, 2, 1, 2, 5]
def baseStart_579074 : Nat := 118140960795 + 579074 * 2 ^ 59
def prefixEnd_579074 : Nat := 4983230072969 + 3 ^ 40 * 579074 * 2
def baseEnd_579074 : Nat := 132152576231898935116397

theorem tailTrace_579074 : CollatzResearch.WordTrace tailWord_579074 prefixEnd_579074 132152576231898935116397 := by
  unfold tailWord_579074
  simp only [CollatzResearch.WordTrace]
  refine ⟨5280140976030317702660069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14080375936080847207093517 5280140976030317702660069)
  ·
    refine ⟨990026433005684569248763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5280140976030317702660069 990026433005684569248763)
    ·
      refine ⟨1485039649508526853873145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 990026433005684569248763 1485039649508526853873145)
      ·
        refine ⟨1113779737131395140404859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1485039649508526853873145 1113779737131395140404859)
        ·
          refine ⟨1670669605697092710607289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1113779737131395140404859 1670669605697092710607289)
          ·
            refine ⟨1253002204272819532955467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1670669605697092710607289 1253002204272819532955467)
            ·
              refine ⟨1879503306409229299433201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1253002204272819532955467 1879503306409229299433201)
              ·
                refine ⟨1409627479806921974574901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1879503306409229299433201 1409627479806921974574901)
                ·
                  refine ⟨132152576231898935116397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1409627479806921974574901 132152576231898935116397)
                  ·
                    rfl

theorem cell21_579074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_579074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579074 prefixEnd_579074 := by exact prefixLift 579074
  have htrace : WordTrace (prefixWord ++ tailWord_579074) baseStart_579074 baseEnd_579074 := by
    simpa [prefixWord, tailWord_579074, baseEnd_579074] using wordTrace_append hprefix tailTrace_579074
  have hstable : (prefixWord ++ tailWord_579074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579074).length < 2 ^ (prefixWord ++ tailWord_579074).sum := by decide
  have hdescent : baseEnd_579074 < baseStart_579074 := by decide
  rcases family_descends (prefixWord ++ tailWord_579074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579178 : List Nat := [3, 1, 3, 2, 1, 3, 2, 6]
def baseStart_579178 : Nat := 118140960795 + 579178 * 2 ^ 59
def prefixEnd_579178 : Nat := 4983230072969 + 3 ^ 40 * 579178 * 2
def baseEnd_579178 : Nat := 44058770149605955127617

theorem tailTrace_579178 : CollatzResearch.WordTrace tailWord_579178 prefixEnd_579178 44058770149605955127617 := by
  unfold tailWord_579178
  simp only [CollatzResearch.WordTrace]
  refine ⟨5281089273936124143106547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14082904730496331048284125 5281089273936124143106547)
  ·
    refine ⟨7921633910904186214659821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5281089273936124143106547 7921633910904186214659821)
    ·
      refine ⟨2970612716589069830497433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7921633910904186214659821 2970612716589069830497433)
      ·
        refine ⟨2227959537441802372873075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2970612716589069830497433 2227959537441802372873075)
        ·
          refine ⟨3341939306162703559309613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2227959537441802372873075 3341939306162703559309613)
          ·
            refine ⟨1253227239811013834741105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3341939306162703559309613 1253227239811013834741105)
            ·
              refine ⟨939920429858260376055829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1253227239811013834741105 939920429858260376055829)
              ·
                refine ⟨44058770149605955127617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 939920429858260376055829 44058770149605955127617)
                ·
                  rfl

theorem cell21_579178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_579178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579178 prefixEnd_579178 := by exact prefixLift 579178
  have htrace : WordTrace (prefixWord ++ tailWord_579178) baseStart_579178 baseEnd_579178 := by
    simpa [prefixWord, tailWord_579178, baseEnd_579178] using wordTrace_append hprefix tailTrace_579178
  have hstable : (prefixWord ++ tailWord_579178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579178).length < 2 ^ (prefixWord ++ tailWord_579178).sum := by decide
  have hdescent : baseEnd_579178 < baseStart_579178 := by decide
  rcases family_descends (prefixWord ++ tailWord_579178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579223 : List Nat := [1, 1, 3, 3, 2, 2, 1, 4, 4]
def baseStart_579223 : Nat := 118140960795 + 579223 * 2 ^ 59
def prefixEnd_579223 : Nat := 4983230072969 + 3 ^ 40 * 579223 * 2
def baseEnd_579223 : Nat := 132186580061907787132759

theorem tailTrace_579223 : CollatzResearch.WordTrace tailWord_579223 prefixEnd_579223 132186580061907787132759 := by
  unfold tailWord_579223
  simp only [CollatzResearch.WordTrace]
  refine ⟨21125998380581469257814323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14083998920387646171876215 21125998380581469257814323)
  ·
    refine ⟨31688997570872203886721485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21125998380581469257814323 31688997570872203886721485)
    ·
      refine ⟨11883374089077076457520557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31688997570872203886721485 11883374089077076457520557)
      ·
        refine ⟨4456265283403903671570209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11883374089077076457520557 4456265283403903671570209)
        ·
          refine ⟨3342198962552927753677657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4456265283403903671570209 3342198962552927753677657)
          ·
            refine ⟨2506649221914695815258243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3342198962552927753677657 2506649221914695815258243)
            ·
              refine ⟨3759973832872043722887365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2506649221914695815258243 3759973832872043722887365)
              ·
                refine ⟨704995093663508198041381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3759973832872043722887365 704995093663508198041381)
                ·
                  refine ⟨132186580061907787132759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 704995093663508198041381 132186580061907787132759)
                  ·
                    rfl

theorem cell21_579223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 4].length) (baseStart_579223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579223 prefixEnd_579223 := by exact prefixLift 579223
  have htrace : WordTrace (prefixWord ++ tailWord_579223) baseStart_579223 baseEnd_579223 := by
    simpa [prefixWord, tailWord_579223, baseEnd_579223] using wordTrace_append hprefix tailTrace_579223
  have hstable : (prefixWord ++ tailWord_579223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579223).length < 2 ^ (prefixWord ++ tailWord_579223).sum := by decide
  have hdescent : baseEnd_579223 < baseStart_579223 := by decide
  rcases family_descends (prefixWord ++ tailWord_579223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579237 : List Nat := [1, 3, 1, 2, 1, 2, 5, 6]
def baseStart_579237 : Nat := 118140960795 + 579237 * 2 ^ 59
def prefixEnd_579237 : Nat := 4983230072969 + 3 ^ 40 * 579237 * 2
def baseEnd_579237 : Nat := 44063258350882291299799

theorem tailTrace_579237 : CollatzResearch.WordTrace tailWord_579237 prefixEnd_579237 44063258350882291299799 := by
  unfold tailWord_579237
  simp only [CollatzResearch.WordTrace]
  refine ⟨21126509002530749648823965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14084339335020499765882643 21126509002530749648823965)
  ·
    refine ⟨7922440875949031118308987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21126509002530749648823965 7922440875949031118308987)
    ·
      refine ⟨11883661313923546677463481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7922440875949031118308987 11883661313923546677463481)
      ·
        refine ⟨8912745985442660008097611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11883661313923546677463481 8912745985442660008097611)
        ·
          refine ⟨13369118978163990012146417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8912745985442660008097611 13369118978163990012146417)
          ·
            refine ⟨10026839233622992509109813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13369118978163990012146417 10026839233622992509109813)
            ·
              refine ⟨940016178152155547729045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10026839233622992509109813 940016178152155547729045)
              ·
                refine ⟨44063258350882291299799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 940016178152155547729045 44063258350882291299799)
                ·
                  rfl

theorem cell21_579237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 6].length) (baseStart_579237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579237 prefixEnd_579237 := by exact prefixLift 579237
  have htrace : WordTrace (prefixWord ++ tailWord_579237) baseStart_579237 baseEnd_579237 := by
    simpa [prefixWord, tailWord_579237, baseEnd_579237] using wordTrace_append hprefix tailTrace_579237
  have hstable : (prefixWord ++ tailWord_579237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579237).length < 2 ^ (prefixWord ++ tailWord_579237).sum := by decide
  have hdescent : baseEnd_579237 < baseStart_579237 := by decide
  rcases family_descends (prefixWord ++ tailWord_579237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579268 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 7]
def baseStart_579268 : Nat := 118140960795 + 579268 * 2 ^ 59
def prefixEnd_579268 : Nat := 4983230072969 + 3 ^ 40 * 579268 * 2
def baseEnd_579268 : Nat := 132196849674997708882667

theorem tailTrace_579268 : CollatzResearch.WordTrace tailWord_579268 prefixEnd_579268 132196849674997708882667 := by
  unfold tailWord_579268
  simp only [CollatzResearch.WordTrace]
  refine ⟨10563819832709220971601229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14085093110278961295468305 10563819832709220971601229)
  ·
    refine ⟨3961432437265957864350461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10563819832709220971601229 3961432437265957864350461)
    ·
      refine ⟨1485537163974734199131423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3961432437265957864350461 1485537163974734199131423)
      ·
        refine ⟨2228305745962101298697135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1485537163974734199131423 2228305745962101298697135)
        ·
          refine ⟨3342458618943151948045703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2228305745962101298697135 3342458618943151948045703)
          ·
            refine ⟨5013687928414727922068555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3342458618943151948045703 5013687928414727922068555)
            ·
              refine ⟨7520531892622091883102833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5013687928414727922068555 7520531892622091883102833)
              ·
                refine ⟨5640398919466568912327125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7520531892622091883102833 5640398919466568912327125)
                ·
                  refine ⟨132196849674997708882667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5640398919466568912327125 132196849674997708882667)
                  ·
                    rfl

theorem cell21_579268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_579268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579268 prefixEnd_579268 := by exact prefixLift 579268
  have htrace : WordTrace (prefixWord ++ tailWord_579268) baseStart_579268 baseEnd_579268 := by
    simpa [prefixWord, tailWord_579268, baseEnd_579268] using wordTrace_append hprefix tailTrace_579268
  have hstable : (prefixWord ++ tailWord_579268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579268).length < 2 ^ (prefixWord ++ tailWord_579268).sum := by decide
  have hdescent : baseEnd_579268 < baseStart_579268 := by decide
  rcases family_descends (prefixWord ++ tailWord_579268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579313 : List Nat := [1, 2, 2, 2, 2, 4, 1, 7]
def baseStart_579313 : Nat := 118140960795 + 579313 * 2 ^ 59
def prefixEnd_579313 : Nat := 4983230072969 + 3 ^ 40 * 579313 * 2
def baseEnd_579313 : Nat := 44069039762695876877525

theorem tailTrace_579313 : CollatzResearch.WordTrace tailWord_579313 prefixEnd_579313 44069039762695876877525 := by
  unfold tailWord_579313
  simp only [CollatzResearch.WordTrace]
  refine ⟨21129280950255414628590593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14086187300170276419060395 21129280950255414628590593)
  ·
    refine ⟨15846960712691560971442945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21129280950255414628590593 15846960712691560971442945)
    ·
      refine ⟨11885220534518670728582209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15846960712691560971442945 11885220534518670728582209)
      ·
        refine ⟨8913915400889003046436657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11885220534518670728582209 8913915400889003046436657)
        ·
          refine ⟨6685436550666752284827493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8913915400889003046436657 6685436550666752284827493)
          ·
            refine ⟨1253519353250016053405155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6685436550666752284827493 1253519353250016053405155)
            ·
              refine ⟨1880279029875024080107733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1253519353250016053405155 1880279029875024080107733)
              ·
                refine ⟨44069039762695876877525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1880279029875024080107733 44069039762695876877525)
                ·
                  rfl

theorem cell21_579313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 7].length) (baseStart_579313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579313 prefixEnd_579313 := by exact prefixLift 579313
  have htrace : WordTrace (prefixWord ++ tailWord_579313) baseStart_579313 baseEnd_579313 := by
    simpa [prefixWord, tailWord_579313, baseEnd_579313] using wordTrace_append hprefix tailTrace_579313
  have hstable : (prefixWord ++ tailWord_579313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579313).length < 2 ^ (prefixWord ++ tailWord_579313).sum := by decide
  have hdescent : baseEnd_579313 < baseStart_579313 := by decide
  rcases family_descends (prefixWord ++ tailWord_579313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579327 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 7]
def baseStart_579327 : Nat := 118140960795 + 579327 * 2 ^ 59
def prefixEnd_579327 : Nat := 4983230072969 + 3 ^ 40 * 579327 * 2
def baseEnd_579327 : Nat := 132210314278826717399213

theorem tailTrace_579327 : CollatzResearch.WordTrace tailWord_579327 prefixEnd_579327 132210314278826717399213 := by
  unfold tailWord_579327
  simp only [CollatzResearch.WordTrace]
  refine ⟨21129791572204695019600235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14086527714803130013066823 21129791572204695019600235)
  ·
    refine ⟨31694687358307042529400353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21129791572204695019600235 31694687358307042529400353)
    ·
      refine ⟨23771015518730281897050265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31694687358307042529400353 23771015518730281897050265)
      ·
        refine ⟨17828261639047711422787699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23771015518730281897050265 17828261639047711422787699)
        ·
          refine ⟨26742392458571567134181549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17828261639047711422787699 26742392458571567134181549)
          ·
            refine ⟨10028397171964337675318081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26742392458571567134181549 10028397171964337675318081)
            ·
              refine ⟨7521297878973253256488561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10028397171964337675318081 7521297878973253256488561)
              ·
                refine ⟨5640973409229939942366421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7521297878973253256488561 5640973409229939942366421)
                ·
                  refine ⟨132210314278826717399213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5640973409229939942366421 132210314278826717399213)
                  ·
                    rfl

theorem cell21_579327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 7].length) (baseStart_579327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579327 prefixEnd_579327 := by exact prefixLift 579327
  have htrace : WordTrace (prefixWord ++ tailWord_579327) baseStart_579327 baseEnd_579327 := by
    simpa [prefixWord, tailWord_579327, baseEnd_579327] using wordTrace_append hprefix tailTrace_579327
  have hstable : (prefixWord ++ tailWord_579327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579327).length < 2 ^ (prefixWord ++ tailWord_579327).sum := by decide
  have hdescent : baseEnd_579327 < baseStart_579327 := by decide
  rcases family_descends (prefixWord ++ tailWord_579327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579389 : List Nat := [1, 4, 1, 4, 1, 10]
def baseStart_579389 : Nat := 118140960795 + 579389 * 2 ^ 59
def prefixEnd_579389 : Nat := 4983230072969 + 3 ^ 40 * 579389 * 2
def baseEnd_579389 : Nat := 4897202352723273606139

theorem tailTrace_579389 : CollatzResearch.WordTrace tailWord_579389 prefixEnd_579389 4897202352723273606139 := by
  unfold tailWord_579389
  simp only [CollatzResearch.WordTrace]
  refine ⟨21132052897980079608357221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14088035265320053072238147 21132052897980079608357221)
  ·
    refine ⟨3962259918371264926566979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21132052897980079608357221 3962259918371264926566979)
    ·
      refine ⟨5943389877556897389850469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3962259918371264926566979 5943389877556897389850469)
      ·
        refine ⟨1114385602041918260596963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5943389877556897389850469 1114385602041918260596963)
        ·
          refine ⟨1671578403062877390895445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1114385602041918260596963 1671578403062877390895445)
          ·
            refine ⟨4897202352723273606139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1671578403062877390895445 4897202352723273606139)
            ·
              rfl

theorem cell21_579389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 10].length) (baseStart_579389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579389 prefixEnd_579389 := by exact prefixLift 579389
  have htrace : WordTrace (prefixWord ++ tailWord_579389) baseStart_579389 baseEnd_579389 := by
    simpa [prefixWord, tailWord_579389, baseEnd_579389] using wordTrace_append hprefix tailTrace_579389
  have hstable : (prefixWord ++ tailWord_579389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579389).length < 2 ^ (prefixWord ++ tailWord_579389).sum := by decide
  have hdescent : baseEnd_579389 < baseStart_579389 := by decide
  rcases family_descends (prefixWord ++ tailWord_579389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579437 : List Nat := [1, 5, 1, 1, 1, 1, 3, 5, 3]
def baseStart_579437 : Nat := 118140960795 + 579437 * 2 ^ 59
def prefixEnd_579437 : Nat := 4983230072969 + 3 ^ 40 * 579437 * 2
def baseEnd_579437 : Nat := 132235417777490970565655

theorem tailTrace_579437 : CollatzResearch.WordTrace tailWord_579437 prefixEnd_579437 132235417777490970565655 := by
  unfold tailWord_579437
  simp only [CollatzResearch.WordTrace]
  refine ⟨21133803601806183806104565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14089202401204122537403043 21133803601806183806104565)
  ·
    refine ⟨1981294087669329731822303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21133803601806183806104565 1981294087669329731822303)
    ·
      refine ⟨2971941131503994597733455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1981294087669329731822303 2971941131503994597733455)
      ·
        refine ⟨4457911697255991896600183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2971941131503994597733455 4457911697255991896600183)
        ·
          refine ⟨6686867545883987844900275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4457911697255991896600183 6686867545883987844900275)
          ·
            refine ⟨10030301318825981767350413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6686867545883987844900275 10030301318825981767350413)
            ·
              refine ⟨3761362994559743162756405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10030301318825981767350413 3761362994559743162756405)
              ·
                refine ⟨352627780739975921508413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3761362994559743162756405 352627780739975921508413)
                ·
                  refine ⟨132235417777490970565655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 352627780739975921508413 132235417777490970565655)
                  ·
                    rfl

theorem cell21_579437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_579437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579437 prefixEnd_579437 := by exact prefixLift 579437
  have htrace : WordTrace (prefixWord ++ tailWord_579437) baseStart_579437 baseEnd_579437 := by
    simpa [prefixWord, tailWord_579437, baseEnd_579437] using wordTrace_append hprefix tailTrace_579437
  have hstable : (prefixWord ++ tailWord_579437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579437).length < 2 ^ (prefixWord ++ tailWord_579437).sum := by decide
  have hdescent : baseEnd_579437 < baseStart_579437 := by decide
  rcases family_descends (prefixWord ++ tailWord_579437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579454 : List Nat := [4, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_579454 : Nat := 118140960795 + 579454 * 2 ^ 59
def prefixEnd_579454 : Nat := 4983230072969 + 3 ^ 40 * 579454 * 2
def baseEnd_579454 : Nat := 132239297409102718782287

theorem tailTrace_579454 : CollatzResearch.WordTrace tailWord_579454 prefixEnd_579454 132239297409102718782287 := by
  unfold tailWord_579454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2641802955343074463684177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14089615761829730472982277 2641802955343074463684177)
  ·
    refine ⟨1981352216507305847763133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2641802955343074463684177 1981352216507305847763133)
    ·
      refine ⟨743007081190239692911175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1981352216507305847763133 743007081190239692911175)
      ·
        refine ⟨1114510621785359539366763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 743007081190239692911175 1114510621785359539366763)
        ·
          refine ⟨1671765932678039309050145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1114510621785359539366763 1671765932678039309050145)
          ·
            refine ⟨1253824449508529481787609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1671765932678039309050145 1253824449508529481787609)
            ·
              refine ⟨940368337131397111340707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1253824449508529481787609 940368337131397111340707)
              ·
                refine ⟨1410552505697095667011061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 940368337131397111340707 1410552505697095667011061)
                ·
                  refine ⟨132239297409102718782287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1410552505697095667011061 132239297409102718782287)
                  ·
                    rfl

theorem cell21_579454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_579454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579454 prefixEnd_579454 := by exact prefixLift 579454
  have htrace : WordTrace (prefixWord ++ tailWord_579454) baseStart_579454 baseEnd_579454 := by
    simpa [prefixWord, tailWord_579454, baseEnd_579454] using wordTrace_append hprefix tailTrace_579454
  have hstable : (prefixWord ++ tailWord_579454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579454).length < 2 ^ (prefixWord ++ tailWord_579454).sum := by decide
  have hdescent : baseEnd_579454 < baseStart_579454 := by decide
  rcases family_descends (prefixWord ++ tailWord_579454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579482 : List Nat := [3, 1, 1, 4, 2, 1, 4, 5]
def baseStart_579482 : Nat := 118140960795 + 579482 * 2 ^ 59
def prefixEnd_579482 : Nat := 4983230072969 + 3 ^ 40 * 579482 * 2
def baseEnd_579482 : Nat := 44081895796860297438521

theorem tailTrace_579482 : CollatzResearch.WordTrace tailWord_579482 prefixEnd_579482 44081895796860297438521 := by
  unfold tailWord_579482
  simp only [CollatzResearch.WordTrace]
  refine ⟨5283861221660789122873175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14090296591095437660995133 5283861221660789122873175)
  ·
    refine ⟨7925791832491183684309763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5283861221660789122873175 7925791832491183684309763)
    ·
      refine ⟨11888687748736775526464645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7925791832491183684309763 11888687748736775526464645)
      ·
        refine ⟨2229128952888145411212121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11888687748736775526464645 2229128952888145411212121)
        ·
          refine ⟨1671846714666109058409091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2229128952888145411212121 1671846714666109058409091)
          ·
            refine ⟨2507770071999163587613637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1671846714666109058409091 2507770071999163587613637)
            ·
              refine ⟨470206888499843172677557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2507770071999163587613637 470206888499843172677557)
              ·
                refine ⟨44081895796860297438521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 470206888499843172677557 44081895796860297438521)
                ·
                  rfl

theorem cell21_579482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_579482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579482 prefixEnd_579482 := by exact prefixLift 579482
  have htrace : WordTrace (prefixWord ++ tailWord_579482) baseStart_579482 baseEnd_579482 := by
    simpa [prefixWord, tailWord_579482, baseEnd_579482] using wordTrace_append hprefix tailTrace_579482
  have hstable : (prefixWord ++ tailWord_579482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579482).length < 2 ^ (prefixWord ++ tailWord_579482).sum := by decide
  have hdescent : baseEnd_579482 < baseStart_579482 := by decide
  rcases family_descends (prefixWord ++ tailWord_579482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579541 : List Nat := [1, 3, 2, 3, 2, 1, 2, 7]
def baseStart_579541 : Nat := 118140960795 + 579541 * 2 ^ 59
def prefixEnd_579541 : Nat := 4983230072969 + 3 ^ 40 * 579541 * 2
def baseEnd_579541 : Nat := 44086383998136633610703

theorem tailTrace_579541 : CollatzResearch.WordTrace tailWord_579541 prefixEnd_579541 44086383998136633610703 := by
  unfold tailWord_579541
  simp only [CollatzResearch.WordTrace]
  refine ⟨21137596793429409567890477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14091731195619606378593651 21137596793429409567890477)
  ·
    refine ⟨7926598797536028587958929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21137596793429409567890477 7926598797536028587958929)
    ·
      refine ⟨5944949098152021440969197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7926598797536028587958929 5944949098152021440969197)
      ·
        refine ⟨2229355911807008040363449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5944949098152021440969197 2229355911807008040363449)
        ·
          refine ⟨1672016933855256030272587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2229355911807008040363449 1672016933855256030272587)
          ·
            refine ⟨2508025400782884045408881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1672016933855256030272587 2508025400782884045408881)
            ·
              refine ⟨1881019050587163034056661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2508025400782884045408881 1881019050587163034056661)
              ·
                refine ⟨44086383998136633610703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1881019050587163034056661 44086383998136633610703)
                ·
                  rfl

theorem cell21_579541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 7].length) (baseStart_579541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579541 prefixEnd_579541 := by exact prefixLift 579541
  have htrace : WordTrace (prefixWord ++ tailWord_579541) baseStart_579541 baseEnd_579541 := by
    simpa [prefixWord, tailWord_579541, baseEnd_579541] using wordTrace_append hprefix tailTrace_579541
  have hstable : (prefixWord ++ tailWord_579541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579541).length < 2 ^ (prefixWord ++ tailWord_579541).sum := by decide
  have hdescent : baseEnd_579541 < baseStart_579541 := by decide
  rcases family_descends (prefixWord ++ tailWord_579541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579617 : List Nat := [1, 2, 3, 2, 4, 1, 8]
def baseStart_579617 : Nat := 118140960795 + 579617 * 2 ^ 59
def prefixEnd_579617 : Nat := 4983230072969 + 3 ^ 40 * 579617 * 2
def baseEnd_579617 : Nat := 14697388469983406396143

theorem tailTrace_579617 : CollatzResearch.WordTrace tailWord_579617 prefixEnd_579617 14697388469983406396143 := by
  unfold tailWord_579617
  simp only [CollatzResearch.WordTrace]
  refine ⟨21140368741154074547657105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14093579160769383031771403 21140368741154074547657105)
  ·
    refine ⟨15855276555865555910742829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21140368741154074547657105 15855276555865555910742829)
    ·
      refine ⟨5945728708449583466528561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15855276555865555910742829 5945728708449583466528561)
      ·
        refine ⟨4459296531337187599896421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5945728708449583466528561 4459296531337187599896421)
        ·
          refine ⟨836118099625722674980579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4459296531337187599896421 836118099625722674980579)
          ·
            refine ⟨1254177149438584012470869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836118099625722674980579 1254177149438584012470869)
            ·
              refine ⟨14697388469983406396143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1254177149438584012470869 14697388469983406396143)
              ·
                rfl

theorem cell21_579617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 8].length) (baseStart_579617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579617 prefixEnd_579617 := by exact prefixLift 579617
  have htrace : WordTrace (prefixWord ++ tailWord_579617) baseStart_579617 baseEnd_579617 := by
    simpa [prefixWord, tailWord_579617, baseEnd_579617] using wordTrace_append hprefix tailTrace_579617
  have hstable : (prefixWord ++ tailWord_579617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579617).length < 2 ^ (prefixWord ++ tailWord_579617).sum := by decide
  have hdescent : baseEnd_579617 < baseStart_579617 := by decide
  rcases family_descends (prefixWord ++ tailWord_579617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579662 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_579662 : Nat := 118140960795 + 579662 * 2 ^ 59
def prefixEnd_579662 : Nat := 4983230072969 + 3 ^ 40 * 579662 * 2
def baseEnd_579662 : Nat := 132286765842940579315195

theorem tailTrace_579662 : CollatzResearch.WordTrace tailWord_579662 prefixEnd_579662 132286765842940579315195 := by
  unfold tailWord_579662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2642751253248880904130655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14094673350660698155363493 2642751253248880904130655)
  ·
    refine ⟨3964126879873321356195983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2642751253248880904130655 3964126879873321356195983)
    ·
      refine ⟨5946190319809982034293975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3964126879873321356195983 5946190319809982034293975)
      ·
        refine ⟨8919285479714973051440963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5946190319809982034293975 8919285479714973051440963)
        ·
          refine ⟨13378928219572459577161445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8919285479714973051440963 13378928219572459577161445)
          ·
            refine ⟨2508549041169836170717771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13378928219572459577161445 2508549041169836170717771)
            ·
              refine ⟨3762823561754754256076657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2508549041169836170717771 3762823561754754256076657)
              ·
                refine ⟨2822117671316065692057493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3762823561754754256076657 2822117671316065692057493)
                ·
                  refine ⟨132286765842940579315195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2822117671316065692057493 132286765842940579315195)
                  ·
                    rfl

theorem cell21_579662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_579662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579662 prefixEnd_579662 := by exact prefixLift 579662
  have htrace : WordTrace (prefixWord ++ tailWord_579662) baseStart_579662 baseEnd_579662 := by
    simpa [prefixWord, tailWord_579662, baseEnd_579662] using wordTrace_append hprefix tailTrace_579662
  have hstable : (prefixWord ++ tailWord_579662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579662).length < 2 ^ (prefixWord ++ tailWord_579662).sum := by decide
  have hdescent : baseEnd_579662 < baseStart_579662 := by decide
  rcases family_descends (prefixWord ++ tailWord_579662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579682 : List Nat := [3, 3, 2, 2, 2, 2, 1, 1, 5]
def baseStart_579682 : Nat := 118140960795 + 579682 * 2 ^ 59
def prefixEnd_579682 : Nat := 4983230072969 + 3 ^ 40 * 579682 * 2
def baseEnd_579682 : Nat := 132291330115424988981821

theorem tailTrace_579682 : CollatzResearch.WordTrace tailWord_579682 prefixEnd_579682 132291330115424988981821 := by
  unfold tailWord_579682
  simp only [CollatzResearch.WordTrace]
  refine ⟨5285684871479647662193325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14095159657279060432515533 5285684871479647662193325)
  ·
    refine ⟨1982131826804867873322497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5285684871479647662193325 1982131826804867873322497)
    ·
      refine ⟨1486598870103650904991873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1982131826804867873322497 1486598870103650904991873)
      ·
        refine ⟨1114949152577738178743905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1486598870103650904991873 1114949152577738178743905)
        ·
          refine ⟨836211864433303634057929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1114949152577738178743905 836211864433303634057929)
          ·
            refine ⟨627158898324977725543447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 836211864433303634057929 627158898324977725543447)
            ·
              refine ⟨940738347487466588315171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627158898324977725543447 940738347487466588315171)
              ·
                refine ⟨1411107521231199882472757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 940738347487466588315171 1411107521231199882472757)
                ·
                  refine ⟨132291330115424988981821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1411107521231199882472757 132291330115424988981821)
                  ·
                    rfl

theorem cell21_579682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_579682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579682 prefixEnd_579682 := by exact prefixLift 579682
  have htrace : WordTrace (prefixWord ++ tailWord_579682) baseStart_579682 baseEnd_579682 := by
    simpa [prefixWord, tailWord_579682, baseEnd_579682] using wordTrace_append hprefix tailTrace_579682
  have hstable : (prefixWord ++ tailWord_579682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579682).length < 2 ^ (prefixWord ++ tailWord_579682).sum := by decide
  have hdescent : baseEnd_579682 < baseStart_579682 := by decide
  rcases family_descends (prefixWord ++ tailWord_579682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579693 : List Nat := [1, 5, 1, 1, 2, 1, 4, 6]
def baseStart_579693 : Nat := 118140960795 + 579693 * 2 ^ 59
def prefixEnd_579693 : Nat := 4983230072969 + 3 ^ 40 * 579693 * 2
def baseEnd_579693 : Nat := 44097946821763804766155

theorem tailTrace_579693 : CollatzResearch.WordTrace tailWord_579693 prefixEnd_579693 44097946821763804766155 := by
  unfold tailWord_579693
  simp only [CollatzResearch.WordTrace]
  refine ⟨21143140688878739527423733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14095427125919159684949155 21143140688878739527423733)
  ·
    refine ⟨1982169439582381830695975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21143140688878739527423733 1982169439582381830695975)
    ·
      refine ⟨2973254159373572746043963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1982169439582381830695975 2973254159373572746043963)
      ·
        refine ⟨4459881239060359119065945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2973254159373572746043963 4459881239060359119065945)
        ·
          refine ⟨3344910929295269339299459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4459881239060359119065945 3344910929295269339299459)
          ·
            refine ⟨5017366393942904008949189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3344910929295269339299459 5017366393942904008949189)
            ·
              refine ⟨940756198864294501677973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5017366393942904008949189 940756198864294501677973)
              ·
                refine ⟨44097946821763804766155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 940756198864294501677973 44097946821763804766155)
                ·
                  rfl

theorem cell21_579693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 6].length) (baseStart_579693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579693 prefixEnd_579693 := by exact prefixLift 579693
  have htrace : WordTrace (prefixWord ++ tailWord_579693) baseStart_579693 baseEnd_579693 := by
    simpa [prefixWord, tailWord_579693, baseEnd_579693] using wordTrace_append hprefix tailTrace_579693
  have hstable : (prefixWord ++ tailWord_579693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579693).length < 2 ^ (prefixWord ++ tailWord_579693).sum := by decide
  have hdescent : baseEnd_579693 < baseStart_579693 := by decide
  rcases family_descends (prefixWord ++ tailWord_579693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579696 : List Nat := [2, 1, 1, 1, 5, 4, 2, 1, 4]
def baseStart_579696 : Nat := 118140960795 + 579696 * 2 ^ 59
def prefixEnd_579696 : Nat := 4983230072969 + 3 ^ 40 * 579696 * 2
def baseEnd_579696 : Nat := 132294525106164075748459

theorem tailTrace_579696 : CollatzResearch.WordTrace tailWord_579696 prefixEnd_579696 132294525106164075748459 := by
  unfold tailWord_579696
  simp only [CollatzResearch.WordTrace]
  refine ⟨10571625053933935519891471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14095500071911914026521961 10571625053933935519891471)
  ·
    refine ⟨15857437580900903279837207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10571625053933935519891471 15857437580900903279837207)
    ·
      refine ⟨23786156371351354919755811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15857437580900903279837207 23786156371351354919755811)
      ·
        refine ⟨35679234557027032379633717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23786156371351354919755811 35679234557027032379633717)
        ·
          refine ⟨3344928239721284285590661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35679234557027032379633717 3344928239721284285590661)
          ·
            refine ⟨627174044947740803548249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3344928239721284285590661 627174044947740803548249)
            ·
              refine ⟨470380533710805602661187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 627174044947740803548249 470380533710805602661187)
              ·
                refine ⟨705570800566208403991781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470380533710805602661187 705570800566208403991781)
                ·
                  refine ⟨132294525106164075748459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 705570800566208403991781 132294525106164075748459)
                  ·
                    rfl

theorem cell21_579696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 4].length) (baseStart_579696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579696 prefixEnd_579696 := by exact prefixLift 579696
  have htrace : WordTrace (prefixWord ++ tailWord_579696) baseStart_579696 baseEnd_579696 := by
    simpa [prefixWord, tailWord_579696, baseEnd_579696] using wordTrace_append hprefix tailTrace_579696
  have hstable : (prefixWord ++ tailWord_579696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579696).length < 2 ^ (prefixWord ++ tailWord_579696).sum := by decide
  have hdescent : baseEnd_579696 < baseStart_579696 := by decide
  rcases family_descends (prefixWord ++ tailWord_579696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579741 : List Nat := [1, 4, 2, 1, 1, 4, 1, 4, 3]
def baseStart_579741 : Nat := 118140960795 + 579741 * 2 ^ 59
def prefixEnd_579741 : Nat := 4983230072969 + 3 ^ 40 * 579741 * 2
def baseEnd_579741 : Nat := 132304794719253997498367

theorem tailTrace_579741 : CollatzResearch.WordTrace tailWord_579741 prefixEnd_579741 132304794719253997498367 := by
  unfold tailWord_579741
  simp only [CollatzResearch.WordTrace]
  refine ⟨21144891392704843725171077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14096594261803229150114051 21144891392704843725171077)
  ·
    refine ⟨3964667136132158198469577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21144891392704843725171077 3964667136132158198469577)
    ·
      refine ⟨2973500352099118648852183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3964667136132158198469577 2973500352099118648852183)
      ·
        refine ⟨4460250528148677973278275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2973500352099118648852183 4460250528148677973278275)
        ·
          refine ⟨6690375792223016959917413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4460250528148677973278275 6690375792223016959917413)
          ·
            refine ⟨1254445461041815679984515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6690375792223016959917413 1254445461041815679984515)
            ·
              refine ⟨1881668191562723519976773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254445461041815679984515 1881668191562723519976773)
              ·
                refine ⟨352812785918010659995645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1881668191562723519976773 352812785918010659995645)
                ·
                  refine ⟨132304794719253997498367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 352812785918010659995645 132304794719253997498367)
                  ·
                    rfl

theorem cell21_579741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_579741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579741 prefixEnd_579741 := by exact prefixLift 579741
  have htrace : WordTrace (prefixWord ++ tailWord_579741) baseStart_579741 baseEnd_579741 := by
    simpa [prefixWord, tailWord_579741, baseEnd_579741] using wordTrace_append hprefix tailTrace_579741
  have hstable : (prefixWord ++ tailWord_579741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579741).length < 2 ^ (prefixWord ++ tailWord_579741).sum := by decide
  have hdescent : baseEnd_579741 < baseStart_579741 := by decide
  rcases family_descends (prefixWord ++ tailWord_579741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579758 : List Nat := [4, 1, 4, 2, 1, 1, 1, 2, 5]
def baseStart_579758 : Nat := 118140960795 + 579758 * 2 ^ 59
def prefixEnd_579758 : Nat := 4983230072969 + 3 ^ 40 * 579758 * 2
def baseEnd_579758 : Nat := 132308674350865745714999

theorem tailTrace_579758 : CollatzResearch.WordTrace tailWord_579758 prefixEnd_579758 132308674350865745714999 := by
  unfold tailWord_579758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2643188929205406953567491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14097007622428837085693285 2643188929205406953567491)
  ·
    refine ⟨3964783393808110430351237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2643188929205406953567491 3964783393808110430351237)
    ·
      refine ⟨743396886339020705690857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3964783393808110430351237 743396886339020705690857)
      ·
        refine ⟨557547664754265529268143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 743396886339020705690857 557547664754265529268143)
        ·
          refine ⟨836321497131398293902215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557547664754265529268143 836321497131398293902215)
          ·
            refine ⟨1254482245697097440853323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836321497131398293902215 1254482245697097440853323)
            ·
              refine ⟨1881723368545646161279985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254482245697097440853323 1881723368545646161279985)
              ·
                refine ⟨1411292526409234620959989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1881723368545646161279985 1411292526409234620959989)
                ·
                  refine ⟨132308674350865745714999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1411292526409234620959989 132308674350865745714999)
                  ·
                    rfl

theorem cell21_579758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_579758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579758 prefixEnd_579758 := by exact prefixLift 579758
  have htrace : WordTrace (prefixWord ++ tailWord_579758) baseStart_579758 baseEnd_579758 := by
    simpa [prefixWord, tailWord_579758, baseEnd_579758] using wordTrace_append hprefix tailTrace_579758
  have hstable : (prefixWord ++ tailWord_579758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579758).length < 2 ^ (prefixWord ++ tailWord_579758).sum := by decide
  have hdescent : baseEnd_579758 < baseStart_579758 := by decide
  rcases family_descends (prefixWord ++ tailWord_579758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579769 : List Nat := [1, 2, 1, 4, 1, 2, 5, 5]
def baseStart_579769 : Nat := 118140960795 + 579769 * 2 ^ 59
def prefixEnd_579769 : Nat := 4983230072969 + 3 ^ 40 * 579769 * 2
def baseEnd_579769 : Nat := 44103728233577390343881

theorem tailTrace_579769 : CollatzResearch.WordTrace tailWord_579769 prefixEnd_579769 44103728233577390343881 := by
  unfold tailWord_579769
  simp only [CollatzResearch.WordTrace]
  refine ⟨21145912636603404507190361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14097275091068936338126907 21145912636603404507190361)
  ·
    refine ⟨15859434477452553380392771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21145912636603404507190361 15859434477452553380392771)
    ·
      refine ⟨23789151716178830070589157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15859434477452553380392771 23789151716178830070589157)
      ·
        refine ⟨4460465946783530638235467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23789151716178830070589157 4460465946783530638235467)
        ·
          refine ⟨6690698920175295957353201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4460465946783530638235467 6690698920175295957353201)
          ·
            refine ⟨5018024190131471968014901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6690698920175295957353201 5018024190131471968014901)
            ·
              refine ⟨470439767824825497001397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5018024190131471968014901 470439767824825497001397)
              ·
                refine ⟨44103728233577390343881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 470439767824825497001397 44103728233577390343881)
                ·
                  rfl

theorem cell21_579769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 5].length) (baseStart_579769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579769 prefixEnd_579769 := by exact prefixLift 579769
  have htrace : WordTrace (prefixWord ++ tailWord_579769) baseStart_579769 baseEnd_579769 := by
    simpa [prefixWord, tailWord_579769, baseEnd_579769] using wordTrace_append hprefix tailTrace_579769
  have hstable : (prefixWord ++ tailWord_579769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579769).length < 2 ^ (prefixWord ++ tailWord_579769).sum := by decide
  have hdescent : baseEnd_579769 < baseStart_579769 := by decide
  rcases family_descends (prefixWord ++ tailWord_579769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579800 : List Nat := [2, 1, 2, 2, 4, 2, 2, 1, 5]
def baseStart_579800 : Nat := 118140960795 + 579800 * 2 ^ 59
def prefixEnd_579800 : Nat := 4983230072969 + 3 ^ 40 * 579800 * 2
def baseEnd_579800 : Nat := 132318259323083006014913

theorem tailTrace_579800 : CollatzResearch.WordTrace tailWord_579800 prefixEnd_579800 132318259323083006014913 := by
  unfold tailWord_579800
  simp only [CollatzResearch.WordTrace]
  refine ⟨10573521649745548400784427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14098028866327397867712569 10573521649745548400784427)
  ·
    refine ⟨15860282474618322601176641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10573521649745548400784427 15860282474618322601176641)
    ·
      refine ⟨11895211855963741950882481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15860282474618322601176641 11895211855963741950882481)
      ·
        refine ⟨8921408891972806463161861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11895211855963741950882481 8921408891972806463161861)
        ·
          refine ⟨1672764167244901211842849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8921408891972806463161861 1672764167244901211842849)
          ·
            refine ⟨1254573125433675908882137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1672764167244901211842849 1254573125433675908882137)
            ·
              refine ⟨940929844075256931661603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1254573125433675908882137 940929844075256931661603)
              ·
                refine ⟨1411394766112885397492405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 940929844075256931661603 1411394766112885397492405)
                ·
                  refine ⟨132318259323083006014913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1411394766112885397492405 132318259323083006014913)
                  ·
                    rfl

theorem cell21_579800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 5].length) (baseStart_579800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579800 prefixEnd_579800 := by exact prefixLift 579800
  have htrace : WordTrace (prefixWord ++ tailWord_579800) baseStart_579800 baseEnd_579800 := by
    simpa [prefixWord, tailWord_579800, baseEnd_579800] using wordTrace_append hprefix tailTrace_579800
  have hstable : (prefixWord ++ tailWord_579800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579800).length < 2 ^ (prefixWord ++ tailWord_579800).sum := by decide
  have hdescent : baseEnd_579800 < baseStart_579800 := by decide
  rcases family_descends (prefixWord ++ tailWord_579800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579921 : List Nat := [1, 2, 2, 1, 4, 4, 1, 6]
def baseStart_579921 : Nat := 118140960795 + 579921 * 2 ^ 59
def prefixEnd_579921 : Nat := 4983230072969 + 3 ^ 40 * 579921 * 2
def baseEnd_579921 : Nat := 44115291057204561499333

theorem tailTrace_579921 : CollatzResearch.WordTrace tailWord_579921 prefixEnd_579921 44115291057204561499333 := by
  unfold tailWord_579921
  simp only [CollatzResearch.WordTrace]
  refine ⟨21151456532052734466723617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14100971021368489644482411 21151456532052734466723617)
  ·
    refine ⟨15863592399039550850042713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21151456532052734466723617 15863592399039550850042713)
    ·
      refine ⟨11897694299279663137532035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15863592399039550850042713 11897694299279663137532035)
      ·
        refine ⟨17846541448919494706298053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11897694299279663137532035 17846541448919494706298053)
        ·
          refine ⟨3346226521672405257430885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17846541448919494706298053 3346226521672405257430885)
          ·
            refine ⟨627417472813575985768291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3346226521672405257430885 627417472813575985768291)
            ·
              refine ⟨941126209220363978652437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627417472813575985768291 941126209220363978652437)
              ·
                refine ⟨44115291057204561499333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 941126209220363978652437 44115291057204561499333)
                ·
                  rfl

theorem cell21_579921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 6].length) (baseStart_579921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579921 prefixEnd_579921 := by exact prefixLift 579921
  have htrace : WordTrace (prefixWord ++ tailWord_579921) baseStart_579921 baseEnd_579921 := by
    simpa [prefixWord, tailWord_579921, baseEnd_579921] using wordTrace_append hprefix tailTrace_579921
  have hstable : (prefixWord ++ tailWord_579921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579921).length < 2 ^ (prefixWord ++ tailWord_579921).sum := by decide
  have hdescent : baseEnd_579921 < baseStart_579921 := by decide
  rcases family_descends (prefixWord ++ tailWord_579921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579938 : List Nat := [3, 3, 2, 1, 1, 3, 3, 5]
def baseStart_579938 : Nat := 118140960795 + 579938 * 2 ^ 59
def prefixEnd_579938 : Nat := 4983230072969 + 3 ^ 40 * 579938 * 2
def baseEnd_579938 : Nat := 44116584267741810904877

theorem tailTrace_579938 : CollatzResearch.WordTrace tailWord_579938 prefixEnd_579938 44116584267741810904877 := by
  unfold tailWord_579938
  simp only [CollatzResearch.WordTrace]
  refine ⟨5288019143247786592523117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14101384381994097580061645 5288019143247786592523117)
  ·
    refine ⟨1983007178717919972196169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5288019143247786592523117 1983007178717919972196169)
    ·
      refine ⟨1487255384038439979147127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1983007178717919972196169 1487255384038439979147127)
      ·
        refine ⟨2230883076057659968720691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1487255384038439979147127 2230883076057659968720691)
        ·
          refine ⟨3346324614086489953081037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2230883076057659968720691 3346324614086489953081037)
          ·
            refine ⟨1254871730282433732405389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3346324614086489953081037 1254871730282433732405389)
            ·
              refine ⟨470576898855912649652021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1254871730282433732405389 470576898855912649652021)
              ·
                refine ⟨44116584267741810904877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 470576898855912649652021 44116584267741810904877)
                ·
                  rfl

theorem cell21_579938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_579938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579938 prefixEnd_579938 := by exact prefixLift 579938
  have htrace : WordTrace (prefixWord ++ tailWord_579938) baseStart_579938 baseEnd_579938 := by
    simpa [prefixWord, tailWord_579938, baseEnd_579938] using wordTrace_append hprefix tailTrace_579938
  have hstable : (prefixWord ++ tailWord_579938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579938).length < 2 ^ (prefixWord ++ tailWord_579938).sum := by decide
  have hdescent : baseEnd_579938 < baseStart_579938 := by decide
  rcases family_descends (prefixWord ++ tailWord_579938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579952 : List Nat := [2, 1, 1, 1, 4, 3, 1, 5, 3]
def baseStart_579952 : Nat := 118140960795 + 579952 * 2 ^ 59
def prefixEnd_579952 : Nat := 4983230072969 + 3 ^ 40 * 579952 * 2
def baseEnd_579952 : Nat := 132352947793964519481269

theorem tailTrace_579952 : CollatzResearch.WordTrace tailWord_579952 prefixEnd_579952 132352947793964519481269 := by
  unfold tailWord_579952
  simp only [CollatzResearch.WordTrace]
  refine ⟨10576293597470213380551055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14101724796626951174068073 10576293597470213380551055)
  ·
    refine ⟨15864440396205320070826583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10576293597470213380551055 15864440396205320070826583)
    ·
      refine ⟨23796660594307980106239875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15864440396205320070826583 23796660594307980106239875)
      ·
        refine ⟨35694990891461970159359813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23796660594307980106239875 35694990891461970159359813)
        ·
          refine ⟨6692810792149119404879965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35694990891461970159359813 6692810792149119404879965)
          ·
            refine ⟨2509804047055919776829987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6692810792149119404879965 2509804047055919776829987)
            ·
              refine ⟨3764706070583879665244981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2509804047055919776829987 3764706070583879665244981)
              ·
                refine ⟨352941194117238718616717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3764706070583879665244981 352941194117238718616717)
                ·
                  refine ⟨132352947793964519481269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 352941194117238718616717 132352947793964519481269)
                  ·
                    rfl

theorem cell21_579952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 3].length) (baseStart_579952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579952 prefixEnd_579952 := by exact prefixLift 579952
  have htrace : WordTrace (prefixWord ++ tailWord_579952) baseStart_579952 baseEnd_579952 := by
    simpa [prefixWord, tailWord_579952, baseEnd_579952] using wordTrace_append hprefix tailTrace_579952
  have hstable : (prefixWord ++ tailWord_579952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579952).length < 2 ^ (prefixWord ++ tailWord_579952).sum := by decide
  have hdescent : baseEnd_579952 < baseStart_579952 := by decide
  rcases family_descends (prefixWord ++ tailWord_579952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579958 : List Nat := [5, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_579958 : Nat := 118140960795 + 579958 * 2 ^ 59
def prefixEnd_579958 : Nat := 4983230072969 + 3 ^ 40 * 579958 * 2
def baseEnd_579958 : Nat := 132354317075709842381257

theorem tailTrace_579958 : CollatzResearch.WordTrace tailWord_579958 prefixEnd_579958 132354317075709842381257 := by
  unfold tailWord_579958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1322050377057418111613783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14101870688612459857213685 1322050377057418111613783)
  ·
    refine ⟨1983075565586127167420675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1322050377057418111613783 1983075565586127167420675)
    ·
      refine ⟨2974613348379190751131013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1983075565586127167420675 2974613348379190751131013)
      ·
        refine ⟨557740002821098265837065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2974613348379190751131013 557740002821098265837065)
        ·
          refine ⟨418305002115823699377799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557740002821098265837065 418305002115823699377799)
          ·
            refine ⟨627457503173735549066699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418305002115823699377799 627457503173735549066699)
            ·
              refine ⟨941186254760603323600049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627457503173735549066699 941186254760603323600049)
              ·
                refine ⟨705889691070452492700037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 941186254760603323600049 705889691070452492700037)
                ·
                  refine ⟨132354317075709842381257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 705889691070452492700037 132354317075709842381257)
                  ·
                    rfl

theorem cell21_579958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_579958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579958 prefixEnd_579958 := by exact prefixLift 579958
  have htrace : WordTrace (prefixWord ++ tailWord_579958) baseStart_579958 baseEnd_579958 := by
    simpa [prefixWord, tailWord_579958, baseEnd_579958] using wordTrace_append hprefix tailTrace_579958
  have hstable : (prefixWord ++ tailWord_579958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579958).length < 2 ^ (prefixWord ++ tailWord_579958).sum := by decide
  have hdescent : baseEnd_579958 < baseStart_579958 := by decide
  rcases family_descends (prefixWord ++ tailWord_579958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579969 : List Nat := [1, 2, 4, 3, 1, 1, 2, 4, 3]
def baseStart_579969 : Nat := 118140960795 + 579969 * 2 ^ 59
def prefixEnd_579969 : Nat := 4983230072969 + 3 ^ 40 * 579969 * 2
def baseEnd_579969 : Nat := 132356827425576267697901

theorem tailTrace_579969 : CollatzResearch.WordTrace tailWord_579969 prefixEnd_579969 132356827425576267697901 := by
  unfold tailWord_579969
  simp only [CollatzResearch.WordTrace]
  refine ⟨21153207235878838664470961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14102138157252559109647307 21153207235878838664470961)
  ·
    refine ⟨15864905426909128998353221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21153207235878838664470961 15864905426909128998353221)
    ·
      refine ⟨2974669767545461687191229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15864905426909128998353221 2974669767545461687191229)
      ·
        refine ⟨1115501162829548132696711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2974669767545461687191229 1115501162829548132696711)
        ·
          refine ⟨1673251744244322199045067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1115501162829548132696711 1673251744244322199045067)
          ·
            refine ⟨2509877616366483298567601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1673251744244322199045067 2509877616366483298567601)
            ·
              refine ⟨1882408212274862473925701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2509877616366483298567601 1882408212274862473925701)
              ·
                refine ⟨352951539801536713861069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1882408212274862473925701 352951539801536713861069)
                ·
                  refine ⟨132356827425576267697901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 352951539801536713861069 132356827425576267697901)
                  ·
                    rfl

theorem cell21_579969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 3].length) (baseStart_579969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579969 prefixEnd_579969 := by exact prefixLift 579969
  have htrace : WordTrace (prefixWord ++ tailWord_579969) baseStart_579969 baseEnd_579969 := by
    simpa [prefixWord, tailWord_579969, baseEnd_579969] using wordTrace_append hprefix tailTrace_579969
  have hstable : (prefixWord ++ tailWord_579969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579969).length < 2 ^ (prefixWord ++ tailWord_579969).sum := by decide
  have hdescent : baseEnd_579969 < baseStart_579969 := by decide
  rcases family_descends (prefixWord ++ tailWord_579969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579997 : List Nat := [1, 4, 2, 1, 4, 1, 1, 7]
def baseStart_579997 : Nat := 118140960795 + 579997 * 2 ^ 59
def prefixEnd_579997 : Nat := 4983230072969 + 3 ^ 40 * 579997 * 2
def baseEnd_579997 : Nat := 44121072469018147077059

theorem tailTrace_579997 : CollatzResearch.WordTrace tailWord_579997 prefixEnd_579997 44121072469018147077059 := by
  unfold tailWord_579997
  simp only [CollatzResearch.WordTrace]
  refine ⟨21154228479777399446490245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14102818986518266297660163 21154228479777399446490245)
  ·
    refine ⟨3966417839958262396216921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21154228479777399446490245 3966417839958262396216921)
    ·
      refine ⟨2974813379968696797162691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3966417839958262396216921 2974813379968696797162691)
      ·
        refine ⟨4462220069953045195744037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2974813379968696797162691 4462220069953045195744037)
        ·
          refine ⟨836666263116195974202007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4462220069953045195744037 836666263116195974202007)
          ·
            refine ⟨1254999394674293961303011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836666263116195974202007 1254999394674293961303011)
            ·
              refine ⟨1882499092011440941954517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254999394674293961303011 1882499092011440941954517)
              ·
                refine ⟨44121072469018147077059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1882499092011440941954517 44121072469018147077059)
                ·
                  rfl

theorem cell21_579997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 7].length) (baseStart_579997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_579997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_579997 prefixEnd_579997 := by exact prefixLift 579997
  have htrace : WordTrace (prefixWord ++ tailWord_579997) baseStart_579997 baseEnd_579997 := by
    simpa [prefixWord, tailWord_579997, baseEnd_579997] using wordTrace_append hprefix tailTrace_579997
  have hstable : (prefixWord ++ tailWord_579997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579997).length < 2 ^ (prefixWord ++ tailWord_579997).sum := by decide
  have hdescent : baseEnd_579997 < baseStart_579997 := by decide
  rcases family_descends (prefixWord ++ tailWord_579997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580020 : List Nat := [2, 5, 2, 2, 1, 1, 3, 2, 3]
def baseStart_580020 : Nat := 118140960795 + 580020 * 2 ^ 59
def prefixEnd_580020 : Nat := 4983230072969 + 3 ^ 40 * 580020 * 2
def baseEnd_580020 : Nat := 132368466320411512347797

theorem tailTrace_580020 : CollatzResearch.WordTrace tailWord_580020 prefixEnd_580020 132368466320411512347797 := by
  unfold tailWord_580020
  simp only [CollatzResearch.WordTrace]
  refine ⟨10577533679347037187288757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14103378239129382916385009 10577533679347037187288757)
  ·
    refine ⟨991643782438784736308321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10577533679347037187288757 991643782438784736308321)
    ·
      refine ⟨743732836829088552231241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 991643782438784736308321 743732836829088552231241)
      ·
        refine ⟨557799627621816414173431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 743732836829088552231241 557799627621816414173431)
        ·
          refine ⟨836699441432724621260147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557799627621816414173431 836699441432724621260147)
          ·
            refine ⟨1255049162149086931890221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836699441432724621260147 1255049162149086931890221)
            ·
              refine ⟨470643435805907599458833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1255049162149086931890221 470643435805907599458833)
              ·
                refine ⟨352982576854430699594125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 470643435805907599458833 352982576854430699594125)
                ·
                  refine ⟨132368466320411512347797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 352982576854430699594125 132368466320411512347797)
                  ·
                    rfl

theorem cell21_580020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_580020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580020 prefixEnd_580020 := by exact prefixLift 580020
  have htrace : WordTrace (prefixWord ++ tailWord_580020) baseStart_580020 baseEnd_580020 := by
    simpa [prefixWord, tailWord_580020, baseEnd_580020] using wordTrace_append hprefix tailTrace_580020
  have hstable : (prefixWord ++ tailWord_580020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580020).length < 2 ^ (prefixWord ++ tailWord_580020).sum := by decide
  have hdescent : baseEnd_580020 < baseStart_580020 := by decide
  rcases family_descends (prefixWord ++ tailWord_580020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580028 : List Nat := [2, 2, 2, 4, 1, 1, 3, 1, 5]
def baseStart_580028 : Nat := 118140960795 + 580028 * 2 ^ 59
def prefixEnd_580028 : Nat := 4983230072969 + 3 ^ 40 * 580028 * 2
def baseEnd_580028 : Nat := 132370292029405276214447

theorem tailTrace_580028 : CollatzResearch.WordTrace tailWord_580028 prefixEnd_580028 132370292029405276214447 := by
  unfold tailWord_580028
  simp only [CollatzResearch.WordTrace]
  refine ⟨10577679571332545870434369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14103572761776727827245825 10577679571332545870434369)
  ·
    refine ⟨7933259678499409402825777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10577679571332545870434369 7933259678499409402825777)
    ·
      refine ⟨5949944758874557052119333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7933259678499409402825777 5949944758874557052119333)
      ·
        refine ⟨1115614642288979447272375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5949944758874557052119333 1115614642288979447272375)
        ·
          refine ⟨1673421963433469170908563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1115614642288979447272375 1673421963433469170908563)
          ·
            refine ⟨2510132945150203756362845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1673421963433469170908563 2510132945150203756362845)
            ·
              refine ⟨941299854431326408636067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2510132945150203756362845 941299854431326408636067)
              ·
                refine ⟨1411949781646989612954101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941299854431326408636067 1411949781646989612954101)
                ·
                  refine ⟨132370292029405276214447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1411949781646989612954101 132370292029405276214447)
                  ·
                    rfl

theorem cell21_580028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_580028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580028 prefixEnd_580028 := by exact prefixLift 580028
  have htrace : WordTrace (prefixWord ++ tailWord_580028) baseStart_580028 baseEnd_580028 := by
    simpa [prefixWord, tailWord_580028, baseEnd_580028] using wordTrace_append hprefix tailTrace_580028
  have hstable : (prefixWord ++ tailWord_580028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580028).length < 2 ^ (prefixWord ++ tailWord_580028).sum := by decide
  have hdescent : baseEnd_580028 < baseStart_580028 := by decide
  rcases family_descends (prefixWord ++ tailWord_580028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580042 : List Nat := [3, 1, 2, 1, 2, 2, 3, 3, 4]
def baseStart_580042 : Nat := 118140960795 + 580042 * 2 ^ 59
def prefixEnd_580042 : Nat := 4983230072969 + 3 ^ 40 * 580042 * 2
def baseEnd_580042 : Nat := 132373487020144362981085

theorem tailTrace_580042 : CollatzResearch.WordTrace tailWord_580042 prefixEnd_580042 132373487020144362981085 := by
  unfold tailWord_580042
  simp only [CollatzResearch.WordTrace]
  refine ⟨5288967441153593032969595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14103913176409581421252253 5288967441153593032969595)
  ·
    refine ⟨7933451161730389549454393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5288967441153593032969595 7933451161730389549454393)
    ·
      refine ⟨5950088371297792162090795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7933451161730389549454393 5950088371297792162090795)
      ·
        refine ⟨8925132556946688243136193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5950088371297792162090795 8925132556946688243136193)
        ·
          refine ⟨6693849417710016182352145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8925132556946688243136193 6693849417710016182352145)
          ·
            refine ⟨5020387063282512136764109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6693849417710016182352145 5020387063282512136764109)
            ·
              refine ⟨1882645148730942051286541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5020387063282512136764109 1882645148730942051286541)
              ·
                refine ⟨705991930774103269232453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1882645148730942051286541 705991930774103269232453)
                ·
                  refine ⟨132373487020144362981085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 705991930774103269232453 132373487020144362981085)
                  ·
                    rfl

theorem cell21_580042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_580042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580042 prefixEnd_580042 := by exact prefixLift 580042
  have htrace : WordTrace (prefixWord ++ tailWord_580042) baseStart_580042 baseEnd_580042 := by
    simpa [prefixWord, tailWord_580042, baseEnd_580042] using wordTrace_append hprefix tailTrace_580042
  have hstable : (prefixWord ++ tailWord_580042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580042).length < 2 ^ (prefixWord ++ tailWord_580042).sum := by decide
  have hdescent : baseEnd_580042 < baseStart_580042 := by decide
  rcases family_descends (prefixWord ++ tailWord_580042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580166 : List Nat := [6, 1, 1, 1, 2, 2, 1, 7]
def baseStart_580166 : Nat := 118140960795 + 580166 * 2 ^ 59
def prefixEnd_580166 : Nat := 4983230072969 + 3 ^ 40 * 580166 * 2
def baseEnd_580166 : Nat := 44133928503182567638055

theorem tailTrace_580166 : CollatzResearch.WordTrace tailWord_580166 prefixEnd_580166 44133928503182567638055 := by
  unfold tailWord_580166
  simp only [CollatzResearch.WordTrace]
  refine ⟨661262263005160665918511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14106928277443427539594901 661262263005160665918511)
  ·
    refine ⟨991893394507740998877767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 661262263005160665918511 991893394507740998877767)
    ·
      refine ⟨1487840091761611498316651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 991893394507740998877767 1487840091761611498316651)
      ·
        refine ⟨2231760137642417247474977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1487840091761611498316651 2231760137642417247474977)
        ·
          refine ⟨1673820103231812935606233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2231760137642417247474977 1673820103231812935606233)
          ·
            refine ⟨1255365077423859701704675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1673820103231812935606233 1255365077423859701704675)
            ·
              refine ⟨1883047616135789552557013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1255365077423859701704675 1883047616135789552557013)
              ·
                refine ⟨44133928503182567638055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1883047616135789552557013 44133928503182567638055)
                ·
                  rfl

theorem cell21_580166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_580166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580166 prefixEnd_580166 := by exact prefixLift 580166
  have htrace : WordTrace (prefixWord ++ tailWord_580166) baseStart_580166 baseEnd_580166 := by
    simpa [prefixWord, tailWord_580166, baseEnd_580166] using wordTrace_append hprefix tailTrace_580166
  have hstable : (prefixWord ++ tailWord_580166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580166).length < 2 ^ (prefixWord ++ tailWord_580166).sum := by decide
  have hdescent : baseEnd_580166 < baseStart_580166 := by decide
  rcases family_descends (prefixWord ++ tailWord_580166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580177 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 6]
def baseStart_580177 : Nat := 118140960795 + 580177 * 2 ^ 59
def prefixEnd_580177 : Nat := 4983230072969 + 3 ^ 40 * 580177 * 2
def baseEnd_580177 : Nat := 132404295859414128230809

theorem tailTrace_580177 : CollatzResearch.WordTrace tailWord_580177 prefixEnd_580177 132404295859414128230809 := by
  unfold tailWord_580177
  simp only [CollatzResearch.WordTrace]
  refine ⟨21160793619125290188042785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14107195746083526792028523 21160793619125290188042785)
  ·
    refine ⟨15870595214343967641032089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21160793619125290188042785 15870595214343967641032089)
    ·
      refine ⟨11902946410757975730774067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15870595214343967641032089 11902946410757975730774067)
      ·
        refine ⟨17854419616136963596161101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11902946410757975730774067 17854419616136963596161101)
        ·
          refine ⟨6695407356051361348560413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17854419616136963596161101 6695407356051361348560413)
          ·
            refine ⟨2510777758519260505710155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6695407356051361348560413 2510777758519260505710155)
            ·
              refine ⟨3766166637778890758565233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2510777758519260505710155 3766166637778890758565233)
              ·
                refine ⟨2824624978334168068923925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3766166637778890758565233 2824624978334168068923925)
                ·
                  refine ⟨132404295859414128230809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2824624978334168068923925 132404295859414128230809)
                  ·
                    rfl

theorem cell21_580177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_580177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580177 prefixEnd_580177 := by exact prefixLift 580177
  have htrace : WordTrace (prefixWord ++ tailWord_580177) baseStart_580177 baseEnd_580177 := by
    simpa [prefixWord, tailWord_580177, baseEnd_580177] using wordTrace_append hprefix tailTrace_580177
  have hstable : (prefixWord ++ tailWord_580177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580177).length < 2 ^ (prefixWord ++ tailWord_580177).sum := by decide
  have hdescent : baseEnd_580177 < baseStart_580177 := by decide
  rcases family_descends (prefixWord ++ tailWord_580177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580197 : List Nat := [1, 3, 1, 3, 5, 1, 1, 1, 5]
def baseStart_580197 : Nat := 118140960795 + 580197 * 2 ^ 59
def prefixEnd_580197 : Nat := 4983230072969 + 3 ^ 40 * 580197 * 2
def baseEnd_580197 : Nat := 132408860131898537897435

theorem tailTrace_580197 : CollatzResearch.WordTrace tailWord_580197 prefixEnd_580197 132408860131898537897435 := by
  unfold tailWord_580197
  simp only [CollatzResearch.WordTrace]
  refine ⟨21161523079052833603770845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14107682052701889069180563 21161523079052833603770845)
  ·
    refine ⟨7935571154644812601414067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21161523079052833603770845 7935571154644812601414067)
    ·
      refine ⟨11903356731967218902121101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7935571154644812601414067 11903356731967218902121101)
      ·
        refine ⟨4463758774487707088295413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11903356731967218902121101 4463758774487707088295413)
        ·
          refine ⟨418477385108222539527695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4463758774487707088295413 418477385108222539527695)
          ·
            refine ⟨627716077662333809291543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418477385108222539527695 627716077662333809291543)
            ·
              refine ⟨941574116493500713937315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627716077662333809291543 941574116493500713937315)
              ·
                refine ⟨1412361174740251070905973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941574116493500713937315 1412361174740251070905973)
                ·
                  refine ⟨132408860131898537897435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1412361174740251070905973 132408860131898537897435)
                  ·
                    rfl

theorem cell21_580197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_580197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580197 prefixEnd_580197 := by exact prefixLift 580197
  have htrace : WordTrace (prefixWord ++ tailWord_580197) baseStart_580197 baseEnd_580197 := by
    simpa [prefixWord, tailWord_580197, baseEnd_580197] using wordTrace_append hprefix tailTrace_580197
  have hstable : (prefixWord ++ tailWord_580197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580197).length < 2 ^ (prefixWord ++ tailWord_580197).sum := by decide
  have hdescent : baseEnd_580197 < baseStart_580197 := by decide
  rcases family_descends (prefixWord ++ tailWord_580197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580253 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 6]
def baseStart_580253 : Nat := 118140960795 + 580253 * 2 ^ 59
def prefixEnd_580253 : Nat := 4983230072969 + 3 ^ 40 * 580253 * 2
def baseEnd_580253 : Nat := 132421640094854884963987

theorem tailTrace_580253 : CollatzResearch.WordTrace tailWord_580253 prefixEnd_580253 132421640094854884963987 := by
  unfold tailWord_580253
  simp only [CollatzResearch.WordTrace]
  refine ⟨21163565566849955167809413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14109043711233303445206275 21163565566849955167809413)
  ·
    refine ⟨3968168543784366593964265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21163565566849955167809413 3968168543784366593964265)
    ·
      refine ⟨2976126407838274945473199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3968168543784366593964265 2976126407838274945473199)
      ·
        refine ⟨4464189611757412418209799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2976126407838274945473199 4464189611757412418209799)
        ·
          refine ⟨6696284417636118627314699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4464189611757412418209799 6696284417636118627314699)
          ·
            refine ⟨10044426626454177940972049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6696284417636118627314699 10044426626454177940972049)
            ·
              refine ⟨7533319969840633455729037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10044426626454177940972049 7533319969840633455729037)
              ·
                refine ⟨2824994988690237545898389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7533319969840633455729037 2824994988690237545898389)
                ·
                  refine ⟨132421640094854884963987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2824994988690237545898389 132421640094854884963987)
                  ·
                    rfl

theorem cell21_580253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_580253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580253 prefixEnd_580253 := by exact prefixLift 580253
  have htrace : WordTrace (prefixWord ++ tailWord_580253) baseStart_580253 baseEnd_580253 := by
    simpa [prefixWord, tailWord_580253, baseEnd_580253] using wordTrace_append hprefix tailTrace_580253
  have hstable : (prefixWord ++ tailWord_580253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580253).length < 2 ^ (prefixWord ++ tailWord_580253).sum := by decide
  have hdescent : baseEnd_580253 < baseStart_580253 := by decide
  rcases family_descends (prefixWord ++ tailWord_580253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580329 : List Nat := [1, 2, 1, 1, 1, 2, 4, 5, 4]
def baseStart_580329 : Nat := 118140960795 + 580329 * 2 ^ 59
def prefixEnd_580329 : Nat := 4983230072969 + 3 ^ 40 * 580329 * 2
def baseEnd_580329 : Nat := 132438984330295641697165

theorem tailTrace_580329 : CollatzResearch.WordTrace tailWord_580329 prefixEnd_580329 132438984330295641697165 := by
  unfold tailWord_580329
  simp only [CollatzResearch.WordTrace]
  refine ⟨21166337514574620147576041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14110891676383080098384027 21166337514574620147576041)
  ·
    refine ⟨15874753135930965110682031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21166337514574620147576041 15874753135930965110682031)
    ·
      refine ⟨23812129703896447666023047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15874753135930965110682031 23812129703896447666023047)
      ·
        refine ⟨35718194555844671499034571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23812129703896447666023047 35718194555844671499034571)
        ·
          refine ⟨53577291833767007248551857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35718194555844671499034571 53577291833767007248551857)
          ·
            refine ⟨40182968875325255436413893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53577291833767007248551857 40182968875325255436413893)
            ·
              refine ⟨7534306664123485394327605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40182968875325255436413893 7534306664123485394327605)
              ·
                refine ⟨706341249761576755718213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7534306664123485394327605 706341249761576755718213)
                ·
                  refine ⟨132438984330295641697165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 706341249761576755718213 132438984330295641697165)
                  ·
                    rfl

theorem cell21_580329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 4].length) (baseStart_580329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580329 prefixEnd_580329 := by exact prefixLift 580329
  have htrace : WordTrace (prefixWord ++ tailWord_580329) baseStart_580329 baseEnd_580329 := by
    simpa [prefixWord, tailWord_580329, baseEnd_580329] using wordTrace_append hprefix tailTrace_580329
  have hstable : (prefixWord ++ tailWord_580329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580329).length < 2 ^ (prefixWord ++ tailWord_580329).sum := by decide
  have hdescent : baseEnd_580329 < baseStart_580329 := by decide
  rcases family_descends (prefixWord ++ tailWord_580329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580360 : List Nat := [2, 1, 3, 2, 2, 4, 7]
def baseStart_580360 : Nat := 118140960795 + 580360 * 2 ^ 59
def prefixEnd_580360 : Nat := 4983230072969 + 3 ^ 40 * 580360 * 2
def baseEnd_580360 : Nat := 14716228772516275186715

theorem tailTrace_580360 : CollatzResearch.WordTrace tailWord_580360 prefixEnd_580360 14716228772516275186715 := by
  unfold tailWord_580360
  simp only [CollatzResearch.WordTrace]
  refine ⟨10583734088731156220977267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14111645451641541627969689 10583734088731156220977267)
  ·
    refine ⟨15875601133096734331465901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10583734088731156220977267 15875601133096734331465901)
    ·
      refine ⟨5953350424911275374299713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15875601133096734331465901 5953350424911275374299713)
      ·
        refine ⟨4465012818683456530724785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5953350424911275374299713 4465012818683456530724785)
        ·
          refine ⟨3348759614012592398043589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4465012818683456530724785 3348759614012592398043589)
          ·
            refine ⟨627892427627361074633173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3348759614012592398043589 627892427627361074633173)
            ·
              refine ⟨14716228772516275186715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 627892427627361074633173 14716228772516275186715)
              ·
                rfl

theorem cell21_580360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 7].length) (baseStart_580360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580360 prefixEnd_580360 := by exact prefixLift 580360
  have htrace : WordTrace (prefixWord ++ tailWord_580360) baseStart_580360 baseEnd_580360 := by
    simpa [prefixWord, tailWord_580360, baseEnd_580360] using wordTrace_append hprefix tailTrace_580360
  have hstable : (prefixWord ++ tailWord_580360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580360).length < 2 ^ (prefixWord ++ tailWord_580360).sum := by decide
  have hdescent : baseEnd_580360 < baseStart_580360 := by decide
  rcases family_descends (prefixWord ++ tailWord_580360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580425 : List Nat := [1, 2, 1, 1, 2, 7, 2, 2, 3]
def baseStart_580425 : Nat := 118140960795 + 580425 * 2 ^ 59
def prefixEnd_580425 : Nat := 4983230072969 + 3 ^ 40 * 580425 * 2
def baseEnd_580425 : Nat := 132460892838220808096969

theorem tailTrace_580425 : CollatzResearch.WordTrace tailWord_580425 prefixEnd_580425 132460892838220808096969 := by
  unfold tailWord_580425
  simp only [CollatzResearch.WordTrace]
  refine ⟨21169838922226828543070729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14113225948151219028713819 21169838922226828543070729)
  ·
    refine ⟨15877379191670121407303047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21169838922226828543070729 15877379191670121407303047)
    ·
      refine ⟨23816068787505182110954571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15877379191670121407303047 23816068787505182110954571)
      ·
        refine ⟨35724103181257773166431857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23816068787505182110954571 35724103181257773166431857)
        ·
          refine ⟨26793077385943329874823893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35724103181257773166431857 26793077385943329874823893)
          ·
            refine ⟨627962751233046793941185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 26793077385943329874823893 627962751233046793941185)
            ·
              refine ⟨470972063424785095455889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 627962751233046793941185 470972063424785095455889)
              ·
                refine ⟨353229047568588821591917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 470972063424785095455889 353229047568588821591917)
                ·
                  refine ⟨132460892838220808096969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 353229047568588821591917 132460892838220808096969)
                  ·
                    rfl

theorem cell21_580425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 3].length) (baseStart_580425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580425 prefixEnd_580425 := by exact prefixLift 580425
  have htrace : WordTrace (prefixWord ++ tailWord_580425) baseStart_580425 baseEnd_580425 := by
    simpa [prefixWord, tailWord_580425, baseEnd_580425] using wordTrace_append hprefix tailTrace_580425
  have hstable : (prefixWord ++ tailWord_580425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580425).length < 2 ^ (prefixWord ++ tailWord_580425).sum := by decide
  have hdescent : baseEnd_580425 < baseStart_580425 := by decide
  rcases family_descends (prefixWord ++ tailWord_580425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580467 : List Nat := [1, 1, 1, 2, 2, 1, 5, 5, 3]
def baseStart_580467 : Nat := 118140960795 + 580467 * 2 ^ 59
def prefixEnd_580467 : Nat := 4983230072969 + 3 ^ 40 * 580467 * 2
def baseEnd_580467 : Nat := 132470477810438068396883

theorem tailTrace_580467 : CollatzResearch.WordTrace tailWord_580467 prefixEnd_580467 132470477810438068396883 := by
  unfold tailWord_580467
  simp only [CollatzResearch.WordTrace]
  refine ⟨21171370788074669716099655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14114247192049779810733103 21171370788074669716099655)
  ·
    refine ⟨31757056182112004574149483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21171370788074669716099655 31757056182112004574149483)
    ·
      refine ⟨47635584273168006861224225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31757056182112004574149483 47635584273168006861224225)
      ·
        refine ⟨35726688204876005145918169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47635584273168006861224225 35726688204876005145918169)
        ·
          refine ⟨26795016153657003859438627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35726688204876005145918169 26795016153657003859438627)
          ·
            refine ⟨40192524230485505789157941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26795016153657003859438627 40192524230485505789157941)
            ·
              refine ⟨3768049146608016167733557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40192524230485505789157941 3768049146608016167733557)
              ·
                refine ⟨353254607494501515725021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3768049146608016167733557 353254607494501515725021)
                ·
                  refine ⟨132470477810438068396883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 353254607494501515725021 132470477810438068396883)
                  ·
                    rfl

theorem cell21_580467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 3].length) (baseStart_580467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580467 prefixEnd_580467 := by exact prefixLift 580467
  have htrace : WordTrace (prefixWord ++ tailWord_580467) baseStart_580467 baseEnd_580467 := by
    simpa [prefixWord, tailWord_580467, baseEnd_580467] using wordTrace_append hprefix tailTrace_580467
  have hstable : (prefixWord ++ tailWord_580467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580467).length < 2 ^ (prefixWord ++ tailWord_580467).sum := by decide
  have hdescent : baseEnd_580467 < baseStart_580467 := by decide
  rcases family_descends (prefixWord ++ tailWord_580467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580512 : List Nat := [2, 1, 1, 4, 1, 1, 6, 5]
def baseStart_580512 : Nat := 118140960795 + 580512 * 2 ^ 59
def prefixEnd_580512 : Nat := 4983230072969 + 3 ^ 40 * 580512 * 2
def baseEnd_580512 : Nat := 44160249141175996715597

theorem tailTrace_580512 : CollatzResearch.WordTrace tailWord_580512 prefixEnd_580512 44160249141175996715597 := by
  unfold tailWord_580512
  simp only [CollatzResearch.WordTrace]
  refine ⟨10586506036455821200743895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14115341381941094934325193 10586506036455821200743895)
  ·
    refine ⟨15879759054683731801115843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10586506036455821200743895 15879759054683731801115843)
    ·
      refine ⟨23819638582025597701673765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15879759054683731801115843 23819638582025597701673765)
      ·
        refine ⟨4466182234129799569063831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23819638582025597701673765 4466182234129799569063831)
        ·
          refine ⟨6699273351194699353595747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4466182234129799569063831 6699273351194699353595747)
          ·
            refine ⟨10048910026792049030393621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6699273351194699353595747 10048910026792049030393621)
            ·
              refine ⟨471042657505877298299701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10048910026792049030393621 471042657505877298299701)
              ·
                refine ⟨44160249141175996715597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 471042657505877298299701 44160249141175996715597)
                ·
                  rfl

theorem cell21_580512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 5].length) (baseStart_580512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580512 prefixEnd_580512 := by exact prefixLift 580512
  have htrace : WordTrace (prefixWord ++ tailWord_580512) baseStart_580512 baseEnd_580512 := by
    simpa [prefixWord, tailWord_580512, baseEnd_580512] using wordTrace_append hprefix tailTrace_580512
  have hstable : (prefixWord ++ tailWord_580512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580512).length < 2 ^ (prefixWord ++ tailWord_580512).sum := by decide
  have hdescent : baseEnd_580512 < baseStart_580512 := by decide
  rcases family_descends (prefixWord ++ tailWord_580512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580529 : List Nat := [1, 2, 2, 4, 4, 1, 7]
def baseStart_580529 : Nat := 118140960795 + 580529 * 2 ^ 59
def prefixEnd_580529 : Nat := 4983230072969 + 3 ^ 40 * 580529 * 2
def baseEnd_580529 : Nat := 14720514117237748707047

theorem tailTrace_580529 : CollatzResearch.WordTrace tailWord_580529 prefixEnd_580529 14720514117237748707047 := by
  unfold tailWord_580529
  simp only [CollatzResearch.WordTrace]
  refine ⟨21173632113850054304856641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14115754742566702869904427 21173632113850054304856641)
  ·
    refine ⟨15880224085387540728642481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21173632113850054304856641 15880224085387540728642481)
    ·
      refine ⟨11910168064040655546481861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15880224085387540728642481 11910168064040655546481861)
      ·
        refine ⟨2233156512007622914965349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11910168064040655546481861 2233156512007622914965349)
        ·
          refine ⟨418716846001429296556003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2233156512007622914965349 418716846001429296556003)
          ·
            refine ⟨628075269002143944834005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418716846001429296556003 628075269002143944834005)
            ·
              refine ⟨14720514117237748707047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 628075269002143944834005 14720514117237748707047)
              ·
                rfl

theorem cell21_580529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 7].length) (baseStart_580529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580529 prefixEnd_580529 := by exact prefixLift 580529
  have htrace : WordTrace (prefixWord ++ tailWord_580529) baseStart_580529 baseEnd_580529 := by
    simpa [prefixWord, tailWord_580529, baseEnd_580529] using wordTrace_append hprefix tailTrace_580529
  have hstable : (prefixWord ++ tailWord_580529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580529).length < 2 ^ (prefixWord ++ tailWord_580529).sum := by decide
  have hdescent : baseEnd_580529 < baseStart_580529 := by decide
  rcases family_descends (prefixWord ++ tailWord_580529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580650 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 6]
def baseStart_580650 : Nat := 118140960795 + 580650 * 2 ^ 59
def prefixEnd_580650 : Nat := 4983230072969 + 3 ^ 40 * 580650 * 2
def baseEnd_580650 : Nat := 132512240903670416846509

theorem tailTrace_580650 : CollatzResearch.WordTrace tailWord_580650 prefixEnd_580650 132512240903670416846509 := by
  unfold tailWord_580650
  simp only [CollatzResearch.WordTrace]
  refine ⟨5294511336602922992502851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14118696897607794646674269 5294511336602922992502851)
  ·
    refine ⟨7941767004904384488754277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5294511336602922992502851 7941767004904384488754277)
    ·
      refine ⟨1489081313419572091641427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7941767004904384488754277 1489081313419572091641427)
      ·
        refine ⟨2233621970129358137462141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1489081313419572091641427 2233621970129358137462141)
        ·
          refine ⟨837608238798509301548303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2233621970129358137462141 837608238798509301548303)
          ·
            refine ⟨1256412358197763952322455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837608238798509301548303 1256412358197763952322455)
            ·
              refine ⟨1884618537296645928483683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1256412358197763952322455 1884618537296645928483683)
              ·
                refine ⟨2826927805944968892725525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1884618537296645928483683 2826927805944968892725525)
                ·
                  refine ⟨132512240903670416846509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2826927805944968892725525 132512240903670416846509)
                  ·
                    rfl

theorem cell21_580650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_580650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580650 prefixEnd_580650 := by exact prefixLift 580650
  have htrace : WordTrace (prefixWord ++ tailWord_580650) baseStart_580650 baseEnd_580650 := by
    simpa [prefixWord, tailWord_580650, baseEnd_580650] using wordTrace_append hprefix tailTrace_580650
  have hstable : (prefixWord ++ tailWord_580650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580650).length < 2 ^ (prefixWord ++ tailWord_580650).sum := by decide
  have hdescent : baseEnd_580650 < baseStart_580650 := by decide
  rcases family_descends (prefixWord ++ tailWord_580650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580709 : List Nat := [1, 3, 1, 3, 2, 1, 2, 4, 4]
def baseStart_580709 : Nat := 118140960795 + 580709 * 2 ^ 59
def prefixEnd_580709 : Nat := 4983230072969 + 3 ^ 40 * 580709 * 2
def baseEnd_580709 : Nat := 132525705507499425363055

theorem tailTrace_580709 : CollatzResearch.WordTrace tailWord_580709 prefixEnd_580709 132525705507499425363055 := by
  unfold tailWord_580709
  simp only [CollatzResearch.WordTrace]
  refine ⟨21180197253197945046409181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14120131502131963364272787 21180197253197945046409181)
  ·
    refine ⟨7942573969949229392403443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21180197253197945046409181 7942573969949229392403443)
    ·
      refine ⟨11913860954923844088605165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7942573969949229392403443 11913860954923844088605165)
      ·
        refine ⟨4467697858096441533226937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11913860954923844088605165 4467697858096441533226937)
        ·
          refine ⟨3350773393572331149920203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4467697858096441533226937 3350773393572331149920203)
          ·
            refine ⟨5026160090358496724880305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3350773393572331149920203 5026160090358496724880305)
            ·
              refine ⟨3769620067768872543660229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5026160090358496724880305 3769620067768872543660229)
              ·
                refine ⟨706803762706663601936293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3769620067768872543660229 706803762706663601936293)
                ·
                  refine ⟨132525705507499425363055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 706803762706663601936293 132525705507499425363055)
                  ·
                    rfl

theorem cell21_580709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_580709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580709 prefixEnd_580709 := by exact prefixLift 580709
  have htrace : WordTrace (prefixWord ++ tailWord_580709) baseStart_580709 baseEnd_580709 := by
    simpa [prefixWord, tailWord_580709, baseEnd_580709] using wordTrace_append hprefix tailTrace_580709
  have hstable : (prefixWord ++ tailWord_580709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580709).length < 2 ^ (prefixWord ++ tailWord_580709).sum := by decide
  have hdescent : baseEnd_580709 < baseStart_580709 := by decide
  rcases family_descends (prefixWord ++ tailWord_580709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580726 : List Nat := [5, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_580726 : Nat := 118140960795 + 580726 * 2 ^ 59
def prefixEnd_580726 : Nat := 4983230072969 + 3 ^ 40 * 580726 * 2
def baseEnd_580726 : Nat := 132529585139111173579687

theorem tailTrace_580726 : CollatzResearch.WordTrace tailWord_580726 prefixEnd_580726 132529585139111173579687 := by
  unfold tailWord_580726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1323801080883522309361127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14120544862757571299852021 1323801080883522309361127)
  ·
    refine ⟨1985701621325283464041691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1323801080883522309361127 1985701621325283464041691)
    ·
      refine ⟨2978552431987925196062537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1985701621325283464041691 2978552431987925196062537)
      ·
        refine ⟨2233914323990943897046903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2978552431987925196062537 2233914323990943897046903)
        ·
          refine ⟨3350871485986415845570355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2233914323990943897046903 3350871485986415845570355)
          ·
            refine ⟨5026307228979623768355533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3350871485986415845570355 5026307228979623768355533)
            ·
              refine ⟨1884865210867358913133325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5026307228979623768355533 1884865210867358913133325)
              ·
                refine ⟨706824454075259592424997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1884865210867358913133325 706824454075259592424997)
                ·
                  refine ⟨132529585139111173579687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 706824454075259592424997 132529585139111173579687)
                  ·
                    rfl

theorem cell21_580726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_580726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580726 prefixEnd_580726 := by exact prefixLift 580726
  have htrace : WordTrace (prefixWord ++ tailWord_580726) baseStart_580726 baseEnd_580726 := by
    simpa [prefixWord, tailWord_580726, baseEnd_580726] using wordTrace_append hprefix tailTrace_580726
  have hstable : (prefixWord ++ tailWord_580726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580726).length < 2 ^ (prefixWord ++ tailWord_580726).sum := by decide
  have hdescent : baseEnd_580726 < baseStart_580726 := by decide
  rcases family_descends (prefixWord ++ tailWord_580726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580850 : List Nat := [3, 2, 1, 3, 4, 1, 2, 5]
def baseStart_580850 : Nat := 118140960795 + 580850 * 2 ^ 59
def prefixEnd_580850 : Nat := 4983230072969 + 3 ^ 40 * 580850 * 2
def baseEnd_580850 : Nat := 44185961209504837837589

theorem tailTrace_580850 : CollatzResearch.WordTrace tailWord_580850 prefixEnd_580850 44185961209504837837589 := by
  unfold tailWord_580850
  simp only [CollatzResearch.WordTrace]
  refine ⟨5296334986421781531823001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14123559963791417418194669 5296334986421781531823001)
  ·
    refine ⟨3972251239816336148867251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5296334986421781531823001 3972251239816336148867251)
    ·
      refine ⟨5958376859724504223300877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3972251239816336148867251 5958376859724504223300877)
      ·
        refine ⟨2234391322396689083737829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5958376859724504223300877 2234391322396689083737829)
        ·
          refine ⟨418948372949379203200843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2234391322396689083737829 418948372949379203200843)
          ·
            refine ⟨628422559424068804801265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418948372949379203200843 628422559424068804801265)
            ·
              refine ⟨471316919568051603600949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 628422559424068804801265 471316919568051603600949)
              ·
                refine ⟨44185961209504837837589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 471316919568051603600949 44185961209504837837589)
                ·
                  rfl

theorem cell21_580850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_580850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580850 prefixEnd_580850 := by exact prefixLift 580850
  have htrace : WordTrace (prefixWord ++ tailWord_580850) baseStart_580850 baseEnd_580850 := by
    simpa [prefixWord, tailWord_580850, baseEnd_580850] using wordTrace_append hprefix tailTrace_580850
  have hstable : (prefixWord ++ tailWord_580850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580850).length < 2 ^ (prefixWord ++ tailWord_580850).sum := by decide
  have hdescent : baseEnd_580850 < baseStart_580850 := by decide
  rcases family_descends (prefixWord ++ tailWord_580850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580875 : List Nat := [1, 1, 1, 1, 5, 5, 7]
def baseStart_580875 : Nat := 118140960795 + 580875 * 2 ^ 59
def prefixEnd_580875 : Nat := 4983230072969 + 3 ^ 40 * 580875 * 2
def baseEnd_580875 : Nat := 14729287663235558399561

theorem tailTrace_580875 : CollatzResearch.WordTrace tailWord_580875 prefixEnd_580875 14729287663235558399561 := by
  unfold tailWord_580875
  simp only [CollatzResearch.WordTrace]
  refine ⟨21186251770596555396952079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14124167847064370264634719 21186251770596555396952079)
  ·
    refine ⟨31779377655894833095428119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21186251770596555396952079 31779377655894833095428119)
    ·
      refine ⟨47669066483842249643142179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31779377655894833095428119 47669066483842249643142179)
      ·
        refine ⟨71503599725763374464713269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47669066483842249643142179 71503599725763374464713269)
        ·
          refine ⟨6703462474290316356066869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71503599725763374464713269 6703462474290316356066869)
          ·
            refine ⟨628449606964717158381269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6703462474290316356066869 628449606964717158381269)
            ·
              refine ⟨14729287663235558399561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 628449606964717158381269 14729287663235558399561)
              ·
                rfl

theorem cell21_580875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 7].length) (baseStart_580875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580875 prefixEnd_580875 := by exact prefixLift 580875
  have htrace : WordTrace (prefixWord ++ tailWord_580875) baseStart_580875 baseEnd_580875 := by
    simpa [prefixWord, tailWord_580875, baseEnd_580875] using wordTrace_append hprefix tailTrace_580875
  have hstable : (prefixWord ++ tailWord_580875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580875).length < 2 ^ (prefixWord ++ tailWord_580875).sum := by decide
  have hdescent : baseEnd_580875 < baseStart_580875 := by decide
  rcases family_descends (prefixWord ++ tailWord_580875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580895 : List Nat := [1, 1, 2, 4, 4, 2, 2, 1, 4]
def baseStart_580895 : Nat := 118140960795 + 580895 * 2 ^ 59
def prefixEnd_580895 : Nat := 4983230072969 + 3 ^ 40 * 580895 * 2
def baseEnd_580895 : Nat := 132568153241604435262675

theorem tailTrace_580895 : CollatzResearch.WordTrace tailWord_580895 prefixEnd_580895 132568153241604435262675 := by
  unfold tailWord_580895
  simp only [CollatzResearch.WordTrace]
  refine ⟨21186981230524098812680139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14124654153682732541786759 21186981230524098812680139)
  ·
    refine ⟨31780471845786148219020209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21186981230524098812680139 31780471845786148219020209)
    ·
      refine ⟨23835353884339611164265157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31780471845786148219020209 23835353884339611164265157)
      ·
        refine ⟨4469128853313677093299717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23835353884339611164265157 4469128853313677093299717)
        ·
          refine ⟨837961659996314454993697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4469128853313677093299717 837961659996314454993697)
          ·
            refine ⟨628471244997235841245273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 837961659996314454993697 628471244997235841245273)
            ·
              refine ⟨471353433747926880933955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 628471244997235841245273 471353433747926880933955)
              ·
                refine ⟨707030150621890321400933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 471353433747926880933955 707030150621890321400933)
                ·
                  refine ⟨132568153241604435262675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 707030150621890321400933 132568153241604435262675)
                  ·
                    rfl

theorem cell21_580895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 4].length) (baseStart_580895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580895 prefixEnd_580895 := by exact prefixLift 580895
  have htrace : WordTrace (prefixWord ++ tailWord_580895) baseStart_580895 baseEnd_580895 := by
    simpa [prefixWord, tailWord_580895, baseEnd_580895] using wordTrace_append hprefix tailTrace_580895
  have hstable : (prefixWord ++ tailWord_580895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580895).length < 2 ^ (prefixWord ++ tailWord_580895).sum := by decide
  have hdescent : baseEnd_580895 < baseStart_580895 := by decide
  rcases family_descends (prefixWord ++ tailWord_580895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580940 : List Nat := [2, 2, 1, 3, 2, 2, 4, 2, 3]
def baseStart_580940 : Nat := 118140960795 + 580940 * 2 ^ 59
def prefixEnd_580940 : Nat := 4983230072969 + 3 ^ 40 * 580940 * 2
def baseEnd_580940 : Nat := 132578422854694357012583

theorem tailTrace_580940 : CollatzResearch.WordTrace tailWord_580940 prefixEnd_580940 132578422854694357012583 := by
  unfold tailWord_580940
  simp only [CollatzResearch.WordTrace]
  refine ⟨10594311257680535749034137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14125748343574047665378849 10594311257680535749034137)
  ·
    refine ⟨7945733443260401811775603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10594311257680535749034137 7945733443260401811775603)
    ·
      refine ⟨11918600164890602717663405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7945733443260401811775603 11918600164890602717663405)
      ·
        refine ⟨4469475061833976019123777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11918600164890602717663405 4469475061833976019123777)
        ·
          refine ⟨3352106296375482014342833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4469475061833976019123777 3352106296375482014342833)
          ·
            refine ⟨2514079722281611510757125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3352106296375482014342833 2514079722281611510757125)
            ·
              refine ⟨471389947927802158266961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2514079722281611510757125 471389947927802158266961)
              ·
                refine ⟨353542460945851618700221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 471389947927802158266961 353542460945851618700221)
                ·
                  refine ⟨132578422854694357012583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 353542460945851618700221 132578422854694357012583)
                  ·
                    rfl

theorem cell21_580940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_580940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580940 prefixEnd_580940 := by exact prefixLift 580940
  have htrace : WordTrace (prefixWord ++ tailWord_580940) baseStart_580940 baseEnd_580940 := by
    simpa [prefixWord, tailWord_580940, baseEnd_580940] using wordTrace_append hprefix tailTrace_580940
  have hstable : (prefixWord ++ tailWord_580940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580940).length < 2 ^ (prefixWord ++ tailWord_580940).sum := by decide
  have hdescent : baseEnd_580940 < baseStart_580940 := by decide
  rcases family_descends (prefixWord ++ tailWord_580940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580951 : List Nat := [1, 1, 3, 2, 3, 2, 3, 6]
def baseStart_580951 : Nat := 118140960795 + 580951 * 2 ^ 59
def prefixEnd_580951 : Nat := 4983230072969 + 3 ^ 40 * 580951 * 2
def baseEnd_580951 : Nat := 44193644401520260776409

theorem tailTrace_580951 : CollatzResearch.WordTrace tailWord_580951 prefixEnd_580951 44193644401520260776409 := by
  unfold tailWord_580951
  simp only [CollatzResearch.WordTrace]
  refine ⟨21189023718321220376718707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14126015812214146917812471 21189023718321220376718707)
  ·
    refine ⟨31783535577481830565078061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21189023718321220376718707 31783535577481830565078061)
    ·
      refine ⟨11918825841555686461904273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31783535577481830565078061 11918825841555686461904273)
      ·
        refine ⟨8939119381166764846428205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11918825841555686461904273 8939119381166764846428205)
        ·
          refine ⟨3352169767937536817410577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8939119381166764846428205 3352169767937536817410577)
          ·
            refine ⟨2514127325953152613057933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3352169767937536817410577 2514127325953152613057933)
            ·
              refine ⟨942797747232432229896725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2514127325953152613057933 942797747232432229896725)
              ·
                refine ⟨44193644401520260776409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 942797747232432229896725 44193644401520260776409)
                ·
                  rfl

theorem cell21_580951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 6].length) (baseStart_580951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580951 prefixEnd_580951 := by exact prefixLift 580951
  have htrace : WordTrace (prefixWord ++ tailWord_580951) baseStart_580951 baseEnd_580951 := by
    simpa [prefixWord, tailWord_580951, baseEnd_580951] using wordTrace_append hprefix tailTrace_580951
  have hstable : (prefixWord ++ tailWord_580951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580951).length < 2 ^ (prefixWord ++ tailWord_580951).sum := by decide
  have hdescent : baseEnd_580951 < baseStart_580951 := by decide
  rcases family_descends (prefixWord ++ tailWord_580951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580957 : List Nat := [1, 4, 5, 1, 1, 1, 1, 2, 5]
def baseStart_580957 : Nat := 118140960795 + 580957 * 2 ^ 59
def prefixEnd_580957 : Nat := 4983230072969 + 3 ^ 40 * 580957 * 2
def baseEnd_580957 : Nat := 132582302486306105229215

theorem tailTrace_580957 : CollatzResearch.WordTrace tailWord_580957 prefixEnd_580957 132582302486306105229215 := by
  unfold tailWord_580957
  simp only [CollatzResearch.WordTrace]
  refine ⟨21189242556299483401437125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14126161704199655600958083 21189242556299483401437125)
  ·
    refine ⟨3972982979306153137769461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21189242556299483401437125 3972982979306153137769461)
    ·
      refine ⟨372467154309951856665887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3972982979306153137769461 372467154309951856665887)
      ·
        refine ⟨558700731464927784998831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372467154309951856665887 558700731464927784998831)
        ·
          refine ⟨838051097197391677498247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558700731464927784998831 838051097197391677498247)
          ·
            refine ⟨1257076645796087516247371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 838051097197391677498247 1257076645796087516247371)
            ·
              refine ⟨1885614968694131274371057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1257076645796087516247371 1885614968694131274371057)
              ·
                refine ⟨1414211226520598455778293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1885614968694131274371057 1414211226520598455778293)
                ·
                  refine ⟨132582302486306105229215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1414211226520598455778293 132582302486306105229215)
                  ·
                    rfl

theorem cell21_580957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_580957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580957 prefixEnd_580957 := by exact prefixLift 580957
  have htrace : WordTrace (prefixWord ++ tailWord_580957) baseStart_580957 baseEnd_580957 := by
    simpa [prefixWord, tailWord_580957, baseEnd_580957] using wordTrace_append hprefix tailTrace_580957
  have hstable : (prefixWord ++ tailWord_580957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580957).length < 2 ^ (prefixWord ++ tailWord_580957).sum := by decide
  have hdescent : baseEnd_580957 < baseStart_580957 := by decide
  rcases family_descends (prefixWord ++ tailWord_580957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580999 : List Nat := [1, 1, 4, 2, 2, 2, 2, 4, 3]
def baseStart_580999 : Nat := 118140960795 + 580999 * 2 ^ 59
def prefixEnd_580999 : Nat := 4983230072969 + 3 ^ 40 * 580999 * 2
def baseEnd_580999 : Nat := 132591887458523365529129

theorem tailTrace_580999 : CollatzResearch.WordTrace tailWord_580999 prefixEnd_580999 132591887458523365529129 := by
  unfold tailWord_580999
  simp only [CollatzResearch.WordTrace]
  refine ⟨21190774422147324574466051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14127182948098216382977367 21190774422147324574466051)
  ·
    refine ⟨31786161633220986861699077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21190774422147324574466051 31786161633220986861699077)
    ·
      refine ⟨5959905306228935036568577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31786161633220986861699077 5959905306228935036568577)
      ·
        refine ⟨4469928979671701277426433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5959905306228935036568577 4469928979671701277426433)
        ·
          refine ⟨3352446734753775958069825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4469928979671701277426433 3352446734753775958069825)
          ·
            refine ⟨2514335051065331968552369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3352446734753775958069825 2514335051065331968552369)
            ·
              refine ⟨1885751288298998976414277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2514335051065331968552369 1885751288298998976414277)
              ·
                refine ⟨353578366556062308077677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1885751288298998976414277 353578366556062308077677)
                ·
                  refine ⟨132591887458523365529129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 353578366556062308077677 132591887458523365529129)
                  ·
                    rfl

theorem cell21_580999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 3].length) (baseStart_580999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_580999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_580999 prefixEnd_580999 := by exact prefixLift 580999
  have htrace : WordTrace (prefixWord ++ tailWord_580999) baseStart_580999 baseEnd_580999 := by
    simpa [prefixWord, tailWord_580999, baseEnd_580999] using wordTrace_append hprefix tailTrace_580999
  have hstable : (prefixWord ++ tailWord_580999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580999).length < 2 ^ (prefixWord ++ tailWord_580999).sum := by decide
  have hdescent : baseEnd_580999 < baseStart_580999 := by decide
  rcases family_descends (prefixWord ++ tailWord_580999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
